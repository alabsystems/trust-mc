// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Design 5 (docs/chc-hole-fix-designs-2026-09-24.md, "Legacy loop-contract
//! latch"): loop contracts outside the body the CHC lane encodes.
//!
//! The harness body's own loops (with whatever `FunctionInlinePass` inlined)
//! are rewritten by `LoopContractPass` and booked by
//! `loop_modifies_frame::prescan_loop_contract_legacy_latches`. Anywhere else a
//! contracted loop is never checked: a body the walker WALKS is the callee's
//! raw body (`walker_transformed_body` opts in contract items only), so its
//! register call answers `{ true }` and the invariant is never evaluated; a
//! callee the walker HAVOCS drops the loop with the rest of its body. Under
//! `-Z loop-contracts` both lose an obligation Kani checks, so a harness that
//! can reach one never reports SUCCESSFUL. Three bookings, all unblessed:
//!
//! * [`prescan_loop_contracts_beyond_body`] (`LOOP_CONTRACT_BEYOND_BODY`),
//!   once per harness body: a live call or drop of the encoded body that can
//!   reach a loop contract; one more when a function whose address the harness
//!   takes can reach one (then a call through any pointer or `dyn` receiver
//!   may run it); one when there is no call graph at all. It does not depend
//!   on which bodies the walker later walks, drops or bails out of, and it
//!   sees through non-local generic code (`Iterator::count` over a local
//!   iterator) and through vtables and fn pointers made anywhere the collector
//!   looked.
//! * `WALKED_LOOP_CONTRACT`: a register call the walker meets in a walked body.
//! * `HAVOCKED_LOOP_CONTRACT`: a havocked callee that [`Scan`] finds reaches a
//!   register call.
//!
//! [`Scan`] answers "can this call reach a loop contract?". It asks the
//! reachability collector's call graph first (`kani_middle/loop_contract_reach.rs`),
//! whose yes and whose "clear" no are final. Where the graph cannot say (the
//! reach passes a function the collector abstracted at the stub boundary, or
//! the collector never read the function) it reads RAW bodies: local bodies,
//! closures, fn items, drop glue, and the monomorphized body of any non-local
//! instance whose generic arguments name an item of this crate. A non-local
//! body whose arguments name none cannot call this crate statically (the
//! orphan rule keeps its impls out of reach); a call through a pointer or a
//! vtable is the address-taken answer's. Running out of budget answers yes.
//!
//! None of them is waived except in the two-lane retry's properties lane
//! (`loop_contracts::is_two_lane_properties_lane`), whose success only counts
//! beside the obligations lane's, which books them; the driver never prints a
//! properties-lane success as a proof (`loop_two_lane::demote_properties_lane_success`).

use crate::codegen_ay::shared::mono_ty;
use rustc_public::CrateDef;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{Body, LocalDecl, Operand, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, GenericArgs, RigidTy, Ty, TyKind};
use std::collections::HashSet;
use tracing::debug;

use super::super::ChcCtx;
use crate::callee_body::CalleeBody;
use crate::kani_middle::attributes;
use crate::kani_middle::loop_contract_reach::{LoopContractReach, REGISTER_MARKER};

/// A `kani_register_loop_contract` call in a walked body. Unblessed.
pub(super) const WALKED_LOOP_CONTRACT: &str = "loop_contract_in_walked_body";

/// A havocked callee that reaches a `kani_register_loop_contract` call (or a
/// scan that ran out of budget before it could tell). Unblessed.
pub(super) const HAVOCKED_LOOP_CONTRACT: &str = "loop_contract_in_havocked_callee";

/// A loop contract the encoded body can reach outside itself: through a live
/// call or drop, through a function whose address is taken, or with no call
/// graph to say otherwise. Unblessed.
pub(in crate::codegen_ay::chc) const LOOP_CONTRACT_BEYOND_BODY: &str =
    "loop_contract_beyond_harness_body";

/// Bodies [`Scan`] reads before it gives up and answers yes.
const MAX_SCAN_BODIES: usize = 256;

/// Type nesting the generic-argument walks follow.
const MAX_TY_DEPTH: usize = 8;

/// Book `reason` unless this is the properties lane.
pub(super) fn book(ctx: &ChcCtx<'_, '_>, reason: &'static str) {
    if !crate::kani_middle::transform::loop_contracts::is_two_lane_properties_lane() {
        ctx.record_sound_fallback_reason(reason);
    }
}

/// The `(FnDef, args)` a call operand names, normalized against the walk the
/// same way the rest of the walker does (body-ty first, raw FnDef fallback).
fn callee_fn_def(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> Option<(rustc_public::ty::FnDef, GenericArgs)> {
    let raw = func.ty(locals).ok()?;
    match ctx.resolve_body_ty(raw).kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => Some((def, args)),
        _ => match raw.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => Some((def, args)),
            _ => None,
        },
    }
}

fn is_register_def(def: rustc_public::ty::FnDef) -> bool {
    attributes::fn_marker(def).as_deref() == Some(REGISTER_MARKER)
        || def.name().contains(REGISTER_MARKER)
}

/// Is this call, inside a walked body, a `kani_register_loop_contract` call
/// (any `_transformed` role)?
pub(super) fn is_loop_contract_register_call(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> bool {
    callee_fn_def(ctx, func, locals).is_some_and(|(def, _)| is_register_def(def))
}

/// Does the callee the walker is about to havoc reach a loop contract?
pub(super) fn havocked_callee_reaches_loop_contract(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> bool {
    let Some((def, args)) = callee_fn_def(ctx, func, locals) else {
        // A fn pointer or an untypable operand: `INDIRECT_CALL_HAVOCKED`
        // books the indirect case, and the harness-body prescan books every
        // loop contract a fn pointer or vtable can reach.
        return false;
    };
    let graph = crate::kani_middle::dyn_universe::current_harness_universe()
        .and_then(|universe| universe.loop_contract_reach());
    Scan::new(ctx, graph.as_deref()).call(def, &args)
}

/// Design 5 backstop: book, once per harness body, every way the body can
/// reach a loop contract outside itself (see the module docs):
///
/// * each live call or drop that [`Scan`] says reaches one; the register
///   calls themselves are the body's own loops and are skipped;
/// * one more when some function whose address the harness takes reaches one
///   (`LoopContractReach::address_taken`);
/// * one when there is no call graph (a body encoded outside a per-harness
///   codegen): fail closed.
///
/// Accounted with no freed variable, as the legacy latch is and for the same
/// reason: the missing check frees no value, and a run that fails a check of
/// the concrete loop also fails Kani's contract. Unaccounted under
/// `#[kani::should_panic]` or with no harness instance, so a panic is never
/// certified there (`loop_modifies_frame::prescan_loop_contract_legacy_latches`).
pub(in crate::codegen_ay::chc) fn prescan_loop_contracts_beyond_body(ctx: &mut ChcCtx<'_, '_>) {
    if !ctx.loop_contracts
        || crate::kani_middle::transform::loop_contracts::is_two_lane_properties_lane()
    {
        return;
    }
    let reach = crate::kani_middle::dyn_universe::current_harness_universe()
        .and_then(|universe| universe.loop_contract_reach());
    let hits = count_loop_contracts_beyond_body(ctx, reach.as_deref());
    if hits == 0 {
        return;
    }
    let should_panic = ctx.current_instance.is_none_or(|instance| {
        crate::kani_middle::attributes::KaniAttributes::for_instance(ctx.tcx, instance)
            .has_should_panic()
    });
    for _ in 0..hits {
        if should_panic {
            ctx.record_sound_fallback_reason(LOOP_CONTRACT_BEYOND_BODY);
        } else {
            ctx.record_sound_fallback_reason_identified(LOOP_CONTRACT_BEYOND_BODY, None);
        }
    }
    debug!(hits, should_panic, "design 5: loop contract(s) beyond the harness body booked");
}

/// How many bookings [`prescan_loop_contracts_beyond_body`] makes for this
/// body under `reach` (`None`: no call graph). Each question gets a fresh
/// [`Scan`]: a scan's visited set is only sound within one question.
pub(in crate::codegen_ay) fn count_loop_contracts_beyond_body(
    ctx: &ChcCtx<'_, '_>,
    reach: Option<&LoopContractReach>,
) -> usize {
    let Some(reach) = reach else {
        debug!("design 5: no call graph for this body -> fail closed");
        return 1;
    };
    let body = ctx.body;
    let live = crate::codegen_ay::chc::loop_modifies_frame::reachable_block_mask(body);
    let mut hits = 0usize;
    if let Some(taken) =
        reach.address_taken().find(|taken| Scan::new(ctx, Some(reach)).instance(*taken))
    {
        debug!(address_taken = %taken.name(), "design 5: a loop contract is reachable indirectly");
        hits += 1;
    }
    for (bb, block) in body.blocks.iter().enumerate() {
        if !live[bb] {
            continue;
        }
        let mut scan = Scan::new(ctx, Some(reach));
        let reaches = match &block.terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let Some((def, args)) = callee_fn_def(ctx, func, body.locals()) else {
                    // A call through a pointer: the address-taken answer.
                    continue;
                };
                if is_register_def(def) {
                    continue;
                }
                scan.call(def, &args)
            }
            TerminatorKind::Drop { place, .. } => {
                let Ok(ty) = place.ty(body.locals()) else { continue };
                // Glue that does not resolve (unresolved params) may reach a
                // contract: count it as reaching (fail closed).
                mono_ty::drop_in_place(ctx.resolve_body_ty(ty))
                    .is_none_or(|glue| scan.instance(glue))
            }
            _ => continue,
        };
        if reaches {
            debug!(bb, "design 5: live call or drop reaches a loop contract beyond the body");
            hits += 1;
        }
    }
    hits
}

fn is_local(ctx: &ChcCtx<'_, '_>, def_id: rustc_public::DefId) -> bool {
    rustc_internal::internal(ctx.tcx, def_id).is_local()
}

/// One reach question (see the module docs).
pub(in crate::codegen_ay::chc) struct Scan<'a, 'tcx, 'body> {
    ctx: &'a ChcCtx<'tcx, 'body>,
    /// The collector's answers, when a per-harness codegen installed them.
    graph: Option<&'a LoopContractReach>,
    visited: HashSet<String>,
    bodies: usize,
}

impl<'a, 'tcx, 'body> Scan<'a, 'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn new(
        ctx: &'a ChcCtx<'tcx, 'body>,
        graph: Option<&'a LoopContractReach>,
    ) -> Self {
        Self { ctx, graph, visited: HashSet::new(), bodies: 0 }
    }

    /// Out of budget: answer YES (fail-closed).
    fn over_budget(&mut self) -> bool {
        self.bodies += 1;
        self.bodies > MAX_SCAN_BODIES
    }

    /// Does a call of `def` at `args` reach a register call?
    fn call(&mut self, def: rustc_public::ty::FnDef, args: &GenericArgs) -> bool {
        if is_register_def(def) {
            return true;
        }
        match Instance::resolve(def, args) {
            Ok(instance) => self.instance(instance),
            Err(_) => {
                // Unresolvable at this point of the walk: follow what the
                // arguments name, and the polymorphic body of a local callee.
                self.generic_args(args, 0)
                    || (is_local(self.ctx, def.def_id())
                        && def.callee_body().is_some_and(|body| self.body(&body)))
            }
        }
    }

    pub(in crate::codegen_ay::chc) fn instance(&mut self, instance: Instance) -> bool {
        if !self.visited.insert(instance.mangled_name()) {
            return false;
        }
        if matches!(instance.kind, InstanceKind::Virtual { .. }) {
            // A `dyn` call: the address-taken answer covers every loop
            // contract a vtable can reach.
            return false;
        }
        if let Some(answer) = self.graph.and_then(|graph| graph.reaches(&instance)) {
            return answer;
        }
        let def_id = instance.def.def_id();
        let internal = rustc_internal::internal(self.ctx.tcx, def_id);
        let local = is_local(self.ctx, def_id) || self.ctx.tcx.is_closure_like(internal);
        if !local && !self.args_name_local_item(&instance.args(), 0) {
            // The orphan rule: a non-local body whose generic arguments name
            // no item of this crate cannot call one statically.
            return false;
        }
        if self.over_budget() {
            return true;
        }
        match instance.callee_body() {
            Some(body) => self.body(&body),
            // No body to read (an intrinsic, an extern): follow what the
            // arguments name.
            None => self.generic_args(&instance.args(), 0),
        }
    }

    fn body(&mut self, body: &Body) -> bool {
        for block in &body.blocks {
            let reached = match &block.terminator.kind {
                TerminatorKind::Call { func, .. } => {
                    let Some((def, args)) = callee_fn_def(self.ctx, func, body.locals()) else {
                        continue;
                    };
                    self.call(def, &args)
                }
                TerminatorKind::Drop { place, .. } => {
                    let Ok(ty) = place.ty(body.locals()) else { continue };
                    // Unresolvable glue may reach a contract (fail closed).
                    mono_ty::drop_in_place(self.ctx.resolve_body_ty(ty))
                        .is_none_or(|glue| self.instance(glue))
                }
                _ => continue,
            };
            if reached {
                return true;
            }
        }
        false
    }

    /// Follow the closures and fn items `args` name.
    fn generic_args(&mut self, args: &GenericArgs, depth: usize) -> bool {
        args.0.iter().any(|arg| match arg {
            GenericArgKind::Type(ty) => self.ty(*ty, depth),
            _ => false,
        })
    }

    fn ty(&mut self, ty: Ty, depth: usize) -> bool {
        if depth > MAX_TY_DEPTH {
            return false;
        }
        let TyKind::RigidTy(rigid) = ty.kind() else { return false };
        match rigid {
            RigidTy::Closure(closure_def, closure_args) => {
                if !self.visited.insert(format!("{closure_def:?}{closure_args:?}")) {
                    return false;
                }
                if self.over_budget() {
                    return true;
                }
                closure_def.body().is_some_and(|body| self.body(&body))
                    || self.generic_args(&closure_args, depth + 1)
            }
            RigidTy::FnDef(def, fn_args) => self.call(def, &fn_args),
            RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _) => self.ty(inner, depth + 1),
            RigidTy::Array(inner, _) | RigidTy::Slice(inner) => self.ty(inner, depth + 1),
            RigidTy::Tuple(items) => items.iter().any(|item| self.ty(*item, depth + 1)),
            RigidTy::Adt(_, adt_args) => self.generic_args(&adt_args, depth + 1),
            _ => false,
        }
    }

    /// Do `args` name an item of this crate (an ADT, closure, coroutine, fn
    /// item or trait object of a local trait), at any nesting? Past the depth
    /// limit, yes (fail-closed).
    fn args_name_local_item(&self, args: &GenericArgs, depth: usize) -> bool {
        args.0.iter().any(|arg| match arg {
            GenericArgKind::Type(ty) => self.ty_names_local_item(*ty, depth),
            _ => false,
        })
    }

    fn ty_names_local_item(&self, ty: Ty, depth: usize) -> bool {
        if depth > MAX_TY_DEPTH {
            return true;
        }
        let local = |def_id: rustc_public::DefId| is_local(self.ctx, def_id);
        let TyKind::RigidTy(rigid) = ty.kind() else { return false };
        match rigid {
            RigidTy::Adt(def, args) => {
                local(def.def_id()) || self.args_name_local_item(&args, depth + 1)
            }
            RigidTy::Closure(def, args) => {
                local(def.def_id()) || self.args_name_local_item(&args, depth + 1)
            }
            RigidTy::Coroutine(def, args) => {
                local(def.def_id()) || self.args_name_local_item(&args, depth + 1)
            }
            RigidTy::CoroutineClosure(def, args) => {
                local(def.def_id()) || self.args_name_local_item(&args, depth + 1)
            }
            RigidTy::FnDef(def, args) => {
                local(def.def_id()) || self.args_name_local_item(&args, depth + 1)
            }
            RigidTy::Dynamic(predicates, _) => {
                predicates.iter().any(|predicate| match &predicate.value {
                    rustc_public::ty::ExistentialPredicate::Trait(trait_ref) => {
                        local(trait_ref.def_id.def_id())
                            || self.args_name_local_item(&trait_ref.generic_args, depth + 1)
                    }
                    rustc_public::ty::ExistentialPredicate::Projection(projection) => {
                        self.args_name_local_item(&projection.generic_args, depth + 1)
                            || matches!(&projection.term, rustc_public::ty::TermKind::Type(term)
                                if self.ty_names_local_item(*term, depth + 1))
                    }
                    rustc_public::ty::ExistentialPredicate::AutoTrait(def) => local(def.def_id()),
                })
            }
            RigidTy::FnPtr(sig) => sig
                .value
                .inputs_and_output
                .iter()
                .any(|item| self.ty_names_local_item(*item, depth + 1)),
            RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _) => {
                self.ty_names_local_item(inner, depth + 1)
            }
            RigidTy::Array(inner, _) | RigidTy::Slice(inner) => {
                self.ty_names_local_item(inner, depth + 1)
            }
            RigidTy::Tuple(items) => {
                items.iter().any(|item| self.ty_names_local_item(*item, depth + 1))
            }
            RigidTy::Foreign(def) => local(def.def_id()),
            _ => false,
        }
    }
}
