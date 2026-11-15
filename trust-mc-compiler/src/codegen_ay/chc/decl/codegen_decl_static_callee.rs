// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pre-scan callee bodies for static references before entry rule emission.
//!
//! Part of #4014: `collect_static_state_vars()` only scans the harness body.
//! When the inline walker processes a callee that references statics not in
//! the harness, the static's address falls through to the promoted-constant
//! fallback and the entry rule never constrains the memory array. This module
//! fixes the phase ordering by discovering callee statics during declaration.

use crate::callee_body::CalleeBody;
use std::collections::HashSet;

use rustc_public::CrateDef;
use rustc_public::mir::{AggregateKind, Operand, Rvalue, StatementKind};

use crate::codegen_ay::shared::const_pointer::{self, ConstRead, ConstTarget, TargetKey};
use tracing::debug;

use super::ChcCtx;
use super::codegen_types::CodegenTypes;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Pre-registers statics found in a callee body before inline translation.
    ///
    /// Registers the layout size and memory-init mirror of every static a
    /// constant pointer in `callee_body` names that no body registered yet, so
    /// the entry rule seeds it. The static's ADDRESS is its one object
    /// (`mint_object`, keyed by its definition): there is no per-AllocId
    /// address to alias and no second object to mint (D1).
    ///
    /// Part of #4014: Fix unconstrained static mut in inlined callee bodies.
    pub(in crate::codegen_ay::chc) fn register_callee_body_statics(
        &mut self,
        callee_body: &rustc_public::mir::Body,
    ) {
        use rustc_public::ty::{RigidTy, TyKind};

        for bb_data in &callee_body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(_lhs, rhs) = &stmt.kind else {
                    continue;
                };
                let const_op = match rhs {
                    Rvalue::Use(Operand::Constant(c), ..) => c,
                    _ => continue,
                };

                let mir_const = &const_op.const_;
                if !matches!(
                    mir_const.ty().kind(),
                    TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
                ) {
                    continue;
                }
                let Some(ptr) =
                    const_pointer::const_bytes(mir_const).and_then(|b| b.stored_pointer(0))
                else {
                    continue;
                };
                let ConstTarget::Static(static_def) = ptr.kind() else {
                    continue;
                };

                // Already registered (from the harness body or a previous callee).
                if self.ref_resolution.registered_static_memory.contains(&static_def) {
                    continue;
                }

                let static_name = static_def.name();
                let static_ty = static_def.ty();

                let Some(sort) = Self::translate_ty(static_ty) else {
                    continue;
                };

                // The static's ONE object (D1): minted by the shared walk, or
                // here on first sight — never twice.
                let Some(obj_id) = self.mint_object(TargetKey::Static(static_def)) else {
                    continue;
                };
                self.ref_resolution.registered_static_memory.insert(static_def);
                let addr = crate::codegen_ay::provenance::Loc::of_address(
                    crate::codegen_ay::chc::decl::global_objects::object_base_for(obj_id),
                );

                // Record static layout metadata for entry-rule size/alignment
                // constraints on callee-discovered statics.
                if let Some(type_size) = self.get_type_size(static_ty) {
                    let type_align = self.get_type_align(static_ty).unwrap_or(1);
                    self.ref_resolution.static_alloc_sizes.push((
                        obj_id,
                        type_size as u32,
                        type_align,
                    ));
                }

                // Read initial value and register memory init. The static's
                // own bytes come from `const_pointer::target_bytes`, which
                // declines a foreign (`extern "C"`) static (no initializer
                // body: evaluating one span_bugs, uncatchable by `.ok()`) and
                // a still-generic one. The None-path below leaves the static
                // memory unconstrained. NEVER assume zero.
                let internal_def_id =
                    rustc_public::rustc_internal::internal(self.tcx, static_def.def_id());
                let init_alloc_opt = const_pointer::target_bytes(
                    self.tcx,
                    &const_pointer::TargetKey::Static(static_def),
                )
                .map(|(bytes, _)| bytes);
                if let Some(ref bytes) = init_alloc_opt {
                    self.note_pointer_slots(bytes, static_ty, 0);
                }
                let init_expr_opt = init_alloc_opt
                    .as_ref()
                    .and_then(|bytes| self.static_init_from_alloc(bytes, &sort, static_ty));

                // P2-S1: contract CHECK harness — a callee `static mut` must
                // NOT have its memory pinned to the initializer (the contract
                // holds for arbitrary ambient state; pinning is fail-open).
                // Interior-mut immutable statics flow through the per-field
                // gate inside `register_static_memory_init_entries`.
                // Kani-INTERNAL statics stay pinned, exactly as on the
                // harness-side path (codegen_decl_static.rs, P2-S1): the
                // contract machinery's `#[kanitool::recursion_tracker]`
                // reentry flag must start at its initializer (`false`).
                // Havocking it lets the solver enter the RECURSION/REPLACE
                // arm on the OUTERMOST call, where `requires` is an
                // ASSERTION rather than an assumption — a spurious CEX for
                // every contract harness. The tracker is emitted INSIDE the
                // contracted callee, so it always reaches this
                // callee-discovered path and never the harness-side one.
                // This narrows the havoc to ambient program state; it is
                // not an exemption for anything the program can observe.
                let is_kani_internal_static =
                    crate::kani_middle::attributes::KaniAttributes::for_item(
                        self.tcx,
                        internal_def_id,
                    )
                    .is_recursion_tracker();
                let contract_havoc_mut_static = self.contract_static_havoc
                    && !is_kani_internal_static
                    && self.tcx.is_mutable_static(internal_def_id);

                if contract_havoc_mut_static {
                    debug!(
                        static_name = %static_name,
                        obj_id,
                        "CHC: contract harness — callee static mut left havocked (P2-S1)"
                    );
                } else if let Some(init_value) = init_expr_opt {
                    let mutable = self.tcx.is_mutable_static(internal_def_id);
                    self.register_static_memory_init_entries(static_ty, init_value, addr, mutable);
                    debug!(
                        static_name = %static_name,
                        obj_id,
                        "CHC: registered callee static memory init (#4014)"
                    );
                } else {
                    debug!(
                        static_name = %static_name,
                        obj_id,
                        "CHC: callee static address allocated, no init value (#4014)"
                    );
                }
            }
        }
    }

    /// How many closure-nesting levels the static pre-scan descends.
    ///
    /// A closure constructed inside a body is machinery *of* that body, so
    /// following it is a bounded, well-targeted descent — unlike following
    /// every `Call` terminator, which would open the whole call graph.
    /// Depth 1 is what reaches Kani's contract recursion tracker; 3 covers
    /// the nested check/replace closures the contract expansion builds
    /// underneath it.
    const MAX_CLOSURE_PRESCAN_DEPTH: usize = 3;

    /// Resolves the bodies of closures **constructed** inside `body`.
    ///
    /// `seen` de-duplicates by closure `DefId` so a body reached along two
    /// paths is scanned once and the descent always terminates.
    fn prescan_closure_bodies(
        body: &rustc_public::mir::Body,
        seen: &mut HashSet<rustc_public::DefId>,
    ) -> Vec<rustc_public::mir::Body> {
        use rustc_public::mir::mono::Instance;
        use rustc_public::ty::ClosureKind;

        let mut bodies = Vec::new();
        for bb_data in &body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(_lhs, rhs) = &stmt.kind else {
                    continue;
                };
                let Rvalue::Aggregate(AggregateKind::Closure(closure_def, closure_args), _) = rhs
                else {
                    continue;
                };
                if !seen.insert(closure_def.def_id()) {
                    continue;
                }
                // The call kind is not recorded at the construction site; try
                // each shape and take the first that yields a body.
                for kind in [ClosureKind::FnOnce, ClosureKind::FnMut, ClosureKind::Fn] {
                    if let Ok(instance) =
                        Instance::resolve_closure(*closure_def, closure_args, kind)
                        && let Some(closure_body) = instance.callee_body()
                    {
                        bodies.push(closure_body);
                        break;
                    }
                }
            }
        }
        bodies
    }

    /// Pre-scans harness body Call terminators for callee statics.
    ///
    /// Resolves each Call's target Instance, obtains its body, and calls
    /// `register_callee_body_statics` so that static addresses and memory
    /// init values are available before `emit_entry_rule()`.
    ///
    /// Part of #4014.
    pub(in crate::codegen_ay::chc) fn prescan_callee_statics(&mut self) {
        use rustc_public::mir::TerminatorKind;
        use rustc_public::mir::mono::{Instance, InstanceKind};
        use rustc_public::ty::{RigidTy, TyKind};

        // Ordinary RustCall forwarding shims can read constants several calls
        // below the host. Discover their native, monomorphic bodies before the
        // entry image closes, rather than discovering a new typed view while
        // walking them. A bounded breadth-first scan keeps recursion and large
        // library graphs finite. Exhaustion grants no authority: an actually
        // used view found later still takes the existing late-seed refusal.
        const MAX_CALLEE_BODIES: usize = 128;
        const MAX_CALLEE_STATEMENTS: usize = 16_384;
        enum PendingCallee {
            Instance(Instance),
            Resolved(rustc_public::mir::Body),
        }
        let direct_callees = |body: &rustc_public::mir::Body,
                              fn_item_reads: &mut Vec<rustc_public::ty::Ty>|
         -> Vec<Instance> {
            let mut instances: Vec<Instance> = body
                .blocks
                .iter()
                .filter_map(|bb| {
                    let TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
                        return None;
                    };
                    let func_ty = func.ty(body.locals()).ok()?;
                    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() else {
                        return None;
                    };
                    Instance::resolve(def, &args).ok()
                })
                .collect();
            // A referenced function ITEM is not a direct Call terminator:
            // `Box::new(&f)` reaches `f` through native forwarding shims. Its
            // exact FnDef type supplies the instance, never its ZST size,
            // reference bits, a diagnostic name, or a unique implementation.
            // This only discovers the body's entry read types; it does not
            // mint function-pointer or referent-value authority.
            for local in body.locals() {
                let mut ty = local.ty;
                for _ in 0..8 {
                    match ty.kind() {
                        TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => {
                            ty = inner;
                        }
                        TyKind::RigidTy(RigidTy::FnDef(def, args)) => {
                            if let Ok(instance) = Instance::resolve(def, &args) {
                                instances.push(instance);
                                fn_item_reads.push(ty);
                            }
                            break;
                        }
                        _ => break,
                    }
                }
            }
            instances
        };
        let mut fn_item_reads = Vec::new();
        let mut queue: std::collections::VecDeque<_> =
            direct_callees(self.body, &mut fn_item_reads)
                .into_iter()
                .map(PendingCallee::Instance)
                .collect();
        // Calling through `&FnDef` can materialize a function-item dereference
        // inside a forwarding shim even though its body only reads arguments.
        // Register that exact native view at every track level before entry;
        // Mem's local/deref-array scan must not be its implicit producer.
        for ty in fn_item_reads.drain(..) {
            self.note_extra_read_type(ty);
        }
        let mut seen = HashSet::new();
        let mut callee_bodies = Vec::new();
        let mut visited = 0usize;
        let mut remaining_statements = MAX_CALLEE_STATEMENTS;
        while let Some(pending) = queue.pop_front() {
            if visited == MAX_CALLEE_BODIES {
                break;
            }
            let body = match pending {
                PendingCallee::Instance(instance) => {
                    if !seen.insert(instance) {
                        continue;
                    }
                    visited += 1;
                    if matches!(instance.kind, InstanceKind::Virtual { .. }) {
                        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = instance.ty().kind()
                        else {
                            continue;
                        };
                        let Some(method_trait) = self.resolve_parent_trait_def_id(def) else {
                            continue;
                        };
                        let Some(dispatch_trait) =
                            crate::codegen_ay::chc::dyn_dispatch_scope::dispatch_trait_for_call(
                                self,
                                method_trait,
                                &args,
                            )
                        else {
                            continue;
                        };
                        let mut candidates =
                            crate::codegen_ay::chc::dyn_coercion::collect_dyn_trait_candidates(
                                self,
                                dispatch_trait.def_id,
                            );
                        candidates.truncate(MAX_CALLEE_BODIES - visited);
                        let (bodies, _) =
                            crate::codegen_ay::chc::dyn_coercion::resolve_dispatch_bodies(
                                self,
                                &candidates,
                                def,
                                &args,
                            );
                        // This is read discovery only. The ordinary dispatch
                        // still checks coverage, metadata and current validity.
                        // A missing or budget-skipped body keeps the existing
                        // late-seed refusal when an actual walk reaches it.
                        queue.extend(
                            bodies
                                .into_iter()
                                .map(|resolved| PendingCallee::Resolved(resolved.body)),
                        );
                        continue;
                    }
                    let Some(body) = instance.callee_body() else { continue };
                    body
                }
                PendingCallee::Resolved(body) => {
                    visited += 1;
                    body
                }
            };
            let cost = body
                .blocks
                .iter()
                .try_fold(0usize, |sum, bb| sum.checked_add(bb.statements.len().saturating_add(1)));
            let Some(cost) = cost.filter(|cost| *cost <= remaining_statements) else {
                continue;
            };
            remaining_statements -= cost;
            queue.extend(
                direct_callees(&body, &mut fn_item_reads).into_iter().map(PendingCallee::Instance),
            );
            for ty in fn_item_reads.drain(..) {
                self.note_extra_read_type(ty);
            }
            self.register_callee_body_consts(&body);
            self.prescan_array_semantic_eq(&body);
            callee_bodies.push(body);
        }

        // Part of #4014 (completion): a static can sit one or more CLOSURE
        // levels below the harness's direct callee, where a depth-1 Call scan
        // never sees it. Kani's contract expansion has exactly that shape —
        // the `#[kanitool::recursion_tracker]` REENTRY flag is declared inside
        // `<contracted fn>::{closure#0}`, never in the contracted fn's own
        // body. Discovered only later by the inline walker, its memory init
        // arrives after `emit_entry_rule()` has already run, so the flag stays
        // UNCONSTRAINED: the solver reads REENTRY = true on the OUTERMOST call,
        // enters the contract's replace arm — where `requires` is an ASSERTION
        // rather than an assumption — and reports a spurious counterexample on
        // every recursive-contract harness. Seeding the queue from the harness
        // body as well as its callees keeps closures created at either level in
        // scope.
        let mut seen_closures: HashSet<rustc_public::DefId> = HashSet::new();
        let mut queue: Vec<(rustc_public::mir::Body, usize)> =
            Self::prescan_closure_bodies(self.body, &mut seen_closures)
                .into_iter()
                .map(|b| (b, 1))
                .collect();
        for callee_body in &callee_bodies {
            queue.extend(
                Self::prescan_closure_bodies(callee_body, &mut seen_closures)
                    .into_iter()
                    .map(|b| (b, 1)),
            );
        }
        while let Some((closure_body, depth)) = queue.pop() {
            self.register_callee_body_consts(&closure_body);
            self.prescan_array_semantic_eq(&closure_body);
            if depth < Self::MAX_CLOSURE_PRESCAN_DEPTH {
                queue.extend(
                    Self::prescan_closure_bodies(&closure_body, &mut seen_closures)
                        .into_iter()
                        .map(|b| (b, depth + 1)),
                );
            }
        }
    }
}
