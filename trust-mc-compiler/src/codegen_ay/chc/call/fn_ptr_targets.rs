// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Which function a call through a function pointer can run (design 3 of
//! `docs/chc-hole-fix-designs-2026-09-24.md`, "fn-pointer identity and
//! candidate completeness", with the critique's required changes).
//!
//! **Identity (D1).** A reified pointer is a constant id minted per instance
//! (`crate::codegen_ay::fn_ptr_identity`), and [`ChcCtx::fn_ptr_targets`]
//! maps every minted id back to its function. The ids are tagged pointer
//! values into objects from `FN_PTR_OBJ_BASE` up, which no allocation uses,
//! so no integer or heap address the encoder produces for anything else can
//! equal one. The id is a function of the instance alone
//! (`fn_ptr_identity_value`), so a pointer a constant or static holds reads
//! as the same id. A constant pointer value is then exact.
//!
//! **Complete or fail closed.** A call's candidate set is complete when every
//! value the pointer can hold is known:
//!
//! * the pointer is one minted id (exact);
//! * the pointer term is an if-then-else tree whose leaves are all minted ids;
//! * the pointer term is what the host produced for a local whose every
//!   definition is a reification or a copy of another such local, with no
//!   borrow, call destination, projection or argument binding
//!   ([`ChcCtx::host_fn_ptr_local_domain`]);
//! * otherwise, the harness's reachability universe
//!   (`kani_middle/dyn_universe.rs`) lists every function reified at a
//!   compatible fn-pointer type, provided no constant or static holds a
//!   function pointer (the encoder does not read those values as ids) and no
//!   transmute produces a pointer of that type. A pointer loaded from memory
//!   or returned by a call then still has a complete set.
//!
//! A complete set is dispatched under `pointer == id` per arm, and its default
//! arm is not blessed: it is the checked obligation `pointer ∈ ids` with the
//! message [`INVALID_FN_PTR_MESSAGE`], so a wrong completeness argument shows
//! up as a failure instead of a dropped behaviour. Anything else (a pointer
//! read from a static or a const, one of a transmuted type, one in a harness
//! with no universe, or one built from an unkeyable operand) records
//! [`FN_PTR_CANDIDATES_INCOMPLETE`],
//! which is not on the blessed list: a proof resting on it is demoted, and a
//! counterexample through it is never certified Genuine. A candidate whose
//! body cannot be walked records [`FN_PTR_TARGET_UNWALKABLE`]. A walked
//! indirect call (fn pointer or dyn) that still reaches the walker's havoc
//! fallback records [`INDIRECT_CALL_HAVOCKED`] (`terminator_exec.rs`), where
//! it used to ride the blessed `nested_call_overapprox`.

use crate::codegen_ay::chc::codegen_ctx::Havoc;
use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{
    CastKind, Operand, PointerCoercion, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{BTreeSet, HashSet};
use tracing::debug;

use super::ChcCtx;
use super::inline_body::DeferredInlineCheck;
use crate::codegen_ay::chc::chc_fresh_name;
use crate::codegen_ay::fn_ptr_identity::{FnPtrTarget, fn_ptr_target_of_ty};
use crate::codegen_ay::types::POINTER_WIDTH;
use trust_mc_core::violation::PropertyKind;

/// A reification whose operand is neither a function item nor a closure, or
/// does not resolve: the pointer is a fresh value, not an identity.
pub(in crate::codegen_ay::chc) const FN_PTR_IDENTITY_UNKEYABLE: &str = "fn_ptr_identity_unkeyable";
/// A call through a pointer whose possible values are not all known: its
/// default arm stands for functions no arm walks.
pub(in crate::codegen_ay::chc) const FN_PTR_CANDIDATES_INCOMPLETE: &str =
    "fn_ptr_candidates_incomplete";
/// A candidate target whose body could not be walked (no body, or over the
/// inline budget): its obligations and effects are missing.
pub(in crate::codegen_ay::chc) const FN_PTR_TARGET_UNWALKABLE: &str = "fn_ptr_target_unwalkable";
/// A walked indirect call (fn pointer or `dyn`) that reached the walker's
/// havoc fallback: its target, and so its obligations, are unknown.
pub(in crate::codegen_ay::chc) const INDIRECT_CALL_HAVOCKED: &str = "nested_indirect_call_havocked";
/// A dispatch arm whose value sort differs from the merge's: the arm's value
/// and effects fall to the default arm.
pub(in crate::codegen_ay::chc) const DISPATCH_ARM_VALUE_DROPPED: &str =
    "dispatch_arm_value_dropped";

/// The obligation of a dispatch whose set the harness universe completed
/// (the pointer was loaded from memory or returned by a call) reads a freed
/// variable: a violation of it is never certified Genuine. A sound havoc: the
/// obligation's reachability, and so every proof, is unchanged.
pub(in crate::codegen_ay::chc) const FN_PTR_OBLIGATION_UNCERTIFIED: &str =
    "fn_ptr_obligation_value_uncertified";

/// The property description of the default-arm obligation.
pub(in crate::codegen_ay::chc) const INVALID_FN_PTR_MESSAGE: &str = "invalid function pointer";

/// Two instances whose identities collide (see `fn_ptr_identity_value`).
pub(in crate::codegen_ay::chc) const FN_PTR_IDENTITY_COLLISION: &str = "fn_ptr_identity_collision";

/// Every reason this module records.
#[cfg_attr(not(test), allow(dead_code))]
pub(in crate::codegen_ay::chc) const FN_PTR_REASONS: [&str; 7] = [
    FN_PTR_OBLIGATION_UNCERTIFIED,
    FN_PTR_IDENTITY_COLLISION,
    FN_PTR_IDENTITY_UNKEYABLE,
    FN_PTR_CANDIDATES_INCOMPLETE,
    FN_PTR_TARGET_UNWALKABLE,
    INDIRECT_CALL_HAVOCKED,
    DISPATCH_ARM_VALUE_DROPPED,
];

/// The candidate targets of one call through a function pointer.
pub(in crate::codegen_ay::chc) struct FnPtrCandidates {
    /// `(id, target)` for every candidate, in id order.
    pub(in crate::codegen_ay::chc) targets: Vec<(u64, FnPtrTarget)>,
    /// The pointer is a single minted id.
    pub(in crate::codegen_ay::chc) exact: bool,
    /// Every value the pointer can hold is one of `targets`' ids.
    pub(in crate::codegen_ay::chc) complete: bool,
    /// Completeness came from the harness universe, not from the pointer's
    /// term: the value was loaded from memory or returned by a call. The
    /// memory model can return a value the program never stored there (a
    /// type-punned read of another type's cell is unconstrained), so the
    /// "invalid function pointer" obligation may fail on a value no execution
    /// has. It still proves every real value is an id; its failure is not
    /// evidence ([`ChcCtx::fn_ptr_obligation_default`]).
    pub(in crate::codegen_ay::chc) from_universe: bool,
}

/// The constant value of a pointer-width bit-vector term, if it is one.
pub(in crate::codegen_ay::chc) fn pointer_const_value(expr: &Expr) -> Option<u64> {
    match expr.value() {
        ExprValue::BitVecConst { value, .. } => u64::try_from(value.clone()).ok(),
        _ => None,
    }
}

/// The leaves of an if-then-else tree of constants, or `None` when some leaf
/// is not a constant.
pub(in crate::codegen_ay::chc) fn ite_const_leaves(
    expr: &Expr,
    out: &mut BTreeSet<u64>,
) -> Option<()> {
    if let Some(value) = pointer_const_value(expr) {
        out.insert(value);
        return Some(());
    }
    match expr.value() {
        ExprValue::Ite { then_expr, else_expr, .. } => {
            ite_const_leaves(then_expr, out)?;
            ite_const_leaves(else_expr, out)
        }
        _ => None,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The id of `target`, registered on first use.
    pub(in crate::codegen_ay::chc) fn fn_ptr_id_for_target(&mut self, target: FnPtrTarget) -> u64 {
        if let Some(id) = self.fn_ptr_ids.get(&target.key).and_then(pointer_const_value) {
            return id;
        }
        let id = target.identity_value();
        if let Some(existing) = self.fn_ptr_targets.get(&id)
            && existing.key != target.key
        {
            // Two functions share one id: a call through either may walk the
            // other. Never expected (see `fn_ptr_identity_value`); fail closed.
            debug!(id, first = %existing.label(), second = %target.label(), "fn_ptr: identity collision");
            self.record_sound_fallback_reason(FN_PTR_IDENTITY_COLLISION);
        }
        self.fn_ptr_ids
            .insert(target.key.clone(), Expr::bitvec_const(u128::from(id), POINTER_WIDTH));
        debug!(id, target = %target.label(), "fn_ptr: minted identity");
        self.fn_ptr_targets.insert(id, target);
        id
    }

    /// The pointer value a reification of an operand of type `ty` produces:
    /// the target's id, or a fresh value recorded as
    /// [`FN_PTR_IDENTITY_UNKEYABLE`] when `ty` names no target.
    pub(in crate::codegen_ay::chc) fn fn_ptr_value_for_reified_ty(
        &mut self,
        ty: rustc_public::ty::Ty,
    ) -> Expr {
        // A type with residual generic parameters would resolve to a generic
        // instance, whose key differs from the monomorphic one the host mints.
        let monomorphic = !rustc_middle::ty::TypeVisitableExt::has_param(
            &rustc_public::rustc_internal::internal(self.tcx, ty),
        );
        match fn_ptr_target_of_ty(ty).filter(|_| monomorphic) {
            Some(target) => {
                let id = self.fn_ptr_id_for_target(target);
                Expr::bitvec_const(u128::from(id), POINTER_WIDTH)
            }
            None => {
                debug!(?ty, "fn_ptr: reified operand names no function; fresh pointer value");
                let booked = self.record_sound_fallback_reason(FN_PTR_IDENTITY_UNKEYABLE);
                Havoc::booked(
                    booked,
                    chc_fresh_name("__fn_ptr_unkeyable"),
                    ay_bindings::Sort::bitvec(POINTER_WIDTH),
                )
            }
        }
    }

    /// The ids a closed host fn-pointer local can hold (see the module doc),
    /// or `None` when some definition of it, or of a local it copies, is
    /// anything but a reification or a local copy.
    pub(in crate::codegen_ay::chc) fn host_fn_ptr_local_domain(
        &mut self,
        local: usize,
    ) -> Option<Vec<u64>> {
        if let Some(cached) = self.fn_ptr_local_domains.get(&local) {
            return cached.clone();
        }
        let domain = self.compute_host_fn_ptr_local_domain(local);
        self.fn_ptr_local_domains.insert(local, domain.clone());
        domain
    }

    fn compute_host_fn_ptr_local_domain(&mut self, local: usize) -> Option<Vec<u64>> {
        let body = self.body;
        let arg_count = body.arg_locals().len();
        // A local whose value can change other than by a whole-local
        // assignment in this body.
        let mut escaping: HashSet<usize> = HashSet::new();
        for block in &body.blocks {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(place, rvalue) => {
                        if !place.projection.is_empty() {
                            escaping.insert(place.local);
                        }
                        if let Rvalue::Ref(_, _, borrowed) | Rvalue::AddressOf(_, borrowed) =
                            rvalue
                        {
                            escaping.insert(borrowed.local);
                        }
                    }
                    StatementKind::SetDiscriminant { place, .. } => {
                        escaping.insert(place.local);
                    }
                    _ => {}
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { destination, .. } => {
                    escaping.insert(destination.local);
                }
                TerminatorKind::InlineAsm { .. } => return None,
                _ => {}
            }
        }

        let mut ids: BTreeSet<u64> = BTreeSet::new();
        let mut visited: HashSet<usize> = HashSet::new();
        let mut worklist = vec![local];
        while let Some(current) = worklist.pop() {
            if !visited.insert(current) {
                continue;
            }
            if current == 0 || current <= arg_count || escaping.contains(&current) {
                return None;
            }
            let mut defined = false;
            for block in &body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(place, rvalue) = &stmt.kind else { continue };
                    if place.local != current {
                        continue;
                    }
                    defined = true;
                    match rvalue {
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                        | Rvalue::Cast(
                            CastKind::PointerCoercion(PointerCoercion::UnsafeFnPointer),
                            Operand::Copy(src) | Operand::Move(src),
                            _,
                        ) if src.projection.is_empty() => worklist.push(src.local),
                        Rvalue::Cast(
                            CastKind::PointerCoercion(
                                PointerCoercion::ReifyFnPointer { .. }
                                | PointerCoercion::ClosureFnPointer(_),
                            ),
                            operand,
                            _,
                        ) => {
                            let ty = self.resolve_body_ty(operand.ty(body.locals()).ok()?);
                            let target = fn_ptr_target_of_ty(ty)?;
                            ids.insert(self.fn_ptr_id_for_target(target));
                        }
                        _ => return None,
                    }
                }
            }
            if !defined {
                return None;
            }
        }
        (!ids.is_empty()).then(|| ids.into_iter().collect())
    }

    /// Remember that the host translated `operand` to `expr`: when the
    /// operand is a closed fn-pointer local, `expr` can hold only that
    /// local's ids.
    pub(in crate::codegen_ay::chc) fn note_fn_ptr_operand_domain(
        &mut self,
        operand: &Operand,
        expr: &Expr,
    ) {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else { return };
        if !place.projection.is_empty() || pointer_const_value(expr).is_some() {
            return;
        }
        let Some(decl) = self.body.locals().get(place.local) else { return };
        if !matches!(decl.ty.kind(), TyKind::RigidTy(RigidTy::FnPtr(..))) {
            return;
        }
        let Some(domain) = self.host_fn_ptr_local_domain(place.local) else { return };
        match self.fn_ptr_value_domains.get_mut(expr) {
            // The term is the value of both locals: it lies in both domains.
            Some(existing) => existing.retain(|id| domain.contains(id)),
            None => {
                self.fn_ptr_value_domains.insert(expr.clone(), domain);
            }
        }
    }

    /// The candidates of a call through a pointer whose term is `pointer`.
    ///
    /// Complete when the pointer's possible values are known (see the module
    /// doc); otherwise the targets the host reifies, so a counterexample can
    /// still be found, with `complete == false`.
    pub(in crate::codegen_ay::chc) fn fn_ptr_call_candidates(
        &mut self,
        pointer: Option<&Expr>,
        call_ty: Option<rustc_public::ty::Ty>,
    ) -> FnPtrCandidates {
        if let Some(pointer) = pointer {
            if let Some(id) = pointer_const_value(pointer) {
                let targets: Vec<_> = self
                    .fn_ptr_targets
                    .get(&id)
                    .map(|target| vec![(id, target.clone())])
                    .unwrap_or_default();
                let known = !targets.is_empty();
                return FnPtrCandidates {
                    targets,
                    exact: known,
                    complete: known,
                    from_universe: false,
                };
            }
            let mut leaves = BTreeSet::new();
            let domain = if ite_const_leaves(pointer, &mut leaves).is_some() {
                Some(leaves.into_iter().collect::<Vec<_>>())
            } else {
                self.fn_ptr_value_domains.get(pointer).cloned()
            };
            if let Some(domain) = domain {
                let targets: Vec<_> = domain
                    .iter()
                    .filter_map(|id| self.fn_ptr_targets.get(id).map(|t| (*id, t.clone())))
                    .collect();
                if targets.len() == domain.len() && !targets.is_empty() {
                    return FnPtrCandidates {
                        targets,
                        exact: false,
                        complete: true,
                        from_universe: false,
                    };
                }
            }
        }
        if let Some(call_ty) = call_ty
            && let Some(targets) = self.universe_fn_ptr_targets(call_ty)
        {
            return FnPtrCandidates { targets, exact: false, complete: true, from_universe: true };
        }
        let (host, _body_missing) = self.host_fn_ptr_reification_targets();
        FnPtrCandidates { targets: host, exact: false, complete: false, from_universe: false }
    }

    /// The default arm of a complete fn-pointer dispatch: the "invalid
    /// function pointer" obligation, uncertified (see
    /// [`FN_PTR_OBLIGATION_UNCERTIFIED`] and `DispatchDefault::Obligation`)
    /// when the universe completed the set.
    ///
    /// A type-punned read (`*(&x as *const usize as *const fn(..))`, or a
    /// callback stored as `*const ()`) loads the pointer from a cell of
    /// another type, which the memory model leaves unconstrained; the
    /// obligation then failed on that value and was certified Genuine, where
    /// Kani proves the harness (`walker_fn_ptr_completeness_dual.rs`
    /// `safe_fnptr_usize_roundtrip`, `safe_fnptr_void_ptr_callback`).
    pub(in crate::codegen_ay::chc) fn fn_ptr_obligation_default(
        &mut self,
        candidates: &FnPtrCandidates,
    ) -> super::codegen_call_virtual_inline::DispatchDefault {
        let taint = candidates.from_universe.then(|| {
            let name = chc_fresh_name("__fn_ptr_value_uncertified");
            let booked = self.record_sound_fallback_reason_identified(
                FN_PTR_OBLIGATION_UNCERTIFIED,
                Some(&name),
            );
            Havoc::booked(booked, name, ay_bindings::Sort::bool())
        });
        super::codegen_call_virtual_inline::DispatchDefault::Obligation {
            message: INVALID_FN_PTR_MESSAGE,
            taint,
        }
    }

    /// Every function the harness reifies at a fn-pointer type compatible
    /// with `call_ty`, when that list is every value a pointer of that type
    /// can hold (see the module doc); `None` otherwise.
    fn universe_fn_ptr_targets(
        &mut self,
        call_ty: rustc_public::ty::Ty,
    ) -> Option<Vec<(u64, FnPtrTarget)>> {
        let universe = self.dyn_universe.clone()?;
        if universe.fn_ptr_in_allocation()
            || universe
                .fn_ptr_transmute_targets()
                .iter()
                .any(|target| fn_ptr_types_compatible(self.tcx, *target, call_ty))
        {
            return None;
        }
        let mut targets: Vec<(u64, FnPtrTarget)> = Vec::new();
        for (operand, reified_ty) in universe.fn_ptr_reifications() {
            if !fn_ptr_types_compatible(self.tcx, *reified_ty, call_ty) {
                continue;
            }
            // A reification this encoder cannot key could be the target.
            let target = fn_ptr_target_of_ty(*operand)?;
            let id = self.fn_ptr_id_for_target(target.clone());
            if !targets.iter().any(|(seen, _)| *seen == id) {
                targets.push((id, target));
            }
        }
        targets.sort_by_key(|(id, _)| *id);
        (!targets.is_empty()).then_some(targets)
    }

    /// Every distinct target the host body reifies, with its id. The flag is
    /// `true` when some reification names no target.
    pub(in crate::codegen_ay::chc) fn host_fn_ptr_reification_targets(
        &mut self,
    ) -> (Vec<(u64, FnPtrTarget)>, bool) {
        let body = self.body;
        let mut casts = Vec::new();
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(
                    _,
                    Rvalue::Cast(
                        CastKind::PointerCoercion(
                            PointerCoercion::ReifyFnPointer { .. }
                            | PointerCoercion::ClosureFnPointer(_),
                        ),
                        operand,
                        _,
                    ),
                ) = &stmt.kind
                {
                    casts.push(operand.clone());
                }
            }
        }
        let mut targets: Vec<(u64, FnPtrTarget)> = Vec::new();
        let mut unkeyable = false;
        for operand in casts {
            let Some(target) = operand
                .ty(body.locals())
                .ok()
                .map(|ty| self.resolve_body_ty(ty))
                .and_then(fn_ptr_target_of_ty)
            else {
                unkeyable = true;
                continue;
            };
            let id = self.fn_ptr_id_for_target(target.clone());
            if !targets.iter().any(|(seen, _)| *seen == id) {
                targets.push((id, target));
            }
        }
        targets.sort_by_key(|(id, _)| *id);
        (targets, unkeyable)
    }
}

/// Can a pointer of fn-pointer type `a` hold a value reified at type `b`?
/// Their signatures agree once every region is erased (subtyping and
/// higher-ranked lifetimes change no value), ignoring `unsafe` (the
/// `UnsafeFnPointer` coercion changes no value either). A non-fn-pointer type
/// is compatible with nothing.
fn fn_ptr_types_compatible(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    a: rustc_public::ty::Ty,
    b: rustc_public::ty::Ty,
) -> bool {
    let (TyKind::RigidTy(RigidTy::FnPtr(stable_a)), TyKind::RigidTy(RigidTy::FnPtr(stable_b))) =
        (a.kind(), b.kind())
    else {
        return false;
    };
    if stable_a.value.abi != stable_b.value.abi
        || stable_a.value.c_variadic != stable_b.value.c_variadic
    {
        return false;
    }
    let erase = |ty: rustc_public::ty::Ty| {
        let internal = rustc_public::rustc_internal::internal(tcx, ty);
        tcx.erase_and_anonymize_regions(tcx.instantiate_bound_regions_with_erased(internal.fn_sig(tcx)))
    };
    let (sa, sb) = (erase(a), erase(b));
    sa.inputs() == sb.inputs() && sa.output() == sb.output()
}

/// The default-arm obligation of a complete fn-pointer dispatch: the pointer
/// is one of `ids`.
pub(in crate::codegen_ay::chc) fn invalid_fn_ptr_obligation(
    ctx: &ChcCtx<'_, '_>,
    pointer: &Expr,
    ids: &[u64],
) -> DeferredInlineCheck {
    let check = ids
        .iter()
        .map(|id| pointer.clone().eq(Expr::bitvec_const(u128::from(*id), POINTER_WIDTH)))
        .reduce(|acc, eq| acc.or(eq))
        .unwrap_or_else(|| Expr::bool_const(false));
    DeferredInlineCheck {
        check,
        kind: PropertyKind::UndefinedBehavior,
        message: Some(INVALID_FN_PTR_MESSAGE.to_string()),
        write_mark: ctx.heap_state.write_mark(),
        merge_key: None,
    }
}
