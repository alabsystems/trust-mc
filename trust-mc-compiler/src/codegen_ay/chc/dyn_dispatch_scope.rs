// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Candidate completeness for `dyn` dispatch (design 3 of
//! `docs/chc-hole-fix-designs-2026-09-24.md`, D2 and the critique's "dyn
//! merges" change).
//!
//! A virtual call is dispatched over a candidate list (`dyn_coercion.rs`:
//! non-blanket impls plus the host body's own `Unsize` coercions) and merged
//! under `vtable == id` with a fresh default arm. Two things decide whether
//! that default arm may stay silent:
//!
//! * **Which list.** The vtable id a coercion site stores is an index in the
//!   list of the TARGET trait object's principal. A call to a supertrait
//!   method on `Box<dyn Sub>` used to dispatch over the supertrait's list, so
//!   the stored id named an unrelated candidate: with `trait MyFn: Fn(u8, u8)
//!   -> u8`, a `Box<dyn MyFn>` call walked the only closure coerced to
//!   `dyn Fn` in the body (`walker_dispatch_candidates_dual.rs::bug_subtrait_*`).
//!   [`dispatch_trait_for_call`] dispatches over the receiver's principal
//!   whenever the called method's trait is it or one of its supertraits, and
//!   refuses anything else.
//! * **Which runtime types.** The reachability collector records every
//!   concrete type unsized to a trait object the harness can reach
//!   (`kani_middle/dyn_universe.rs`). A merge whose walked arms cover every
//!   recorded runtime type of the receiver's trait object is complete: its
//!   default arm is reached only on a model path whose discriminant is none of
//!   the ids (a havocked discriminant, which its producer records). Any other
//!   merge fails closed with [`DYN_CANDIDATES_INCOMPLETE`]. A candidate that
//!   cannot be walked fails closed with [`DYN_CANDIDATE_UNWALKABLE`] when it
//!   is a recorded runtime type, and costs nothing when it is not (it used to
//!   cost nothing either way: `record_aggregate_gap`, then the silent default
//!   arm, `bug_multi_impl_big_body`). With no universe (a body encoded outside
//!   a per-harness codegen) every merge is treated as incomplete.

use rustc_public::ty::{GenericArgKind, GenericArgs, RigidTy, TraitDef, Ty, TyKind};
use tracing::debug;

use super::call::codegen_call_virtual_inline::DispatchDefault;
use super::codegen_ctx::ChcCtx;
use super::dyn_coercion::DynCandidate;

/// A dyn merge whose arms may not cover every runtime type of the receiver.
pub(in crate::codegen_ay::chc) const DYN_CANDIDATES_INCOMPLETE: &str =
    "dyn_dispatch_candidates_incomplete";
/// A candidate that is a recorded runtime type but could not be walked.
pub(in crate::codegen_ay::chc) const DYN_CANDIDATE_UNWALKABLE: &str =
    "dyn_dispatch_candidate_unwalkable";
/// A virtual call whose method's trait is neither the receiver's principal
/// nor one of its supertraits.
pub(in crate::codegen_ay::chc) const DYN_PRINCIPAL_MISMATCH: &str =
    "dyn_dispatch_principal_mismatch";

/// Every reason this module records.
#[cfg_attr(not(test), allow(dead_code))]
pub(in crate::codegen_ay::chc) const DYN_SCOPE_REASONS: [&str; 3] =
    [DYN_CANDIDATES_INCOMPLETE, DYN_CANDIDATE_UNWALKABLE, DYN_PRINCIPAL_MISMATCH];

/// The trait a virtual call dispatches over.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) struct DispatchTrait {
    /// The trait whose candidate list (and vtable ids) the call uses.
    pub(in crate::codegen_ay::chc) def_id: rustc_span::def_id::DefId,
    /// The receiver trait object's principal and its generic arguments.
    principal: Option<(TraitDef, GenericArgs)>,
}

/// The first type argument of a trait method call: its `Self`.
fn self_ty_of(fn_args: &GenericArgs) -> Option<Ty> {
    fn_args.0.iter().find_map(|arg| match arg {
        GenericArgKind::Type(ty) => Some(*ty),
        _ => None,
    })
}

/// The trait a call to a method of `method_trait` with these generic
/// arguments dispatches over: the receiver's principal when the method's
/// trait is it or one of its supertraits (see the module doc). `None` when
/// the receiver is a trait object whose principal has no such relation to
/// `method_trait`: the caller must fail closed.
pub(in crate::codegen_ay::chc) fn dispatch_trait_for_call(
    ctx: &ChcCtx<'_, '_>,
    method_trait: rustc_span::def_id::DefId,
    fn_args: &GenericArgs,
) -> Option<DispatchTrait> {
    let receiver_principal = self_ty_of(fn_args).and_then(|self_ty| {
        let dyn_ty = super::dyn_coercion::find_dyn_trait_tail_ty(ctx, self_ty)?;
        dyn_ty.kind().trait_principal()
    });
    let Some(principal) = receiver_principal else {
        return Some(DispatchTrait { def_id: method_trait, principal: None });
    };
    let principal_def = principal.value.def_id;
    let principal_internal = rustc_public::rustc_internal::internal(
        ctx.tcx,
        rustc_public::CrateDef::def_id(&principal_def),
    );
    let principal = Some((principal_def, principal.value.generic_args));
    if principal_internal == method_trait {
        return Some(DispatchTrait { def_id: method_trait, principal });
    }
    if has_supertrait(ctx, principal_def, method_trait) {
        debug!(?method_trait, ?principal_internal, "dyn dispatch over the receiver's principal");
        return Some(DispatchTrait { def_id: principal_internal, principal });
    }
    debug!(
        ?method_trait,
        ?principal_internal,
        "dyn dispatch: principal does not have the method's trait"
    );
    None
}

/// Is `wanted` a (transitive) supertrait of `trait_def`? Reads the trait
/// predicates of each trait's declaration; a where-clause on a trait's other
/// parameters can only add a trait no valid receiver of this principal calls.
fn has_supertrait(
    ctx: &ChcCtx<'_, '_>,
    trait_def: TraitDef,
    wanted: rustc_span::def_id::DefId,
) -> bool {
    use rustc_public::ty::{ClauseKind, PredicateKind};
    let mut seen: Vec<TraitDef> = vec![trait_def];
    let mut stack = vec![trait_def];
    while let Some(current) = stack.pop() {
        let declaration = TraitDef::declaration(&current);
        #[cfg(not(all(trust_toolchain, version("1.101"))))]
        let predicates = declaration.predicates_of().predicates;
        #[cfg(all(trust_toolchain, version("1.101")))]
        let predicates = declaration
            .clauses_of()
            .clauses
            .into_iter()
            .map(|(clause, span)| (PredicateKind::Clause(clause), span));
        for (predicate, _) in predicates {
            let PredicateKind::Clause(ClauseKind::Trait(trait_predicate)) = predicate else {
                continue;
            };
            let super_def = trait_predicate.trait_ref.def_id;
            if seen.contains(&super_def) {
                continue;
            }
            let super_internal = rustc_public::rustc_internal::internal(
                ctx.tcx,
                rustc_public::CrateDef::def_id(&super_def),
            );
            if super_internal == wanted {
                return true;
            }
            seen.push(super_def);
            stack.push(super_def);
        }
    }
    false
}

/// What a dyn merge knows about its receiver's runtime types.
#[derive(Clone, Debug, Default)]
pub(in crate::codegen_ay::chc) struct DynDispatchScope {
    /// `(vtable id, concrete type)` of every candidate in the dispatch list.
    candidates: Vec<(u64, Ty)>,
    /// The receiver's runtime types per the universe; `None` when unknown.
    runtime: Option<Vec<Ty>>,
}

impl DynDispatchScope {
    /// The scope of a call dispatched over `dispatch_trait` with this list.
    pub(in crate::codegen_ay::chc) fn new(
        ctx: &ChcCtx<'_, '_>,
        dispatch_trait: &DispatchTrait,
        candidates: &[DynCandidate],
    ) -> Self {
        let runtime = match (&ctx.dyn_universe, &dispatch_trait.principal) {
            (Some(universe), Some((principal, args))) => {
                let types = universe.concrete_types(*principal, Some(args));
                // No recorded coercion: the receiver came from somewhere the
                // collector does not see (a stub, a transmute). Likewise an
                // upcast from a trait object with no recorded runtime type.
                (!types.is_empty() && !universe.is_open(*principal, args)).then_some(types)
            }
            _ => None,
        };
        Self {
            candidates: candidates.iter().map(|c| (c.vtable_id, c.concrete_ty)).collect(),
            runtime,
        }
    }

    /// A scope that knows nothing: every candidate may be the runtime type
    /// and every merge is incomplete.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(in crate::codegen_ay::chc) fn unknown() -> Self {
        Self::default()
    }

    /// Can the candidate with this id be the receiver's runtime type?
    ///
    /// A trait object in the list (which `dyn_coercion.rs` no longer puts
    /// there) stands for runtime types the universe lists under ITS principal,
    /// not this one, so it always may be.
    pub(in crate::codegen_ay::chc) fn may_be_runtime(&self, id: u64) -> bool {
        let Some(runtime) = &self.runtime else { return true };
        match self.candidates.iter().find(|(cid, _)| *cid == id) {
            Some((_, ty)) if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) => true,
            Some((_, ty)) => runtime.contains(ty),
            None => true,
        }
    }

    /// Is the candidate with this id the ONLY runtime type, so that walking
    /// it unconditionally is exact?
    pub(in crate::codegen_ay::chc) fn is_sole_runtime(&self, id: u64) -> bool {
        let Some(runtime) = &self.runtime else { return false };
        runtime.len() == 1
            && self.candidates.iter().any(|(cid, ty)| *cid == id && runtime[0] == *ty)
    }

    /// Do arms for the ids in `walked` cover every runtime type?
    pub(in crate::codegen_ay::chc) fn covers_runtime(&self, walked: &[u64]) -> bool {
        let Some(runtime) = &self.runtime else { return false };
        runtime.iter().all(|runtime_ty| {
            self.candidates.iter().any(|(id, ty)| ty == runtime_ty && walked.contains(id))
        })
    }

    /// The default arm of a merge over the discriminant `disc` whose arms
    /// walked `walked`.
    ///
    /// A discriminant built of constants (one id, or an if-then-else of ids:
    /// a walked body's coercion, an upcast's mapped id) names its runtime
    /// types outright: a leaf no arm walked selects the default arm, which
    /// then stands for a real receiver and fails closed whatever the universe
    /// says.
    pub(in crate::codegen_ay::chc) fn default_arm(
        &self,
        walked: &[u64],
        disc: &ay_bindings::Expr,
    ) -> DispatchDefault {
        let mut leaves = std::collections::BTreeSet::new();
        if super::call::fn_ptr_targets::ite_const_leaves(disc, &mut leaves).is_some()
            && leaves.iter().any(|leaf| !walked.contains(leaf))
        {
            return DispatchDefault::FailClosed(DYN_CANDIDATES_INCOMPLETE);
        }
        if self.covers_runtime(walked) {
            DispatchDefault::Covered
        } else {
            DispatchDefault::FailClosed(DYN_CANDIDATES_INCOMPLETE)
        }
    }
}
