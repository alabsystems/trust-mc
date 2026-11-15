// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vtable ids across a `dyn` → `dyn` unsize: trait upcasting (`Box<dyn Sub>`
//! → `Box<dyn Super>`) and dropping an auto trait (`Box<dyn Tr + Send>` →
//! `Box<dyn Tr>`).
//!
//! A coercion site stores the index of its concrete type in the candidate
//! list of the TARGET trait object's principal (`dyn_coercion.rs`), and a
//! dispatch reads that index against the same list. A `dyn` source has no
//! concrete type: its runtime type is whatever the SOURCE's id names in the
//! source principal's list. Before this module the coercion site looked the
//! source trait object itself up as a "concrete type": the host body's own
//! `dyn Sub → dyn Super` cast had put `dyn Sub` in the `Super` list as a
//! pseudo-candidate, the site stored its id, and the dispatch dropped that
//! candidate (it has no method body) and let the merge's default arm stand
//! for it silently. `walker_dyn_upcast_dual.rs`: an `unchecked_add` overflow
//! reached only through an upcast verified SUCCESSFUL clean (Kani FAILED),
//! and its safe twin failed Genuine. A walked body copied the source's id
//! unchanged, which names an unrelated candidate of the target list.
//!
//! Now:
//!
//! * a cast that keeps the principal copies the source's id (the two lists
//!   are the same list: one principal, one host body);
//! * an upcast maps each source candidate to the target list's id of the same
//!   concrete type, as an if-then-else over the source's id. A source id that
//!   names no candidate (a havocked source, which its producer records) maps
//!   to [`DYN_TO_DYN_NO_TARGET`], an id no candidate has;
//! * an upcast whose source id is unknown, or whose candidates map to nothing
//!   in the target list, stores a fresh id and records
//!   [`DYN_TO_DYN_VTABLE_UNMAPPED`], which is not on the blessed list.

use crate::codegen_ay::chc::codegen_ctx::Havoc;
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgs, RigidTy, TraitDef, Ty, TyKind};
use tracing::debug;

use super::chc_fresh_name;
use super::codegen_ctx::ChcCtx;
use super::dyn_coercion::{
    collect_dyn_trait_candidates, extract_concrete_tail_for_dyn, find_dyn_trait_tail_ty,
    peel_pointer_like_wrapper_ty, resolve_vtable_id,
};
use crate::codegen_ay::types::POINTER_WIDTH;

/// An upcast whose target id could not be derived from the source's.
pub(in crate::codegen_ay::chc) const DYN_TO_DYN_VTABLE_UNMAPPED: &str =
    "dyn_to_dyn_vtable_unmapped";

/// The target id of an upcast source whose id names no source candidate.
/// Vtable ids are small list indices, so no candidate has this one.
pub(in crate::codegen_ay::chc) const DYN_TO_DYN_NO_TARGET: u64 = u64::MAX;

/// A `dyn` → `dyn` unsize, by principal.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) struct DynToDyn {
    source: Option<(TraitDef, GenericArgs)>,
    target: Option<(TraitDef, GenericArgs)>,
}

impl DynToDyn {
    /// Does the cast keep the principal (and its arguments)?
    pub(in crate::codegen_ay::chc) fn keeps_principal(&self) -> bool {
        self.source.is_some() && self.source == self.target
    }
}

fn principal_of(ty: Ty) -> Option<(TraitDef, GenericArgs)> {
    ty.kind()
        .trait_principal()
        .map(|principal| (principal.value.def_id, principal.value.generic_args))
}

/// The `dyn` → `dyn` unsize an `Unsize` cast of an operand of type `src_ty`
/// to `target_ty` performs, or `None` when the source's tail is concrete.
pub(in crate::codegen_ay::chc) fn dyn_to_dyn_unsize(
    ctx: &ChcCtx<'_, '_>,
    src_ty: Ty,
    target_ty: Ty,
) -> Option<DynToDyn> {
    let target_inner = peel_pointer_like_wrapper_ty(target_ty);
    let target_tail = find_dyn_trait_tail_ty(ctx, target_inner)?;
    let src_inner = peel_pointer_like_wrapper_ty(src_ty);
    let source_tail = extract_concrete_tail_for_dyn(src_inner, target_inner);
    if !matches!(source_tail.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
        return None;
    }
    Some(DynToDyn { source: principal_of(source_tail), target: principal_of(target_tail) })
}

/// The target's vtable id for a cast whose source id is `source`.
///
/// `None` only for a cast that keeps the principal with an unknown source:
/// the caller may copy whatever it knows of the source, which is exact.
/// Every upcast gets an id: mapped, or fresh with
/// [`DYN_TO_DYN_VTABLE_UNMAPPED`] recorded.
pub(in crate::codegen_ay::chc) fn dyn_to_dyn_vtable(
    ctx: &mut ChcCtx<'_, '_>,
    cast: &DynToDyn,
    source: Option<Expr>,
) -> Option<Expr> {
    if cast.keeps_principal() {
        return source;
    }
    if let Some(mapped) = source.and_then(|source| map_upcast(ctx, cast, &source)) {
        return Some(mapped);
    }
    debug!(?cast, "dyn_to_dyn: upcast id not derivable from the source; fresh id");
    let booked = ctx.record_sound_fallback_reason(DYN_TO_DYN_VTABLE_UNMAPPED);
    Some(Havoc::booked(booked, chc_fresh_name("__dyn_upcast_vtable"), Sort::bitvec(POINTER_WIDTH)))
}

/// `ite(source == s1, t1, ite(source == s2, t2, .. NO_TARGET))` over every
/// source candidate whose concrete type has an id `t` in the target list.
fn map_upcast(ctx: &mut ChcCtx<'_, '_>, cast: &DynToDyn, source: &Expr) -> Option<Expr> {
    let (source_def, _) = cast.source.as_ref()?;
    let (target_def, _) = cast.target.as_ref()?;
    let source_list =
        collect_dyn_trait_candidates(ctx, rustc_internal::internal(ctx.tcx, source_def.def_id()));
    let target_list =
        collect_dyn_trait_candidates(ctx, rustc_internal::internal(ctx.tcx, target_def.def_id()));
    let pairs: Vec<(u64, u64, Ty)> = source_list
        .iter()
        .filter_map(|candidate| {
            resolve_vtable_id(&target_list, candidate.concrete_ty)
                .map(|target_id| (candidate.vtable_id, target_id, candidate.concrete_ty))
        })
        .collect();
    if pairs.is_empty() {
        return None;
    }
    let mut mapped = Expr::bitvec_const(u128::from(DYN_TO_DYN_NO_TARGET), POINTER_WIDTH);
    for (source_id, target_id, concrete_ty) in pairs.iter().rev() {
        // The size/align table the vtable intrinsics read, as a direct
        // coercion site records it.
        let layout = crate::kani_middle::abi::LayoutOf::new(*concrete_ty);
        if let (Some(size), Some(align)) = (layout.size_of(), layout.align_of()) {
            ctx.vtable_type_metadata.entry(*target_id).or_insert((size as u64, align as u64));
        }
        mapped = Expr::ite(
            source.clone().eq(Expr::bitvec_const(u128::from(*source_id), POINTER_WIDTH)),
            Expr::bitvec_const(u128::from(*target_id), POINTER_WIDTH),
            mapped,
        );
    }
    debug!(pairs = pairs.len(), "dyn_to_dyn: upcast ids mapped from the source list");
    Some(mapped)
}
