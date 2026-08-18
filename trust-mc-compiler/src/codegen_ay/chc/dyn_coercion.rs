// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared dyn-coercion type extraction for CHC codegen.
//!
//! Provides wrapper transport and dyn-tail discovery helpers consumed by both
//! the coercion-site (`stmt/codegen_stmt_rvalue_ref/`) and the dispatch-site
//! (call/codegen_call_virtual.rs, call/codegen_call_virtual_inline.rs).
//!
//! Part of #3589: blanket-impl unsized dyn coercion recovery.

use std::collections::HashSet;

use crate::codegen_ay::field_roles::{self, FieldRole};
use crate::codegen_ay::provenance::{Loc, is_value_widened_into_address};
use crate::codegen_ay::ptr_repr::PtrSlot;
use crate::codegen_ay::shared::is_pointer_wrapper_adt;
use crate::kani_middle::abi::LayoutOf;
use ay_bindings::Expr;
use rustc_middle::ty::TypeVisitableExt;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{CastKind, Rvalue};
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::debug;

use super::codegen_ctx::ChcCtx;

// Type resolution and substitution functions moved to dyn_coercion_resolve.rs per #4206.
pub(super) use super::dyn_coercion_resolve::{
    extract_dyn_trait_def_id, normalize_unique_dyn_tail_ty, replace_dyn_self,
    replace_dyn_tail_with_concrete, resolve_unique_concrete_dyn_tail_ty, type_contains_dyn_tail,
};

fn first_type_arg_ty(args: &rustc_public::ty::GenericArgs) -> Option<rustc_public::ty::Ty> {
    args.0.iter().find_map(|arg| match arg {
        GenericArgKind::Type(ty) => Some(*ty),
        _ => None,
    })
}

fn is_std_pointer_wrapper_adt(def: rustc_public::ty::AdtDef) -> bool {
    is_pointer_wrapper_adt(&def.trimmed_name())
        || matches!(
            def.name().as_str(),
            "std::rc::Rc" | "alloc::rc::Rc" | "std::sync::Arc" | "alloc::sync::Arc"
        )
}

fn single_field_storage_ty(
    def: rustc_public::ty::AdtDef,
    args: &rustc_public::ty::GenericArgs,
) -> Option<rustc_public::ty::Ty> {
    let variants = def.variants();
    (variants.len() == 1 && variants[0].fields().len() == 1)
        .then(|| variants[0].fields()[0].ty_with_args(args))
}

/// Peel exactly one pointer-like wrapper layer.
///
/// References, raw pointers, and known smart pointers peel directly.
/// Single-field custom wrappers peel when their storage field is itself a
/// pointer-like type. Generic DST containers (`Outer<T>`, `Cage<T>`) remain.
pub(super) fn peel_pointer_like_wrapper_ty(ty: rustc_public::ty::Ty) -> rustc_public::ty::Ty {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            inner
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) if is_std_pointer_wrapper_adt(def) => {
            first_type_arg_ty(&args).unwrap_or(ty)
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let Some(storage_ty) = single_field_storage_ty(def, &args) else {
                return ty;
            };
            match storage_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
                TyKind::RigidTy(RigidTy::Adt(d, a)) if is_std_pointer_wrapper_adt(d) => {
                    first_type_arg_ty(&a).unwrap_or(ty)
                }
                _ => ty,
            }
        }
        _ => ty,
    }
}

/// Find the `dyn Trait` tail carried by `ty` without erasing any outer DST shell.
pub(super) fn find_dyn_trait_tail_ty(
    _ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
        return Some(ty);
    }

    let peeled = peel_pointer_like_wrapper_ty(ty);
    if peeled != ty {
        return find_dyn_trait_tail_ty(_ctx, peeled);
    }

    let layout = LayoutOf::new(ty);
    if !layout.has_trait_tail() {
        return None;
    }
    let tail = layout.unsized_tail()?;
    matches!(tail.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))).then_some(tail)
}

/// Extract the thin pointer a wrapper or fat-pointer datatype DECLARED it holds.
///
/// Two lanes, and both read a role off the declaration: a field the encoder
/// itself named `fld_ptr` (the pointer-wrapper sorts — `Vec`, `String`,
/// `Slice_*`, `Dyn_*`, `RawVec` — spell the role in the name), or a field the
/// declaration recorded as [`FieldRole::Addr`] in
/// [`crate::codegen_ay::field_roles`], from the MIR type it was built out of
/// (generic ADT / tuple / closure datatypes, whose fields are named after the
/// MIR field: `fld_inner`, `fld_0`, `cap_2`, `Some_field_0`).
///
/// # This is the encoder's second address PRODUCER (Wave 11)
///
/// What comes out is the pointer the wrapper holds, so the return type is
/// [`Loc`]: the consumers that dereference it, free it, offset it or split it
/// into `(obj_id, offset)` inherit that fact instead of re-deriving it from
/// `bitvec_width() == Some(POINTER_WIDTH)`.
///
/// Some callers instead re-pack the result — into a `(data, metadata)` tuple, a
/// `Dyn_Trait` datatype, or a destination local's own pointer datum. That is a
/// real `Loc -> value` crossing, and those sites drop the tag explicitly with
/// `.map(Loc::into_expr)`; grep that spelling to find every one of them.
///
/// # Both lanes read a DECLARED role — the guess is GONE (wave 18)
///
/// What stood here until wave 18 was "the first pointer-width field of a
/// datatype with ≤ 4 fields IS the pointer". That was never a criterion: the
/// `≤ 4` bound was a blast-radius limiter added after `DtSolver`'s
/// `fld_scope_len` was used as a base address (#4099), and inside the bound it
/// fabricated just as freely — `IndexRange`'s `fld_start`, `VecIntoIter`'s
/// `fld_pos`, `Layout`'s `fld_size` and any `struct S(usize, *mut u8)`'s first
/// field all answered "yes, here is your address".
///
/// It was not fixable *here*, and that is the point: the fact was thrown away
/// one module over, at the declaration. `translate_adt_sort` /
/// `translate_ty`'s tuple and closure arms hold the MIR type of every field they
/// declare, and a `&T` / `*mut T` / `Box` / `NonNull` / `Rc` field is an address
/// by construction ([`crate::codegen_ay::provenance::mir_ty_denotes_address`]). They now say so, into the
/// field-role table of `docs/addr-vs-value-conversion-queue.md` §4 item 7, and
/// this function reads it back.
///
/// A datatype whose declaration recorded nothing — a stub sort, a coroutine
/// state machine, a sort reconstructed by name — answers [`None`], and so does a
/// datatype with more than one declared address field (which of them is "the"
/// pointer is exactly the question the shape guess used to answer by position).
/// `None` routes the caller to the demotion lane it already has. That is the
/// trade this function now makes explicit: a demotion is sound, a fabricated
/// address is not.
///
/// # The already-thin lane: the CALLER supplies the provenance
///
/// A bare bitvector has no wrapper to peel, so this function hands it straight
/// back — and the [`Loc`] on that lane is **propagated, not discovered**. The
/// contract is the same one [`crate::codegen_ay::ptr_repr::PtrRepr::classify`]
/// states: the caller must already know `expr` denotes a pointer (it came from
/// a `Ref`/`RawPtr`-typed place, a pointer-wrapper local `translate_adt_ty`
/// flattened to `ptr_sort()`, a callee whose signature returns a pointer, or a
/// `Deref` step MIR only admits through one). Callers that cannot establish it
/// must drop the tag with `.map(Loc::into_expr)` — which most already do — or
/// gate first, as `inline_shared::place` does on `current_ty_opt` and
/// `rvalue_cast` does on the MIR `RawPtr`/`Ref` cast target.
///
/// What the lane now decides for itself is the **representation** half, and
/// that half used to be missing entirely: it tagged EVERY bitvector, of any
/// width, as an address. That is what made `extract_pointer_expr(..).is_some()`
/// useless as the pointer TEST roughly ten `?`/`if let Some` callers use it as
/// — a `bv1` discriminant, a `bv8` byte, a `bv32` index all answered "yes, and
/// here is your address". [`PtrSlot::of_sort`] admits exactly the two shapes an
/// address can have, and [`is_value_widened_into_address`] refuses the one
/// pointer-WIDE shape that is provably not one (a zero/sign-extended narrow
/// datum, whose obj_id lane is forced to the null object). Callers that drop
/// the tag are unaffected — their `.unwrap_or(expr)` returns the same term
/// either way — and callers that keep it now fail closed instead of receiving a
/// fabricated address.
pub(super) fn extract_pointer_expr(expr: &Expr) -> Option<Loc> {
    // Already-thin lane: there is no wrapper to peel, so the pointer term the
    // caller handed in IS the address. This lane is the identity, which is why
    // most callers spell their fallback `.unwrap_or(the same expr)`.
    if expr.sort().is_bitvec() {
        // Thin (one word) or packed wide ([metadata | data], left for `PtrRepr`
        // to split downstream) are the only shapes an address takes; every other
        // width was never one. See the contract note above for who supplies the
        // provenance this shape test does NOT supply.
        if PtrSlot::of_sort(expr.sort()).is_none() || is_value_widened_into_address(expr) {
            return None;
        }
        return Some(Loc::of_address(expr.clone()));
    }

    let dt = expr.sort().datatype_sort()?;
    // PRE-EXISTING, untouched by wave 18: for a multi-constructor datatype this
    // reads the FIRST variant's fields, which is a positional assumption of its
    // own. It is harmless for the shapes this function is called on (the
    // pointer-representation sorts are single-constructor, and an Option-like
    // sort's first constructor is the empty `None_*`, so it declines), and
    // fixing it would be a variant-selection change rather than a provenance
    // one — a separate question from which FIELD holds the address.
    let cons = dt.constructors.first()?;
    // Lane 1: the role spelled in the name. The pointer-wrapper sorts the
    // encoder writes literally declare their address field as `fld_ptr`.
    let ptr_field = cons.fields.iter().find(|field| field.name == "fld_ptr").or_else(|| {
        // Lane 2: the role RECORDED at declaration, for the datatypes whose
        // field names are not free to carry it because they come from MIR.
        //
        // `PtrSlot::Thin` is a REPRESENTATION test, not the provenance decision
        // — that arrived from the declaration. It is here because this producer
        // returns a thin address by contract (Wave 11): a declared-`Addr` field
        // of any other shape (a `Dyn_Trait` datatype, an `&str`'s packed
        // `bv128`, an `&[T; N]` flattened to an Array) is a pointer this
        // function is not the right decoder for, and the caller keeps its lane.
        //
        // EXACTLY ONE such field, or none: a datatype with two declared
        // addresses does not say which one is the pointer it holds, and
        // answering by position is the guess this lane replaced.
        let mut declared = cons.fields.iter().filter(|field| {
            matches!(PtrSlot::of_sort(&field.sort), Some(PtrSlot::Thin))
                && field_roles::declared_field_role(&dt.name, &field.name) == Some(FieldRole::Addr)
        });
        let sole = declared.next();
        if declared.next().is_none() { sole } else { None }
    })?;

    Some(Loc::of_address(expr.clone().field_select(
        &dt.name,
        &ptr_field.name,
        ptr_field.sort.clone(),
    )))
}

/// A dyn-trait candidate: a concrete type that implements a trait, with an
/// assigned sequential ID matching the order in which it was discovered.
#[derive(Debug)]
pub(super) struct DynCandidate {
    pub concrete_ty: rustc_public::ty::Ty,
    pub vtable_id: u64,
}

/// Dispatch body with its vtable ID for aligned stmt/call-side dispatch.
#[derive(Debug)]
pub(super) struct ResolvedDispatchBody {
    pub vtable_id: u64,
    pub body: rustc_public::mir::Body,
}

/// Collect merged dyn-trait candidates: non-blanket impls + MIR coercion sites, deduplicated.
pub(super) fn collect_dyn_trait_candidates(
    ctx: &ChcCtx<'_, '_>,
    trait_def_id: rustc_span::def_id::DefId,
) -> Vec<DynCandidate> {
    let mut candidates: Vec<DynCandidate> = Vec::new();
    let mut seen_types: HashSet<rustc_public::ty::Ty> = HashSet::new();
    let mut next_id: u64 = 0;

    if !ctx.tcx.is_trait(trait_def_id) {
        return candidates;
    }

    // Part of #4097 D2: Skip Phase 1 for auto-traits (Send, Sync, Unpin).
    // Auto-traits are implemented by nearly every type, so trait_impls_of
    // returns hundreds of irrelevant candidates. Phase 2 (MIR coercion) is
    // precise: it finds only the concrete types actually coerced to dyn in
    // this body.
    let trait_name = ctx.tcx.item_name(trait_def_id);
    let is_auto_trait = matches!(trait_name.as_str(), "Send" | "Sync" | "Unpin");

    if !is_auto_trait {
        // Phase 1: non-blanket impls (same as the old find_concrete_virtual_impls).
        let trait_impls = ctx.tcx.trait_impls_of(trait_def_id);
        for impl_def_id in trait_impls.non_blanket_impls().values().flatten() {
            let impl_self_ty = ctx.tcx.type_of(*impl_def_id).skip_binder();
            if impl_self_ty.has_param() {
                continue;
            }
            let stable_ty = rustc_internal::stable(impl_self_ty);
            if seen_types.insert(stable_ty) {
                candidates.push(DynCandidate { concrete_ty: stable_ty, vtable_id: next_id });
                next_id += 1;
            }
        }
    }

    // Phase 2: MIR-coercion-derived concrete types (always appended, not gated
    // on Phase 1 being empty). This is the key fix for #3589: blanket impls
    // like `impl<T: ?Sized + Identity> Identity for Outer<T>` produce concrete
    // coercion sites (e.g., `&Outer<Inner>` → `&dyn Identity`) that Phase 1
    // cannot discover.
    for bb in &ctx.body.blocks {
        for stmt in &bb.statements {
            if let rustc_public::mir::StatementKind::Assign(
                _,
                Rvalue::Cast(
                    CastKind::PointerCoercion(rustc_public::mir::PointerCoercion::Unsize),
                    operand,
                    target_ty,
                ),
            ) = &stmt.kind
            {
                // Check if this coercion targets our trait.
                let target_inner = peel_pointer_like_wrapper_ty(*target_ty);
                let target_trait_def_id = match extract_dyn_trait_def_id(ctx, target_inner) {
                    Some(id) => id,
                    None => continue,
                };
                if target_trait_def_id != trait_def_id {
                    continue;
                }

                // Extract source concrete type.
                let Ok(src_ty) = operand.ty(ctx.body.locals()) else {
                    continue;
                };
                let src_inner = peel_pointer_like_wrapper_ty(src_ty);

                // For struct-with-dyn-tail unsizing, extract the concrete tail.
                let concrete_ty = extract_concrete_tail_for_dyn(src_inner, target_inner);

                if seen_types.insert(concrete_ty) {
                    candidates.push(DynCandidate { concrete_ty, vtable_id: next_id });
                    next_id += 1;
                }
            }
        }
    }

    debug!(
        candidate_count = candidates.len(),
        "dyn_coercion: collected merged candidate sequence (#3589)"
    );
    candidates
}

/// Soundness gate (missed-bug C): is the merged candidate set potentially
/// INCOMPLETE for a single-impl *unconditional* inline?
///
/// `collect_dyn_trait_candidates` Phase 1 silently `continue`s past every
/// non-blanket `has_param()` impl (line ~189) — e.g. `impl<T: Speak> Speak for
/// Loud<T>`. When such a parametric impl is dropped AND Phase 2 found no in-body
/// `Unsize` coercion to this trait to ground the candidate, the sole remaining
/// candidate is a Phase-1 concrete guess (e.g. `Cat`), and the actual runtime
/// type may be a parametric instantiation (`Loud<Cat>`) coerced to `dyn` in a
/// *different* function that Phase 2 never scanned. Inlining the lone concrete
/// impl unconditionally then fabricates a wrong return value that can vacuously
/// discharge a downstream assertion (a latent false Safe). The caller must fail
/// closed (decline → sound over-approximation) in that case.
///
/// Returns `false` (safe to inline) whenever the set is grounded by an in-body
/// coercion or no parametric impl was dropped — so the common single-concrete
/// dispatch and the Phase-2-grounded cases (e.g. `&outer.inner -> &dyn Trait`)
/// keep their precise inline.
pub(super) fn single_candidate_set_is_incomplete(
    ctx: &ChcCtx<'_, '_>,
    trait_def_id: rustc_span::def_id::DefId,
    candidates: &[DynCandidate],
) -> bool {
    if candidates.len() != 1 {
        return false;
    }
    // Auto-traits skip Phase 1 entirely (see collect_dyn_trait_candidates), so a
    // len==1 auto-trait candidate is Phase-2-grounded — nothing was dropped.
    let trait_name = ctx.tcx.item_name(trait_def_id);
    if matches!(trait_name.as_str(), "Send" | "Sync" | "Unpin") {
        return false;
    }
    // Was a parametric non-blanket impl dropped by Phase 1's `has_param` continue?
    let trait_impls = ctx.tcx.trait_impls_of(trait_def_id);
    let dropped_parametric = trait_impls
        .non_blanket_impls()
        .values()
        .flatten()
        .any(|impl_def_id| ctx.tcx.type_of(*impl_def_id).skip_binder().has_param());
    if !dropped_parametric {
        return false;
    }
    // Did Phase 2 observe an in-body Unsize coercion to this trait (grounding the
    // candidate in an actual concrete type used here)? If so, trust the inline.
    !body_has_unsize_coercion_to_trait(ctx, trait_def_id)
}

/// Does the current body contain an `Unsize` `PointerCoercion` whose target is a
/// `dyn` of `trait_def_id`? Mirrors `collect_dyn_trait_candidates` Phase 2's
/// scan; used to decide whether a lone candidate is grounded by a real in-body
/// coercion or is a bare Phase-1 guess.
fn body_has_unsize_coercion_to_trait(
    ctx: &ChcCtx<'_, '_>,
    trait_def_id: rustc_span::def_id::DefId,
) -> bool {
    for bb in &ctx.body.blocks {
        for stmt in &bb.statements {
            if let rustc_public::mir::StatementKind::Assign(
                _,
                Rvalue::Cast(
                    CastKind::PointerCoercion(rustc_public::mir::PointerCoercion::Unsize),
                    _operand,
                    target_ty,
                ),
            ) = &stmt.kind
            {
                let target_inner = peel_pointer_like_wrapper_ty(*target_ty);
                if let Some(id) = extract_dyn_trait_def_id(ctx, target_inner)
                    && id == trait_def_id
                {
                    return true;
                }
            }
        }
    }
    false
}

/// Resolve the vtable ID for a concrete type from the merged candidate sequence.
pub(super) fn resolve_vtable_id(
    candidates: &[DynCandidate],
    concrete_ty: rustc_public::ty::Ty,
) -> Option<u64> {
    candidates.iter().find(|c| c.concrete_ty == concrete_ty).map(|c| c.vtable_id)
}

fn collect_auto_dyn_target_candidates(
    ctx: &ChcCtx<'_, '_>,
    target_ty: rustc_public::ty::Ty,
) -> Vec<DynCandidate> {
    let mut candidates: Vec<DynCandidate> = Vec::new();
    let mut seen_types: HashSet<rustc_public::ty::Ty> = HashSet::new();
    let mut next_id: u64 = 0;
    let target_is_dyn = matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)));

    for bb in &ctx.body.blocks {
        for stmt in &bb.statements {
            let rustc_public::mir::StatementKind::Assign(
                _,
                Rvalue::Cast(
                    CastKind::PointerCoercion(rustc_public::mir::PointerCoercion::Unsize),
                    operand,
                    cast_target_ty,
                ),
            ) = &stmt.kind
            else {
                continue;
            };

            let cast_target_inner = if *cast_target_ty == target_ty {
                *cast_target_ty
            } else {
                peel_pointer_like_wrapper_ty(*cast_target_ty)
            };
            let matches_target = cast_target_inner == target_ty
                || (target_is_dyn && type_contains_dyn_tail(cast_target_inner, target_ty));
            if !matches_target {
                continue;
            }

            let Ok(src_ty) = operand.ty(ctx.body.locals()) else {
                continue;
            };
            let src_inner = peel_pointer_like_wrapper_ty(src_ty);
            let concrete_ty = extract_concrete_tail_for_dyn(src_inner, cast_target_inner);
            if seen_types.insert(concrete_ty) {
                candidates.push(DynCandidate { concrete_ty, vtable_id: next_id });
                next_id += 1;
            }
        }
    }

    if candidates.is_empty()
        && let Some(concrete_ty) = resolve_unique_concrete_dyn_tail_ty(ctx, target_ty)
    {
        candidates.push(DynCandidate { concrete_ty, vtable_id: 0 });
    }

    candidates
}

pub(super) fn resolve_dyn_target_vtable_id(
    ctx: &ChcCtx<'_, '_>,
    target_ty: rustc_public::ty::Ty,
    concrete_ty: rustc_public::ty::Ty,
) -> Option<u64> {
    if let Some(trait_def_id) = extract_dyn_trait_def_id(ctx, target_ty) {
        let candidates = collect_dyn_trait_candidates(ctx, trait_def_id);
        return resolve_vtable_id(&candidates, concrete_ty);
    }

    let candidates = collect_auto_dyn_target_candidates(ctx, target_ty);
    resolve_vtable_id(&candidates, concrete_ty)
}

/// Resolve concrete implementations for virtual dispatch from the merged
/// candidate sequence.
///
/// For each candidate, substitutes the concrete type into fn_args, resolves
/// the Instance, and collects bodies. This replaces the old two-step
/// find_concrete_virtual_impls + find_fn_trait_impls_via_coercion pattern.
/// Resolve concrete dispatch bodies for the candidate set.
///
/// The second return is DROP-REPORTING (soundness): `true` when a candidate's
/// instance RESOLVED but its body fetch returned None (transform-panic
/// fail-close in `walker_transformed_body`, or a body-less instance). A
/// silently narrowed candidate set is a false-Safe channel at the SINGLE-impl
/// consumer path (unconditional inline of the one survivor, no disc guard) —
/// consumers must refuse that path when this is set. Bogus-candidate skips
/// (resolve panic/mismatch, unsubstitutable args) are NOT drops: those
/// candidates never applied.
pub(super) fn resolve_dispatch_bodies(
    ctx: &ChcCtx<'_, '_>,
    candidates: &[DynCandidate],
    fn_def: rustc_public::ty::FnDef,
    fn_args: &rustc_public::ty::GenericArgs,
) -> (Vec<ResolvedDispatchBody>, bool) {
    let mut results = Vec::new();
    let mut dropped_resolved_candidate = false;

    for candidate in candidates {
        if let Some(drop_self_ty) =
            wrapped_dyn_drop_self_ty(ctx, fn_def, fn_args, candidate.concrete_ty)
        {
            let drop_instance = Instance::resolve_drop_in_place(drop_self_ty);
            // Drop-glue shims stay on the RAW fetch: they are gate-false by
            // construction (no contract attrs on synthesized glue), so the
            // transformed route would be an identical no-op.
            if !drop_instance.is_empty_shim()
                && let Some(body) = drop_instance.body()
            {
                results.push(ResolvedDispatchBody { vtable_id: candidate.vtable_id, body });
            }
            continue;
        }

        let concrete_args = replace_dyn_self(fn_args, candidate.concrete_ty);
        let Some(concrete_args) = concrete_args else {
            continue;
        };

        // Part of #3748: Wrap Instance::resolve in catch_unwind because rustc
        // can ICE with SignatureMismatch when the candidate is a closure whose
        // signature doesn't match the expected trait args (e.g., 3-param closure
        // vs Fn<(f32, i32)>). This happens when multiple closures implement Fn
        // traits and collect_dyn_trait_candidates returns all of them.
        let resolve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            Instance::resolve(fn_def, &concrete_args)
        }));
        let resolve_result = match resolve_result {
            Ok(r) => r,
            Err(_) => {
                debug!(
                    ?candidate.concrete_ty,
                    "dyn_coercion: Instance::resolve panicked (signature mismatch), skipping"
                );
                continue;
            }
        };
        match resolve_result {
            Ok(concrete_instance) => {
                // TRANSFORMED fetch (scope-gated): contracted impl methods
                // dispatched via dyn need the mode-dispatched body; everything
                // else gets the raw body verbatim.
                if let Some(body) = crate::kani_middle::transform::walker_transformed_body(
                    ctx.tcx,
                    concrete_instance,
                ) {
                    debug!(
                        ?candidate.concrete_ty,
                        vtable_id = candidate.vtable_id,
                        "dyn_coercion: resolved dispatch body (#3589)"
                    );
                    results.push(ResolvedDispatchBody { vtable_id: candidate.vtable_id, body });
                } else {
                    debug!(
                        ?candidate.concrete_ty,
                        "dyn_coercion: resolved instance yielded no body — dropped candidate reported"
                    );
                    dropped_resolved_candidate = true;
                }
            }
            Err(_) => {
                // Try resolving as a closure (Fn/FnMut/FnOnce blanket impls).
                if let TyKind::RigidTy(RigidTy::Closure(def, args)) = candidate.concrete_ty.kind() {
                    for kind in [
                        rustc_public::ty::ClosureKind::FnOnce,
                        rustc_public::ty::ClosureKind::FnMut,
                        rustc_public::ty::ClosureKind::Fn,
                    ] {
                        let closure_result =
                            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                Instance::resolve_closure(def, &args, kind)
                            }));
                        if let Ok(Ok(inst)) = closure_result {
                            if let Some(body) =
                                crate::kani_middle::transform::walker_transformed_body(
                                    ctx.tcx, inst,
                                )
                            {
                                debug!("dyn_coercion: resolved closure impl (#3589)");
                                results.push(ResolvedDispatchBody {
                                    vtable_id: candidate.vtable_id,
                                    body,
                                });
                                break;
                            }
                            debug!(
                                "dyn_coercion: resolved closure impl yielded no body — dropped candidate reported"
                            );
                            dropped_resolved_candidate = true;
                        }
                    }
                }
            }
        }
    }

    (results, dropped_resolved_candidate)
}

fn is_drop_drop_fn(ctx: &ChcCtx<'_, '_>, fn_def: rustc_public::ty::FnDef) -> bool {
    let def_id = rustc_internal::internal(ctx.tcx, fn_def.def_id());
    ctx.tcx.def_path_str(def_id).ends_with("Drop::drop")
}

fn wrapped_dyn_drop_self_ty(
    ctx: &ChcCtx<'_, '_>,
    fn_def: rustc_public::ty::FnDef,
    fn_args: &rustc_public::ty::GenericArgs,
    concrete_tail_ty: rustc_public::ty::Ty,
) -> Option<rustc_public::ty::Ty> {
    if !is_drop_drop_fn(ctx, fn_def) {
        return None;
    }

    for arg in &fn_args.0 {
        if let GenericArgKind::Type(ty) = arg {
            let ty = ctx.resolve_body_ty(*ty);
            let effective_ty = peel_pointer_like_wrapper_ty(ty);
            if !matches!(effective_ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)))
                && find_dyn_trait_tail_ty(ctx, ty).is_some()
            {
                return replace_dyn_tail_with_concrete(ty, concrete_tail_ty);
            }
        }
    }
    None
}

/// For struct-with-dyn-tail unsizing, extract the concrete tail field type from
/// the source struct. E.g., for `Pair<i32, u8>` unsized to `Pair<i32, dyn Debug>`,
/// returns `u8`. For direct dyn coercion (src is not an ADT), returns `src_inner`.
/// Part of #3445.
pub(super) fn extract_concrete_tail_for_dyn(
    src_inner: rustc_public::ty::Ty,
    target_inner: rustc_public::ty::Ty,
) -> rustc_public::ty::Ty {
    // Direct dyn coercion: source is not an ADT wrapping the concrete type.
    if matches!(target_inner.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
        return src_inner;
    }
    // Struct-with-dyn-tail: extract the last field from the source ADT.
    if let TyKind::RigidTy(RigidTy::Adt(adt_def, ref args)) = src_inner.kind() {
        let variants = adt_def.variants();
        if variants.len() == 1 {
            if let Some(last_field) = variants[0].fields().last() {
                return last_field.ty_with_args(args);
            }
        }
    }
    src_inner
}
