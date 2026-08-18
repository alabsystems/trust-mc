// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Projected inline assignment helpers.
//!
//! Handles functional write-back for projected statement assignments and call
//! destinations inside inline virtual bodies.
//! Projection chain update and type helpers split to projected_assign_helpers.rs
//! per #4206.

use ay_bindings::Expr;
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::mir::{LocalDecl, Operand, Place, ProjectionElem};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;

use super::super::ChcCtx;
use super::super::inline_shared::inline_operand_to_expr;
use super::projected_assign_helpers::{
    inline_deref_pointee_ty, inline_store_through, load_inline_value_from_memory,
    mirror_static_state_var_update, record_inline_heap_vtable_forward,
    record_inline_loaded_value_vtable_forward, update_inline_value_expr,
};
use super::walker::InlineWalkCtx;
use crate::codegen_ay::chc::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::chc::decl::codegen_types::CodegenTypes;
use crate::codegen_ay::provenance::{Loc, MaybeLoc, is_value_widened_into_address};
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::rustc_public_bridge::IndexedVal;

/// The address an inline `Deref`-prefixed write goes through.
///
/// # Provenance comes from MIR here, not from a width test
///
/// Both callers below have already established that the place's first
/// projection is a `Deref`, which is only well-typed in MIR when the local
/// holds a pointer (`&T`, `&mut T`, `*const T`, `*mut T`, `Box<T>` — the same
/// set `inline_deref_pointee_ty` accepts). The LOCAL therefore holds a pointer,
/// and `extract_pointer_expr` peels the wrapper datatype when the pointer is
/// stored inside one. Neither step is a guess. What that premise does not fix
/// is whether the walker's TERM for the local is that pointer — see the
/// address-vs-value section below, which is why only one of the two lanes
/// returns a [`Loc`].
///
/// What the surviving width test decides is **representation**, not provenance:
/// the memory model is addressed by a `POINTER_WIDTH` bitvector and nothing
/// else can be stored through, so a differently-shaped term has no store lane
/// available and the caller must take the functional lane. Both call sites used
/// to spell that test out inline and read it as "is this an address?"; there is
/// now one copy of it, and it answers only the question it can actually answer.
///
/// # The one thing the representation test still could not answer
///
/// A term that is `bv(POINTER_WIDTH)` *because a coercion widened a narrower
/// datum into it* satisfies the store-lane test as readily as a real address,
/// and the tag then named it as the destination of a `build_memory_store`. That
/// is the `is_value_widened_into_address` fabrication — obj_id forced to zero,
/// i.e. the null object — which `normalize_deref_address_expr` refuses by name
/// on the CHC deref path. Refused here too. All three callers already handle
/// `None` by taking the functional lane.
///
/// # ADDRESS-VS-VALUE: what the two lanes rest on
///
/// The MIR premise above establishes that the *Rust local* holds a pointer. It
/// does **not** by itself establish that `root` — the walker's term for that
/// local — is that pointer. The wrong lane here does not fail loudly: it stores
/// through a fabricated destination, i.e. it silently loses or misplaces the
/// write.
///
/// ## The #3980 substitution is EXCLUDED, and that is now a proof rather than a
/// discriminator
///
/// The hazard this function used to name is `resolve_mut_ref_value_args`
/// (#3980, `fn_trait_dispatch.rs`), which OVERWRITES a `&mut T` arg's term with
/// the pointee's VALUE because the walker models `Deref` as the identity. It
/// cannot produce a term that reaches *either* lane below, and its own guard is
/// what says so — read the conjunction it substitutes under:
///
/// * it substitutes only when `is_address` holds, and `is_address` requires
///   `pointee_sort.bitvec_width() != Some(POINTER_WIDTH)`;
/// * the term it substitutes is `Expr::var(in_name, in_sort)` where `in_sort`
///   is that same `pointee_sort` (candidates are filtered on
///   `out_sort == &pointee_sort`), so a substituted term is never
///   `bv(POINTER_WIDTH)` and never survives the shape test above;
/// * when the pointee type does not translate at all, `translate_ty` returns
///   `None` there too and the loop `continue`s without touching the arg;
/// * case (b) of that function (`is_already_value`) records a bridging pair and
///   writes nothing, so it changes no term.
///
/// So #3980 is excluded by that proof, in BOTH lanes, and the pointee width is
/// no longer load-bearing for it. The width test is kept because it still
/// separates the shape where a *different* producer commonly hands this
/// function a non-address (below) from the shapes where it rarely can.
///
/// ## The residual, named exactly
///
/// The producer that can put a non-address into a pointer-typed local's term is
/// the walker's own transparent-reference lane:
/// `inline_shared::place::inline_ref_place_to_expr` returns
/// [`crate::codegen_ay::chc::call::inline_shared::place::InlineRefExpr`], whose
/// `Transparent` arm is *the referenced place's own term* — `&x` modelled by
/// `x`'s term — while only its `Address` arm mints an address. That fact is
/// produced and then dropped one call later, at `inline_shared/rvalue.rs`'s
/// `.map(InlineRefExpr::into_expr)`, because `local_exprs` is still
/// `HashMap<usize, Expr>`. For `&mut x` with `x: usize` / `x: *mut T` /
/// `x: Box<T>` the transparent term is `bv(POINTER_WIDTH)` and is
/// indistinguishable here from a real address, so `*ptr = v` through it takes
/// the store lane and writes at a fabricated destination.
///
/// That residual is CONCENTRATED in, but not confined to, the wall lane: a
/// pointee whose sort is a datatype takes the ESTABLISHED lane, and if the
/// transparent term is that datatype's own value with a sole declared address
/// field, `extract_pointer_expr` peels the field and the shape test passes.
/// The `Known` tag is therefore as strong as this function's evidence gets and
/// no stronger; only the plumbing below makes it exact.
///
/// Carrying that fact is walker plumbing, not a tag: it means recording, per
/// body walk (local numbering is per-body), which locals were bound from a
/// `Transparent` result and propagating that through `Rvalue::Use` copies.
/// Refusing the case *without* that fact is NOT the safe direction — the
/// functional lane it would fall to leaves the memory mirror stale, which loses
/// the write just as silently — so the behaviour is deliberately unchanged.
///
/// ## What changed instead: the tag stops asserting
///
/// The pointer-width / untranslatable-pointee lane no longer mints a [`Loc`].
/// It returns [`MaybeLoc::Unknown`], which is this campaign's sanctioned way to
/// say "an address is what the caller needs, and nothing here established one"
/// — the same marker the `MaybeLoc` receiver lanes carry. Callers proceed
/// exactly as before (the emitted encoding is unchanged), but they route their
/// load/store through the `#[deprecated]` untyped shims, so the residual is
/// listed by `cargo check` and greppable through
/// [`MaybeLoc::as_addr_expr`] instead of hiding inside a `Loc`.
pub(super) fn inline_deref_target_addr(
    root: &Expr,
    pointee_ty: Option<rustc_public::ty::Ty>,
) -> Option<MaybeLoc> {
    let addr = crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(root)
        .map(Loc::into_expr)
        .unwrap_or_else(|| root.clone());
    if addr.sort().bitvec_width() != Some(POINTER_WIDTH) || is_value_widened_into_address(&addr) {
        return None;
    }
    match pointee_ty.and_then(<ChcCtx<'_, '_> as CodegenTypes>::translate_ty) {
        // ESTABLISHED lane — a pointer by MIR type, and #3980 is excluded by the
        // proof above. No other producer known to this module can put a
        // non-address here at a non-pointer-width pointee.
        Some(sort) if sort.bitvec_width() != Some(POINTER_WIDTH) => {
            Some(MaybeLoc::Known(Loc::of_address(addr)))
        }
        // UNRESOLVED WALL lane. `MaybeLoc::Unknown`, not `Loc`: the MIR premise
        // alone does not establish that this TERM is the pointer, and the
        // transparent-reference producer named above can supply a
        // width-indistinguishable non-address here.
        pointee_sort => {
            tracing::debug!(
                ?pointee_sort,
                "inline_deref_target_addr: pointee is pointer-width or unknown — \
                 address-vs-value unreported, routed as MaybeLoc::Unknown (#3980)"
            );
            Some(MaybeLoc::Unknown(addr))
        }
    }
}

/// Handle Deref-prefixed projected writes as memory stores.
///
/// Part of #3793: When an inline body writes through a dereferenced pointer
/// (e.g., `*ptr = val` or `(*ptr).field = val`), the write must go to memory
/// via `build_memory_store()`, not to `local_exprs`. Without this, side effects
/// of inlined drop bodies (like `CELL = 1`) are silently lost.
///
/// Returns `true` if the assignment was handled as a memory store (constraints
/// emitted via `ctx.build_memory_store`), `false` if this is not a Deref-prefixed
/// write and should fall through to the functional `apply_inline_projected_assign`.
pub(in crate::codegen_ay::chc) fn try_inline_memory_store(
    ctx: &mut ChcCtx<'_, '_>,
    locals: &[LocalDecl],
    local_exprs: &HashMap<usize, Expr>,
    place: &rustc_public::mir::Place,
    rhs: Expr,
    rhs_vtable: Option<Expr>,
) -> bool {
    // Only handle assignments that start with Deref.
    if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
        return false;
    }
    let Some(root) = local_exprs.get(&place.local) else {
        return false;
    };
    let Some(local_decl) = locals.get(place.local) else {
        tracing::warn!(place_local = place.local, "try_inline_memory_store: no local_decl");
        return false;
    };
    let pointer_ty = ctx.resolve_body_ty(local_decl.ty);
    let Some(pointee_ty) = inline_deref_pointee_ty(ctx, pointer_ty) else {
        tracing::warn!(place_local = place.local, pointer_ty = ?pointer_ty.kind(), "try_inline_memory_store: no pointee_ty");
        return false;
    };

    // Extract the memory address from the pointer expression. MIR already said
    // this local holds a pointer; the helper decides whether that pointer is in
    // a shape the memory model can be addressed by, and uses `pointee_ty` to
    // decide whether the #3980 value-substitution hazard is excluded here.
    let Some(pointer_addr) = inline_deref_target_addr(root, Some(pointee_ty)) else {
        tracing::warn!(place_local = place.local, root_sort = ?root.sort(), "try_inline_memory_store: addr not POINTER_WIDTH");
        return false;
    };

    let proj = &place.projection[1..];
    if proj.is_empty() {
        // Simple `*ptr = rhs` -- store the RHS directly.
        inline_store_through(ctx, &pointer_addr, rhs.clone(), pointee_ty);
        record_inline_heap_vtable_forward(ctx, pointer_addr.as_addr_expr(), rhs_vtable.clone());
        record_inline_loaded_value_vtable_forward(
            ctx,
            pointer_addr.as_addr_expr(),
            pointee_ty,
            rhs_vtable,
        );
        // Part of #3793: Mirror write to static state variable if this address
        // corresponds to a known static. The memory store updates heap arrays,
        // but the outer function reads statics through state variables.
        mirror_static_state_var_update(ctx, pointer_addr.as_addr_expr(), &rhs);
        return true;
    }

    // Deref + further projections: load the current value, apply functional
    // update, then store the entire updated value back.
    let Some(current) = load_inline_value_from_memory(ctx, &pointer_addr, pointee_ty) else {
        return false;
    };
    let Some(updated) =
        update_inline_value_expr(ctx, current, pointee_ty, proj, None, rhs, local_exprs)
    else {
        return false;
    };
    inline_store_through(ctx, &pointer_addr, updated.clone(), pointee_ty);
    record_inline_heap_vtable_forward(ctx, pointer_addr.as_addr_expr(), rhs_vtable.clone());
    record_inline_loaded_value_vtable_forward(
        ctx,
        pointer_addr.as_addr_expr(),
        pointee_ty,
        rhs_vtable,
    );
    mirror_static_state_var_update(ctx, pointer_addr.as_addr_expr(), &updated);
    true
}

pub(in crate::codegen_ay::chc) fn apply_inline_coroutine_set_discriminant<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    local_exprs: &HashMap<usize, Expr>,
    place: &Place,
    ty: rustc_public::ty::Ty,
    variant_index: rustc_public::ty::VariantIdx,
) -> Option<Expr> {
    let current = inline_operand_to_expr(
        ctx,
        &Operand::Copy(place.clone()),
        local_exprs,
        &walk_ctx.resolver,
        walk_ctx.locals,
    )?;
    let discr_width = crate::codegen_ay::types::coroutine_discriminant_select(current.clone())
        .and_then(|expr| expr.sort().bitvec_width())
        .unwrap_or(POINTER_WIDTH);
    let internal_ty = rustc_internal::internal(ctx.tcx, ty);
    let discr = internal_ty.discriminant_for_variant(
        ctx.tcx,
        InternalVariantIdx::from_usize(variant_index.to_index()),
    )?;
    let discr_expr = Expr::bitvec_const(
        sign_extend_discr_val(discr.val, discr.ty, ctx.tcx, discr_width),
        discr_width,
    );
    let updated = crate::codegen_ay::types::coroutine_discriminant_update(&current, discr_expr)?;
    if place.projection.is_empty() {
        return Some(updated);
    }
    apply_inline_projected_assign(ctx, walk_ctx.locals, local_exprs, place, updated)
}

pub(in crate::codegen_ay::chc) fn rebuild_inline_coroutine_receiver<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    local_exprs: &HashMap<usize, Expr>,
    place: &Place,
    ty: rustc_public::ty::Ty,
) -> Option<Expr> {
    if place.local == 1 {
        return None;
    }
    let receiver_decl = walk_ctx.locals.get(1)?;
    let updated = local_exprs.get(&place.local)?.clone();
    match receiver_decl.ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) if inner == ty => Some(updated),
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let variants = def.variants();
            let variant = variants.first()?;
            let fields = variant.fields();
            let field = fields.first()?;
            let field_ty = field.ty_with_args(&args);
            let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = field_ty.kind() else {
                return None;
            };
            if inner != ty {
                return None;
            }
            let receiver_place = Place {
                local: 1,
                projection: vec![ProjectionElem::Field(0, field_ty), ProjectionElem::Deref],
            };
            apply_inline_projected_assign(
                ctx,
                walk_ctx.locals,
                local_exprs,
                &receiver_place,
                updated,
            )
        }
        _ => None,
    }
}

/// Functional update for projected inline writes, including call destinations.
///
/// Part of #3561: covers `(*self).field = rhs`,
/// `(*self).field[idx] = rhs`, and chained field/index write-back.
pub(in crate::codegen_ay::chc) fn apply_inline_projected_assign(
    ctx: &mut ChcCtx<'_, '_>,
    locals: &[LocalDecl],
    local_exprs: &HashMap<usize, Expr>,
    place: &rustc_public::mir::Place,
    rhs: Expr,
) -> Option<Expr> {
    if place.projection.is_empty() {
        return Some(rhs);
    }
    let root = local_exprs.get(&place.local)?;
    let mut current = root.clone();
    let mut current_ty = ctx.resolve_body_ty(locals.get(place.local)?.ty);
    let mut proj = place.projection.as_slice();

    if matches!(proj.first(), Some(ProjectionElem::Deref)) {
        // Store lane vs functional lane. Picking the wrong one here silently
        // loses the write, so the decision is made by the one helper that owns
        // it rather than by an inline width test repeated per call site. The
        // pointee type is resolved up front (it was already needed below) so the
        // helper can use it as the #3980 discriminator.
        let deref_pointee_ty = inline_deref_pointee_ty(ctx, current_ty);
        let pointer_addr = inline_deref_target_addr(&current, deref_pointee_ty);
        let is_memory_addr = pointer_addr.is_some();
        proj = &proj[1..];
        // Part of #3793: Pure `*ptr = rhs` where ptr is a memory address (BV64)
        // must go through try_inline_memory_store, not the functional path.
        // The functional path updates local_exprs[ptr_local] to rhs, which
        // silently loses the memory write and the static state var mirror.
        // Only handle Deref functionally when there are further projections
        // (e.g., `(*self).field = rhs`) that need load-modify-store.
        if proj.is_empty() && is_memory_addr {
            return None;
        }
        current_ty = deref_pointee_ty?;
        // Address -> value crossing: the only way the pointee value is obtained.
        current = match pointer_addr {
            Some(addr) => load_inline_value_from_memory(ctx, &addr, current_ty)?,
            None => current,
        };
    }

    update_inline_value_expr(ctx, current, current_ty, proj, None, rhs, local_exprs)
}
