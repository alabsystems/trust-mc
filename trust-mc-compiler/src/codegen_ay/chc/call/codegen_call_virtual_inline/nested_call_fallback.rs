// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pointer-aware fallback expression generation for nested call over-approximation.
//!
//! Extracted from terminator_exec.rs — Part of #134 D2, #4099.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};

use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::loop_replay::InlineWalkCtx;

/// Part of #134 D2: Check whether a Rust type is pointer-like
/// (reference, raw pointer, Box, Rc, Arc, NonNull, Unique, NonZero).
pub(super) fn is_pointer_like_ty(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(..)) | TyKind::RigidTy(RigidTy::RawPtr(..)) => true,
        TyKind::RigidTy(RigidTy::Adt(def, _)) => {
            let name = def.name();
            matches!(name.as_str(), "Box" | "Rc" | "Arc" | "NonNull" | "Unique" | "NonZero")
        }
        _ => false,
    }
}

/// Part of #134 D2, Part of #4099: Check whether the inline walker destination
/// holds a pointer-like type, including pointers nested inside wrapper types
/// (Option, Result, ManuallyDrop, MaybeUninit, Poll, ControlFlow).
///
/// Used to decide whether an over-approximation fallback variable should carry
/// heap-pointer invariants (alignment, non-null). The `nested_call_fallback_sort`
/// function unwraps Option/Result to get the inner sort, so we must also look
/// inside these wrappers when checking the type to keep the sort and type checks
/// aligned.
pub(super) fn is_pointer_destination(
    ctx: &ChcCtx<'_, '_>,
    walk_ctx: &InlineWalkCtx<'_>,
    destination: &rustc_public::mir::Place,
) -> bool {
    let ty = ctx
        .resolve_inline_local_ty(walk_ctx.body, destination.local)
        .or_else(|| destination.ty(walk_ctx.locals).ok().map(|ty| ctx.resolve_body_ty(ty)));
    let Some(ty) = ty else {
        return false;
    };
    if is_pointer_like_ty(ty) {
        return true;
    }
    // Part of #4099: Look inside wrapper types for nested pointer types.
    if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
        let name = def.name();
        let is_wrapper = matches!(
            name.as_str(),
            "Option" | "Result" | "ManuallyDrop" | "MaybeUninit" | "Poll" | "ControlFlow"
        );
        if is_wrapper && !args.0.is_empty() {
            if let GenericArgKind::Type(inner_ty) = args.0[0] {
                return is_pointer_like_ty(inner_ty);
            }
        }
    }
    false
}

pub(super) fn build_nested_call_fallback_expr(
    effective_sort: ay_bindings::Sort,
    is_pointer_like: bool,
) -> Expr {
    if effective_sort.bitvec_width() == Some(POINTER_WIDTH) && is_pointer_like {
        let upper = super::super::declare_pending_var(
            super::super::chc_fresh_name("__nested_call_overapprox"),
            ay_bindings::Sort::bitvec(32),
        );
        upper.bvor(Expr::bitvec_const(1u64, 32)).concat(Expr::bitvec_const(0u64, 32))
    } else {
        super::super::declare_pending_var(
            super::super::chc_fresh_name("__nested_call_overapprox"),
            effective_sort,
        )
    }
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(super) fn build_nested_call_fallback_expr_for_test(
    effective_sort: ay_bindings::Sort,
    is_pointer_like: bool,
) -> Expr {
    build_nested_call_fallback_expr(effective_sort, is_pointer_like)
}

/// Whether the last path segment names a collection constructor whose result
/// buffer is a PROVABLY-VALID heap allocation.
///
/// All of these produce a `Vec`/`String` whose backing is a live allocation
/// under safe-Rust preconditions:
/// - `<[T]>::into_vec(Box<[T]>)` / `<[T]>::to_vec` — own/copy into a fresh buffer.
/// - `bounded_any` / `exact_any` / `any_vec` / `exact_vec` — trust-mc verifier
///   collection generators, which build the buffer via the above.
///
/// Deliberately EXCLUDES `Vec::from_raw_parts` / `Vec::new` (dangling, no
/// allocation), so a Vec with genuinely-invalid provenance is not marked valid.
fn is_valid_backing_collection_ctor(callee_path: &str) -> bool {
    let method = callee_path.rsplit("::").next().unwrap_or(callee_path);
    matches!(
        method,
        "into_vec" | "to_vec" | "bounded_any" | "exact_any" | "any_vec" | "exact_vec"
    )
}

/// Give the over-approximated return of a provably-allocating collection
/// constructor a VALID heap-backing pointer, so a later `Vec::drop` /
/// `can_dereference` check does not fail spuriously.
///
/// When such a call cannot be inlined (its RawVec/allocator internals have no
/// MIR the walker can descend into), the generic symbolic-datatype fallback
/// gives the returned `Vec` an ARBITRARY `fld_ptr`. Two things then make its
/// drop dealloc-validity check fail spuriously:
///   1. `fld_ptr`'s object id / offset are unconstrained, so the drop's
///      8-alignment and offset-overflow checks can be violated by the solver.
///   2. Nothing modifies the heap-metadata arrays, so `obj_valid` is pruned and
///      the drop reads a FREE `obj_valid__out`, which the solver sets `false`.
///
/// This rebuilds the fallback `Vec` with `fld_ptr = obj_id << 32` (offset 0 is
/// 8-aligned and cannot overflow) for a FRESH heap object, and registers that
/// object as valid (`obj_valid[obj_id] = true`) with a known size. The store
/// threads `obj_valid__out` back to the all-valid entry default
/// (`obj_valid = const_array(true)`, #3159).
///
/// SOUNDNESS: gated on [`is_valid_backing_collection_ctor`]. `<[T]>::into_vec`
/// consumes an owned `Box<[T]>` (a live allocation under safe-Rust
/// preconditions), so its result's backing IS valid. A `Vec` built from
/// raw/unsafe parts (`Vec::from_raw_parts`) does NOT match, so a
/// genuinely-dangling Vec still fails its drop check. The fresh `obj_id` is
/// never the target of any free, so pre-existing invalidations (double-free /
/// explicit dealloc) on OTHER objects are preserved.
pub(super) fn try_build_valid_collection_backing_fallback<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    effective_sort: &ay_bindings::Sort,
    callee_path: Option<&str>,
) -> Option<Expr> {
    if !is_valid_backing_collection_ctor(callee_path?) {
        return None;
    }
    // Must be a `Vec`/`String`-like datatype carrying a heap pointer field.
    let dt = effective_sort.datatype_sort()?;
    let ctor = dt.constructors.first()?;
    if !ctor.fields.iter().any(|f| f.name == "fld_ptr") {
        return None;
    }
    let dt_name = dt.name.clone();
    let ctor_name = ctor.name.clone();
    let fields = ctor.fields.clone();

    let obj_id = ctx.heap_state.next_heap_alloc_id()?;

    // Symbolic base var supplies the len/cap/data fields (kept over-approx);
    // only `fld_ptr` is pinned to a valid, 8-aligned pointer (offset 0) into
    // the fresh backing object.
    let base = super::super::declare_pending_var(
        super::super::chc_fresh_name("__nested_call_overapprox"),
        effective_sort.clone(),
    );
    let valid_ptr =
        Expr::bitvec_const(i128::from(obj_id), 32).concat(Expr::bitvec_const(0u64, 32));
    let args: Vec<Expr> = fields
        .iter()
        .map(|f| {
            if f.name == "fld_ptr" {
                valid_ptr.clone()
            } else {
                base.clone().field_select(dt_name.clone(), f.name.clone(), f.sort.clone())
            }
        })
        .collect();
    let vec_expr = Expr::datatype_constructor(dt_name, ctor_name, args, effective_sort.clone());

    register_valid_backing_alloc(ctx, obj_id);
    ctx.declare_datatype_sort_if_needed(effective_sort);
    Some(vec_expr)
}

/// Register a fresh obj_id as a provably-valid collection backing.
///
/// - Records size 0, which (via the existing zero-size exemptions in
///   `heap_access_checks` / the dealloc stub) makes the buffer's bounds and
///   double-free checks vacuous — sound because the elements are already
///   over-approximated and no concrete size is known.
/// - Flags the id as a provably-valid backing so `heap_access_checks` treats
///   its `obj_valid` check as trivially true instead of selecting a free
///   `obj_valid__out`.
///
/// Deliberately does NOT store into `obj_valid`/`obj_size`: the drop-validity
/// check reads a `obj_valid__out` that is unbound in the (separate) check rule,
/// so a store in the transition rule would not reach it. The trivially-true
/// exemption fixes the check directly and avoids marking every object valid.
fn register_valid_backing_alloc<'tcx, 'body>(ctx: &mut ChcCtx<'tcx, 'body>, obj_id: u32) {
    ctx.heap_state.record_heap_alloc_size(obj_id, 0);
    ctx.heap_state.mark_provably_valid_backing(obj_id);
}
