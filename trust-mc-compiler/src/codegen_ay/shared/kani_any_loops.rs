// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The loops Kani runs to build `kani::any::<T>()`, for the calls both lanes
//! model without them.
//!
//! The kani library's `Arbitrary` for `[T; N]` is `T::any_array::<N>()`, and
//! only the trivially arbitrary types (the integers, the floats and `()`)
//! override `any_array` with a loop-free `any_raw_array`. Every other `T`,
//! `bool` included, runs the default `[(); N].map(|_| T::any())`, one loop of
//! `N` passes (`library/kani_core/src/arbitrary.rs`). Both lanes model
//! `kani::any::<[bool; N]>()` (`inline/handler_boundaries.rs`
//! `any_model_raw_compatible_array`) and `<T as Arbitrary>::any_array::<N>()`
//! as a fresh array, so the loop is never unwound: under a declared
//! `#[kani::unwind(U)]` with `U <= N` Kani fails `unwinding assertion loop 0`
//! and both lanes reported a clean proof (walker fail-closed review, round 1 of
//! the repair after the merge with main; `kani_any_array_unwind_dual.rs`). The
//! loop runs `N` passes whatever the values, so the assertion fails exactly
//! where the call is reached: an exact check.

use rustc_public::CrateDef;
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};

/// Recursion bound for nested types: deeper nesting is left without a count.
const MAX_ANY_TYPE_DEPTH: usize = 8;

/// The most passes any loop of the kani library's `Arbitrary::any` for `ty`
/// runs: `N` for `[T; N]` of a `T` that is not trivially arbitrary, through
/// the library's own impls for arrays, tuples, `Option`, `Result` and `Box`
/// (each builds its parts with their `any()`). `0` when it runs none, and for
/// any other type, whose `any()` is not the library's.
pub(in crate::codegen_ay) fn kani_any_loop_passes(ty: Ty) -> u64 {
    passes(ty, 0)
}

/// [`kani_any_loop_passes`] of `[elem; n]`: what the library's
/// `kani::any::<[elem; n]>()` runs, which `exact_vec`, `any_vec` and the
/// `Vec` `bounded_any::<n>` each call for their elements.
pub(in crate::codegen_ay) fn kani_any_array_loop_passes(elem: Ty, n: u64) -> u64 {
    array_passes(elem, n, 0)
}

fn array_passes(elem: Ty, n: u64, depth: usize) -> u64 {
    let inner = passes(elem, depth + 1);
    if trivially_arbitrary(elem) { inner } else { n.max(inner) }
}

fn passes(ty: Ty, depth: usize) -> u64 {
    if depth > MAX_ANY_TYPE_DEPTH {
        return 0;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Array(elem, len)) => {
            array_passes(elem, len.eval_target_usize().ok().unwrap_or(0), depth)
        }
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            tys.iter().map(|ty| passes(*ty, depth + 1)).max().unwrap_or(0)
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let name = def.name();
            let library_wrapper = matches!(
                name.as_str(),
                "std::option::Option"
                    | "core::option::Option"
                    | "std::result::Result"
                    | "core::result::Result"
                    | "std::boxed::Box"
                    | "alloc::boxed::Box"
            );
            if !library_wrapper {
                return 0;
            }
            // `Option<T>` and `Box<T, A>` build a `T` (never the allocator),
            // `Result<T, E>` a `T` or an `E`.
            let parts = if name.ends_with("Result") { 2 } else { 1 };
            args.0
                .iter()
                .filter_map(|arg| match arg {
                    GenericArgKind::Type(ty) => Some(*ty),
                    _ => None,
                })
                .take(parts)
                .map(|ty| passes(ty, depth + 1))
                .max()
                .unwrap_or(0)
        }
        _ => 0,
    }
}

/// The kani library's `trivial_arbitrary!` types: their `any_array` is the
/// loop-free `any_raw_array`.
fn trivially_arbitrary(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)) => true,
        TyKind::RigidTy(RigidTy::Tuple(tys)) => tys.is_empty(),
        _ => false,
    }
}

/// The message of the check: Kani's wording, and why trust-mc states it here.
pub(in crate::codegen_ay) fn kani_any_unwind_message(passes: u64) -> String {
    format!(
        "unwinding assertion loop 0 (kani's Arbitrary::any_array runs {passes} passes, past the \
         declared unwind bound)"
    )
}
