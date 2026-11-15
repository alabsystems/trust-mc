// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Nested-call model of `<Vec<T> as kani::BoundedArbitrary>::bounded_any`
//! (`String` keeps its library body, see `is_bounded_any_ctor_name`).
//!
//! `bounded_any` is usually reached INSIDE an inlined body: `Option<T>`'s and
//! `Result<T, E>`'s impls call `T::bounded_any::<N>()` from a closure, and a
//! `#[derive(BoundedArbitrary)]` body calls it per `#[bounded]` field. Walking
//! the library body havocs `Vec::from`, `as_mut_ptr` and `ptr::add`, whose
//! raw-pointer arguments trip the fail-closed
//! `inline_nested_call_writes_through_pointer` net, so every such harness was
//! demoted after its rows proved (ledger row 72: 11/11 rows proved on
//! `bounded-arbitrary/option.rs`, then `chc_translation_drop=3`). The walker
//! returns the same value the harness-level model builds
//! (`codegen_call_kani_any_vec::bounded_any_value`) instead.

use ay_bindings::Expr;
use rustc_public::mir::{LocalDecl, Operand};
use rustc_public::ty::Ty;
use tracing::debug;

use super::super::ChcCtx;
use super::super::codegen_call_kani_any_vec::{bounded_any_call, bounded_any_value};
use super::super::codegen_types::CodegenTypes;

/// The value of a `bounded_any::<N>` call for `Vec<T>` whose result
/// has type `dest_ty`, or `None` to leave the call to the ordinary nested path,
/// with the passes of the `any_array` loop the model does not run
/// (`shared::kani_any_loops`).
pub(super) fn try_inline_bounded_any_call(
    ctx: &mut ChcCtx<'_, '_>,
    func: &Operand,
    locals: &[LocalDecl],
    dest_ty: Ty,
) -> Option<(Expr, u64)> {
    let (target, bound) = bounded_any_call(func, locals, dest_ty)?;
    let sort = ChcCtx::translate_ty(dest_ty)?;
    let (value, _) = bounded_any_value(ctx, target, bound, &sort)?;
    debug!(?target, bound, "nested bounded_any: native model");
    let super::super::codegen_call_kani_any_vec::BoundedAnyTarget::Vec(elem) = target;
    Some((
        value,
        crate::codegen_ay::shared::kani_any_loops::kani_any_array_loop_passes(elem, bound),
    ))
}
