// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared rvalue/operand translation for inline body translators.
//!
//! Provides a unified `inline_rvalue_to_expr` and `inline_operand_to_expr` used
//! by the closure, virtual, and quantifier inline translators. Place resolution
//! is parameterized via `PlaceResolver` to abstract over capture-array vs
//! memory-backed field-map strategies.
//!
//! Part of #3241: deduplicate inline translator divergences.
//! Part of #3913 Step 6: split into rvalue.rs + place.rs submodules.

use ay_bindings::Expr;
use std::collections::HashMap;

mod discriminant;
pub(in crate::codegen_ay) mod field_map_projection;
pub(in crate::codegen_ay) mod place;
pub(in crate::codegen_ay) mod rvalue;
mod rvalue_cast;
mod rvalue_ptr;
mod subslice;

/// Strategy for resolving projected places within inline body translation.
///
/// Closures access captured variables via `local_1.field(N)` → `captures[N]`.
/// Virtual methods access self fields via `(*self).field` → memory-backed loads.
#[derive(Clone, Copy)]
pub(in crate::codegen_ay) enum PlaceResolver<'a> {
    /// Closure capture resolution: local 1 field projections → captures array.
    Captures(&'a [Expr]),
    /// Virtual method resolution: projected places via Deref/Datatype/memory-backed loads.
    FieldMap(&'a HashMap<(usize, usize), Expr>),
}

// Re-export the primary public API so existing callers continue to work.
pub(in crate::codegen_ay) use place::{
    inline_coroutine_discriminant_expr, inline_operand_to_expr, resolve_place,
};
pub(in crate::codegen_ay) use rvalue::inline_rvalue_to_expr;
pub(in crate::codegen_ay) use subslice::apply_inline_subslice_write;
