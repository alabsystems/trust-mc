// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! String-path primitive comparison + `Step::unchecked` + wrapping/checked arithmetic.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//! Decomposed into submodules — Part of #2408.

pub(in crate::codegen_ay) mod bit_intrinsics;
pub(in crate::codegen_ay::chc) mod cmp_array;
pub(in crate::codegen_ay::chc) mod cmp_handlers;
mod cmp_raw_pointer;
pub(in crate::codegen_ay::chc) mod cmp_slice_backing;
mod dispatch_chain;
mod div_euclid;
mod exact_div;
mod fallback_dispatch;
pub(in crate::codegen_ay::chc) mod fast_math;
pub(in crate::codegen_ay::chc) mod float_predicates;
pub(in crate::codegen_ay::chc) mod float_rounding;
pub(in crate::codegen_ay) mod float_to_int_saturating;
pub(crate) mod math;
mod math_axioms;
pub(in crate::codegen_ay::chc) mod math_const;
pub(in crate::codegen_ay::chc) mod math_const_prescan;
mod math_range_axioms;
pub(in crate::codegen_ay::chc) mod misc_intrinsics;
mod misc_intrinsics_mem_zeroed;
mod misc_intrinsics_pointer;
mod misc_intrinsics_volatile;
mod misc_intrinsics_volatile_helpers;
pub(in crate::codegen_ay::chc) mod misc_intrinsics_write_bytes;
mod path_classifier;
mod pow;
pub(in crate::codegen_ay::chc) mod range_contains;
mod slice_as_array;
pub(in crate::codegen_ay::chc) mod slice_contains;
pub(in crate::codegen_ay::chc) mod slice_contains_data;
mod step_saturating;
mod step_wrapping;
mod tail_dispatch;
mod wrapping_abs;

pub(in crate::codegen_ay::chc) use dispatch_chain::CallCmpString;
