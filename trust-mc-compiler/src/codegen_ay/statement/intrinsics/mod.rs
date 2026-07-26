// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Intrinsics for AY codegen.
//!
//! This module implements Rust intrinsics organized by category:
//! - `bits`: Bit manipulation (rotate, funnel shift, ctlz, cttz, ctpop, bswap, bitreverse) + identity
//! - `math`: Floating-point math (sqrt, sin, cos, exp, log, etc.) + fast-math variants
//! - `simd`: SIMD operations (bitwise, arithmetic, comparisons, reductions, shuffle, cast)
//! - `memory`: Memory intrinsics (align_of_val, size_of_val)
//!
//! Split from a single 2294-line file per #1735.

mod bits;
mod bmc_fp_theory;
mod math;
mod math_const_fold;
mod memory;
mod simd;

/// Helper trait for Option-like conversions used in intrinsics.
/// Re-exported from parent module.
pub(super) use super::IntoOption;
