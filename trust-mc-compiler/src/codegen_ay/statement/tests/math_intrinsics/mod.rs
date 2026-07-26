// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Math intrinsic tests.
//!
//! Tests for fast-math finite detection, constant extraction from AY
//! expressions, math intrinsic expression patterns, MIR-driven codegen,
//! and dispatch routing.
//!
//! Decomposed from a single 1,807-line file into per-family modules.
//! Part of #3730 (test decomposition for #3094 float parity work).
//!
//! Submodules:
//! - `fixtures`: Shared probe source and helper functions
//! - `finite_detection`: IEEE 754 exponent field extraction tests
//! - `constant_extraction`: AY expression constant round-trip tests
//! - `constant_folding`: Rust std math function folding verification
//! - `fast_math_expr`: Fast-math BinOp expression shape tests
//! - `math_codegen_f32`: MIR-driven f32 math intrinsic codegen
//! - `math_codegen_f64`: MIR-driven f64 math intrinsic codegen
//! - `fast_math_codegen_f32`: MIR-driven f32 fast-math codegen
//! - `fast_math_codegen_f64`: MIR-driven f64 fast-math codegen
//! - `dispatch_routing`: `dispatch_math()` routing tests

use super::*;

mod fixtures;
use fixtures::*;

mod constant_extraction;
mod constant_folding;
mod dispatch_routing;
mod fast_math_codegen_f32;
mod fast_math_codegen_f64;
mod fast_math_expr;
mod finite_detection;
mod math_codegen_f32;
mod math_codegen_f64;
