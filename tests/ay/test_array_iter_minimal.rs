// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-flags: --unstable=array-iter-unroll
// kani-expect: PROOF
//! Minimal test cases for array iterator support.
//!
//! Related issues:
//! - #468: Array iterator infrastructure support
//! - #492: Zero-length array iteration fix
//!
//! Status:
//! - Zero-length iteration: PASSING (ArrayIterUnrollPass)
//! - Non-zero iteration: PASSING (see test_array_iter_nonzero.rs)
//!
//! ArrayIterUnrollPass transforms array for-loops to indexed loops,
//! bypassing the need for iterator infrastructure (PolymorphicIter, IndexRange).

/// Test zero-length array iteration with local binding.
/// The array is passed as Copy/Move operand in MIR.
#[kani::proof]
fn check_zero_length_iteration() {
    let empty: [u8; 0] = [];
    for _ in empty {
        unreachable!("No iteration should happen");
    }
}

/// Test zero-length array iteration with inline constant.
/// Regression test for #492: array passed as Operand::Constant in MIR.
/// Without ArrayIterUnrollPass transformation, this would fail on
/// IndexRange::next_unchecked which AY can't handle.
#[kani::proof]
fn check_zero_length_constant_iteration() {
    // Inline empty array literal - compiles to Operand::Constant(ZeroSized)
    for _x in [] as [u8; 0] {
        unreachable!("No iteration should happen");
    }
}

/// Test zero-length ZST array iteration.
/// Edge case: [(); 0] is both zero-length AND has ZST element type.
/// The transformation should handle this by using a dummy place and
/// generating Rvalue::Aggregate(Tuple, []) for the element.
#[kani::proof]
fn check_zero_length_zst_iteration() {
    // ZST element type + zero length = double edge case
    let empty: [(); 0] = [];
    for _x in empty {
        unreachable!("No iteration should happen");
    }
}
