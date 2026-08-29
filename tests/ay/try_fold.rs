// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: PROOF
// NOTE: main is a clean PROOF at ay 733ba8cd.
//
//! Tests iterator try_fold encoding — sort-mismatch handling.
//!
//! try_fold returns a wrapper type (Option/Result/ControlFlow) around the
//! accumulator. The IterFold stub produces a symbolic result of the correct
//! destination sort, which is a sound over-approximation.
//!
//! This harness verifies the encoding doesn't crash or produce sort errors.
//! The symbolic result satisfies: result is Some(()) OR result is None.

/// try_fold returning Option<()> — the result is well-typed.
/// The stub produces a symbolic Option<()> value, which satisfies
/// `result.is_some() || result.is_none()` (tautology on Option).
#[kani::proof]
#[kani::unwind(3)]
fn main() {
    let arr = [(1, 2), (2, 2)];
    let result: Option<()> = arr.iter().try_fold((), |_acc, &_i| Some(()));
    // The IterFold stub over-approximates: result can be any Option<()>.
    // Verify the encoding is well-typed by checking the tautological property.
    assert!(result.is_some() || result.is_none());
}
