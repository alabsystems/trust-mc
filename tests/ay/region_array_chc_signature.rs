// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
//! Integration test for region array CHC signatures (#1452).
//!
//! This test verifies that region arrays are added to CHC relation signatures
//! when heap allocation occurs via `assign_region_array_to_relation` (#1448).
//!
//! ## Verification Steps
//!
//! Run with CHC mode to produce SMT output:
//! ```sh
//! ./scripts/trust_mc -Z unstable-options --backend=ay --ay-solver=z3 --ay-chc \
//!     tests/ay/region_array_chc_signature.rs
//! ```
//!
//! Then check the generated SMT file for region arrays in relation signatures:
//! ```sh
//! grep -E 'region_[0-9]+_bv8' tests/ay/region_array_chc_signature__*.symtab.smt2
//! ```
//!
//! Expected: Each `(rule ...)` and `(declare-rel ...)` should include
//! `_test_region_array_signature_region_N_bv8` (input) and
//! `_test_region_array_signature_region_N_bv8__out` (output) state variables.
//!
//! ## What This Tests
//!
//! 1. Box::new triggers heap allocation which creates region arrays
//! 2. Region arrays are added to ChcCtx.state_vars and .output_state_vars
//! 3. These appear in SMT (declare-rel ...) and (rule ...) clauses
//!
//! ## Related Issues
//!
//! - #1448: Region arrays not added to CHC relation signatures (fixed)
//! - #1446: Region array sort mismatch (fixed)
//! - #1443: Region array implementation

/// Test that Box allocation creates region array in CHC signature.
///
/// This harness allocates a Box, triggering `assign_region_array_to_relation`.
/// The region array must appear in CHC relation signatures for soundness.
#[kani::proof]
fn test_region_array_signature() {
    // Allocate a Box - this triggers region array creation for object ID
    let b: Box<u32> = Box::new(42);

    // Verify allocation succeeded via CHC encoding
    // If region array is missing from relation signatures, CHC solver may
    // report unsound results (missing constraints on heap state)
    kani::assert(*b == 42, "boxed value accessible");
}

/// Test multiple allocations create distinct region arrays.
///
/// Each allocation gets a unique obj_id, and thus a unique region array.
/// All must appear in relation signatures.
#[kani::proof]
fn test_multiple_region_arrays() {
    let b1: Box<u32> = Box::new(100);
    let b2: Box<u64> = Box::new(200);

    // Both allocations create region arrays that must be in signatures
    kani::assert(*b1 == 100, "first box");
    kani::assert(*b2 == 200, "second box");
}

/// Test struct allocation creates region array.
///
/// Struct allocation uses same region array mechanism as primitives.
struct TestStruct {
    x: u32,
    y: u64,
}

#[kani::proof]
fn test_struct_region_array() {
    let b: Box<TestStruct> = Box::new(TestStruct { x: 10, y: 20 });

    kani::assert(b.x == 10, "struct field x");
    kani::assert(b.y == 20, "struct field y");
}
