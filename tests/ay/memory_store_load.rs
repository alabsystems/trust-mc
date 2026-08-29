// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: test_memory_store_load_i32=PROOF
// kani-expect: test_memory_store_load_symbolic=BMC_SAFE
// kani-expect: test_memory_multiple_stores=PROOF
// kani-expect: test_memory_store_independence=PROOF
// kani-expect: test_memory_store_load_u64=PROOF
// kani-expect: test_memory_store_load_bool=PROOF
// kani-expect: test_memory_store_load_i8=PROOF
// kani-expect: test_memory_cross_branch=BMC_SAFE
// NOTE: 6 harnesses show PROOF via constant propagation (Part of #4276).
// The CHC encoder correctly emits error rules for kani::assert. The constant
// propagation pass (chc_const_prop.rs, Part of #3371) in split_emit_chc()
// evaluates store-load round-trips via McCarthy axiom (select(store(a,i,v),i)=v),
// resolves assertion conditions to constant true, and eliminate_trivially_false_rules()
// removes error rules whose violation constraint is false. These are genuine proofs
// by compile-time evaluation, not vacuous proofs.
// kani-flags: --ay-chc-track=mem
//
//! Memory store/load round-trip tests for Phase 3 (#892).
//!
//! Tests the CHC encoding of memory operations: store followed by load
//! should return the stored value.
//!
//! # Requirements
//!
//! These tests require mem-level tracking (`--ay-chc-track=mem`) because they
//! test pointer dereference operations. The default `reg` level does not track
//! memory operations (loads havoc, stores no-op).
//!
//! ```bash
//! ./scripts/trust_mc -Z unstable-options --backend=ay --ay-solver=z3 --ay-chc --ay-chc-track=mem tests/ay/memory_store_load.rs
//! ```

/// Test basic i32 memory round-trip: store then load.
#[kani::proof]
fn test_memory_store_load_i32() {
    let mut x: i32 = 0;
    let ptr: &mut i32 = &mut x;
    *ptr = 42;
    kani::assert(*ptr == 42, "load after store should return stored value");
}

/// Test memory round-trip with symbolic value.
#[kani::proof]
fn test_memory_store_load_symbolic() {
    let val: i32 = kani::any();
    kani::assume(val > 0);

    let mut storage: i32 = 0;
    let ptr: &mut i32 = &mut storage;
    *ptr = val;
    kani::assert(*ptr == val, "symbolic store/load round-trip");
    kani::assert(*ptr > 0, "loaded value should satisfy original constraint");
}

/// Test multiple stores to same location.
#[kani::proof]
fn test_memory_multiple_stores() {
    let mut x: i32 = 0;
    let ptr: &mut i32 = &mut x;
    *ptr = 10;
    kani::assert(*ptr == 10, "first store value");
    *ptr = 20;
    kani::assert(*ptr == 20, "second store should overwrite first");
}

/// Test stores to different locations are independent.
#[kani::proof]
fn test_memory_store_independence() {
    let mut x: i32 = 0;
    let mut y: i32 = 0;
    let px: &mut i32 = &mut x;
    let py: &mut i32 = &mut y;
    *px = 100;
    *py = 200;
    kani::assert(*px == 100, "x should be 100");
    kani::assert(*py == 200, "y should be 200");
}

/// Test u64 memory round-trip.
#[kani::proof]
fn test_memory_store_load_u64() {
    let mut x: u64 = 0;
    let ptr: &mut u64 = &mut x;
    *ptr = 0xDEAD_BEEF_CAFE_BABE;
    kani::assert(*ptr == 0xDEAD_BEEF_CAFE_BABE, "u64 store/load round-trip");
}

/// Test bool memory round-trip.
#[kani::proof]
fn test_memory_store_load_bool() {
    let mut flag: bool = false;
    let ptr: &mut bool = &mut flag;
    *ptr = true;
    kani::assert(*ptr, "bool store/load round-trip");
}

/// Test i8 memory round-trip (smallest integer type).
#[kani::proof]
fn test_memory_store_load_i8() {
    let mut x: i8 = 0;
    let ptr: &mut i8 = &mut x;
    *ptr = -42;
    kani::assert(*ptr == -42, "i8 store/load round-trip");
}

/// Test memory persistence across control flow (if-else branches).
/// Verifies SSA tracking handles block boundaries correctly.
#[kani::proof]
fn test_memory_cross_branch() {
    let cond: bool = kani::any();
    let mut x: i32 = 0;
    if cond {
        x = 10;
    } else {
        x = 20;
    }
    // After merge point, x should hold value from taken branch
    kani::assert(x == 10 || x == 20, "value persists across branch");
    kani::assert((cond && x == 10) || (!cond && x == 20), "correct branch value");
}
