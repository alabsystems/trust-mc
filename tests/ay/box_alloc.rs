// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// kani-expect: test_nonnull_dangling=PROOF
// kani-expect: test_nonnull_same_type=PROOF
// kani-expect: test_nonnull_type_erasure_u8_to_i32=PROOF
// kani-expect: test_box_alloc_symbolic=PROOF
// kani-expect: test_box_array=PROOF
// kani-expect: test_box_bool=PROOF
// kani-expect: test_box_alloc_simple=PROOF
// kani-expect: test_box_mutation=PROOF
// kani-expect: test_box_struct=PROOF
// kani-expect: test_box_struct_mutation=PROOF
// kani-expect: test_box_u64=PROOF
// kani-expect: test_box_independence=PROOF
// NOTE: Most harnesses demoted PROOF->UNKNOWN by false proof defense (ay#8578).
// test_nonnull_dangling, test_box_alloc_symbolic, test_box_array, test_box_bool,
// test_nonnull_same_type, test_nonnull_type_erasure_u8_to_i32,
// test_box_alloc_simple, test_box_mutation, test_box_struct,
// test_box_struct_mutation, test_box_u64, and test_box_independence recovered
// to PROOF after ay bump and CHC pointer payload fixes (U242-U248, ay#9185).
// kani-flags: --ay-chc-track=mem
//
//! Heap allocation tests for Phase 4 (#893).
//!
//! Tests Box::new allocation, deallocation patterns, and heap
//! memory operations through the CHC encoding.
//!
//! Box operations require mem-level CHC tracking because:
//! - `*b = value` (deref store) is gated on Mem track level
//! - `*b` (deref load) resolves via memory arrays at Mem level
//! - At Reg level, stores are skipped and loads return unconstrained values
//!
//! Also includes NonNull type erasure regression tests (#912, #943).

use std::ptr::NonNull;

/// Test basic Box allocation and dereference.
#[kani::proof]
fn test_box_alloc_simple() {
    let b: Box<i32> = Box::new(42);
    kani::assert(*b == 42, "boxed value should be accessible");
}

/// Test Box allocation with symbolic value.
#[kani::proof]
fn test_box_alloc_symbolic() {
    let val: i32 = kani::any();
    kani::assume(val > 0);
    let b: Box<i32> = Box::new(val);
    kani::assert(*b == val, "boxed symbolic should equal original");
    kani::assert(*b > 0, "boxed value should satisfy constraint");
}

/// Test Box mutation through dereference.
#[kani::proof]
fn test_box_mutation() {
    let mut b: Box<i32> = Box::new(10);
    *b = 20;
    kani::assert(*b == 20, "boxed value should be modified");
}

/// Test multiple Box allocations are independent.
#[kani::proof]
fn test_box_independence() {
    let b1: Box<i32> = Box::new(100);
    let b2: Box<i32> = Box::new(200);
    kani::assert(*b1 == 100, "first box unchanged");
    kani::assert(*b2 == 200, "second box unchanged");
}

/// Simple struct for heap allocation tests.
struct BoxPair {
    x: i32,
    y: i32,
}

/// Test Box of struct.
#[kani::proof]
fn test_box_struct() {
    let b: Box<BoxPair> = Box::new(BoxPair { x: 10, y: 20 });
    kani::assert(b.x == 10, "struct field x accessible");
    kani::assert(b.y == 20, "struct field y accessible");
}

/// Test Box struct field mutation.
#[kani::proof]
fn test_box_struct_mutation() {
    let mut b: Box<BoxPair> = Box::new(BoxPair { x: 1, y: 2 });
    b.x = 100;
    kani::assert(b.x == 100, "field x modified");
    kani::assert(b.y == 2, "field y unchanged");
}

/// Test boxed array access.
#[kani::proof]
fn test_box_array() {
    let b: Box<[i32; 3]> = Box::new([1, 2, 3]);
    kani::assert(b[0] == 1, "arr[0] == 1");
    kani::assert(b[1] == 2, "arr[1] == 2");
    kani::assert(b[2] == 3, "arr[2] == 3");
}

/// Test Box with different types.
#[kani::proof]
fn test_box_u64() {
    let b: Box<u64> = Box::new(0xDEAD_BEEF_CAFE_BABE);
    kani::assert(*b == 0xDEAD_BEEF_CAFE_BABE, "u64 boxed correctly");
}

/// Test Box with bool type.
#[kani::proof]
fn test_box_bool() {
    let b: Box<bool> = Box::new(true);
    kani::assert(*b, "bool boxed correctly");
}

// Part of #912: NonNull/Unique type erasure regression tests
// Note: Unique<T> is unstable, so we only test NonNull directly.
// Box uses NonNull internally, so the Box tests above also exercise this path.

/// Test NonNull type erasure: same-type round trip.
/// Regression test for #912 - NonNull<T> must use bv64 sort, not datatype.
#[kani::proof]
fn test_nonnull_same_type() {
    let value: i32 = 42;
    let ptr: *const i32 = &value;
    // NonNull::new should preserve the pointer value
    // Use expect() to fail loudly if pointer is null (should never happen for stack ref)
    let nn: NonNull<i32> = NonNull::new(ptr as *mut i32).expect("stack pointer should be non-null");
    let recovered = unsafe { *nn.as_ptr() };
    kani::assert(recovered == 42, "NonNull same-type should work");
}

/// Test NonNull type erasure: cast from u8 to i32.
/// This is the core pattern that breaks without #912 fix.
/// Rust's allocator uses NonNull<u8> internally, then casts to NonNull<T>.
#[kani::proof]
fn test_nonnull_type_erasure_u8_to_i32() {
    // Create a value and get its address
    let value: i32 = 0x1234;
    let ptr_i32: *mut i32 = &value as *const i32 as *mut i32;

    // Cast through u8 pointer (simulating allocator pattern)
    let ptr_u8: *mut u8 = ptr_i32 as *mut u8;

    // Create NonNull<u8> from the u8 pointer
    let nn_u8: NonNull<u8> = NonNull::new(ptr_u8).expect("non-null");

    // Cast NonNull<u8> to NonNull<i32> (type erasure pattern from #912)
    let nn_i32: NonNull<i32> = nn_u8.cast();

    // Read through the typed pointer
    let recovered = unsafe { *nn_i32.as_ptr() };
    kani::assert(recovered == 0x1234, "NonNull cast u8->i32 should preserve value");
}

/// Test NonNull dangling pointer (another common pattern in allocator).
#[kani::proof]
fn test_nonnull_dangling() {
    // NonNull::dangling() creates a well-aligned non-null pointer
    // that doesn't point to valid memory
    let dangling: NonNull<i32> = NonNull::dangling();
    // The pointer should be non-null (aligned to i32)
    kani::assert(!dangling.as_ptr().is_null(), "dangling should be non-null");
}
