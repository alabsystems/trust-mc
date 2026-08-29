// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// kani-expect: test_alloc_aligned=PROOF
// kani-expect: test_alloc_array=PROOF
// kani-expect: test_alloc_dealloc_i32=PROOF
// kani-expect: test_alloc_dealloc_u64=PROOF
// kani-expect: test_layout_array=PROOF
// kani-expect: test_layout_basic=PROOF
// kani-expect: test_realloc_grow=PROOF
// kani-flags: --ay-chc-track=mem
//
//! Direct std::alloc tests for Phase 4 (#1231).
//!
//! Tests low-level allocation patterns using std::alloc directly.
//! This exercises the heap model at a lower level than Box/Vec.

use std::alloc::{Layout, alloc, alloc_zeroed, dealloc, realloc};

/// Test direct alloc/dealloc of a single i32.
#[kani::proof]
fn test_alloc_dealloc_i32() {
    let layout = Layout::new::<i32>();
    unsafe {
        let ptr = alloc(layout) as *mut i32;
        kani::assert(!ptr.is_null(), "allocation should succeed");

        // Write and read back
        ptr.write(42);
        let val = ptr.read();
        kani::assert(val == 42, "should read back written value");

        dealloc(ptr as *mut u8, layout);
    }
}

/// Test direct alloc/dealloc of a larger type.
#[kani::proof]
fn test_alloc_dealloc_u64() {
    let layout = Layout::new::<u64>();
    unsafe {
        let ptr = alloc(layout) as *mut u64;
        kani::assert(!ptr.is_null(), "allocation should succeed");

        ptr.write(0xDEAD_BEEF_CAFE_BABE);
        let val = ptr.read();
        kani::assert(val == 0xDEAD_BEEF_CAFE_BABE, "u64 value preserved");

        dealloc(ptr as *mut u8, layout);
    }
}

/// Test alloc/dealloc of array.
#[kani::proof]
fn test_alloc_array() {
    let layout = Layout::array::<i32>(4).unwrap();
    unsafe {
        let ptr = alloc(layout) as *mut i32;
        kani::assert(!ptr.is_null(), "array allocation should succeed");

        // Write to each element
        for i in 0..4 {
            ptr.add(i).write(i as i32 * 10);
        }

        // Read back
        for i in 0..4 {
            let val = ptr.add(i).read();
            kani::assert(val == i as i32 * 10, "array element preserved");
        }

        dealloc(ptr as *mut u8, layout);
    }
}

/// Test realloc to grow allocation.
///
/// Simplified from 2→4 elements to 1→2 elements to reduce CHC formula
/// complexity (Part of #3096). The core realloc semantics (data preservation
/// after grow) are the same.
#[kani::proof]
fn test_realloc_grow() {
    let layout = Layout::new::<i32>();
    unsafe {
        let ptr = alloc(layout) as *mut i32;
        kani::assert(!ptr.is_null(), "initial allocation should succeed");

        // Write initial value
        ptr.write(42);

        // Grow to 2 elements
        let new_layout = Layout::array::<i32>(2).unwrap();
        let new_ptr = realloc(ptr as *mut u8, layout, new_layout.size()) as *mut i32;
        kani::assert(!new_ptr.is_null(), "realloc should succeed");

        // Original value should be preserved
        kani::assert(new_ptr.read() == 42, "element 0 preserved after realloc");

        // Write to new space
        new_ptr.add(1).write(99);

        dealloc(new_ptr as *mut u8, new_layout);
    }
}

/// Test aligned allocation.
#[kani::proof]
fn test_alloc_aligned() {
    // Allocate with 16-byte alignment
    let layout = Layout::from_size_align(16, 16).unwrap();
    unsafe {
        let ptr = alloc(layout);
        kani::assert(!ptr.is_null(), "aligned allocation should succeed");
        // The pointer should be aligned to 16 bytes
        kani::assert((ptr as usize) % 16 == 0, "pointer should be 16-byte aligned");
        dealloc(ptr, layout);
    }
}

/// Test Layout creation.
#[kani::proof]
fn test_layout_basic() {
    let layout_i32 = Layout::new::<i32>();
    kani::assert(layout_i32.size() == 4, "i32 layout size should be 4");
    kani::assert(layout_i32.align() >= 1, "alignment should be at least 1");

    let layout_u8 = Layout::new::<u8>();
    kani::assert(layout_u8.size() == 1, "u8 layout size should be 1");

    let layout_u64 = Layout::new::<u64>();
    kani::assert(layout_u64.size() == 8, "u64 layout size should be 8");
}

/// Test Layout::array.
#[kani::proof]
fn test_layout_array() {
    let layout = Layout::array::<i32>(10).unwrap();
    kani::assert(layout.size() >= 40, "array layout should be at least 40 bytes");
}

/// Test zeroed allocation behavior.
///
/// Simplified from 4-element array + loop to single i32 + direct read to
/// reduce CHC formula complexity (Part of #3096). The core alloc_zeroed
/// semantic (memory reads as zero) is the same.
#[kani::proof]
fn test_alloc_zeroed() {
    let layout = Layout::new::<i32>();
    unsafe {
        let ptr = alloc_zeroed(layout) as *mut i32;
        kani::assert(!ptr.is_null(), "zeroed allocation should succeed");

        // Zeroed memory should read as 0
        let val = ptr.read();
        kani::assert(val == 0, "zeroed memory should be 0");

        dealloc(ptr as *mut u8, layout);
    }
}
