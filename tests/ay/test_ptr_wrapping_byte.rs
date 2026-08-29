// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: PROOF
//
//! AY harnesses for PtrWrappingByteAdd/PtrWrappingByteSub (#3519).
//!
//! Uses `*mut u32` (sizeof(T) = 4) so byte-level and element-level
//! pointer arithmetic produce distinguishable results.
//! If the encoding incorrectly applied sizeof(T) scaling, the assertions
//! would fail (offset 16 instead of 4).

/// wrapping_byte_add adds N bytes, NOT N elements.
/// For *mut u32 (sizeof = 4), byte_add(4) moves 4 bytes, not 4*4=16.
#[kani::proof]
fn test_wrapping_byte_add_u32() {
    let mut val: u32 = 42;
    let ptr: *mut u32 = &mut val;
    let base = ptr as usize;

    let new_ptr = ptr.wrapping_byte_add(4);
    let new_addr = new_ptr as usize;

    // Byte-level: base + 4. If element-level were used, it would be base + 16.
    kani::assert(
        new_addr == base + 4,
        "wrapping_byte_add(4) should advance by 4 bytes, not 4 elements",
    );
}

/// wrapping_byte_sub undoes wrapping_byte_add on the same offset.
/// Uses roundtrip (add then sub) to verify byte-level subtraction
/// without relying on usize::wrapping_sub encoding.
#[kani::proof]
fn test_wrapping_byte_sub_u32() {
    let mut val: u32 = 42;
    let ptr: *mut u32 = &mut val;

    // byte_add(4) then byte_sub(4) must return to the original address.
    // This verifies byte_sub is the inverse of byte_add.
    let roundtrip = ptr.wrapping_byte_add(4).wrapping_byte_sub(4);
    kani::assert(
        roundtrip as usize == ptr as usize,
        "wrapping_byte_sub(4) should undo wrapping_byte_add(4)",
    );
}
