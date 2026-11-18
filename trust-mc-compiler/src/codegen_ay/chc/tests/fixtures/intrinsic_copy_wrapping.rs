// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

pub fn copy_wrapping_valid() {
    let mut array = [3i32, 7, 11];
    let base = array.as_mut_ptr();
    let source = base.wrapping_add(1);
    let destination = base.wrapping_add(2);
    unsafe { core::intrinsics::copy(source, destination, 1) };
    assert!(array[0] == 3 && array[1] == 7 && array[2] == 7);

    // Leaving an allocation through wrapping arithmetic is defined. Returning
    // to it restores the original window, rather than retaining index one.
    let returned = base.wrapping_sub(1).wrapping_add(1);
    unsafe { core::intrinsics::copy(returned, destination, 1) };
    assert!(array[2] == 3);
}

pub fn copy_far_wrapping_refusal() {
    let mut array = [3i32, 7, 11];
    let base = array.as_mut_ptr();
    // A 2^64-byte step returns to the original address. The new bounded
    // metadata path must abstain instead of calling this element 2^62.
    let returned = base.wrapping_add(1usize << 62);
    unsafe { core::intrinsics::copy(returned, base.wrapping_add(2), 1) };
    assert!(array[2] == 3);
}

pub fn copy_alias_count_valid() {
    let mut array = [3i32, 7, 11];
    let mut count = 4usize;
    let alias = &raw mut count;
    unsafe { *alias = 1 };
    let copied = count;
    let observed = copied as u32 as usize;
    let base = array.as_mut_ptr();
    unsafe { core::intrinsics::copy(base, base.wrapping_add(1), observed) };
    assert!(array[0] == 3 && array[1] == 3 && array[2] == 11);
}

pub fn copy_alias_displacement_valid() {
    let mut array = [3i32, 7, 11];
    let mut step = 1usize;
    let alias = &raw mut step;
    unsafe { *alias = 0 };
    let copied = step;
    let observed = copied as u32 as usize;
    let base = array.as_mut_ptr();
    let source = base.wrapping_sub(observed);
    unsafe { core::intrinsics::copy(source, base.wrapping_add(1), 1) };
    assert!(array[0] == 3 && array[1] == 3 && array[2] == 11);
}

mod mut_ptr {
    #[inline(never)]
    pub fn wrapping_sub(pointer: *mut i32, _count: usize) -> *mut i32 {
        pointer
    }
}

pub fn copy_foreign_wrapping_valid() {
    let mut array = [3i32, 7, 11];
    let base = array.as_mut_ptr();
    let source = mut_ptr::wrapping_sub(base, 1);
    unsafe { core::intrinsics::copy(source, base.wrapping_add(1), 1) };
    assert!(array[0] == 3 && array[1] == 3 && array[2] == 11);
}
