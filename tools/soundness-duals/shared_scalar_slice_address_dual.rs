// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#[repr(C)]
struct Pair {
    first: u64,
    second: u64,
}

#[inline(never)]
fn second_slice(pair: &Pair) -> &[u64] {
    core::slice::from_ref(&pair.second)
}

#[kani::proof]
fn one_element_alias_safe() {
    let pair = Pair { first: 3, second: 7 };
    let slice = second_slice(&pair);
    assert!(slice.len() == 1);
    assert!(slice[0] == 7);
    assert!(slice.as_ptr() == &raw const pair.second);
}

#[kani::proof]
fn one_element_wrong_address_bug() {
    let pair = Pair { first: 3, second: 7 };
    assert!(second_slice(&pair).as_ptr() == &raw const pair.first);
}

#[kani::proof]
fn one_element_dead_owner_after_widening_bug() {
    let value: u64 = kani::any();
    let escaped: &'static [u64];
    {
        let local = value;
        let slice = core::slice::from_ref(&local);
        escaped = unsafe { core::mem::transmute::<&[u64], &'static [u64]>(slice) };
    }
    assert!(escaped[0] == value);
}

#[kani::proof]
fn one_element_dead_owner_before_widening_bug() {
    let value: u64 = kani::any();
    let escaped: &'static [u64];
    {
        let local = value;
        let source = unsafe { core::mem::transmute::<&u64, &'static u64>(&local) };
        escaped = core::slice::from_ref(source);
    }
    assert!(escaped[0] == value);
}

#[kani::proof]
fn one_element_conditional_raw_owner_bug() {
    let value: u64 = kani::any();
    let live = value;
    let escaped: *const u64;
    {
        let dead = value;
        escaped = if kani::any() {
            core::slice::from_ref(&dead).as_ptr()
        } else {
            core::slice::from_ref(&live).as_ptr()
        };
    }
    assert!(unsafe { *escaped } == value);
}

#[kani::proof]
fn one_element_reference_alias_safe() {
    let value: u64 = kani::any();
    let pair = Pair { first: 3, second: value };
    let slice = second_slice(&pair);
    let reference = &slice[0];
    assert!(core::ptr::eq(reference, &pair.second));
    assert!(*reference == value);
}

#[kani::proof]
fn one_element_reference_dead_owner_bug() {
    let value: u64 = kani::any();
    let escaped: &'static u64;
    {
        let local = value;
        let slice = core::slice::from_ref(&local);
        let reference = &slice[0];
        escaped = unsafe { core::mem::transmute::<&u64, &'static u64>(reference) };
    }
    assert!(*escaped == value);
}

#[kani::proof]
fn one_element_conditional_raw_live_safe() {
    let left: u64 = kani::any();
    let right: u64 = kani::any();
    let select_left: bool = kani::any();
    let pointer = if select_left {
        core::slice::from_ref(&left).as_ptr()
    } else {
        core::slice::from_ref(&right).as_ptr()
    };
    let expected = if select_left { left } else { right };
    assert!(unsafe { *pointer } == expected);
}

#[kani::proof]
fn one_element_current_bytes_safe() {
    let mut pair = Pair { first: 3, second: 0x0102_0304_0506_0708 };
    pair.second = 0x0807_0605_0403_0201;
    let slice = second_slice(&pair);
    assert!(slice[0] == 0x0807_0605_0403_0201);
    assert!(slice.as_ptr() == &raw const pair.second);
}

#[kani::proof]
fn one_element_pointer_only_safe() {
    let pair = Pair { first: 3, second: 7 };
    // The root's symbolic aggregate entry must not make a pointer-only use
    // depend on whether its first field has a readable byte image.
    let slice = core::slice::from_ref(&pair.first);
    assert!(slice.len() == 1);
    assert!(slice.as_ptr() == &raw const pair.first);
}

#[kani::proof]
fn one_element_stale_after_raw_write_refusal() {
    let mut pair = Pair { first: 3, second: 7 };
    let pointer = &raw mut pair.second;
    let slice = second_slice(&pair);
    // This unsafe alias write must never leave a clean proof based only on
    // the logical slice's older backing. No aliasing-validity claim is made.
    unsafe { *pointer = 9 };
    assert!(slice[0] == 7);
}

#[kani::proof]
fn one_element_conditional_raw_end_bug() {
    let left: u64 = kani::any();
    let right: u64 = kani::any();
    let select_left: bool = kani::any();
    let pointer = if select_left {
        core::slice::from_ref(&left).as_ptr().wrapping_add(1)
    } else {
        core::slice::from_ref(&right).as_ptr()
    };
    let expected = if select_left { left } else { right };
    assert!(unsafe { *pointer } == expected);
}

#[kani::proof]
fn one_element_conditional_raw_prefix_field_safe() {
    let left: u64 = kani::any();
    let right: u64 = kani::any();
    let select_left: bool = kani::any();
    let pointer = if select_left {
        core::slice::from_ref(&left).as_ptr()
    } else {
        core::slice::from_ref(&right).as_ptr()
    };
    let pair = pointer.cast::<Pair>();
    let expected = if select_left { left } else { right };
    assert!(unsafe { (*pair).first } == expected);
}
