// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Array equality compares the pointee values, never allocation addresses.

#![feature(ptr_metadata)]

#[kani::proof]
fn equal_box_arrays() {
    let a = Box::new([1u32, 2]);
    let b = Box::new([1u32, 2]);
    assert!(a == b);
}

#[kani::proof]
fn negated_equal_box_arrays_must_fail() {
    let a = Box::new([1u32, 2]);
    let b = Box::new([1u32, 2]);
    assert!(a != b);
}

#[kani::proof]
fn different_second_lane() {
    let a = Box::new([1u32, 2]);
    let b = Box::new([1u32, 3]);
    assert!(a != b);
}

#[kani::proof]
fn equal_different_second_lane_must_fail() {
    let a = Box::new([1u32, 2]);
    let b = Box::new([1u32, 3]);
    assert!(a == b);
}

#[kani::proof]
fn copied_array_reference() {
    let a = Box::new([1u32, 2]);
    let b = Box::new([1u32, 2]);
    let first = &*a;
    let alias = first;
    assert!(*alias == *b);
}

#[kani::proof]
fn mutation_updates_second_lane() {
    let mut a = Box::new([1u32, 2]);
    a[1] = 3;
    let b = Box::new([1u32, 3]);
    assert!(a == b);
}

#[kani::proof]
fn smaller_than_pointer_array() {
    let a = Box::new([1u8, 2, 3, 4]);
    let b = Box::new([1u8, 2, 3, 4]);
    assert!(a == b);
}

#[kani::proof]
fn larger_than_pointer_array() {
    let a = Box::new([1u32, 2, 3]);
    let b = Box::new([1u32, 2, 3]);
    assert!(a == b);
}

#[kani::proof]
fn interior_offset_must_not_reuse_allocation_base() {
    let a = Box::new([1u32, 2, 3, 4]);
    let tail = unsafe { &*a.as_ptr().add(2).cast::<[u32; 2]>() };
    assert!(*tail == [1u32, 2]);
}

#[kani::proof]
fn reassigned_reference_must_not_use_old_allocation() {
    let a = Box::new([1u32, 2]);
    let b = Box::new([3u32, 4]);
    let mut reference = &*a;
    if kani::any() {
        reference = &*b;
    }
    assert!(*reference == [1u32, 2]);
}

#[kani::proof]
fn smaller_array_content_difference_must_fail() {
    let a = Box::new([1u8, 2, 3, 4]);
    let b = Box::new([1u8, 2, 3, 5]);
    assert!(a == b);
}

#[kani::proof]
fn empty_box_arrays() {
    let a = Box::new([0u32; 0]);
    let b = Box::new([0u32; 0]);
    assert!(a == b);
}

#[kani::proof]
fn negated_empty_box_arrays_must_fail() {
    let a = Box::new([0u32; 0]);
    let b = Box::new([0u32; 0]);
    assert!(a != b);
}

static DATA: [u32; 4] = [1, 2, 3, 4];
const TAIL: *const u32 = unsafe { DATA.as_ptr().add(2) };
#[inline(never)]
fn refs_eq(a: &&[u32; 2], b: &&[u32; 2]) -> bool {
    a == b
}

#[kani::proof]
fn constant_tail_must_not_be_prefix() {
    let tail = unsafe { &*TAIL.cast::<[u32; 2]>() };
    assert!(*tail == [1u32, 2]);
}
#[kani::proof]
fn constant_tail_contents() {
    let tail = unsafe { &*TAIL.cast::<[u32; 2]>() };
    assert!(*tail == [3u32, 4]);
}
#[kani::proof]
fn nested_equal_ref_must_fail() {
    let a = Box::new([1u32, 2]);
    let b = Box::new([1u32, 2]);
    assert!(!refs_eq(&&*a, &&*b));
}
#[kani::proof]
fn nested_equal_ref() {
    let a = Box::new([1u32, 2]);
    let b = Box::new([1u32, 2]);
    assert!(refs_eq(&&*a, &&*b));
}

#[kani::proof]
fn raw_parts_tail_must_not_be_prefix() {
    let slice = core::ptr::from_raw_parts::<[u32]>(TAIL.cast::<()>(), 2);
    let tail = unsafe { &*slice.cast::<[u32; 2]>() };
    assert!(*tail == [1u32, 2]);
}

#[kani::proof]
fn raw_parts_tail_contents() {
    let slice = core::ptr::from_raw_parts::<[u32]>(TAIL.cast::<()>(), 2);
    let tail = unsafe { &*slice.cast::<[u32; 2]>() };
    assert!(*tail == [3u32, 4]);
}

#[kani::proof]
fn nested_fn_pointer_equal_ref_must_fail() {
    let a = Box::new([1u32, 2]);
    let b = Box::new([1u32, 2]);
    let compare: fn(&&[u32; 2], &&[u32; 2]) -> bool = refs_eq;
    assert!(!compare(&&*a, &&*b));
}

#[kani::proof]
fn mutation_must_not_keep_old_second_lane() {
    let mut a = Box::new([1u32, 2]);
    a[1] = 3;
    let b = Box::new([1u32, 2]);
    assert!(a == b);
}

#[kani::proof]
fn float_signed_zero_values_are_equal() {
    let a = Box::new([0.0f32]);
    let b = Box::new([-0.0f32]);
    assert!(a == b);
}

#[kani::proof]
fn float_signed_zero_ne_must_fail() {
    let a = Box::new([0.0f32]);
    let b = Box::new([-0.0f32]);
    assert!(a != b);
}

#[kani::proof]
fn float_nan_representation_eq_must_fail() {
    let a = Box::new([f32::NAN]);
    let b = Box::new([f32::NAN]);
    assert!(a == b);
}

enum CustomEq {
    A,
    B,
}
impl PartialEq for CustomEq {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

#[kani::proof]
fn custom_eq_is_not_representation_equality() {
    let a = Box::new([CustomEq::A]);
    let b = Box::new([CustomEq::B]);
    assert!(a == b);
}

#[kani::proof]
fn custom_eq_ne_must_fail() {
    let a = Box::new([CustomEq::A]);
    let b = Box::new([CustomEq::B]);
    assert!(a != b);
}

#[derive(PartialEq)]
struct HeterogeneousA(u32);
#[derive(PartialEq)]
struct HeterogeneousB(u32);
impl PartialEq<HeterogeneousB> for HeterogeneousA {
    fn eq(&self, _: &HeterogeneousB) -> bool {
        false
    }
}

#[kani::proof]
fn heterogeneous_equal_bits_must_fail() {
    let a = [HeterogeneousA(1)];
    let b = [HeterogeneousB(1)];
    assert!(a == b);
}

#[kani::proof]
fn heterogeneous_equal_bits_are_not_equal() {
    let a = [HeterogeneousA(1)];
    let b = [HeterogeneousB(1)];
    assert!(a != b);
}

#[kani::proof]
fn heterogeneous_slice_fn_pointer_must_fail() {
    let a = [HeterogeneousA(1)];
    let b = [HeterogeneousB(1)];
    let compare: fn(&[HeterogeneousA], &[HeterogeneousB]) -> bool = PartialEq::eq;
    assert!(compare(&a, &b));
}

#[kani::proof]
fn heterogeneous_slice_fn_pointer_are_not_equal() {
    let a = [HeterogeneousA(1)];
    let b = [HeterogeneousB(1)];
    let compare: fn(&[HeterogeneousA], &[HeterogeneousB]) -> bool = PartialEq::eq;
    assert!(!compare(&a, &b));
}

#[derive(Clone, Copy)]
struct Parity(u8);
impl PartialEq for Parity {
    fn eq(&self, other: &Self) -> bool {
        self.0 % 2 == other.0 % 2
    }
}

#[kani::proof]
fn custom_array_equality_uses_element_bodies() {
    let a = [Parity(1), Parity(2)];
    let b = [Parity(3), Parity(4)];
    assert!(a == b);
}

#[kani::proof]
fn custom_array_equal_parities_ne_must_fail() {
    let a = [Parity(1), Parity(2)];
    let b = [Parity(3), Parity(4)];
    assert!(a != b);
}

#[kani::proof]
fn custom_array_different_parities_eq_must_fail() {
    let a = [Parity(1), Parity(2)];
    let b = [Parity(2), Parity(4)];
    assert!(a == b);
}

#[derive(Clone, Copy)]
struct Divides(u8);
impl PartialEq for Divides {
    fn eq(&self, other: &Self) -> bool {
        self.0 % other.0 == 0
    }
}

#[kani::proof]
fn custom_array_short_circuit_skips_later_panic() {
    let a = [Divides(1), Divides(4)];
    let b = [Divides(2), Divides(0)];
    assert!(a != b);
}

#[kani::proof]
fn custom_array_first_element_panic_must_fail() {
    let a = [Divides(1), Divides(4)];
    let b = [Divides(0), Divides(2)];
    let _ = a == b;
}

#[kani::proof]
fn custom_array_later_element_panic_must_fail() {
    let a = [Divides(4), Divides(4)];
    let b = [Divides(2), Divides(0)];
    let _ = a != b;
}
