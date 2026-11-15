// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: where a `Box`'s data pointer comes from, as the
// far-pointer walk and the wrapped-dereference bound (heap/stack_address.rs)
// see it, beyond `Box::new` and `Box::from_raw` themselves.
// - A valid box moved out of an `Option` (`Some(Box::new(..)).unwrap()`) or a
//   struct field (`let b = h.b`) had an unknown source, so its extent was not
//   modeled and an in-bounds wrapped dereference failed closed where main and
//   Kani prove it (second review of round 9 of fix/chc-false-certificates,
//   2026-10-15, probes r2_boxsrc.rs p05, p06). The walk now follows a field
//   move out of an aggregate local that is not written in part, and the
//   unwrapping of a `Some` / `Ok` aggregate.
// - A far pointer round-tripped through a sized `Box<u8>` or `Box::leak` and
//   stepped back drew a free far bit (`wrapping_step_far_unknown`): the step's
//   64-bit offset was not followed through the inlined `Box::from_raw` /
//   `Box::into_raw` / `Box::leak` bodies (`Box(Unique::new_unchecked(p), _)`,
//   the data pointer read back through `&mut (*m).0`, the transmute of its
//   `NonNull`, `&mut *ptr`), and its dereference or comparison failed closed
//   where main and Kani prove it (probes r2_roundtrip.rs r01, r02, r03, r07).
//   `Box::from_raw` of memory that is not a `Box` allocation is undefined
//   behavior Kani does not report; the box then holds the pointer it was built
//   from, bit for bit.

fn far_k() -> usize {
    let k: usize = kani::any();
    kani::assume(k == 1usize << 48);
    k
}

fn idx4() -> usize {
    let k: usize = kani::any();
    kani::assume(k < 4);
    k
}

struct Holder {
    b: Box<[u8; 4]>,
}

struct Holder16 {
    b: Box<[u8; 16]>,
}

#[kani::proof]
fn safe_box_from_option_unwrap_step_in_bounds() {
    let o = Some(Box::new([6u8; 4]));
    let b = o.unwrap();
    let p = Box::into_raw(b) as *mut u8;
    let v = unsafe { *p.wrapping_add(idx4()) };
    assert!(v == 6);
    unsafe { drop(Box::from_raw(p as *mut [u8; 4])) };
}

#[kani::proof]
fn bug_box_from_option_unwrap_step_out_of_bounds() {
    let o = Some(Box::new([6u8; 4]));
    let b = o.unwrap();
    let p = Box::into_raw(b) as *mut u8;
    let k: usize = kani::any();
    kani::assume(k >= 4 && k < 8);
    let v = unsafe { *p.wrapping_add(k) };
    assert!(v == v);
}

#[kani::proof]
fn safe_box_from_result_unwrap_step_in_bounds() {
    let r: Result<Box<[u8; 4]>, ()> = Ok(Box::new([3u8; 4]));
    let b = r.unwrap();
    let p = Box::into_raw(b) as *mut u8;
    let v = unsafe { *p.wrapping_add(idx4()) };
    assert!(v == 3);
}

#[kani::proof]
fn safe_box_from_struct_field_step_in_bounds() {
    let h = Holder { b: Box::new([8u8; 4]) };
    let b = h.b;
    let p = Box::into_raw(b) as *mut u8;
    let v = unsafe { *p.wrapping_add(idx4()) };
    assert!(v == 8);
    unsafe { drop(Box::from_raw(p as *mut [u8; 4])) };
}

#[kani::proof]
fn bug_box_from_struct_field_step_out_of_bounds() {
    let h = Holder { b: Box::new([8u8; 4]) };
    let b = h.b;
    let p = Box::into_raw(b) as *mut u8;
    let k: usize = kani::any();
    kani::assume(k >= 4 && k < 8);
    let v = unsafe { *p.wrapping_add(k) };
    assert!(v == v);
}

// The field was overwritten with a box over a 4-byte block taken as a
// `Box<[u8; 16]>`: the box moved out of it is bounded by its own allocation.
#[kani::proof]
fn bug_box_from_overwritten_struct_field_reads_past_end() {
    let mut h = Holder16 { b: Box::new([0u8; 16]) };
    let small = Box::into_raw(Box::new([7u8; 4]));
    h.b = unsafe { Box::from_raw(small as *mut [u8; 16]) };
    let b = h.b;
    let p = Box::into_raw(b) as *mut u8;
    let k: usize = kani::any();
    kani::assume(k >= 8 && k < 12);
    let v = unsafe { *p.wrapping_add(k) };
    assert!(v == v);
}

#[kani::proof]
fn safe_far_round_trip_sized_box_step_back() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k = far_k();
    let q = p.wrapping_byte_add(k) as *mut u8;
    let b: Box<u8> = unsafe { Box::from_raw(q) };
    let r = Box::into_raw(b).wrapping_byte_sub(k);
    assert!(unsafe { *r } == 1);
}

#[kani::proof]
fn bug_far_round_trip_sized_box_step_back() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k = far_k();
    let q = p.wrapping_byte_add(k) as *mut u8;
    let b: Box<u8> = unsafe { Box::from_raw(q) };
    let r = Box::into_raw(b).wrapping_byte_sub(k);
    assert!(unsafe { *r } == 2);
}

#[kani::proof]
fn safe_far_round_trip_step_back_other_amount() {
    let a = [1u8, 2, 3, 4];
    let p = a.as_ptr();
    let k = far_k();
    let q = p.wrapping_byte_add(k + 1) as *mut u8;
    let b: Box<u8> = unsafe { Box::from_raw(q) };
    let r = Box::into_raw(b).wrapping_byte_sub(k);
    assert!(unsafe { *r } == 2);
}

#[kani::proof]
fn bug_far_round_trip_step_back_other_amount() {
    let a = [1u8, 2, 3, 4];
    let p = a.as_ptr();
    let k = far_k();
    let q = p.wrapping_byte_add(k + 1) as *mut u8;
    let b: Box<u8> = unsafe { Box::from_raw(q) };
    let r = Box::into_raw(b).wrapping_byte_sub(k);
    assert!(unsafe { *r } == 1);
}

#[kani::proof]
fn safe_far_round_trip_equals_its_source() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_add(far_k()) as *mut u8;
    let b: Box<u8> = unsafe { Box::from_raw(q) };
    let r = Box::into_raw(b);
    assert!(r == q);
}

#[kani::proof]
fn bug_far_round_trip_differs_from_its_source() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_add(far_k()) as *mut u8;
    let b: Box<u8> = unsafe { Box::from_raw(q) };
    let r = Box::into_raw(b);
    assert!(r != q);
}

#[kani::proof]
fn safe_far_round_trip_leak_step_back() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k = far_k();
    let q = p.wrapping_byte_add(k) as *mut u8;
    let b: Box<u8> = unsafe { Box::from_raw(q) };
    let l: &'static mut u8 = Box::leak(b);
    let r = (l as *mut u8).wrapping_byte_sub(k);
    assert!(unsafe { *r } == 1);
}

#[kani::proof]
fn bug_far_round_trip_leak_step_back() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k = far_k();
    let q = p.wrapping_byte_add(k) as *mut u8;
    let b: Box<u8> = unsafe { Box::from_raw(q) };
    let l: &'static mut u8 = Box::leak(b);
    let r = (l as *mut u8).wrapping_byte_sub(k);
    assert!(unsafe { *r } == 2);
}

// The round trip carried through a tuple: the same pointer.
#[kani::proof]
fn safe_far_round_trip_through_tuple_step_back() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k = far_k();
    let t = (p.wrapping_byte_add(k) as *mut u8, 0u8);
    let b: Box<u8> = unsafe { Box::from_raw(t.0) };
    let r = Box::into_raw(b).wrapping_byte_sub(k);
    assert!(unsafe { *r } == 1);
}

// The tuple slot was overwritten before the box was built: a different step.
#[kani::proof]
fn bug_far_round_trip_through_overwritten_tuple() {
    let a = [1u8, 2, 3, 4];
    let p = a.as_ptr();
    let k = far_k();
    let mut t = (p.wrapping_byte_add(k) as *mut u8, 0u8);
    t.0 = p.wrapping_byte_add(k + 1) as *mut u8;
    let b: Box<u8> = unsafe { Box::from_raw(t.0) };
    let r = Box::into_raw(b).wrapping_byte_sub(k);
    assert!(unsafe { *r } == 1);
}
