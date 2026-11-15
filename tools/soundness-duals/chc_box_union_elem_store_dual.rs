// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: an element store through a pointer into an array that
// is a field of a union (`b.h[i] = v` on a `Box<union { x: u32, h: [u16; 2] }>`)
// wrote only the element's own memory views. A later read of the union, whole
// (`b.x`) or through the same element (`b.h[i]`), decoded the union from its
// object's region array, which the store had not touched, and read the value
// from before the store: the bug rows were clean proofs where Kani fails them
// and the safe rows certified counterexamples where Kani proves them. Found
// by the first review of round 9 of fix/chc-false-certificates (2026-10-14,
// probes rv_union3.rs / rv_union4.rs), the same on main f5dfb8d48. Such a
// store now fails closed (deref_mem.rs `deref_elem_store_through_union`).

#[repr(C)]
union U32 {
    x: u32,
    h: [u16; 2],
}

#[repr(C)]
union U64B {
    x: u64,
    b: [u8; 8],
}

#[repr(C)]
struct SA {
    h: [u16; 2],
}

#[kani::proof]
fn bug_box_union_elem0_write_read_whole() {
    let mut b = Box::new(U32 { x: 0x0102_0304 });
    unsafe { b.h[0] = 0xAAAA };
    assert!(unsafe { b.x } == 0x0102_0304);
}

#[kani::proof]
fn safe_box_union_elem0_write_read_whole() {
    let mut b = Box::new(U32 { x: 0x0102_0304 });
    unsafe { b.h[0] = 0xAAAA };
    assert!(unsafe { b.x } == 0x0102_AAAA);
}

#[kani::proof]
fn bug_box_union_elem1_write_read_whole() {
    let mut b = Box::new(U32 { x: 0x0102_0304 });
    unsafe { b.h[1] = 0xAAAA };
    assert!(unsafe { b.x } == 0x0102_0304);
}

#[kani::proof]
fn safe_box_union_elem1_write_read_whole() {
    let mut b = Box::new(U32 { x: 0x0102_0304 });
    unsafe { b.h[1] = 0xAAAA };
    assert!(unsafe { b.x } == 0xAAAA_0304);
}

#[kani::proof]
fn bug_box_union_elem_write_read_same_elem() {
    let mut b = Box::new(U32 { x: 0x0102_0304 });
    unsafe { b.h[1] = 0xAAAA };
    assert!(unsafe { b.h[1] } == 0x0102);
}

#[kani::proof]
fn safe_box_union_elem_write_read_same_elem() {
    let mut b = Box::new(U32 { x: 0x0102_0304 });
    unsafe { b.h[1] = 0xAAAA };
    assert!(unsafe { b.h[1] } == 0xAAAA);
}

#[kani::proof]
fn bug_box_union_byte_write_read_whole() {
    let mut b = Box::new(U64B { x: 0 });
    unsafe { b.b[3] = 0xFF };
    assert!(unsafe { b.x } == 0);
}

#[kani::proof]
fn bug_box_union_elem_write_explicit_deref() {
    let mut b = Box::new(U32 { x: 0x0102_0304 });
    unsafe { (*b).h[0] = 0xAAAA };
    assert!(unsafe { (*b).x } == 0x0102_0304);
}

#[kani::proof]
fn bug_box_union_elem_write_symbolic_value() {
    let mut b = Box::new(U32 { x: 0x0102_0304 });
    let v: u16 = kani::any();
    kani::assume(v != 0x0304);
    unsafe { b.h[0] = v };
    assert!(unsafe { b.x } == 0x0102_0304);
}

#[kani::proof]
fn bug_box_union_elem_write_symbolic_index() {
    let mut b = Box::new(U32 { x: 0x0102_0304 });
    let i: usize = kani::any();
    kani::assume(i < 2);
    unsafe { b.h[i] = 0xAAAA };
    assert!(unsafe { b.h[i] } != 0xAAAA);
}

#[kani::proof]
fn bug_box_union_elem_write_read_other_elem() {
    let mut b = Box::new(U32 { x: 0x0102_0304 });
    unsafe { b.h[0] = 0xAAAA };
    assert!(unsafe { b.h[0] } == 0x0304);
}

#[kani::proof]
fn bug_rawptr_union_elem_write() {
    let p = Box::into_raw(Box::new(U32 { x: 0x0102_0304 }));
    unsafe {
        (*p).h[1] = 0xAAAA;
        assert!((*p).h[1] == 0x0102);
        drop(Box::from_raw(p));
    }
}

// Not a union: the element store stays exact.
#[kani::proof]
fn bug_box_array_elem_write() {
    let mut b = Box::new([1u16, 2]);
    b[0] = 5;
    assert!(b[0] == 1);
}

#[kani::proof]
fn safe_box_array_elem_write() {
    let mut b = Box::new([1u16, 2]);
    b[0] = 5;
    assert!(b[0] == 5 && b[1] == 2);
}

#[kani::proof]
fn bug_box_struct_array_elem_write() {
    let mut b = Box::new(SA { h: [1, 2] });
    b.h[0] = 5;
    assert!(b.h[0] == 1);
}
