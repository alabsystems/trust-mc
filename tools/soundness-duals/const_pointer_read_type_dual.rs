// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness and seed):
//   safe_bytes_of_const       -> VERIFICATION:- SUCCESSFUL
//   bug_bytes_of_const        -> VERIFICATION:- FAILED (assertion)
//   safe_u16_of_const         -> VERIFICATION:- SUCCESSFUL
//   bug_u16_of_const          -> VERIFICATION:- FAILED (assertion)
//   safe_next_via_byte_offset -> VERIFICATION:- SUCCESSFUL
//   bug_next_via_byte_offset  -> VERIFICATION:- FAILED (assertion)
//   safe_symbolic_from_elem   -> VERIFICATION:- SUCCESSFUL
//   bug_symbolic_from_elem    -> VERIFICATION:- FAILED (assertion)
//   safe_read_in_callee       -> VERIFICATION:- SUCCESSFUL
//   bug_read_in_callee        -> VERIFICATION:- FAILED (assertion)
//   safe_static_bytes         -> VERIFICATION:- SUCCESSFUL
//   bug_static_bytes          -> VERIFICATION:- FAILED (assertion)
//   safe_static_elem_bytes    -> VERIFICATION:- SUCCESSFUL
//   bug_static_elem_bytes     -> VERIFICATION:- FAILED (assertion)
//   safe_wide_array_as_bytes  -> VERIFICATION:- SUCCESSFUL
//   bug_wide_array_as_bytes   -> VERIFICATION:- FAILED (assertion)
//   bug_wide_array_first_byte -> VERIFICATION:- FAILED (assertion)
//   safe_scalar_as_halves     -> VERIFICATION:- SUCCESSFUL
//   bug_scalar_as_halves      -> VERIFICATION:- FAILED (assertion)
//   bug_scalar_low_byte       -> VERIFICATION:- FAILED (assertion)
//   safe_byte_array_elem      -> VERIFICATION:- SUCCESSFUL
//   bug_byte_array_elem       -> VERIFICATION:- FAILED (assertion)
//   safe_static_wide_as_bytes -> VERIFICATION:- SUCCESSFUL
//   bug_static_wide_as_bytes  -> VERIFICATION:- FAILED (assertion)
//   bug_static_first_byte     -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. A constant pointer's pointee is the window of its
// target at the pointer's offset, read at the pointee TYPE; a fixed target is
// known WHOLE, at every type the harness reads it through a pointer. A cast
// (`E as *const u32 as *const u8`), a byte offset or a callee reads the object
// at a type no constant names, and a value fact about the window at one type
// never answers a read at another. The rule is stated once, in
// trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs.
//
// Measured on main 5b8582dd4 (round-10 resume, 30 s per harness, ay
// 48c98a43d): on the CHC lane nine safe rows FAILED certified Genuine -- the
// object's cells at the read type were free (only the named window was
// seeded), or the [u16; 2] / [u32; 2] value fact was indexed by byte offset
// after the cast. On the BMC lane `safe_next_via_byte_offset` FAILED certified
// Genuine (a reference constant's bytes are not materialized, so the raw
// pointer derived from it reads unconstrained memory).

#![allow(dead_code)]

// D2: a fixed object read at a type that is not a constant pointer's pointee.
const E: &u32 = &[1u32, 2, 3][1];

#[kani::proof]
fn safe_bytes_of_const() {
    let p = E as *const u32 as *const u8;
    unsafe {
        assert!(*p == 2);
        assert!(*p.add(1) == 0);
    }
}

#[kani::proof]
fn bug_bytes_of_const() {
    let p = E as *const u32 as *const u8;
    unsafe {
        assert!(*p.add(1) == 2);
    }
}

#[kani::proof]
fn safe_u16_of_const() {
    let p = E as *const u32 as *const u16;
    unsafe {
        assert!(*p == 2);
        assert!(*p.add(1) == 0);
    }
}

#[kani::proof]
fn bug_u16_of_const() {
    let p = E as *const u32 as *const u16;
    unsafe {
        assert!(*p == 0);
    }
}

#[kani::proof]
fn safe_next_via_byte_offset() {
    let p = (E as *const u32 as *const u8).wrapping_add(4) as *const u32;
    unsafe {
        assert!(*p == 3);
    }
}

#[kani::proof]
fn bug_next_via_byte_offset() {
    let p = (E as *const u32 as *const u8).wrapping_add(4) as *const u32;
    unsafe {
        assert!(*p == 2);
    }
}

// D2: a symbolic index from an element pointer.
#[kani::proof]
fn safe_symbolic_from_elem() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    let v = unsafe { *(E as *const u32).add(i) };
    assert!(v == 2 || v == 3);
}

#[kani::proof]
fn bug_symbolic_from_elem() {
    let i: usize = kani::any();
    kani::assume(i < 2);
    let v = unsafe { *(E as *const u32).add(i) };
    assert!(v == 2);
}

// D2: the pointer is read in a callee.
fn read_at(p: *const u32, i: usize) -> u32 {
    unsafe { *p.add(i) }
}

#[kani::proof]
fn safe_read_in_callee() {
    assert!(read_at(E, 1) == 3);
}

#[kani::proof]
fn bug_read_in_callee() {
    assert!(read_at(E, 1) == 2);
}

// D2: a fixed static read at a byte type.
static FS: [u32; 2] = [0x0102_0304, 5];

#[kani::proof]
fn safe_static_bytes() {
    let p = &raw const FS as *const u8;
    unsafe {
        assert!(*p == 4);
        assert!(*p.add(3) == 1);
    }
}

#[kani::proof]
fn bug_static_bytes() {
    let p = &raw const FS as *const u8;
    unsafe {
        assert!(*p == 1);
    }
}

// D2 via a constant pointer to a fixed static at an offset, read as bytes.
const F1: &u32 = unsafe { &*(&raw const FS as *const u32).add(1) };

#[kani::proof]
fn safe_static_elem_bytes() {
    let p = F1 as *const u32 as *const u8;
    unsafe {
        assert!(*p == 5);
        assert!(*p.sub(1) == 1);
    }
}

#[kani::proof]
fn bug_static_elem_bytes() {
    let p = F1 as *const u32 as *const u8;
    unsafe {
        assert!(*p.sub(1) == 4);
    }
}

const W: &[u16; 2] = &[0x0201, 0x0403];
const B: &[u8; 4] = &[1, 2, 3, 4];
const D: &u32 = &0x0403_0201;
static SW: [u16; 2] = [0x0201, 0x0403];

#[kani::proof]
fn safe_wide_array_as_bytes() {
    let p = W as *const [u16; 2] as *const u8;
    unsafe {
        assert!(*p == 1);
        assert!(*p.add(1) == 2);
        assert!(*p.add(3) == 4);
    }
}

#[kani::proof]
fn bug_wide_array_as_bytes() {
    let p = W as *const [u16; 2] as *const u8;
    unsafe {
        assert!(*p.add(1) == 1);
    }
}

#[kani::proof]
fn bug_wide_array_first_byte() {
    let p = W as *const [u16; 2] as *const u8;
    unsafe {
        assert!(*p == 2);
    }
}

#[kani::proof]
fn safe_scalar_as_halves() {
    let p = D as *const u32 as *const u16;
    unsafe {
        assert!(*p == 0x0201);
        assert!(*p.add(1) == 0x0403);
    }
}

#[kani::proof]
fn bug_scalar_as_halves() {
    let p = D as *const u32 as *const u16;
    unsafe {
        assert!(*p == 0x0403);
    }
}

#[kani::proof]
fn bug_scalar_low_byte() {
    let p = D as *const u32 as *const u8;
    unsafe {
        assert!(*p == 4);
    }
}

#[kani::proof]
fn safe_byte_array_elem() {
    let p = B as *const [u8; 4] as *const u8;
    unsafe {
        assert!(*p.add(2) == 3);
    }
}

#[kani::proof]
fn bug_byte_array_elem() {
    let p = B as *const [u8; 4] as *const u8;
    unsafe {
        assert!(*p.add(2) == 2);
    }
}

#[kani::proof]
fn safe_static_wide_as_bytes() {
    let p = &raw const SW as *const u8;
    unsafe {
        assert!(*p == 1);
        assert!(*p.add(2) == 3);
    }
}

#[kani::proof]
fn bug_static_wide_as_bytes() {
    let p = &raw const SW as *const u8;
    unsafe {
        assert!(*p.add(2) == 1);
    }
}

#[kani::proof]
fn bug_static_first_byte() {
    let p = &raw const SW as *const u8;
    unsafe {
        assert!(*p == 0);
    }
}
