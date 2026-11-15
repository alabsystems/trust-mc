// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: round 9 of fix/chc-false-certificates named the
// allocation behind a `Box` only through single definitions, so a valid box
// reassigned, chosen on a path, moved out of a holder rebuilt whole, or out of
// a struct whose OTHER field was written, failed closed when its pointer was
// stepped in bounds by `wrapping_add` and read, where Kani and main prove it
// (third review of round 10, 2026-10-15, r3_box.rs b06, r3_box2.rs f01, f02,
// f08). Main proves these only because its every-box-is-fresh route never
// checks the extent: it misses every `bug_` twin here. A box local or holder
// field every definition of which is a fresh `Box::new` is now that
// allocation, and a write to another field of the holder leaves the box
// field as built. A box through `Vec::pop` stays unknown (fail closed).

struct H {
    b: Box<[u8; 4]>,
}

fn step_read(b: Box<[u8; 4]>, k: usize) -> u8 {
    let p = Box::into_raw(b) as *mut u8;
    let q = p.wrapping_add(k);
    let x = unsafe { *q };
    unsafe { drop(Box::from_raw(p as *mut [u8; 4])) };
    x
}

#[kani::proof]
fn safe_box_reassigned() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b = Box::new([5u8, 6, 7, 8]);
    assert!(step_read(b, 3) == 8);
}

#[kani::proof]
fn bug_box_reassigned() {
    let mut b = Box::new([1u8, 2, 3, 4]);
    b = Box::new([5u8, 6, 7, 8]);
    let x = step_read(b, 4);
    assert!(x == x);
}

#[kani::proof]
fn safe_box_chosen_on_path() {
    let c: bool = kani::any();
    let b = if c { Box::new([1u8, 2, 3, 4]) } else { Box::new([5u8, 6, 7, 8]) };
    let x = step_read(b, 0);
    assert!(x == 1 || x == 5);
}

#[kani::proof]
fn bug_box_chosen_on_path() {
    let c: bool = kani::any();
    let b = if c { Box::new([1u8, 2, 3, 4]) } else { Box::new([5u8, 6, 7, 8]) };
    let x = step_read(b, 4);
    assert!(x == x);
}

#[kani::proof]
fn safe_box_struct_other_field_written() {
    struct G {
        b: Box<[u8; 4]>,
        n: u32,
    }
    let mut g = G { b: Box::new([1, 2, 3, 4]), n: 0 };
    g.n = 5;
    assert!(step_read(g.b, 3) == 4 && g.n == 5);
}

#[kani::proof]
fn bug_box_struct_other_field_written() {
    struct G {
        b: Box<[u8; 4]>,
        n: u32,
    }
    let mut g = G { b: Box::new([1, 2, 3, 4]), n: 0 };
    g.n = 5;
    let x = step_read(g.b, 4);
    assert!(x == x && g.n == 5);
}

#[kani::proof]
fn bug_field_after_whole_reassign() {
    struct H2 {
        b: Box<[u8; 4]>,
    }
    let mut h = H2 { b: Box::new([1u8, 2, 3, 4]) };
    h = H2 { b: Box::new([5u8, 6, 7, 8]) };
    let b = h.b;
    let x = step_read(b, 4);
    assert!(x == x);
}

#[kani::proof]
#[kani::unwind(3)]
fn safe_box_through_vec_pop() {
    let mut v: Vec<Box<[u8; 4]>> = Vec::new();
    v.push(Box::new([1, 2, 3, 4]));
    let b = v.pop().unwrap();
    assert!(step_read(b, 3) == 4);
}

#[kani::proof]
#[kani::unwind(3)]
fn bug_box_through_vec_pop() {
    let mut v: Vec<Box<[u8; 4]>> = Vec::new();
    v.push(Box::new([1, 2, 3, 4]));
    let b = v.pop().unwrap();
    let x = step_read(b, 4);
    assert!(x == x);
}

#[kani::proof]
fn safe_plain_box_new() {
    let b = Box::new([1u8, 2, 3, 4]);
    assert!(step_read(b, 3) == 4);
}

#[kani::proof]
fn bug_plain_box_new() {
    let b = Box::new([1u8, 2, 3, 4]);
    let x = step_read(b, 4);
    assert!(x == x);
}

#[kani::proof]
fn safe_field_after_whole_reassign() {
    let mut h = H { b: Box::new([1u8, 2, 3, 4]) };
    h = H { b: Box::new([5u8, 6, 7, 8]) };
    let b = h.b;
    assert!(step_read(b, 3) == 8);
}
