// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: `ref_targets` takes a heap owner's pointer accessor
// (`Vec::as_mut_ptr`, `String::as_mut_ptr`) to the OWNER local, not to the
// allocation the pointer addresses. When the owner is moved to another local
// inside an inner scope, its storage dies while its buffer lives on in the new
// owner, and three lanes read the stale points-to fact (third review of round
// 10 of fix/chc-false-certificates, 2026-10-15, probes r3_dead3.rs h01-h09,
// r3_dead4.rs k01-k05, r3_dead5.rs n02-n05):
// - the dead-target test (#762) certified a dangling access on a read
//   (`safe_moved_read`, the same on main f5dfb8d48) and, once round 10 encoded
//   a one-element integer copy as a typed store, on a copy out of the buffer
//   (`safe_moved_copy_src` and its variants, introduced by round 10);
// - the store side's new dead-target test failed a write into the moved
//   buffer closed (`safe_moved_store`, `safe_moved_copy_dst`);
// - the Reg-level store took `*p = 5` as a narrower store into the Vec handle
//   and havocked the dead handle, so the buffer kept its old value
//   (`bug_moved_copy_dst_then_read`, `bug_moved_store_then_read`; missed on
//   main);
// - a `Vec` in a struct field resolved its buffer pointer by loading a Vec from
//   memory at the struct's value (`safe_struct_vec_moved_copy_src`).
// The dead-target test now tells the dead owner's own storage (or a freed
// buffer: a unique owner never moved out was dropped first) from a moved
// `Vec` buffer, and fails anything else closed; a store through such a pointer
// lands in the buffer's memory; a read of the `Vec`'s model after a write
// through its buffer pointer fails closed; and the struct-embedded `Vec`'s
// pointer is selected through its field. The `bug_dropped_*` rows check that a
// pointer into a dropped `Vec`'s buffer is still a dangling access.

use std::ptr;

struct S {
    v: Vec<u32>,
}

#[kani::proof]
fn bug_moved_read() {
    let w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    let x = unsafe { *p };
    assert!(x == 2 && w.len() == 2);
}

#[kani::proof]
fn safe_moved_read() {
    let w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    let x = unsafe { *p };
    assert!(x == 1 && w.len() == 2);
}

#[kani::proof]
fn bug_moved_copy_src() {
    let w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    let mut out: u32 = 0;
    unsafe { ptr::copy_nonoverlapping(p as *const u32, &mut out, 1) };
    assert!(out == 2 && w.len() == 2);
}

#[kani::proof]
fn safe_moved_copy_src() {
    let w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    let mut out: u32 = 0;
    unsafe { ptr::copy_nonoverlapping(p as *const u32, &mut out, 1) };
    assert!(out == 1 && w.len() == 2);
}

#[kani::proof]
fn bug_moved_store_then_read() {
    let w: Vec<u8>;
    let p: *mut u8;
    {
        let mut v = vec![1u8, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    unsafe { *p = 5 };
    assert!(w[0] == 1);
}

#[kani::proof]
fn safe_moved_store() {
    let w: Vec<u8>;
    let p: *mut u8;
    {
        let mut v = vec![1u8, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    unsafe { *p = 5 };
    assert!(w.len() == 2);
}

#[kani::proof]
fn bug_moved_copy_dst_then_read() {
    let w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    let x: u32 = 5;
    unsafe { ptr::copy_nonoverlapping(&x, p, 1) };
    let y = unsafe { *p };
    assert!(y == 1 && w.len() == 2);
}

#[kani::proof]
fn safe_moved_copy_dst() {
    let w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    let x: u32 = 5;
    unsafe { ptr::copy_nonoverlapping(&x, p, 1) };
    assert!(w.len() == 2);
}

#[kani::proof]
fn bug_dropped_read() {
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
    }
    let x = unsafe { *p };
    assert!(x == x);
}

#[kani::proof]
fn bug_dropped_copy_src() {
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
    }
    let mut out: u32 = 0;
    unsafe { ptr::copy_nonoverlapping(p as *const u32, &mut out, 1) };
}

#[kani::proof]
fn bug_dropped_store() {
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
    }
    unsafe { *p = 3 };
}

#[kani::proof]
fn bug_moved_then_new_owner_dropped() {
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        let _w = v;
    }
    let x = unsafe { *p };
    assert!(x == x);
}

#[kani::proof]
fn bug_swapped_buffer_kept() {
    let mut w = vec![9u32];
    let p: *mut u32;
    {
        let mut v = vec![1u32];
        p = v.as_mut_ptr();
        std::mem::swap(&mut v, &mut w);
    }
    let x = unsafe { *p };
    assert!(x == 9);
}

#[kani::proof]
fn safe_swapped_buffer_kept() {
    let mut w = vec![9u32];
    let p: *mut u32;
    {
        let mut v = vec![1u32];
        p = v.as_mut_ptr();
        std::mem::swap(&mut v, &mut w);
    }
    let x = unsafe { *p };
    assert!(x == 1 && w[0] == 1);
}

#[kani::proof]
fn bug_pointer_to_dead_vec_struct() {
    let p: *const usize;
    {
        let v = vec![1u32, 2];
        p = &v as *const Vec<u32> as *const usize;
    }
    let x = unsafe { *p };
    assert!(x == x);
}

#[kani::proof]
fn bug_struct_vec_moved_copy_src() {
    let w: S;
    let p: *mut u32;
    {
        let mut s = S { v: vec![3u32, 4] };
        p = s.v.as_mut_ptr();
        w = s;
    }
    let mut out = 0u32;
    unsafe { ptr::copy_nonoverlapping(p as *const u32, &mut out, 1) };
    assert!(out == 4 && w.v.len() == 2);
}

#[kani::proof]
fn safe_struct_vec_moved_copy_src() {
    let w: S;
    let p: *mut u32;
    {
        let mut s = S { v: vec![3u32, 4] };
        p = s.v.as_mut_ptr();
        w = s;
    }
    let mut out = 0u32;
    unsafe { ptr::copy_nonoverlapping(p as *const u32, &mut out, 1) };
    assert!(out == 3 && w.v.len() == 2);
}

#[kani::proof]
fn bug_fnmut_copy_src() {
    let w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    let mut out = 0u32;
    let d = &mut out as *mut u32;
    let mut f = move || unsafe { ptr::copy_nonoverlapping(p as *const u32, d, 1) };
    f();
    assert!(out == 2 && w.len() == 2);
}

#[kani::proof]
fn safe_fnmut_copy_src() {
    let w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    let mut out = 0u32;
    let d = &mut out as *mut u32;
    let mut f = move || unsafe { ptr::copy_nonoverlapping(p as *const u32, d, 1) };
    f();
    assert!(out == 1 && w.len() == 2);
}

#[kani::proof]
fn bug_string_moved_read() {
    let w: String;
    let p: *mut u8;
    {
        let mut s = String::from("ab");
        p = s.as_mut_ptr();
        w = s;
    }
    let x = unsafe { *p };
    assert!(x == b'b' && w.len() == 2);
}

#[kani::proof]
fn safe_string_moved_read() {
    let w: String;
    let p: *mut u8;
    {
        let mut s = String::from("ab");
        p = s.as_mut_ptr();
        w = s;
    }
    let x = unsafe { *p };
    assert!(x == b'a' && w.len() == 2);
}

#[kani::proof]
fn bug_string_dropped_read() {
    let p: *mut u8;
    {
        let mut s = String::from("ab");
        p = s.as_mut_ptr();
    }
    let x = unsafe { *p };
    assert!(x == x);
}

#[kani::proof]
fn bug_moved_on_one_path() {
    let c: bool = kani::any();
    let w: Option<Vec<u32>>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = if c { Some(v) } else { None };
    }
    let x = unsafe { *p };
    assert!(x == 1 && (w.is_some() || !c));
}

#[kani::proof]
fn bug_moved_then_reallocated() {
    let mut w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32];
        p = v.as_mut_ptr();
        w = v;
    }
    for i in 0..4 {
        w.push(i);
    }
    let x = unsafe { *p };
    assert!(x == x);
}

#[kani::proof]
fn safe_moved_no_assert() {
    let _w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        _w = v;
    }
    let mut out: u32 = 0;
    unsafe { ptr::copy_nonoverlapping(p as *const u32, &mut out, 1) };
}

#[kani::proof]
fn bug_moved_twice_read_second() {
    let w2: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        let w1 = v;
        w2 = w1;
    }
    let x = unsafe { *p.add(1) };
    assert!(x == 1 && w2.len() == 2);
}

#[kani::proof]
fn safe_moved_twice_read_second() {
    let w2: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        let w1 = v;
        w2 = w1;
    }
    let x = unsafe { *p.add(1) };
    assert!(x == 2 && w2.len() == 2);
}

#[kani::proof]
fn safe_moved_vec_ptr_write_call() {
    let w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    unsafe { ptr::write(p, 5) };
    assert!(w.len() == 2);
}

#[kani::proof]
fn safe_moved_vec_ptr_read_call() {
    let w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    let x = unsafe { ptr::read(p) };
    assert!(x == 1 && w.len() == 2);
}

#[kani::proof]
fn safe_moved_vec_u8_copy_dst() {
    let _w: Vec<u8>;
    let p: *mut u8;
    {
        let mut v = vec![1u8, 2];
        p = v.as_mut_ptr();
        _w = v;
    }
    unsafe { ptr::copy_nonoverlapping(&7u8, p, 1) };
}

#[kani::proof]
fn safe_moved_vec_u8_copy_src() {
    let w: Vec<u8>;
    let p: *mut u8;
    {
        let mut v = vec![7u8, 8];
        p = v.as_mut_ptr();
        w = v;
    }
    let mut out: u8 = 0;
    unsafe { ptr::copy_nonoverlapping(p as *const u8, &mut out, 1) };
    assert!(out == 7 && w[1] == 8);
}

#[kani::proof]
fn bug_moved_vec_u8_copy_src() {
    let w: Vec<u8>;
    let p: *mut u8;
    {
        let mut v = vec![7u8, 8];
        p = v.as_mut_ptr();
        w = v;
    }
    let mut out: u8 = 0;
    unsafe { ptr::copy_nonoverlapping(p as *const u8, &mut out, 1) };
    assert!(out == 8 && w[1] == 8);
}

#[kani::proof]
fn safe_moved_vec_copy_src_second_elem() {
    let w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    let mut out: u32 = 0;
    unsafe { ptr::copy_nonoverlapping(p.add(1) as *const u32, &mut out, 1) };
    assert!(out == 2 && w.len() == 2);
}

#[kani::proof]
fn safe_moved_vec_read_via_noinline_fn() {
    #[inline(never)]
    fn rd(p: *const u32) -> u32 {
        unsafe { *p }
    }
    let w: Vec<u32>;
    let p: *mut u32;
    {
        let mut v = vec![1u32, 2];
        p = v.as_mut_ptr();
        w = v;
    }
    assert!(rd(p) == 1 && w.len() == 2);
}
