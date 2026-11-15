// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: a raw read through a `Vec`'s buffer pointer
// (`as_ptr`, `as_mut_ptr`) after the `Vec` changed. The `Vec` stubs keep the
// contents in the `Vec`'s own model and do not write the buffer's memory: an
// `IndexMut` store after `as_ptr` was not seen by a later `*p.add(1)`, and a
// `push` or `shrink_to_fit` that reallocates, or a drop that frees the buffer,
// left the old cells readable, with no dangling-pointer check reported. Each
// `bug_` row below was a clean proof and each `safe_` row with a store a
// certified false counterexample, on main f5dfb8d48 and on round 9 of
// fix/chc-false-certificates alike (second review of round 9, 2026-10-15,
// probes r2_vec.rs v02, v03, v09, v12, r2_vec2.rs w02, w03, w09, w20-w22,
// w31). An access through a pointer whose definition chain reaches a `Vec`
// buffer accessor, after a possible change of that `Vec` reachable from the
// accessor, now fails the harness closed (heap/vec_buffer_access.rs). The
// controls keep main's verdicts: no change, a `clear` of plain scalars (the
// buffer stays and keeps its bytes), a move of the `Vec`, and a read past the
// literal's buffer.

fn idx2() -> usize {
    let k: usize = kani::any();
    kani::assume(k < 2);
    k
}

#[kani::proof]
fn safe_indexmut_then_wrapped_read() {
    let mut v = vec![1u16, 2];
    let p = v.as_ptr();
    v[1] = 9;
    let x = unsafe { *p.wrapping_add(1) };
    assert!(x == 9);
}

#[kani::proof]
fn bug_indexmut_then_wrapped_read() {
    let mut v = vec![1u16, 2];
    let p = v.as_ptr();
    v[1] = 9;
    let x = unsafe { *p.wrapping_add(1) };
    assert!(x == 2);
}

#[kani::proof]
fn safe_indexmut_then_add_read() {
    let mut v = vec![1u16, 2];
    let p = v.as_ptr();
    v[1] = 9;
    let x = unsafe { *p.add(1) };
    assert!(x == 9);
}

#[kani::proof]
fn bug_indexmut_then_add_read() {
    let mut v = vec![1u16, 2];
    let p = v.as_ptr();
    v[1] = 9;
    let x = unsafe { *p.add(1) };
    assert!(x == 2);
}

#[kani::proof]
fn safe_indexmut_then_read_without_step() {
    let mut v = vec![1u16, 2];
    let p = v.as_ptr();
    v[0] = 9;
    let x = unsafe { *p };
    assert!(x == 9);
}

#[kani::proof]
fn bug_indexmut_then_read_without_step() {
    let mut v = vec![1u16, 2];
    let p = v.as_ptr();
    v[0] = 9;
    let x = unsafe { *p };
    assert!(x == 1);
}

#[kani::proof]
fn bug_indexmut_symbolic_then_wrapped_read() {
    let mut v = vec![1u16, 2];
    let p = v.as_ptr();
    let k: usize = kani::any();
    kani::assume(k < 2);
    v[k] = 9;
    let x = unsafe { *p.wrapping_add(k) };
    assert!(x != 9);
}

#[kani::proof]
fn bug_push_then_read_dangles() {
    let mut v = vec![1u16, 2];
    let p = v.as_ptr();
    v.push(3);
    let x = unsafe { *p.wrapping_add(1) };
    assert!(x == 2);
}

#[kani::proof]
fn bug_push_then_read_without_step_dangles() {
    let mut v = vec![1u16, 2];
    let p = v.as_ptr();
    v.push(3);
    let x = unsafe { *p };
    assert!(x == 1);
}

#[kani::proof]
fn bug_drop_then_read_dangles() {
    let v = vec![1u16, 2];
    let p = v.as_ptr();
    drop(v);
    let x = unsafe { *p.add(1) };
    assert!(x == 2);
}

#[kani::proof]
fn bug_shrink_then_read_dangles() {
    let mut v = vec![1u16, 2];
    let p = v.as_ptr();
    v.pop();
    v.shrink_to_fit();
    let x = unsafe { *p.wrapping_add(0) };
    assert!(x == 1);
}

#[kani::proof]
fn safe_control_read_without_change() {
    let v = vec![1u16, 2];
    let p = v.as_ptr();
    let x = unsafe { *p.wrapping_add(1) };
    assert!(x == 2);
}

#[kani::proof]
fn safe_control_read_before_change() {
    let mut v = vec![1u16, 2];
    let p = v.as_ptr();
    let x = unsafe { *p.add(1) };
    v[1] = 9;
    assert!(x == 2 && v[1] == 9);
}

#[kani::proof]
fn safe_control_clear_keeps_buffer() {
    let mut v = vec![1u16, 2];
    let p = v.as_ptr();
    v.clear();
    let x = unsafe { *p.wrapping_add(1) };
    assert!(x == 2);
}

#[kani::proof]
fn safe_control_moved_vec_keeps_buffer() {
    let v = vec![1u16, 2];
    let p = v.as_ptr();
    let w = v;
    let x = unsafe { *p.wrapping_add(idx2()) };
    assert!(x == 1 || x == 2);
    drop(w);
}

#[kani::proof]
fn bug_control_read_past_literal_buffer() {
    let v = vec![1u16, 2];
    let p = v.as_ptr();
    let k: usize = kani::any();
    kani::assume(k >= 2 && k < 4);
    let x = unsafe { *p.wrapping_add(k) };
    assert!(x == x);
}
