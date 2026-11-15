// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// kani-flags: -Z function-contracts
//
// Oracle: corpus-rev Kani with `-Z function-contracts` (see the manifest entry
// for the measurement): every `bug_` harness FAILS and every `safe_` harness
// is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: a `copy_nonoverlapping` inside a contract, into a field
// at a non-zero offset. Kani's contract instrumentation runs the body in a
// closure that captured the reference, and the copy lane's chain-less refusal
// found no definition chain from the destination to its ref target, so the
// copy took the demoting fallback (`chc_fallback=1`): `#[kani::modifies(p)]`
// with a copy into `&mut p.b` failed where main and Kani prove it (second
// review of round 9 of fix/chc-false-certificates, 2026-10-15, probe
// r2_contract_copy.rs k05). Main proved it by dropping the target's
// projection (the copy wrote `p.a`, which `modifies(p)` also covers), and
// failed `modifies(&p.b)` for the same reason. The one-element integer copy is
// now the typed store `*dst = *src`, which the frame checks see as the store
// it is.

use std::ptr;

#[derive(kani::Arbitrary)]
#[repr(C)]
struct Pair {
    a: u32,
    b: u32,
}

#[kani::modifies(p)]
fn copy_b_whole(p: &mut Pair) {
    let src: u32 = 5;
    unsafe { ptr::copy_nonoverlapping(&src as *const u32, &mut p.b as *mut u32, 1) };
}

#[kani::proof_for_contract(copy_b_whole)]
fn safe_copy_b_under_modifies_whole() {
    let mut p: Pair = kani::any();
    copy_b_whole(&mut p);
}

#[kani::modifies(&p.b)]
fn copy_b(p: &mut Pair) {
    let src: u32 = 5;
    unsafe { ptr::copy_nonoverlapping(&src as *const u32, &mut p.b as *mut u32, 1) };
}

#[kani::proof_for_contract(copy_b)]
fn safe_copy_b_under_modifies_field() {
    let mut p: Pair = kani::any();
    copy_b(&mut p);
}

#[kani::modifies(&p.a)]
fn copy_b_outside(p: &mut Pair) {
    let src: u32 = 5;
    unsafe { ptr::copy_nonoverlapping(&src as *const u32, &mut p.b as *mut u32, 1) };
}

#[kani::proof_for_contract(copy_b_outside)]
fn bug_copy_b_outside_modifies_frame() {
    let mut p: Pair = kani::any();
    copy_b_outside(&mut p);
}

#[kani::modifies(&p.b)]
#[kani::ensures(|_| p.b == 5)]
fn copy_b_ensures(p: &mut Pair) {
    let src: u32 = 5;
    unsafe { ptr::copy_nonoverlapping(&src as *const u32, &mut p.b as *mut u32, 1) };
}

#[kani::proof_for_contract(copy_b_ensures)]
fn safe_copy_b_ensures_value() {
    let mut p: Pair = kani::any();
    copy_b_ensures(&mut p);
}

#[kani::modifies(&p.b)]
#[kani::ensures(|_| p.b == 6)]
fn copy_b_ensures_bad(p: &mut Pair) {
    let src: u32 = 5;
    unsafe { ptr::copy_nonoverlapping(&src as *const u32, &mut p.b as *mut u32, 1) };
}

#[kani::proof_for_contract(copy_b_ensures_bad)]
fn bug_copy_b_ensures_wrong_value() {
    let mut p: Pair = kani::any();
    copy_b_ensures_bad(&mut p);
}

#[kani::modifies(&p.b)]
#[kani::ensures(|_| p.a == old(p.a))]
fn copy_b_keeps_a(p: &mut Pair) {
    let src: u32 = 5;
    unsafe { ptr::copy_nonoverlapping(&src as *const u32, &mut p.b as *mut u32, 1) };
}

#[kani::proof_for_contract(copy_b_keeps_a)]
fn safe_copy_b_keeps_field_a() {
    let mut p: Pair = kani::any();
    copy_b_keeps_a(&mut p);
}
