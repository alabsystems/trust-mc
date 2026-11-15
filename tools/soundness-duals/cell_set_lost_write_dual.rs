// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a `Cell::set` / `Cell::replace` store was lost in the
//! CHC lane: the next `Cell::get` read the value the cell held BEFORE the
//! store. Pre-existing on main 25905b622; recorded by the design 3 review of
//! fix/chc-fnptr-identity (2026-09-26) as finding R5 in
//! docs/chc-hole-fix-designs-2026-09-24.md. The bug_ rows are that review's
//! probes; the safe_ twins assert the stored value instead of the stale one.
//! Every row matches since fix/chc-cell-set-write (see REPAIR below); the
//! wider shapes of the same defect are in cell_register_coherence_dual.rs.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, Kani 0.67.0, measured
//! 2026-09-26; see the manifest entry):
//!   bug_cell_u8_branch          -> VERIFICATION:- FAILED  ('assertion failed: c.get() < 100')
//!   safe_cell_u8_branch         -> VERIFICATION:- SUCCESSFUL
//!   bug_cell_u8_uncond          -> VERIFICATION:- FAILED  ('assertion failed: c.get() < 100')
//!   safe_cell_u8_uncond         -> VERIFICATION:- SUCCESSFUL
//!   bug_cell_const_init_u8_eq   -> VERIFICATION:- FAILED  ('assertion failed: c.get() == 0')
//!   safe_cell_const_init_u8_eq  -> VERIFICATION:- SUCCESSFUL
//!   bug_cell_const_init_u32     -> VERIFICATION:- FAILED  ('assertion failed: c.get() == 0')
//!   safe_cell_const_init_u32    -> VERIFICATION:- SUCCESSFUL
//!   bug_cell_any_init_u8        -> VERIFICATION:- FAILED  ('assertion failed: c.get() < 100')
//!   safe_cell_any_init_u8       -> VERIFICATION:- SUCCESSFUL
//!   bug_cell_fn_uncond          -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   safe_cell_fn_uncond         -> VERIFICATION:- SUCCESSFUL
//!   bug_cell_fn_branch          -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   safe_cell_fn_branch         -> VERIFICATION:- SUCCESSFUL  (control: stale and stored agree)
//!   bug_cell_fn_eq              -> VERIFICATION:- FAILED  ('assertion failed: c.get() == g')
//!   safe_cell_fn_eq             -> VERIFICATION:- SUCCESSFUL
//!   bug_cell_fn_replace         -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   safe_cell_fn_replace        -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM (R5, measured with TRUST_MC_LOG by the design 3 review, and
//! re-traced on main 1f7de891d before the repair):
//! `Cell::set` is modeled as a store to the cell's memory-mirror address
//! (`codegen_call_cell`: `emit_cell_set` in
//! trust-mc-compiler/src/codegen_ay/chc/call/codegen_call_cell.rs). The next
//! `&c` -- the `Cell::get` receiver -- re-mirrors the local `c`'s STALE state
//! variable into that same address (the address comes from `ref_address`, in
//! trust-mc-compiler/src/codegen_ay/chc/stmt/codegen_stmt_rvalue_ref/ref_address.rs:
//! "Mem-level reference ... recorded concrete stack address provenance"; the
//! copy is the "Ref/AddressOf value mirroring" block of
//! trust-mc-compiler/src/codegen_ay/chc/stmt/codegen_stmt_assign_simple.rs),
//! and `get` reads that mirror by store-to-load forwarding. The store is
//! overwritten before any read can observe it.
//!
//! REPAIR (fix/chc-cell-set-write, 2026-09-26): the store also binds the
//! referent local's state variable to the stored value
//! (trust-mc-compiler/src/codegen_ay/chc/call/codegen_call_cell_register.rs),
//! so the re-mirror copies the stored value, and fails closed where that
//! binding cannot be built exactly and the register would be re-mirrored.
//!
//! The hole cut both ways, and every red row was certified: each bug_ row was
//! SUCCESSFUL [AY:PROOF_QUALIFIERS:clean] (a missed bug), and each safe_ twin
//! that asserts the stored value was FAILED [AY:CTREX_CAT:Genuine] (a false
//! certificate). A repair must turn both halves green together; a repair that
//! only havocs the read would fail the bug_ rows and keep the safe_ rows red.
//! `dual_b_get_reads_stored.rs` cannot catch this: its `set(5); get() == 6`
//! fails for the stored and the stale value alike.
//!
//! Lane scope: CHC only. The bounded lane is correct on the integer rows, but
//! it PROVES bug_cell_fn_uncond and bug_cell_fn_eq and fails them only by an
//! unsupported_construct_fallback demotion, and it fails the fn-pointer safe_
//! twins uncertified (see the manifest note).
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s cell_set_lost_write_dual.rs

use std::cell::Cell;

#[inline(never)]
fn sink<T>(_value: T) {}
fn add_safe(a: u8, b: u8) -> u8 {
    a.wrapping_add(b)
}
fn sub_safe(a: u8, b: u8) -> u8 {
    a.wrapping_sub(b)
}
fn add_ub(a: u8, b: u8) -> u8 {
    unsafe { a.unchecked_add(b) }
}

// ---- u8 payload, conditional set -------------------------------------------

#[kani::proof]
fn bug_cell_u8_branch() {
    let c = Cell::new(0u8);
    if kani::any() {
        c.set(200);
    }
    assert!(c.get() < 100);
}

#[kani::proof]
fn safe_cell_u8_branch() {
    let b: bool = kani::any();
    let c = Cell::new(0u8);
    if b {
        c.set(200);
    }
    assert!(c.get() == if b { 200 } else { 0 });
}

// ---- u8 payload, unconditional set -----------------------------------------

#[kani::proof]
fn bug_cell_u8_uncond() {
    let c = Cell::new(0u8);
    c.set(200);
    assert!(c.get() < 100);
}

#[kani::proof]
fn safe_cell_u8_uncond() {
    let c = Cell::new(0u8);
    c.set(200);
    assert!(c.get() >= 100);
}

#[kani::proof]
fn bug_cell_const_init_u8_eq() {
    let c = Cell::new(0u8);
    c.set(200);
    assert!(c.get() == 0);
}

#[kani::proof]
fn safe_cell_const_init_u8_eq() {
    let c = Cell::new(0u8);
    c.set(200);
    assert!(c.get() == 200);
}

// ---- u32 payload ------------------------------------------------------------

#[kani::proof]
fn bug_cell_const_init_u32() {
    let c: Cell<u32> = Cell::new(0);
    c.set(5);
    assert!(c.get() == 0);
}

#[kani::proof]
fn safe_cell_const_init_u32() {
    let c: Cell<u32> = Cell::new(0);
    c.set(5);
    assert!(c.get() == 5);
}

// ---- nondeterministic initial value -----------------------------------------

#[kani::proof]
fn bug_cell_any_init_u8() {
    let c = Cell::new(kani::any::<u8>());
    kani::assume(c.get() < 10);
    c.set(200);
    assert!(c.get() < 100);
}

#[kani::proof]
fn safe_cell_any_init_u8() {
    let c = Cell::new(kani::any::<u8>());
    kani::assume(c.get() < 10);
    c.set(200);
    assert!(c.get() >= 100);
}

// ---- fn-pointer payload -----------------------------------------------------

#[kani::proof]
fn bug_cell_fn_uncond() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let c: Cell<fn(u8, u8) -> u8> = Cell::new(add_safe);
    c.set(add_ub);
    sink((c.get())(a, b));
}

#[kani::proof]
fn safe_cell_fn_uncond() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let c: Cell<fn(u8, u8) -> u8> = Cell::new(add_ub);
    c.set(add_safe);
    sink((c.get())(a, b));
}

#[kani::proof]
fn bug_cell_fn_branch() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let c: Cell<fn(u8, u8) -> u8> = Cell::new(add_safe);
    if kani::any() {
        c.set(add_ub);
    }
    sink((c.get())(a, b));
}

#[kani::proof]
fn safe_cell_fn_branch() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let c: Cell<fn(u8, u8) -> u8> = Cell::new(add_safe);
    if kani::any() {
        c.set(sub_safe);
    }
    sink((c.get())(a, b));
}

#[kani::proof]
fn bug_cell_fn_eq() {
    let c: Cell<fn(u8, u8) -> u8> = Cell::new(add_safe);
    if kani::any() {
        c.set(add_ub);
    }
    let g: fn(u8, u8) -> u8 = add_safe;
    assert!(c.get() == g);
}

#[kani::proof]
fn safe_cell_fn_eq() {
    let c: Cell<fn(u8, u8) -> u8> = Cell::new(add_safe);
    c.set(add_ub);
    let g: fn(u8, u8) -> u8 = add_ub;
    assert!(c.get() == g);
}

#[kani::proof]
fn bug_cell_fn_replace() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let c: Cell<fn(u8, u8) -> u8> = Cell::new(add_safe);
    if kani::any() {
        let _old = c.replace(add_ub);
    }
    sink((c.get())(a, b));
}

#[kani::proof]
fn safe_cell_fn_replace() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let c: Cell<fn(u8, u8) -> u8> = Cell::new(add_ub);
    let _old = c.replace(add_safe);
    sink((c.get())(a, b));
}
