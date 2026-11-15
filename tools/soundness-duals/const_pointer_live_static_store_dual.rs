// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness and seed):
//   bug_symbolic_store_via_pointer_static   -> VERIFICATION:- FAILED (assertion)
//   safe_symbolic_store_via_pointer_static  -> VERIFICATION:- SUCCESSFUL
//   bug_conditional_repoint_store           -> VERIFICATION:- FAILED (assertion)
//   safe_conditional_repoint_store          -> VERIFICATION:- SUCCESSFUL
//   bug_store_in_callee_via_pointer_static  -> VERIFICATION:- FAILED (assertion)
//   safe_store_in_callee_via_pointer_static -> VERIFICATION:- SUCCESSFUL
//   bug_store_via_reloaded_pointer          -> VERIFICATION:- FAILED (assertion)
//   safe_store_via_reloaded_pointer         -> VERIFICATION:- SUCCESSFUL
//   bug_read_after_direct_write_symbolic    -> VERIFICATION:- FAILED (assertion)
//   safe_read_after_direct_write_symbolic   -> VERIFICATION:- SUCCESSFUL
//   bug_live_wide_write_then_bytes          -> VERIFICATION:- FAILED (assertion)
//   safe_live_wide_write_then_bytes         -> VERIFICATION:- SUCCESSFUL
//   bug_live_scalar_write_then_half         -> VERIFICATION:- FAILED (assertion)
//   safe_live_scalar_write_then_half        -> VERIFICATION:- SUCCESSFUL
//   bug_live_bytes_write_then_wide          -> VERIFICATION:- FAILED (assertion)
//   safe_live_bytes_write_then_wide         -> VERIFICATION:- SUCCESSFUL
//
// WHY THIS FILE EXISTS. A LIVE static (`static mut`, or interior-mutable) has
// two representations on the CHC lane: its state variable, and the typed
// memory its address names. A store through an INEXACT pointer into it -- a
// symbolic offset from a pointer static, a conditionally repointed pointer
// static, a callee, a pointer stored to memory and reloaded -- and a read
// through a pointer cast to another pointee type must never let a stale
// representation answer. These rows pin that: a missed bug here is a false
// proof. The constant-pointer rule is stated once, in
// trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs.
//
// Measured on main 5b8582dd4 and with the rule (round-10 resume, 30 s per
// harness, ay 48c98a43d): every bug_ row FAILED on both lanes; the safe_ rows
// fail closed (OverApproximation / EncodingGap / Unknown). No row here is a
// missed bug or a false certificate on either side.

#![allow(dead_code)]
#![allow(static_mut_refs)]

static mut MS: [u32; 2] = [1, 2];
static mut PS: *mut u32 = unsafe { &raw mut MS[0] };

#[kani::proof]
fn bug_symbolic_store_via_pointer_static() {
    unsafe {
        let i: usize = kani::any();
        kani::assume(i < 2);
        *PS.add(i) = 7;
        assert!(MS[1] == 2);
    }
}

#[kani::proof]
fn safe_symbolic_store_via_pointer_static() {
    unsafe {
        let i: usize = kani::any();
        kani::assume(i < 2);
        *PS.add(i) = 7;
        assert!(MS[0] == 7 || MS[1] == 7);
    }
}

static mut MR: [u32; 2] = [1, 2];
static mut PR: *mut u32 = unsafe { &raw mut MR[1] };

#[kani::proof]
fn bug_conditional_repoint_store() {
    unsafe {
        if kani::any::<bool>() {
            PR = &raw mut MR[0];
        }
        *PR = 7;
        assert!(MR[1] == 2);
    }
}

#[kani::proof]
fn safe_conditional_repoint_store() {
    unsafe {
        if kani::any::<bool>() {
            PR = &raw mut MR[0];
        }
        *PR = 7;
        assert!(MR[0] == 7 || MR[1] == 7);
    }
}

fn write_through(p: *mut u32) {
    unsafe {
        *p = 9;
    }
}

#[kani::proof]
fn bug_store_in_callee_via_pointer_static() {
    unsafe {
        write_through(PS.add(1));
        assert!(MS[1] == 2);
    }
}

#[kani::proof]
fn safe_store_in_callee_via_pointer_static() {
    unsafe {
        write_through(PS.add(1));
        assert!(MS[1] == 9);
    }
}

static mut HOLDER: [*mut u32; 1] = [std::ptr::null_mut()];

#[kani::proof]
fn bug_store_via_reloaded_pointer() {
    unsafe {
        HOLDER[0] = PS.add(1);
        *HOLDER[0] = 5;
        assert!(MS[1] == 2);
    }
}

#[kani::proof]
fn safe_store_via_reloaded_pointer() {
    unsafe {
        HOLDER[0] = PS.add(1);
        *HOLDER[0] = 5;
        assert!(MS[1] == 5);
    }
}

#[kani::proof]
fn bug_read_after_direct_write_symbolic() {
    unsafe {
        let i: usize = kani::any();
        kani::assume(i < 2);
        MS[1] = 9;
        let v = *PS.add(i);
        assert!(v != 9);
    }
}

#[kani::proof]
fn safe_read_after_direct_write_symbolic() {
    unsafe {
        let i: usize = kani::any();
        kani::assume(i < 2);
        MS[1] = 9;
        let v = *PS.add(i);
        assert!(v == 1 || v == 9);
    }
}

static mut MW: [u16; 2] = [0x0201, 0x0403];
static mut MX: u32 = 0x0403_0201;

#[kani::proof]
fn bug_live_wide_write_then_bytes() {
    unsafe {
        MW[0] = 0x0605;
        let p = &raw const MW as *const u8;
        assert!(*p == 1);
    }
}

#[kani::proof]
fn safe_live_wide_write_then_bytes() {
    unsafe {
        MW[0] = 0x0605;
        let p = &raw const MW as *const u8;
        assert!(*p == 5);
    }
}

#[kani::proof]
fn bug_live_scalar_write_then_half() {
    unsafe {
        MX = 0x0807_0605;
        let p = &raw const MX as *const u16;
        assert!(*p == 0x0201);
    }
}

#[kani::proof]
fn safe_live_scalar_write_then_half() {
    unsafe {
        MX = 0x0807_0605;
        let p = &raw const MX as *const u16;
        assert!(*p == 0x0605);
    }
}

#[kani::proof]
fn bug_live_bytes_write_then_wide() {
    unsafe {
        let p = &raw mut MW as *mut u8;
        *p = 9;
        assert!(MW[0] == 0x0201);
    }
}

#[kani::proof]
fn safe_live_bytes_write_then_wide() {
    unsafe {
        let p = &raw mut MW as *mut u8;
        *p = 9;
        assert!(MW[0] == 0x0209);
    }
}
