// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; corpus-rev Kani 0.67.0, one run of this file, every
// bug_ row failing on its own assertion):
//   safe_volatile_then_fetch_add_read                 -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_then_fetch_add_read                  -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_fetch_or_read                       -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_fetch_or_read                        -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_fetch_sub_read                      -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_fetch_sub_read                       -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_cast_fetch_add_cast_read            -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_cast_fetch_add_cast_read             -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_cast_store_cast_read                -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_cast_store_cast_read                 -> VERIFICATION:- FAILED (assertion)
//   safe_write_volatile_load                          -> VERIFICATION:- SUCCESSFUL
//   bug_write_volatile_load                           -> VERIFICATION:- FAILED (assertion)
//   safe_method_volatile_load                         -> VERIFICATION:- SUCCESSFUL
//   bug_method_volatile_load                          -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_cast_load                           -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_cast_load                            -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_swap_old                            -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_swap_old                             -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_fetch_add_load                      -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_fetch_add_load                       -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_bool_load                           -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_bool_load                            -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_read_as_ptr                         -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_read_as_ptr                          -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_then_store_other_static             -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_then_store_other_static              -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_stmt_store_same_read                -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_stmt_store_same_read                 -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_b_store_a_read_b                    -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_b_store_a_read_b                     -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_b_store_a_load_b                    -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_b_store_a_load_b                     -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_b_stmt_store_a_read_b               -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_b_stmt_store_a_read_b                -> VERIFICATION:- FAILED (assertion)
//   safe_mut_volatile_read_direct                     -> VERIFICATION:- SUCCESSFUL
//   bug_mut_volatile_read_direct                      -> VERIFICATION:- FAILED (assertion)
//   safe_mut_volatile_then_field_store_read           -> VERIFICATION:- SUCCESSFUL
//   bug_mut_volatile_then_field_store_read            -> VERIFICATION:- FAILED (assertion)
//   safe_mut_volatile_add_addr_read                   -> VERIFICATION:- SUCCESSFUL
//   bug_mut_volatile_add_addr_read                    -> VERIFICATION:- FAILED (assertion)
//   safe_mut_volatile_then_assign_raw_read            -> VERIFICATION:- SUCCESSFUL
//   bug_mut_volatile_then_assign_raw_read             -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_mut_array_elem_read                 -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_mut_array_elem_read                  -> VERIFICATION:- FAILED (assertion)
//   safe_volatile_mut_array_elem_then_store_raw_read  -> VERIFICATION:- SUCCESSFUL
//   bug_volatile_mut_array_elem_then_store_raw_read   -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. The CHC lane keeps a static in its state variable and
// in a memory image, and since fix/chc-atomic-as-ptr-live every store that
// changes the state rewrites the image from it (`sync_static_image`). That is
// sound only if every store into the image also updates or havocs the state.
// `write_volatile` did not: the volatile store's Mem bridge
// (`ptr_receiver_mem::emit_mem_store_transition`) wrote one typed view of the
// image and nothing else. A later atomic RMW or store then synced the image
// from the stale state: `write_volatile(A.as_ptr(), 9); A.fetch_add(1);`
// `*A.as_ptr() == 6` PROVED where Kani reads 10, and `fetch_or(0)` lost the 9
// (review round 1 of that branch, findings 1 and 2). Loads, a swap's old value
// and `static mut` reads after a volatile write read the stale state on main
// as well (finding 3). The volatile store now takes the call model's static
// route (`plan_static_store_route`): the state is written along the static
// place path and the image synced from it, or both are havocked and the
// stored bytes written back. A store into a static's image that no route
// makes fails the harness closed (`static_image_written_unrouted`).
//
// Measured 2026-10-15 (30 s per harness, ay d80d17a90, frozen nightly; this
// branch's round-1 bundle, compiler d52360f5e06d, by the strict dual gate;
// main and round 0 by the same driver invocation, one run per harness): CHC
// on main f5dfb8d48's bundle 10 missed bugs and 4 false certificates; on
// round 0 (compiler f78b21069ddb) 15 missed bugs and 4 false certificates;
// here 0 missed bugs and 0 false certificates, 41 of 46 rows match. BMC
// (unchanged code): no missed bug or false certificate. The remaining red
// rows are known-red in the manifest with their cause.

#![allow(dead_code, static_mut_refs, invalid_reference_casting)]
use std::ptr::{addr_of, addr_of_mut, write_volatile};
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};

#[repr(C)]
struct Pair {
    a: AtomicU32,
    b: AtomicU32,
}
static VR: AtomicU32 = AtomicU32::new(5);
static VL: AtomicU32 = AtomicU32::new(5);
static VM: AtomicU32 = AtomicU32::new(5);
static VA: AtomicU32 = AtomicU32::new(5);
static VS: AtomicU32 = AtomicU32::new(5);
static VO: AtomicU32 = AtomicU32::new(5);
static VW: AtomicU32 = AtomicU32::new(5);
static VD: AtomicU32 = AtomicU32::new(5);
static VT: AtomicU32 = AtomicU32::new(5);
static VQ: AtomicU32 = AtomicU32::new(5);
static VB: AtomicBool = AtomicBool::new(false);
static OTHER: AtomicU32 = AtomicU32::new(5);
static CA: AtomicU32 = AtomicU32::new(5);
static CB: AtomicU32 = AtomicU32::new(5);
static CC: AtomicU32 = AtomicU32::new(5);
static PR: Pair = Pair { a: AtomicU32::new(1), b: AtomicU32::new(2) };
static PV: Pair = Pair { a: AtomicU32::new(1), b: AtomicU32::new(2) };
static PS: Pair = Pair { a: AtomicU32::new(1), b: AtomicU32::new(2) };
static mut Q: (u32, u32) = (1, 2);
static mut QF: (u32, u32) = (1, 2);
static mut X: u32 = 5;
static mut XA: u32 = 5;
static mut G: [u32; 4] = [1, 2, 3, 4];
static mut GS: [u32; 4] = [1, 2, 3, 4];

// The review's introduced rows: a volatile write, an atomic RMW or store on
// the same static, then a raw read.
#[kani::proof]
fn safe_volatile_then_fetch_add_read() {
    unsafe { write_volatile(VR.as_ptr(), 9) };
    VR.fetch_add(1, Ordering::SeqCst);
    unsafe { assert!(*VR.as_ptr() == 10) }
}
#[kani::proof]
fn bug_volatile_then_fetch_add_read() {
    unsafe { write_volatile(VR.as_ptr(), 9) };
    VR.fetch_add(1, Ordering::SeqCst);
    unsafe { assert!(*VR.as_ptr() == 6) }
}
#[kani::proof]
fn safe_volatile_fetch_or_read() {
    unsafe { write_volatile(VO.as_ptr(), 9) };
    VO.fetch_or(0, Ordering::SeqCst);
    unsafe { assert!(*VO.as_ptr() == 9) }
}
#[kani::proof]
fn bug_volatile_fetch_or_read() {
    unsafe { write_volatile(VO.as_ptr(), 9) };
    VO.fetch_or(0, Ordering::SeqCst);
    unsafe { assert!(*VO.as_ptr() == 5) }
}
#[kani::proof]
fn safe_volatile_fetch_sub_read() {
    unsafe { write_volatile(VS.as_ptr(), 9) };
    VS.fetch_sub(1, Ordering::SeqCst);
    unsafe { assert!(*VS.as_ptr() == 8) }
}
#[kani::proof]
fn bug_volatile_fetch_sub_read() {
    unsafe { write_volatile(VS.as_ptr(), 9) };
    VS.fetch_sub(1, Ordering::SeqCst);
    unsafe { assert!(*VS.as_ptr() == 4) }
}
#[kani::proof]
fn safe_volatile_cast_fetch_add_cast_read() {
    let p = &CA as *const AtomicU32 as *mut u32;
    unsafe { write_volatile(p, 9) };
    CA.fetch_add(1, Ordering::SeqCst);
    unsafe { assert!(*p == 10) }
}
#[kani::proof]
fn bug_volatile_cast_fetch_add_cast_read() {
    let p = &CA as *const AtomicU32 as *mut u32;
    unsafe { write_volatile(p, 9) };
    CA.fetch_add(1, Ordering::SeqCst);
    unsafe { assert!(*p == 6) }
}
#[kani::proof]
fn safe_volatile_cast_store_cast_read() {
    let p = &CC as *const AtomicU32 as *mut u32;
    unsafe { write_volatile(p, 9) };
    CC.fetch_or(0, Ordering::SeqCst);
    unsafe { assert!(*p == 9) }
}
#[kani::proof]
fn bug_volatile_cast_store_cast_read() {
    let p = &CC as *const AtomicU32 as *mut u32;
    unsafe { write_volatile(p, 9) };
    CC.fetch_or(0, Ordering::SeqCst);
    unsafe { assert!(*p == 5) }
}
// The volatile write reaches the static's state.
#[kani::proof]
fn safe_write_volatile_load() {
    unsafe { write_volatile(VL.as_ptr(), 9) };
    assert!(VL.load(Ordering::SeqCst) == 9)
}
#[kani::proof]
fn bug_write_volatile_load() {
    unsafe { write_volatile(VL.as_ptr(), 9) };
    assert!(VL.load(Ordering::SeqCst) == 5)
}
#[kani::proof]
fn safe_method_volatile_load() {
    unsafe { VM.as_ptr().write_volatile(9) };
    assert!(VM.load(Ordering::SeqCst) == 9)
}
#[kani::proof]
fn bug_method_volatile_load() {
    unsafe { VM.as_ptr().write_volatile(9) };
    assert!(VM.load(Ordering::SeqCst) == 5)
}
#[kani::proof]
fn safe_volatile_cast_load() {
    let p = &CB as *const AtomicU32 as *mut u32;
    unsafe { write_volatile(p, 9) };
    assert!(CB.load(Ordering::SeqCst) == 9)
}
#[kani::proof]
fn bug_volatile_cast_load() {
    let p = &CB as *const AtomicU32 as *mut u32;
    unsafe { write_volatile(p, 9) };
    assert!(CB.load(Ordering::SeqCst) == 5)
}
#[kani::proof]
fn safe_volatile_swap_old() {
    unsafe { write_volatile(VW.as_ptr(), 9) };
    let old = VW.swap(1, Ordering::SeqCst);
    assert!(old == 9)
}
#[kani::proof]
fn bug_volatile_swap_old() {
    unsafe { write_volatile(VW.as_ptr(), 9) };
    let old = VW.swap(1, Ordering::SeqCst);
    assert!(old == 5)
}
#[kani::proof]
fn safe_volatile_fetch_add_load() {
    unsafe { write_volatile(VA.as_ptr(), 9) };
    VA.fetch_add(1, Ordering::SeqCst);
    assert!(VA.load(Ordering::SeqCst) == 10)
}
#[kani::proof]
fn bug_volatile_fetch_add_load() {
    unsafe { write_volatile(VA.as_ptr(), 9) };
    VA.fetch_add(1, Ordering::SeqCst);
    assert!(VA.load(Ordering::SeqCst) == 6)
}
#[kani::proof]
fn safe_volatile_bool_load() {
    unsafe { write_volatile(VB.as_ptr(), true) };
    assert!(VB.load(Ordering::SeqCst))
}
#[kani::proof]
fn bug_volatile_bool_load() {
    unsafe { write_volatile(VB.as_ptr(), true) };
    assert!(!VB.load(Ordering::SeqCst))
}
// The volatile write and the raw read, with a store of another static or
// another part in between.
#[kani::proof]
fn safe_volatile_read_as_ptr() {
    unsafe { write_volatile(VD.as_ptr(), 9) };
    unsafe { assert!(*VD.as_ptr() == 9) }
}
#[kani::proof]
fn bug_volatile_read_as_ptr() {
    unsafe { write_volatile(VD.as_ptr(), 9) };
    unsafe { assert!(*VD.as_ptr() == 5) }
}
#[kani::proof]
fn safe_volatile_then_store_other_static() {
    unsafe { write_volatile(VT.as_ptr(), 9) };
    OTHER.store(1, Ordering::SeqCst);
    unsafe { assert!(*VT.as_ptr() == 9) }
}
#[kani::proof]
fn bug_volatile_then_store_other_static() {
    unsafe { write_volatile(VT.as_ptr(), 9) };
    OTHER.store(1, Ordering::SeqCst);
    unsafe { assert!(*VT.as_ptr() == 5) }
}
#[kani::proof]
fn safe_volatile_stmt_store_same_read() {
    unsafe { write_volatile(VQ.as_ptr(), 9) };
    unsafe { *VQ.as_ptr() += 1 };
    unsafe { assert!(*VQ.as_ptr() == 10) }
}
#[kani::proof]
fn bug_volatile_stmt_store_same_read() {
    unsafe { write_volatile(VQ.as_ptr(), 9) };
    unsafe { *VQ.as_ptr() += 1 };
    unsafe { assert!(*VQ.as_ptr() == 6) }
}
#[kani::proof]
fn safe_volatile_b_store_a_read_b() {
    unsafe { write_volatile(PR.b.as_ptr(), 9) };
    PR.a.store(4, Ordering::SeqCst);
    unsafe { assert!(*PR.b.as_ptr() == 9) }
}
#[kani::proof]
fn bug_volatile_b_store_a_read_b() {
    unsafe { write_volatile(PR.b.as_ptr(), 9) };
    PR.a.store(4, Ordering::SeqCst);
    unsafe { assert!(*PR.b.as_ptr() == 2) }
}
#[kani::proof]
fn safe_volatile_b_store_a_load_b() {
    unsafe { write_volatile(PV.b.as_ptr(), 9) };
    PV.a.store(4, Ordering::SeqCst);
    assert!(PV.b.load(Ordering::SeqCst) == 9)
}
#[kani::proof]
fn bug_volatile_b_store_a_load_b() {
    unsafe { write_volatile(PV.b.as_ptr(), 9) };
    PV.a.store(4, Ordering::SeqCst);
    assert!(PV.b.load(Ordering::SeqCst) == 2)
}
#[kani::proof]
fn safe_volatile_b_stmt_store_a_read_b() {
    unsafe { write_volatile(PS.b.as_ptr(), 9) };
    unsafe { *PS.a.as_ptr() = 4 };
    unsafe { assert!(*PS.b.as_ptr() == 9) }
}
#[kani::proof]
fn bug_volatile_b_stmt_store_a_read_b() {
    unsafe { write_volatile(PS.b.as_ptr(), 9) };
    unsafe { *PS.a.as_ptr() = 4 };
    unsafe { assert!(*PS.b.as_ptr() == 2) }
}
// `static mut`: the volatile write reaches the state a direct read selects.
#[kani::proof]
fn safe_mut_volatile_read_direct() {
    unsafe {
        write_volatile(addr_of_mut!(Q.1), 9);
        assert!(Q.1 == 9)
    }
}
#[kani::proof]
fn bug_mut_volatile_read_direct() {
    unsafe {
        write_volatile(addr_of_mut!(Q.1), 9);
        assert!(Q.1 == 2)
    }
}
#[kani::proof]
fn safe_mut_volatile_then_field_store_read() {
    unsafe {
        write_volatile(addr_of_mut!(QF.1), 9);
        QF.0 = 4;
        assert!(*addr_of!(QF.1) == 9)
    }
}
#[kani::proof]
fn bug_mut_volatile_then_field_store_read() {
    unsafe {
        write_volatile(addr_of_mut!(QF.1), 9);
        QF.0 = 4;
        assert!(*addr_of!(QF.1) == 2)
    }
}
#[kani::proof]
fn safe_mut_volatile_add_addr_read() {
    unsafe {
        write_volatile(addr_of_mut!(X), 9);
        X += 1;
        assert!(*addr_of!(X) == 10)
    }
}
#[kani::proof]
fn bug_mut_volatile_add_addr_read() {
    unsafe {
        write_volatile(addr_of_mut!(X), 9);
        X += 1;
        assert!(*addr_of!(X) == 6)
    }
}
#[kani::proof]
fn safe_mut_volatile_then_assign_raw_read() {
    unsafe {
        write_volatile(addr_of_mut!(XA), 9);
        XA = 4;
        assert!(*addr_of!(XA) == 4)
    }
}
#[kani::proof]
fn bug_mut_volatile_then_assign_raw_read() {
    unsafe {
        write_volatile(addr_of_mut!(XA), 9);
        XA = 4;
        assert!(*addr_of!(XA) == 9)
    }
}
#[kani::proof]
fn safe_volatile_mut_array_elem_read() {
    unsafe {
        write_volatile(addr_of_mut!(G[2]), 9);
        assert!(G[2] == 9)
    }
}
#[kani::proof]
fn bug_volatile_mut_array_elem_read() {
    unsafe {
        write_volatile(addr_of_mut!(G[2]), 9);
        assert!(G[2] == 3)
    }
}
#[kani::proof]
fn safe_volatile_mut_array_elem_then_store_raw_read() {
    unsafe {
        write_volatile(addr_of_mut!(GS[2]), 9);
        GS[0] = 7;
        assert!(*addr_of!(GS[2]) == 9)
    }
}
#[kani::proof]
fn bug_volatile_mut_array_elem_then_store_raw_read() {
    unsafe {
        write_volatile(addr_of_mut!(GS[2]), 9);
        GS[0] = 7;
        assert!(*addr_of!(GS[2]) == 3)
    }
}
