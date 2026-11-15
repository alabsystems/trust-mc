// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Allocation identity and message-panic reachability in the BMC lane.
//
// Measured 2026-09-14 before the fix (frozen dev-cli lane, BMC):
//  * two address-taken locals had address symbols with no distinctness
//    constraint; the solver put them at one address, so a byte-memory write
//    through `pa` (an atomic intrinsic reads and writes byte memory, not the
//    typed environment) was read back through `pb`, and
//    kani/Intrinsics/Atomic/Unstable/AtomicAdd was certified Genuine on a safe
//    program. A plain `*pa = 5` does NOT reproduce it (that store goes through
//    the typed environment), which is why these harnesses use atomic_xadd;
//  * `Arguments::from_str` was stubbed as diverging, which cut the edge into the
//    block of an INLINED callee that calls `panic_nounwind_fmt`; that block then
//    had no path condition (read as `true`) and the NonZero precondition panic
//    fired on the constant 120 (kani/Enum/discriminant_128bits.rs).
//
// Oracles: `safe_*` MUST be SUCCESSFUL; `bug_*` MUST FAIL.

#![feature(core_intrinsics)]

use std::intrinsics::{AtomicOrdering, atomic_xadd};
use std::num::NonZeroU128;

#[kani::proof]
fn safe_atomic_add_through_two_locals() {
    let mut a1 = 0u8;
    let mut a2 = 0u8;
    let p1: *mut u8 = &mut a1;
    let p2: *mut u8 = &mut a2;
    unsafe {
        let x1 = atomic_xadd::<_, _, { AtomicOrdering::SeqCst }>(p1, 1u8);
        let x2 = atomic_xadd::<_, _, { AtomicOrdering::SeqCst }>(p2, 1u8);
        assert!(x1 == 0);
        assert!(x2 == 0);
        assert!(*p1 == 1);
    }
}

#[kani::proof]
fn bug_atomic_add_claimed_visible_through_other_local() {
    let mut a1 = 0u8;
    let mut a2 = 0u8;
    let p1: *mut u8 = &mut a1;
    let p2: *mut u8 = &mut a2;
    unsafe {
        let _ = atomic_xadd::<_, _, { AtomicOrdering::SeqCst }>(p1, 1u8);
        let x2 = atomic_xadd::<_, _, { AtomicOrdering::SeqCst }>(p2, 1u8);
        assert!(x2 == 1);
    }
}

fn create() -> Option<NonZeroU128> {
    unsafe { Some(NonZeroU128::new_unchecked(120u128.into())) }
}

#[kani::proof]
fn safe_inlined_nonzero_new_unchecked() {
    let opt = create();
    assert!(opt.is_some());
    assert!(opt.unwrap().get() == 120);
}

#[kani::proof]
fn bug_inlined_nonzero_claimed_121() {
    let opt = create();
    assert!(opt.unwrap().get() == 121);
}
