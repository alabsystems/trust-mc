// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Minimal test for raw atomic_cxchg intrinsic tuple equality.
// Isolates the encoding gap in AtomicCxchg/main.rs (30 CAS operations).
//
// kani-expect: UNKNOWN
// kani-expect: check_two_cxchg_same_var=PROOF
// kani-expect: check_single_cxchg=PROOF
// NOTE: check_single_cxchg nondeterministic (ay#8578/Spacer) — flips PROOF↔UNKNOWN across runs.

#![feature(core_intrinsics)]
use std::intrinsics::{AtomicOrdering, atomic_cxchg};

#[kani::proof]
fn check_single_cxchg() {
    let mut a = 0u8;
    let ptr: *mut u8 = &mut a;
    unsafe {
        let result = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(
            ptr, 0, 1,
        );
        assert!(result == (0, true));
    }
}

#[kani::proof]
fn check_two_cxchg_same_var() {
    let mut a = 0u8;
    let ptr: *mut u8 = &mut a;
    unsafe {
        let x = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(
            ptr, 0, 1,
        );
        assert!(x == (0, true));
        let y = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(
            ptr, 1, 1,
        );
        assert!(y == (1, true));
    }
}
