// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Test: raw cxchg with manual field decomposition instead of tuple PartialEq.
// If this PROOFs, the gap is in tuple PartialEq dispatch, not CAS encoding.
//
// kani-expect: check_three_decomposed=PROOF

#![feature(core_intrinsics)]
use std::intrinsics::{AtomicOrdering, atomic_cxchg};

#[kani::proof]
fn check_three_decomposed() {
    let mut a1 = 0u8;
    let mut a2 = 0u8;
    let mut a3 = 0u8;

    let p1: *mut u8 = &mut a1;
    let p2: *mut u8 = &mut a2;
    let p3: *mut u8 = &mut a3;

    unsafe {
        let x1 = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p1, 0, 1);
        let x2 = atomic_cxchg::<_, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p2, 0, 1);
        let x3 = atomic_cxchg::<_, { AtomicOrdering::Acquire }, { AtomicOrdering::Relaxed }>(p3, 0, 1);

        assert!(x1.0 == 0 && x1.1);
        assert!(x2.0 == 0 && x2.1);
        assert!(x3.0 == 0 && x3.1);

        let y1 = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p1, 1, 1);
        let y2 = atomic_cxchg::<_, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p2, 1, 1);
        let y3 = atomic_cxchg::<_, { AtomicOrdering::Acquire }, { AtomicOrdering::Relaxed }>(p3, 1, 1);

        assert!(y1.0 == 1 && y1.1);
        assert!(y2.0 == 1 && y2.1);
        assert!(y3.0 == 1 && y3.1);
    }
}
