// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Scale test for raw atomic_cxchg — find the breaking point between 2 and 15 vars.
//
// kani-expect: PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).

#![feature(core_intrinsics)]
use std::intrinsics::{AtomicOrdering, atomic_cxchg};

#[kani::proof]
fn check_five_vars() {
    let mut a1 = 0u8;
    let mut a2 = 0u8;
    let mut a3 = 0u8;
    let mut a4 = 0u8;
    let mut a5 = 0u8;

    let p1: *mut u8 = &mut a1;
    let p2: *mut u8 = &mut a2;
    let p3: *mut u8 = &mut a3;
    let p4: *mut u8 = &mut a4;
    let p5: *mut u8 = &mut a5;

    unsafe {
        let x1 = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p1, 0, 1);
        let x2 = atomic_cxchg::<_, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p2, 0, 1);
        let x3 = atomic_cxchg::<_, { AtomicOrdering::Acquire }, { AtomicOrdering::Relaxed }>(p3, 0, 1);
        let x4 = atomic_cxchg::<_, { AtomicOrdering::Relaxed }, { AtomicOrdering::Relaxed }>(p4, 0, 1);
        let x5 = atomic_cxchg::<_, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(p5, 0, 1);

        assert!(x1 == (0, true));
        assert!(x2 == (0, true));
        assert!(x3 == (0, true));
        assert!(x4 == (0, true));
        assert!(x5 == (0, true));

        let y1 = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p1, 1, 1);
        let y2 = atomic_cxchg::<_, { AtomicOrdering::AcqRel }, { AtomicOrdering::Acquire }>(p2, 1, 1);
        let y3 = atomic_cxchg::<_, { AtomicOrdering::Acquire }, { AtomicOrdering::Relaxed }>(p3, 1, 1);
        let y4 = atomic_cxchg::<_, { AtomicOrdering::Relaxed }, { AtomicOrdering::Relaxed }>(p4, 1, 1);
        let y5 = atomic_cxchg::<_, { AtomicOrdering::Release }, { AtomicOrdering::Relaxed }>(p5, 1, 1);

        assert!(y1 == (1, true));
        assert!(y2 == (1, true));
        assert!(y3 == (1, true));
        assert!(y4 == (1, true));
        assert!(y5 == (1, true));
    }
}
