// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Budget probe: 4 CAS rounds with decomposed comparison + 3 with tuple eq.
//
// kani-expect: UNKNOWN
// kani-expect: check_three_tuple_one_decomposed=PROOF
// kani-expect: check_four_decomposed=PROOF
// NOTE: Most harnesses (1/2) demoted PROOF→UNKNOWN by false proof defense (ay#8578).

#![feature(core_intrinsics)]
use std::intrinsics::{AtomicOrdering, atomic_cxchg};

#[kani::proof]
fn check_four_decomposed() {
    let mut a = 0u8;
    let p: *mut u8 = &mut a;
    unsafe {
        let r1 = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, 0, 1);
        assert!(r1.0 == 0 && r1.1);
        let r2 = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, 1, 2);
        assert!(r2.0 == 1 && r2.1);
        let r3 = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, 2, 3);
        assert!(r3.0 == 2 && r3.1);
        let r4 = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, 3, 4);
        assert!(r4.0 == 3 && r4.1);
    }
}

#[kani::proof]
fn check_three_tuple_one_decomposed() {
    let mut a = 0u8;
    let p: *mut u8 = &mut a;
    unsafe {
        let r1 = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, 0, 1);
        assert!(r1 == (0, true));
        let r2 = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, 1, 2);
        assert!(r2 == (1, true));
        let r3 = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, 2, 3);
        assert!(r3 == (2, true));
        let r4 = atomic_cxchg::<_, { AtomicOrdering::SeqCst }, { AtomicOrdering::SeqCst }>(p, 3, 4);
        assert!(r4.0 == 3 && r4.1);  // decomposed 4th assertion
    }
}
