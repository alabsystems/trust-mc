// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Budget probe: field-wise decomposed comparison to bypass PartialEq.
//
// kani-expect: PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).

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
