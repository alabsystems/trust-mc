// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Budget probe: exactly 4 tuple equality assertions.
//
// kani-expect: PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).

#![feature(core_intrinsics)]
use std::intrinsics::{AtomicOrdering, atomic_cxchg};

#[kani::proof]
fn check_four_tuple_eq() {
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
        assert!(r4 == (3, true));
    }
}
