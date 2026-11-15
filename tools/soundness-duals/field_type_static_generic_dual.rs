// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness):
//   safe_* -> VERIFICATION:- SUCCESSFUL
//   bug_*  -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS (design trust-mc-reds-final §3, Rule A, test A3).
// Statics that hold atomics: a bare atomic static, a struct static with an
// atomic field, and a generic function instantiated at an atomic. The CHC
// lane's static mirror read the atomic's field type with a shallow
// substitution and panicked in rustc on `AtomicPrimitive::Storage`, killing
// the whole file (round 10 fixed the two static sites; this file guards the
// one rule, `shared::mono_ty::field_ty`, that replaces them).

use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};

static COUNTER: AtomicU32 = AtomicU32::new(10);

struct Stats {
    hits: AtomicUsize,
    limit: usize,
}

static STATS: Stats = Stats { hits: AtomicUsize::new(0), limit: 4 };

fn bump<T: Bump>(t: &T) -> u64 {
    t.bump()
}

trait Bump {
    fn bump(&self) -> u64;
}

impl Bump for AtomicU32 {
    fn bump(&self) -> u64 {
        self.fetch_add(1, Ordering::SeqCst) as u64
    }
}

#[kani::proof]
fn safe_static_atomic() {
    let old = COUNTER.fetch_add(5, Ordering::SeqCst);
    assert!(old == 10);
    assert!(COUNTER.load(Ordering::SeqCst) == 15);
}

#[kani::proof]
fn bug_static_atomic() {
    COUNTER.fetch_add(5, Ordering::SeqCst);
    assert!(COUNTER.load(Ordering::SeqCst) == 10);
}

#[kani::proof]
fn safe_static_struct_atomic() {
    STATS.hits.fetch_add(1, Ordering::SeqCst);
    assert!(STATS.hits.load(Ordering::SeqCst) == 1);
    assert!(STATS.limit == 4);
}

#[kani::proof]
fn bug_static_struct_atomic() {
    STATS.hits.fetch_add(1, Ordering::SeqCst);
    assert!(STATS.hits.load(Ordering::SeqCst) == 0);
}

#[kani::proof]
fn safe_generic_static() {
    let old = bump(&COUNTER);
    assert!(old == 10);
    assert!(COUNTER.load(Ordering::SeqCst) == 11);
}

#[kani::proof]
fn bug_generic_static() {
    bump(&COUNTER);
    assert!(COUNTER.load(Ordering::SeqCst) == 10);
}
