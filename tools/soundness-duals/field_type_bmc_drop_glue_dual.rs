// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness):
//   safe_* -> VERIFICATION:- SUCCESSFUL
//   bug_*  -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS (design trust-mc-reds-final §3, Rule A, test A1).
// Dropping a value that owns an atomic. The BMC lane decides whether a `Drop`
// it skips is benign by walking the dropped type's fields; it read each
// field's DECLARED type with a shallow substitution, so `AtomicU8`'s field
// came back as `UnsafeCell<<T as AtomicPrimitive>::Storage>` with `T` free,
// its shallow parameter guard did not look inside the projection, and
// `resolve_drop_in_place` on it panicked in rustc
// (`normalize_erasing_regions.rs`, "cannot normalize ... Storage"), killing
// every harness of the file. The field's type must be instantiated at the
// ADT's own arguments (`shared::mono_ty::field_ty`), and the parameter test
// must be deep (`shared::mono_ty::has_unresolved_params`).

use std::sync::Arc;
use std::sync::atomic::{AtomicU8, Ordering};

struct Holder {
    flag: AtomicU8,
    tag: u8,
}

#[kani::proof]
fn safe_arc_atomic_drop() {
    let v: u8 = kani::any();
    let a = Arc::new(AtomicU8::new(v));
    a.store(v.wrapping_add(1), Ordering::SeqCst);
    let seen = a.load(Ordering::SeqCst);
    drop(a);
    assert!(seen == v.wrapping_add(1));
}

#[kani::proof]
fn bug_arc_atomic_drop() {
    let v: u8 = kani::any();
    let a = Arc::new(AtomicU8::new(v));
    a.store(v.wrapping_add(1), Ordering::SeqCst);
    let seen = a.load(Ordering::SeqCst);
    drop(a);
    assert!(seen == v);
}

#[kani::proof]
fn safe_struct_atomic_drop() {
    let t: u8 = kani::any();
    let h = Holder { flag: AtomicU8::new(0), tag: t };
    h.flag.store(1, Ordering::SeqCst);
    let seen = h.flag.load(Ordering::SeqCst);
    let tag = h.tag;
    drop(h);
    assert!(seen == 1 && tag == t);
}

#[kani::proof]
fn bug_struct_atomic_drop() {
    let t: u8 = kani::any();
    let h = Holder { flag: AtomicU8::new(0), tag: t };
    h.flag.store(1, Ordering::SeqCst);
    let seen = h.flag.load(Ordering::SeqCst);
    drop(h);
    assert!(seen == 0);
}
