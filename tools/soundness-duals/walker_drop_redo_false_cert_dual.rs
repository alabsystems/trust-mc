// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (KNOWN-RED false-certificate tracker) -- a `Box<dyn>` method
//! writes a field of `*self`, moves the old value out with `mem::replace` and
//! drops it; the walked `Drop::drop` body of the moved-out value checks the
//! field it holds.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   safe_dyn_redo_entry_overflows  -> VERIFICATION:- SUCCESSFUL
//!   bug_dyn_redo_written_overflows -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_dyn_redo_both_overflow     -> VERIFICATION:- FAILED  (same check; control)
//!
//! Measured 2026-09-24 at ay 5d900fd2f (CHC lane):
//!   harness                         branch 328b4a952027        main 72090d76d40a
//!   safe_dyn_redo_entry_overflows   FAILED Genuine             SUCCESSFUL clean
//!   bug_dyn_redo_written_overflows  SUCCESSFUL clean           SUCCESSFUL clean
//!   bug_dyn_redo_both_overflow      FAILED Genuine             SUCCESSFUL clean
//!
//! MECHANISM (the lost write is pre-existing; the false certificate is NEW with
//! the walker branch's drop-body check emission):
//! 1. The dyn call is devirtualized and `redo` runs on the harness's statement
//!    path. `Box::new` stored the whole `S2` into the object's typed region
//!    array (`region_<obj>_bv24`). The field store `(*self).a = v` does not fit
//!    that region's sort, so it goes to the type-indexed `u8` array instead
//!    (`heap/memory_impl_region.rs`, "build_memory_store - region sort mismatch,
//!    using type array (#1446)"). `mem::replace(self, ..)` then reads the whole
//!    `*self` with a "region array select" of the region array, which never saw
//!    the write, so `old.a` is the ENTRY value.
//! 2. `drop(old)` is walked by the statement-path drop consumer
//!    (`rules/codegen_rules/transition_drop/codegen_drop.rs`, "Drop(drop_in_place::<S2>)
//!    -> inlined drop body") through `walk_drop_body` (`call/inline_body.rs`).
//!    The walked `Drop::drop` body stores nothing and the write happened before
//!    the walk began (its write mark is taken at walk entry), so
//!    `drop_body_check_after_walk_store` is not recorded. The branch emits the
//!    body's `unchecked_add` check, which tests `255 + 1` for the safe row and is
//!    certified Genuine, and `254 + 1` for the bug row, which is proved. Main
//!    emits no drop-body checks, so every row is SUCCESSFUL clean there.
//!    A probe with `mem::forget(old)` in place of `drop(old)` is SUCCESSFUL clean
//!    on the branch: the `Box<dyn>` drop of the replacement value reads it
//!    correctly, so the false certificate comes from the drop of `old`.
//!
//! Promoted from the 2026-09-24 walker drop-certificate verification (probe
//! p10_entry_overflow.rs safe_dyn_redo_entry_overflows); the bug twin and the
//! control are new.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_drop_redo_false_cert_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Swap2 {
    fn redo(&mut self);
}
pub struct S2 {
    a: u8,
    b: u8,
    c: u8,
}
impl Drop for S2 {
    fn drop(&mut self) {
        sink(unsafe { self.a.unchecked_add(self.b) });
    }
}
impl Swap2 for S2 {
    fn redo(&mut self) {
        self.a = self.a.wrapping_add(self.c);
        let old = core::mem::replace(self, S2 { a: 0, b: 0, c: 0 });
        drop(old);
    }
}

// Entry a = 255 would overflow, but redo writes a = 0 before the old value is
// moved out and dropped.
#[kani::proof]
fn safe_dyn_redo_entry_overflows() {
    let mut o: Box<dyn Swap2> = Box::new(S2 { a: 255, b: 1, c: 1 });
    o.redo();
}

// The other way round: entry a = 254 does not overflow, the written a = 255 does.
#[kani::proof]
fn bug_dyn_redo_written_overflows() {
    let mut o: Box<dyn Swap2> = Box::new(S2 { a: 254, b: 1, c: 1 });
    o.redo();
}

// Control: entry and written value both overflow (c = 0 leaves a = 255).
#[kani::proof]
fn bug_dyn_redo_both_overflow() {
    let mut o: Box<dyn Swap2> = Box::new(S2 { a: 255, b: 1, c: 0 });
    o.redo();
}
