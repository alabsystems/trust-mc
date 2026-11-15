// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (missed-bug tripwire) -- `u8::unchecked_add` UB inside a
//! `Drop` impl, walked by the CHC drop-body consumers.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_drop_box_dyn_multi  -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   bug_drop_box_dyn_single -> VERIFICATION:- FAILED  (same check)
//!   safe_drop_box_dyn_multi -> VERIFICATION:- SUCCESSFUL
//!   bug_drop_direct         -> VERIFICATION:- FAILED  (same check; control)
//!   safe_drop_direct        -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. Dropping a `Box<dyn Tr>` inlines the concrete type's
//! drop glue through the drop consumers (`transition_drop/dyn_dispatch.rs` for
//! one candidate, `dyn_dispatch_multi.rs` for several). They walk the drop body
//! with `translate_inline_body` and used the walk's VALUE and assert guard only,
//! discarding its `deferred_checks`, so the `unchecked_add` check the walker
//! records inside `Drop::drop` never became an error rule and the harness
//! verified SUCCESSFUL clean. The consumers now emit the checks at the drop
//! (`emit_deferred_inline_checks_at`; the multi-candidate consumer weakens each
//! candidate's checks by its `disc == id` guard), and a drop the walker itself
//! inlines parks its checks for the walker's `Drop` arm to absorb.
//!
//! `bug_drop_direct` drops a concrete value (statement-path drop glue), the
//! control. The safe twins are the precision guards.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_drop_body_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub trait Tr {
    fn id(&self) -> u8;
}
pub struct DA {
    a: u8,
    b: u8,
}
pub struct DB {
    a: u8,
    b: u8,
}
impl Drop for DA {
    fn drop(&mut self) {
        sink(unsafe { self.a.unchecked_add(self.b) });
    }
}
impl Drop for DB {
    fn drop(&mut self) {
        sink(unsafe { self.a.unchecked_add(self.b) });
    }
}
impl Tr for DA {
    fn id(&self) -> u8 {
        1
    }
}
impl Tr for DB {
    fn id(&self) -> u8 {
        2
    }
}

#[kani::proof]
fn bug_drop_box_dyn_multi() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Tr> = if kani::any() { Box::new(DA { a, b }) } else { Box::new(DB { a, b }) };
    sink(o.id());
}

#[kani::proof]
fn bug_drop_box_dyn_single() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let o: Box<dyn Tr> = Box::new(DA { a, b });
    sink(o.id());
}

#[kani::proof]
fn safe_drop_box_dyn_multi() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    let o: Box<dyn Tr> = if kani::any() { Box::new(DA { a, b }) } else { Box::new(DB { a, b }) };
    sink(o.id());
}

#[kani::proof]
fn bug_drop_direct() {
    let d = DA { a: kani::any(), b: kani::any() };
    drop(d);
}

#[kani::proof]
fn safe_drop_direct() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    kani::assume(a < 100 && b < 100);
    let d = DA { a, b };
    drop(d);
}
