// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a method named `take` (or `as_mut`) on an `Option` type
//! that is not core's `Option::take`.
//!
//! Three CHC lanes recognized `Option::take`/`Option::as_mut` by the callee's
//! NAME alone (it contains `Option` and ends in `::take`/`::as_mut`) and
//! replaced the call with core's semantics, without looking at the body:
//! - the host fast path (`codegen_call_dispatch_option_ptr.rs`,
//!   `try_dispatch_option_state_fast_path`): `*self = None`, result = `*self`;
//! - the walker fast path (`codegen_call_virtual_inline/nested_option_state.rs`,
//!   `try_inline_option_state_call`), the same inside an inline walk;
//! - the spawn-scheduler bridge (`codegen_call_virtual_inline/vtable_prop.rs`,
//!   `attach_spawn_task_slot_vtable`), which filled an empty caller update of
//!   `self` with `None` and handed the result the active task's vtable.
//! A user trait implemented for `Option<u8>` (`<Option<u8> as Peek>::take`)
//! reaches all three. Fixed by identifying core's inherent method by its def
//! path (`core::option::Option::<T>::take`, printed through `std`); any other
//! callee keeps what its walked body established.
//!
//! The host rows need the user `take` to stay a call: it recurses twelve
//! levels, past the MIR inliner's depth, and the innermost call is the one the
//! fast path modeled. The spawn bridge is pinned by unit tests
//! (test_call_block_on_with_spawn_task_slot.rs): the spawn lane fails closed on
//! whole harnesses of this shape (EncodingGap on bug and safe rows alike).
//!
//! Oracle: the corpus-rev Kani 4c0fce8c3 (Kani 0.67.0) FAILS every bug_ row on
//! the assertion it carries and verifies every safe_ row (manifest entry).
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s option_take_by_name_dual.rs

pub trait Peek {
    fn take(&mut self) -> Self;
}

impl Peek for Option<u8> {
    // Counts the payload down to 0 through recursion and restores it on the way
    // out: `*self` ends unchanged and the result is `Some(0)`.
    fn take(&mut self) -> Self {
        match *self {
            Some(n) if n > 0 => {
                *self = Some(n - 1);
                let r = Peek::take(self);
                *self = Some(n);
                r
            }
            _ => *self,
        }
    }
}

// ---- host fast path ------------------------------------------------------------

#[kani::proof]
fn bug_user_take_host() {
    let mut o = Some(12u8);
    let r = Peek::take(&mut o);
    assert!(o == Some(12));
    assert!(r != Some(0));
}

#[kani::proof]
fn safe_user_take_host() {
    let mut o = Some(12u8);
    let r = Peek::take(&mut o);
    assert!(o == Some(12) && r == Some(0));
}

#[kani::proof]
fn bug_core_take_host() {
    let mut o = Some(5u8);
    let r = o.take();
    assert!(r == Some(5));
    assert!(o.is_some());
}

#[kani::proof]
fn safe_core_take_host() {
    let mut o = Some(5u8);
    let r = o.take();
    assert!(o.is_none() && r == Some(5));
}

// ---- walker fast path (dyn door) -------------------------------------------------

pub trait Swap {
    fn take(&mut self) -> Option<u8>;
}

impl Swap for Option<u8> {
    fn take(&mut self) -> Option<u8> {
        None
    }
}

pub trait Keep {
    fn user_take(&self) -> Option<u8>;
    fn core_take(&self) -> (Option<u8>, Option<u8>);
}

pub struct KA;
pub struct KB;

impl Keep for KA {
    fn user_take(&self) -> Option<u8> {
        let mut o = Some(5u8);
        let _r = Swap::take(&mut o);
        o
    }
    fn core_take(&self) -> (Option<u8>, Option<u8>) {
        let mut o = Some(5u8);
        let r = o.take();
        (o, r)
    }
}

impl Keep for KB {
    fn user_take(&self) -> Option<u8> {
        let mut o = Some(5u8);
        let _r = Swap::take(&mut o);
        o
    }
    fn core_take(&self) -> (Option<u8>, Option<u8>) {
        let mut o = Some(5u8);
        let r = o.take();
        (o, r)
    }
}

fn pick() -> Box<dyn Keep> {
    if kani::any() { Box::new(KA) } else { Box::new(KB) }
}

#[kani::proof]
fn bug_user_take_walk() {
    assert!(pick().user_take().is_none());
}

#[kani::proof]
fn safe_user_take_walk() {
    assert!(pick().user_take() == Some(5));
}

#[kani::proof]
fn bug_core_take_walk() {
    let (o, _r) = pick().core_take();
    assert!(o.is_some());
}

#[kani::proof]
fn safe_core_take_walk() {
    let (o, r) = pick().core_take();
    assert!(o.is_none() && r == Some(5));
}
