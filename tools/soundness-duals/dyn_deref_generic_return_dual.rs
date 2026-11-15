// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness and seed):
//   safe_* -> VERIFICATION:- SUCCESSFUL
//   bug_*  -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. Found while landing design trust-mc-reds-final
// (2026-10-14), outside that design. A trait method called through a generic
// `T: Deref<Target = dyn Trait>` (here `Box<dyn Identity>`) returns 0 in the
// CHC lane: `bug_box_dyn_returns_zero` (the method returns 7) is proved, and
// so are both `!= 7` twins, while the safe `== id` twin gets a counterexample
// certified Genuine. The same call on a `Box<dyn Identity>` parameter, with
// no generic `Deref`, returns 7 (a FAILED, Genuine, `!= 7`). Every bug twin
// has a constant input, so a vacuous encoding cannot pass it.
//
// FIXED (decision TRUSTMC-OPEN-REDS, docs/DECISION_QUEUE.md): the inlined
// `Box::deref` reads the box's `NonNull` out of `&box` (`copy ((*_r).0.0)`),
// and that VALUE-of edge flowed through the cast and the reborrow into the
// devirtualized method's `self` as a points-at edge, so `(*self).id` read the
// box's own pointer bits (0 for every heap address). A value-of edge onto an
// address-typed field is now dropped whatever type spells the address
// (`ChcCtx::value_is_address`).

use std::ops::Deref;

trait Identity {
    fn id(&self) -> u16;
}

struct Inner {
    id: u8,
}

impl Identity for Inner {
    fn id(&self) -> u16 {
        self.id.into()
    }
}

fn id_from_coerce<T>(identity: T) -> u16
where
    T: Deref<Target = dyn Identity>,
{
    identity.id()
}

#[kani::proof]
fn safe_box_dyn_returns_its_id() {
    let id: u8 = kani::any();
    let boxed: Box<dyn Identity> = Box::new(Inner { id });
    assert!(id_from_coerce(boxed) == id as u16);
}

#[kani::proof]
fn bug_box_dyn_returns_seven() {
    let id: u8 = 7;
    let boxed: Box<dyn Identity> = Box::new(Inner { id });
    assert!(id_from_coerce(boxed) != 7);
}

#[kani::proof]
fn bug_box_dyn_returns_zero() {
    let boxed: Box<dyn Identity> = Box::new(Inner { id: 7 });
    assert!(id_from_coerce(boxed) == 0);
}

#[kani::proof]
fn bug_box_dyn_returns_a_different_id() {
    let id: u8 = kani::any();
    let boxed: Box<dyn Identity> = Box::new(Inner { id });
    assert!(id_from_coerce(boxed) != id as u16);
}

#[kani::proof]
fn safe_double_box_dyn_returns_its_id() {
    let id: u8 = kani::any();
    let boxed: Box<Box<dyn Identity>> = Box::new(Box::new(Inner { id }));
    assert!(id_from_coerce(*boxed) == id as u16);
}

#[kani::proof]
fn bug_double_box_dyn_returns_seven() {
    let id: u8 = 7;
    let boxed: Box<Box<dyn Identity>> = Box::new(Box::new(Inner { id }));
    assert!(id_from_coerce(*boxed) != 7);
}
