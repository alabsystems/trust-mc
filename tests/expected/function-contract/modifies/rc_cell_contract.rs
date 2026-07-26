// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Zfunction-contracts

use std::cell::Cell;
use std::ops::Deref;
use std::rc::Rc;

// Regression based on <https://github.com/model-checking/kani/issues/2907>.
// Use Cell's raw interior pointer so the contract does not borrow through a
// temporary guard whose lifetime ends inside the attribute expression.
#[kani::modifies(ptr.deref().as_ptr())]
fn modify(ptr: &Rc<Cell<u32>>) {
    ptr.set(1);
}

#[kani::proof_for_contract(modify)]
fn main() {
    let ptr = Rc::new(Cell::new(kani::any()));
    modify(&ptr);
    std::mem::forget(ptr);
}
