// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a SHARED slice view whose elements are `Freeze` by type but reach
// interior-mutable state through a pointer: `&Cell<u8>`, `Box<Cell<u8>>`,
// `Rc<Cell<u8>>` and `Arc<AtomicU8>` elements, set through the view and set
// through the other alias, over `s[..]` and `s[a..]`.
//
// Written by the adversarial review of m3/soundness-fixes-2 (2026-09-13) around
// acdd6604e: the BMC index stubs copy the referent for a view that
// `slice_view_is_frozen` accepts, and `definitely_freeze` stops at pointers. The
// copy holds the same pointers, so a write through either alias must be seen
// through the other, or the harness must fail closed.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

use std::cell::Cell;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicU8, Ordering};

#[kani::proof]
fn refs_to_cells_set_after_view_safe() {
    let cells = [Cell::new(1u8), Cell::new(2u8)];
    let refs: [&Cell<u8>; 2] = [&cells[0], &cells[1]];
    let view: &[&Cell<u8>] = &refs[..];
    cells[0].set(7);
    assert!(view[0].get() == 7 && view[1].get() == 2);
}

#[kani::proof]
fn refs_to_cells_set_after_view_must_fail() {
    let cells = [Cell::new(1u8), Cell::new(2u8)];
    let refs: [&Cell<u8>; 2] = [&cells[0], &cells[1]];
    let view: &[&Cell<u8>] = &refs[..];
    cells[0].set(7);
    assert!(view[0].get() == 1);
}

#[kani::proof]
fn refs_to_cells_set_through_view_safe() {
    let cells = [Cell::new(1u8), Cell::new(2u8)];
    let refs: [&Cell<u8>; 2] = [&cells[0], &cells[1]];
    let view: &[&Cell<u8>] = &refs[..];
    view[1].set(7);
    assert!(cells[1].get() == 7 && cells[0].get() == 1);
}

#[kani::proof]
fn refs_to_cells_set_through_view_must_fail() {
    let cells = [Cell::new(1u8), Cell::new(2u8)];
    let refs: [&Cell<u8>; 2] = [&cells[0], &cells[1]];
    let view: &[&Cell<u8>] = &refs[..];
    view[1].set(7);
    assert!(cells[1].get() == 2);
}

#[kani::proof]
fn refs_to_cells_range_view_set_after_safe() {
    let cells = [Cell::new(1u8), Cell::new(2u8), Cell::new(3u8)];
    let refs: [&Cell<u8>; 3] = [&cells[0], &cells[1], &cells[2]];
    let view: &[&Cell<u8>] = &refs[1..];
    cells[1].set(7);
    assert!(view.len() == 2 && view[0].get() == 7 && view[1].get() == 3);
}

#[kani::proof]
fn refs_to_cells_range_view_set_after_must_fail() {
    let cells = [Cell::new(1u8), Cell::new(2u8), Cell::new(3u8)];
    let refs: [&Cell<u8>; 3] = [&cells[0], &cells[1], &cells[2]];
    let view: &[&Cell<u8>] = &refs[1..];
    cells[1].set(7);
    assert!(view[0].get() == 2);
}

#[kani::proof]
fn box_cells_set_through_view_safe() {
    let arr = [Box::new(Cell::new(1u8)), Box::new(Cell::new(2u8))];
    let view: &[Box<Cell<u8>>] = &arr[..];
    view[0].set(7);
    assert!(arr[0].get() == 7 && arr[1].get() == 2);
}

#[kani::proof]
fn box_cells_set_through_view_must_fail() {
    let arr = [Box::new(Cell::new(1u8)), Box::new(Cell::new(2u8))];
    let view: &[Box<Cell<u8>>] = &arr[..];
    view[0].set(7);
    assert!(arr[0].get() == 1);
}

#[kani::proof]
fn box_cells_set_after_view_safe() {
    let arr = [Box::new(Cell::new(1u8)), Box::new(Cell::new(2u8))];
    let view: &[Box<Cell<u8>>] = &arr[..];
    arr[1].set(9);
    assert!(view[1].get() == 9 && view[0].get() == 1);
}

#[kani::proof]
fn box_cells_set_after_view_must_fail() {
    let arr = [Box::new(Cell::new(1u8)), Box::new(Cell::new(2u8))];
    let view: &[Box<Cell<u8>>] = &arr[..];
    arr[1].set(9);
    assert!(view[1].get() == 2);
}

#[kani::proof]
fn rc_cells_set_after_view_safe() {
    let shared = Rc::new(Cell::new(1u8));
    let arr = [shared.clone(), Rc::new(Cell::new(2u8))];
    let view: &[Rc<Cell<u8>>] = &arr[..];
    shared.set(7);
    assert!(view[0].get() == 7 && view[1].get() == 2);
}

#[kani::proof]
fn rc_cells_set_after_view_must_fail() {
    let shared = Rc::new(Cell::new(1u8));
    let arr = [shared.clone(), Rc::new(Cell::new(2u8))];
    let view: &[Rc<Cell<u8>>] = &arr[..];
    shared.set(7);
    assert!(view[0].get() == 1);
}

#[kani::proof]
fn rc_cells_set_through_view_safe() {
    let shared = Rc::new(Cell::new(1u8));
    let arr = [shared.clone(), Rc::new(Cell::new(2u8))];
    let view: &[Rc<Cell<u8>>] = &arr[..];
    view[0].set(7);
    assert!(shared.get() == 7);
}

#[kani::proof]
fn rc_cells_set_through_view_must_fail() {
    let shared = Rc::new(Cell::new(1u8));
    let arr = [shared.clone(), Rc::new(Cell::new(2u8))];
    let view: &[Rc<Cell<u8>>] = &arr[..];
    view[0].set(7);
    assert!(shared.get() == 1);
}

#[kani::proof]
fn arc_atomics_set_after_view_safe() {
    let shared = Arc::new(AtomicU8::new(1));
    let arr = [shared.clone()];
    let view: &[Arc<AtomicU8>] = &arr[..];
    shared.store(7, Ordering::SeqCst);
    assert!(view[0].load(Ordering::SeqCst) == 7);
}

#[kani::proof]
fn arc_atomics_set_after_view_must_fail() {
    let shared = Arc::new(AtomicU8::new(1));
    let arr = [shared.clone()];
    let view: &[Arc<AtomicU8>] = &arr[..];
    shared.store(7, Ordering::SeqCst);
    assert!(view[0].load(Ordering::SeqCst) == 1);
}

#[kani::proof]
fn box_cells_range_view_set_through_safe() {
    let arr = [Box::new(Cell::new(1u8)), Box::new(Cell::new(2u8)), Box::new(Cell::new(3u8))];
    let view: &[Box<Cell<u8>>] = &arr[1..];
    view[0].set(7);
    assert!(arr[1].get() == 7 && arr[0].get() == 1 && arr[2].get() == 3);
}

#[kani::proof]
fn box_cells_range_view_set_through_must_fail() {
    let arr = [Box::new(Cell::new(1u8)), Box::new(Cell::new(2u8)), Box::new(Cell::new(3u8))];
    let view: &[Box<Cell<u8>>] = &arr[1..];
    view[0].set(7);
    assert!(arr[1].get() == 2);
}
