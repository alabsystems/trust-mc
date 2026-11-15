// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Live storage semantics: positive, assertion, bounds and fallback controls.
#![allow(dead_code)]
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};
static CELLS: [AtomicU32; 2] = [AtomicU32::new(11), AtomicU32::new(23)];
#[kani::proof]
fn slice_safe() {
    let s: &[AtomicU32] = &CELLS;
    let t = s;
    t[1].store(39, SeqCst);
    assert!(CELLS[1].load(SeqCst) == 39, "written cell");
    assert!(CELLS[0].load(SeqCst) == 11, "neighbor");
}
#[kani::proof]
fn slice_bug() {
    let s: &[AtomicU32] = &CELLS;
    s[1].store(39, SeqCst);
    assert!(CELLS[1].load(SeqCst) == 23, "stale cell");
}
#[kani::proof]
fn choice_safe() {
    let c: bool = kani::any();
    let r = if c { &CELLS[0] } else { &CELLS[1] };
    r.store(39, SeqCst);
    assert!(c || CELLS[1].load(SeqCst) == 39, "false arm");
    assert!(!c || CELLS[1].load(SeqCst) == 23, "true arm neighbor");
    assert!(!c || CELLS[0].load(SeqCst) == 39, "true arm");
    assert!(c || CELLS[0].load(SeqCst) == 11, "false arm neighbor");
}
#[kani::proof]
fn choice_bug() {
    let c: bool = kani::any();
    let r = if c { &CELLS[0] } else { &CELLS[1] };
    r.store(39, SeqCst);
    assert!(c || CELLS[1].load(SeqCst) == 23, "stale false arm");
}
#[kani::proof]
fn symbolic_safe() {
    let i: usize = kani::any();
    if i < 2 {
        CELLS[i].store(39, SeqCst);
        assert!(CELLS[i].load(SeqCst) == 39, "selected");
        assert!(i == 0 || CELLS[0].load(SeqCst) == 11, "neighbor");
    }
}
#[kani::proof]
fn symbolic_bug() {
    let i: usize = kani::any();
    if i < 2 {
        CELLS[i].store(39, SeqCst);
        assert!(CELLS[i].load(SeqCst) != 39, "wrong selected");
    }
}
#[kani::proof]
fn iter_safe() {
    for cell in CELLS.iter() {
        cell.store(39, SeqCst);
    }
    assert!(CELLS[1].load(SeqCst) == 39, "last cell");
    assert!(CELLS[0].load(SeqCst) == 39, "first cell");
}
#[kani::proof]
fn iter_bug() {
    for cell in CELLS.iter() {
        cell.store(39, SeqCst);
    }
    assert!(CELLS[1].load(SeqCst) == 23, "stale last cell");
}

#[kani::proof]
fn aliases_cross_view_safe() {
    let s: &[AtomicU32] = &CELLS;
    let t = s;
    let r = &t[1];
    assert!(std::ptr::eq(r, &CELLS[1]), "same storage");
    r.store(39, SeqCst);
    assert!(unsafe { *CELLS[1].as_ptr() } == 39, "scalar view");
    assert!(CELLS[0].load(SeqCst) == 11, "neighbor");
}
#[kani::proof]
fn sequential_rmw_safe() {
    let s: &[AtomicU32] = &CELLS;
    s[1].store(39, SeqCst);
    let old = CELLS[1].fetch_add(2, SeqCst);
    s[0].store(57, SeqCst);
    assert!(old == 39, "old RMW value");
    assert!(CELLS[1].load(SeqCst) == 41, "later state");
    assert!(unsafe { *CELLS[1].as_ptr() } == 41, "later scalar view");
    assert!(CELLS[0].load(SeqCst) == 57, "other store");
}
#[kani::proof]
fn sequential_rmw_bug() {
    let s: &[AtomicU32] = &CELLS;
    s[1].store(39, SeqCst);
    let old = CELLS[1].fetch_add(2, SeqCst);
    assert!(old == 23, "stale old RMW");
}
#[kani::proof]
fn cursor_snapshot_safe() {
    let mut it = CELLS.iter();
    match it.next() {
        Some(first) => match it.next() {
            Some(second) => {
                first.store(39, SeqCst);
                second.store(57, SeqCst);
                assert!(std::ptr::eq(first, &CELLS[0]), "first identity after next");
                assert!(std::ptr::eq(second, &CELLS[1]), "second identity");
            }
            None => assert!(false, "second exists"),
        },
        None => assert!(false, "first exists"),
    }
    match it.next() {
        None => (),
        Some(_) => assert!(false, "exhausted"),
    }
    assert!(CELLS[0].load(SeqCst) == 39, "snapshot cell");
    assert!(CELLS[1].load(SeqCst) == 57, "second cell");
}
#[kani::proof]
fn early_break_safe() {
    let mut count = 0;
    for cell in CELLS.iter() {
        cell.store(39, SeqCst);
        count += 1;
        break;
    }
    assert!(count == 1, "one side effect");
    assert!(CELLS[0].load(SeqCst) == 39, "first cell");
    assert!(CELLS[1].load(SeqCst) == 23, "unvisited neighbor");
}
#[kani::proof]
fn early_break_bug() {
    for cell in CELLS.iter() {
        cell.store(39, SeqCst);
        break;
    }
    assert!(CELLS[1].load(SeqCst) == 39, "unvisited cell is not written");
}
#[kani::proof]
fn conditional_write_safe() {
    let c: bool = kani::any();
    let r = if c { &CELLS[0] } else { &CELLS[1] };
    if c {
        r.store(39, SeqCst);
    }
    assert!(CELLS[1].load(SeqCst) == 23, "never written");
    assert!(c || CELLS[0].load(SeqCst) == 11, "no write on false arm");
}
#[kani::proof]
fn conditional_write_bug() {
    let c: bool = kani::any();
    if c {
        CELLS[1].store(39, SeqCst);
    }
    assert!(CELLS[1].load(SeqCst) == 39, "missing write on false path");
}
#[kani::proof]
fn two_objects_safe() {
    let c: bool = kani::any();
    static OTHER: [AtomicU32; 2] = [AtomicU32::new(5), AtomicU32::new(7)];
    let r = if c { &CELLS[1] } else { &OTHER[1] };
    r.store(39, SeqCst);
    assert!(!c || OTHER[1].load(SeqCst) == 7, "other allocation untouched");
    assert!(c || CELLS[1].load(SeqCst) == 23, "first allocation untouched");
    assert!(c || OTHER[1].load(SeqCst) == 39, "other allocation written");
    assert!(!c || CELLS[1].load(SeqCst) == 39, "first allocation written");
}
#[kani::proof]
fn oob_bug() {
    let i: usize = kani::any();
    CELLS[i].store(39, SeqCst);
    assert!(true, "bounds error remains");
}
#[kani::proof]
fn iter_skip_safe() {
    let c: bool = kani::any();
    let mut count = 0usize;
    for cell in CELLS.iter() {
        if count == 0 || c {
            cell.store(39, SeqCst);
        }
        count += 1;
    }
    assert!(count == 2, "all iterations");
    assert!(CELLS[0].load(SeqCst) == 39, "first written");
    assert!(c || CELLS[1].load(SeqCst) == 23, "second skipped");
    assert!(!c || CELLS[1].load(SeqCst) == 39, "second written");
}

#[kani::proof]
fn guard_mixed_producer() {
    let c: bool = kani::any();
    let mut it = CELLS.iter();
    let candidate = if c { it.next() } else { Some(&CELLS[1]) };
    if let Some(cell) = candidate {
        cell.store(39, SeqCst);
    }
    assert!(c || CELLS[1].load(SeqCst) == 39, "mixed producer remains guarded");
}
#[kani::proof]
fn guard_opaque_receiver() {
    let cell = std::hint::black_box(&CELLS[1]);
    cell.store(39, SeqCst);
    assert!(CELLS[1].load(SeqCst) == 39, "opaque producer remains guarded");
}
