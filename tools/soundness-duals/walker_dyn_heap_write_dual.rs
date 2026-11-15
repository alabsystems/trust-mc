// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (KNOWN-RED missed-bug tracker) -- a heap write to a
//! `Box<dyn>` payload that later dyn reads (methods and drops walked by the
//! CHC walker) do not see.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_write_then_coerce_const    -> VERIFICATION:- FAILED  ('assertion failed: o.get() < 255')
//!   bug_write_then_coerce_method   -> VERIFICATION:- FAILED  (same check)
//!   safe_write_then_coerce_method  -> VERIFICATION:- SUCCESSFUL
//!   bug_write_before_box_control   -> VERIFICATION:- FAILED  (same check; control)
//!   bug_multi_bump_then_get        -> VERIFICATION:- FAILED  ('assertion failed: o.get() < 255')
//!   bug_multi_bump_then_drop       -> VERIFICATION:- FAILED  ('attempt to compute `unchecked_add` which would overflow')
//!   safe_multi_bump_then_drop      -> VERIFICATION:- SUCCESSFUL
//!   bug_single_bump_then_get       -> VERIFICATION:- FAILED  ('assertion failed: o.get() < 255'; control)
//!   bug_write_then_ref_coerce      -> VERIFICATION:- FAILED  ('assertion failed: o.get() < 255')
//!   bug_write_b_then_coerce        -> VERIFICATION:- FAILED  ('assertion failed: r.b < 255')
//!   safe_write_then_coerce_const   -> VERIFICATION:- SUCCESSFUL
//!   bug_write_wide_then_coerce     -> VERIFICATION:- FAILED  ('assertion failed: o.get() < 255')
//!   safe_write_wide_then_coerce    -> VERIFICATION:- SUCCESSFUL
//!   bug_tuple_leaf_then_coerce     -> VERIFICATION:- FAILED  ('assertion failed: o.get() < 255')
//!   safe_tuple_leaf_then_coerce    -> VERIFICATION:- SUCCESSFUL
//!   bug_pair_leaf_then_coerce      -> VERIFICATION:- FAILED  ('assertion failed: o.get() < 255')
//!   bug_tuple_whole_then_coerce    -> VERIFICATION:- FAILED  ('assertion failed: o.get() < 255')
//!   bug_struct_field_whole_then_coerce  -> VERIFICATION:- FAILED ('assertion failed: o.get() < 255')
//!   safe_struct_field_whole_then_coerce -> VERIFICATION:- SUCCESSFUL
//!   bug_struct_copy_read_then_coerce    -> VERIFICATION:- FAILED ('assertion failed: o.get() < 255')
//!   safe_struct_copy_read_then_coerce   -> VERIFICATION:- SUCCESSFUL
//!   safe_ptr_write_then_coerce     -> VERIFICATION:- SUCCESSFUL
//!   safe_mem_replace_then_coerce   -> VERIFICATION:- SUCCESSFUL
//!   bug_store_call_then_coerce     -> VERIFICATION:- FAILED  ('assertion failed: o.get() < 255 || k != 3')
//!   safe_store_call_then_coerce    -> VERIFICATION:- SUCCESSFUL
//!   timing_sentinel_runs_last      -> VERIFICATION:- SUCCESSFUL
//!   safe_pair_leaf_then_coerce     -> VERIFICATION:- SUCCESSFUL
//!   bug_deep_tuple_leaf_then_coerce    -> VERIFICATION:- FAILED ('assertion failed: o.get() < 255')
//!   safe_deep_tuple_leaf_then_coerce   -> VERIFICATION:- SUCCESSFUL
//!   bug_tuple_leaf_then_ref_coerce     -> VERIFICATION:- FAILED ('assertion failed: o.get() < 255')
//!   safe_tuple_leaf_then_ref_coerce    -> VERIFICATION:- SUCCESSFUL
//!   safe_tuple_whole_then_coerce       -> VERIFICATION:- SUCCESSFUL
//!   bug_tuple_field_whole_then_coerce  -> VERIFICATION:- FAILED ('assertion failed: o.get() < 255')
//!   safe_tuple_field_whole_then_coerce -> VERIFICATION:- SUCCESSFUL
//!   bug_struct_leaf_then_coerce    -> VERIFICATION:- FAILED ('assertion failed: o.get() < 255')
//!   safe_struct_leaf_then_coerce   -> VERIFICATION:- SUCCESSFUL
//!   bug_ptr_write_then_coerce      -> VERIFICATION:- FAILED ('assertion failed: o.get() < 255')
//!   bug_mem_replace_then_coerce    -> VERIFICATION:- FAILED ('assertion failed: o.get() < 255')
//!   bug_helper_field_then_coerce   -> VERIFICATION:- FAILED ('assertion failed: o.get() < 255')
//!   safe_helper_field_then_coerce  -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISMS (pre-existing, NOT fixed; main misses each the same way):
//! 1. A STATEMENT WRITE TO A BOX PAYLOAD BEFORE THE UNSIZE COERCION.
//!    `let mut d = Box::new(DV { a, .. }); d.a = 255; let o: Box<dyn Tv> = d;`
//!    -- later reads through `o` see the `Box::new` constructor value, not the
//!    stored one, so `o.get() < 255` is proved (and a drop's checks on the
//!    payload inherit it). A write BEFORE `Box::new` is seen
//!    (`bug_write_before_box_control`). FIXED on fix/chc-lost-writes
//!    (2026-09-26): the coercion republished the payload's value as its
//!    CONCRETE type array holds it into the field cells the dyn read uses
//!    (`try_translate_dyn_trait_coercion`, the #4225 alias store), and a
//!    field store (another sort) reaches only those field cells, so the
//!    republished constructor value overwrote the stored one. After a field
//!    store the alias store now republishes the field view's own value
//!    (`heap/heap_unsize_alias.rs`); after stores of both kinds, or a store
//!    that may precede the coercion in a later-encoded block, it fails
//!    closed (`unsize_alias_view_stale`). The five rows after the controls
//!    were added with the fix (checked against the corpus-rev Kani
//!    4c0fce8c3): a `&dyn` coercion of the payload, a write of the second
//!    field read back through a cast, a safe twin of the constant write (a
//!    false certificate before the fix), and a `u16` field.
//!    TUPLE FIELDS (review of fix/chc-lost-writes, 2026-09-27). A tuple-typed
//!    field keeps a view of its own, its type-indexed array, which the walked
//!    impl reads when it projects into the tuple (`(self.x.0).0`) and which
//!    no leaf store writes; republishing the leaves left it at the
//!    constructor's value, so `bug_tuple_leaf_then_coerce` verified
//!    SUCCESSFUL clean on the first fix (the baseline timed out) and
//!    `bug_pair_leaf_then_coerce` was a missed bug on both. The interim fix
//!    failed closed after a field store to a payload with a tuple field. Since
//!    review follow-up 2 (2026-09-27) the walked impl's field map rebuilds a
//!    tuple, or a nested struct, field of `self` from its scalar leaves
//!    (`call/inline_field_map_reconstruct.rs`), the cells the republish
//!    writes, so the tuple rows are exact; only a field the field map still
//!    loads whole (an array of tuples) fails closed.
//!    The struct rows (a whole nested-struct field store, an impl reading a
//!    copy of the nested struct) and the store forms (`ptr::write`,
//!    `mem::replace`, a call between the store and the coercion) are exact
//!    and pin the field-view republish; each was a missed bug or a false
//!    certificate on the baseline. The bug twins of the `ptr::write` and
//!    `mem::replace` rows, and a store through a walked helper, ran into the
//!    driver watchdog (about 395 s): the const-prop guard
//!    `has_scalarized_obj_size_bounds` fired on the payload's in-bounds cells,
//!    so the drop's obligations stayed symbolic. The guard now keeps only VCs
//!    whose scalarized cells may lie out of bounds, and the rows decide in
//!    under a second. They are last in the file (the driver checks harnesses
//!    in reverse source order, so they run first), and
//!    `timing_sentinel_runs_last`, first in the file, is never checked if one
//!    of them brings the watchdog back (docs/chc-hole-fix-designs-2026-09-24.md,
//!    fix/chc-lost-writes).
//! 2. A `&mut self` DYN CALL WITH TWO OR MORE CANDIDATES LOSES ITS HEAP WRITE.
//!    `merge_guarded_dispatch_results`
//!    (`codegen_call_virtual_inline/dispatch.rs`) types each alias key's pending
//!    value by the FIRST impl's sort; the second impl's update hits "alias-update
//!    sort mismatch ... dropping" and `continue`s, the first's is lost with it,
//!    no alias update reaches the host transition, and the unwritten cell is
//!    framed as unchanged: after `o.bump(250)` the cell still holds `a`. With one
//!    impl the write is kept (`bug_single_bump_then_get`).
//!
//! Promoted from the 2026-09-24 adversarial review (drop-and-closure lens,
//! drop-closure/p9_write_coerce.rs and p8_multi_bump.rs; verifier probes
//! c1_controls.rs and p8s_single.rs).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_dyn_heap_write_dual.rs

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

#[inline(never)]
fn touch(x: u8) -> u8 {
    x
}

// TIMING GUARD. The driver checks harnesses in reverse source order, so this
// row, first in the file, runs LAST. When a row above it runs into the driver
// watchdog (the field-store rows at the end of the file did, at about 390 s,
// until fix/chc-lost-writes' review follow-up let constant propagation
// collapse their VCs), the driver exits and this row is never checked: the
// gate reads it as an error.
#[kani::proof]
fn timing_sentinel_runs_last() {
    let k = touch(3);
    assert!(k == 3);
}

// --- a single-impl read-only trait -------------------------------------------

pub trait Tv {
    fn get(&self) -> u8;
}
pub struct DV {
    a: u8,
    b: u8,
}
impl Tv for DV {
    fn get(&self) -> u8 {
        self.a
    }
}

pub struct DW {
    a: u16,
    b: u8,
}
impl Tv for DW {
    fn get(&self) -> u8 {
        self.a as u8
    }
}

// --- a two-impl trait with a `&mut self` writer and Drop impls ---------------

pub trait Tr {
    fn bump(&mut self, k: u8);
    fn get(&self) -> u8;
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
    fn bump(&mut self, k: u8) {
        self.a = self.a.wrapping_add(k);
    }
    fn get(&self) -> u8 {
        self.a
    }
}
impl Tr for DB {
    fn bump(&mut self, k: u8) {
        self.a = self.a.wrapping_add(k);
    }
    fn get(&self) -> u8 {
        self.a
    }
}

// --- the same writer behind a single-impl trait (control) --------------------

pub trait Ts {
    fn bump(&mut self, k: u8);
    fn get(&self) -> u8;
}
pub struct DS {
    a: u8,
    b: u8,
}
impl Drop for DS {
    fn drop(&mut self) {
        sink(unsafe { self.a.unchecked_add(self.b) });
    }
}
impl Ts for DS {
    fn bump(&mut self, k: u8) {
        self.a = self.a.wrapping_add(k);
    }
    fn get(&self) -> u8 {
        self.a
    }
}

#[kani::proof]
fn bug_write_then_coerce_const() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    d.a = 255;
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn bug_write_then_coerce_method() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    d.a = d.a.wrapping_add(250);
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn safe_write_then_coerce_method() {
    let a: u8 = kani::any();
    kani::assume(a < 4);
    let mut d = Box::new(DV { a, b: 1 });
    d.a = d.a.wrapping_add(250);
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn bug_write_before_box_control() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut v = DV { a, b: 1 };
    v.a = v.a.wrapping_add(250);
    let o: Box<dyn Tv> = Box::new(v);
    assert!(o.get() < 255);
}

#[kani::proof]
fn bug_multi_bump_then_get() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut o: Box<dyn Tr> = Box::new(DA { a, b: 1 });
    o.bump(250);
    assert!(o.get() < 255);
    core::mem::forget(o);
}

#[kani::proof]
fn bug_multi_bump_then_drop() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut o: Box<dyn Tr> = Box::new(DA { a, b: 1 });
    o.bump(250);
}

#[kani::proof]
fn safe_multi_bump_then_drop() {
    let a: u8 = kani::any();
    kani::assume(a < 4);
    let mut o: Box<dyn Tr> = Box::new(DA { a, b: 1 });
    o.bump(250);
}

#[kani::proof]
fn bug_single_bump_then_get() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut o: Box<dyn Ts> = Box::new(DS { a, b: 1 });
    o.bump(250);
    assert!(o.get() < 255);
    core::mem::forget(o);
}

#[kani::proof]
fn bug_write_then_ref_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    d.a = 255;
    let o: &dyn Tv = &*d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn bug_write_b_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a: 0, b: a });
    d.b = 255;
    let o: Box<dyn Tv> = d;
    let r: &DV = unsafe { &*(&*o as *const dyn Tv as *const DV) };
    assert!(r.b < 255);
}

#[kani::proof]
fn safe_write_then_coerce_const() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    d.a = 200;
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}

#[kani::proof]
fn bug_write_wide_then_coerce() {
    let a: u16 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DW { a, b: 1 });
    d.a = 255;
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn safe_write_wide_then_coerce() {
    let a: u16 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DW { a, b: 1 });
    d.a = 254;
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

// --- tuple and nested-struct payload fields (review of fix/chc-lost-writes) ---

pub struct D3 {
    x: ((u8, u8), u8),
    z: u8,
}
impl Tv for D3 {
    fn get(&self) -> u8 {
        (self.x.0).0
    }
}
pub struct N2 {
    x: (u8, u8),
    z: u8,
}
impl Tv for N2 {
    fn get(&self) -> u8 {
        self.x.0
    }
}
#[derive(Clone, Copy)]
pub struct In {
    p: u8,
    q: u8,
}
pub struct NS {
    i: In,
    z: u8,
}
impl Tv for NS {
    fn get(&self) -> u8 {
        self.i.p
    }
}
pub struct NC {
    i: In,
    z: u8,
}
impl Tv for NC {
    fn get(&self) -> u8 {
        let i = self.i;
        i.p
    }
}

#[kani::proof]
fn bug_tuple_leaf_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(D3 { x: ((a, 1), 2), z: 4 });
    d.x.0.0 = 255;
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn safe_tuple_leaf_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(D3 { x: ((a, 1), 2), z: 4 });
    d.x.0.0 = 200;
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}

#[kani::proof]
fn bug_pair_leaf_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N2 { x: (a, 1), z: 4 });
    d.x.0 = 255;
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn bug_tuple_whole_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(D3 { x: ((a, 1), 2), z: 4 });
    *d = D3 { x: ((255, 1), 2), z: 4 };
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn bug_struct_field_whole_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(NS { i: In { p: a, q: 1 }, z: 4 });
    d.i = In { p: 255, q: 2 };
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn safe_struct_field_whole_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(NS { i: In { p: a, q: 1 }, z: 4 });
    d.i = In { p: 200, q: 2 };
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}

#[kani::proof]
fn bug_struct_copy_read_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(NC { i: In { p: a, q: 1 }, z: 4 });
    d.i.p = 255;
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn safe_struct_copy_read_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(NC { i: In { p: a, q: 1 }, z: 4 });
    d.i.p = 200;
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}

#[kani::proof]
fn safe_ptr_write_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    unsafe {
        core::ptr::write(&mut d.a as *mut u8, 200);
    }
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}

#[kani::proof]
fn safe_mem_replace_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    let _ = core::mem::replace(&mut d.a, 200);
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}

#[kani::proof]
fn bug_store_call_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    d.a = 255;
    let k = touch(3);
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255 || k != 3);
}

#[kani::proof]
fn safe_store_call_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    d.a = 200;
    let k = touch(3);
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200 && k == 3);
}

// --- tuple payloads, exact since the field map rebuilds tuples from leaves ---

pub struct D5 {
    x: (((u8, u8), u8), u8),
    z: u8,
}
impl Tv for D5 {
    fn get(&self) -> u8 {
        ((self.x.0).0).0
    }
}

#[kani::proof]
fn safe_pair_leaf_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N2 { x: (a, 1), z: 4 });
    d.x.0 = 200;
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}

#[kani::proof]
fn bug_deep_tuple_leaf_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(D5 { x: (((a, 1), 2), 3), z: 4 });
    d.x.0.0.0 = 255;
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn safe_deep_tuple_leaf_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(D5 { x: (((a, 1), 2), 3), z: 4 });
    d.x.0.0.0 = 200;
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}

#[kani::proof]
fn bug_tuple_leaf_then_ref_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(D3 { x: ((a, 1), 2), z: 4 });
    d.x.0.0 = 255;
    let o: &dyn Tv = &*d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn safe_tuple_leaf_then_ref_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(D3 { x: ((a, 1), 2), z: 4 });
    d.x.0.0 = 200;
    let o: &dyn Tv = &*d;
    assert!(o.get() == 200);
}

#[kani::proof]
fn safe_tuple_whole_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(D3 { x: ((a, 1), 2), z: 4 });
    *d = D3 { x: ((200, 1), 2), z: 4 };
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}

#[kani::proof]
fn bug_tuple_field_whole_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N2 { x: (a, 1), z: 4 });
    d.x = (255, 1);
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn safe_tuple_field_whole_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(N2 { x: (a, 1), z: 4 });
    d.x = (200, 1);
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}

#[kani::proof]
fn bug_struct_leaf_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(NS { i: In { p: a, q: 1 }, z: 4 });
    d.i.p = 255;
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn safe_struct_leaf_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(NS { i: In { p: a, q: 1 }, z: 4 });
    d.i.p = 200;
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}

// --- field stores through a helper, ptr::write and mem::replace (timing) ------
//
// Their VCs kept the drop's memory-safety obligations over symbolic pointers
// (the const-prop guard `has_scalarized_obj_size_bounds` fired on in-bounds
// cells) and the per-property solve ran into the driver watchdog. They are
// LAST in the file so they run FIRST; `timing_sentinel_runs_last` reports a
// watchdog exit.

fn seta(p: &mut DV, v: u8) {
    p.a = v;
}

#[kani::proof]
fn bug_ptr_write_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    unsafe {
        core::ptr::write(&mut d.a as *mut u8, 255);
    }
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn bug_mem_replace_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    let _ = core::mem::replace(&mut d.a, 255);
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn bug_helper_field_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    seta(&mut d, 255);
    let o: Box<dyn Tv> = d;
    assert!(o.get() < 255);
}

#[kani::proof]
fn safe_helper_field_then_coerce() {
    let a: u8 = kani::any();
    kani::assume(a < 10);
    let mut d = Box::new(DV { a, b: 1 });
    seta(&mut d, 200);
    let o: Box<dyn Tv> = d;
    assert!(o.get() == 200);
}
