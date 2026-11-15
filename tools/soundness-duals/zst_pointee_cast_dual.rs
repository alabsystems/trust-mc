// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle: MUST FAIL (the two `bug_` harnesses); the three `safe_` harnesses MUST VERIFY.
//
// THE HARNESS NAMES CARRY `_deref` ON PURPOSE. That is the trigger, not decoration.
// `resolve_ref_chain_allocation` tested `pointee_base.contains("_deref")` against the
// FULLY QUALIFIED name `fn::local_N`, and the allocation's owning function is the
// HARNESS -- so `check_zst_deref::local_2` read as a `_deref` alias, skipped the early
// return, resolved to None, and the caller's `continue` dropped the object-extent
// obligation. A first version of this file named its harnesses `bug_zst_alloc_read_as_
// sized` etc. and passed IDENTICALLY on the unfixed and fixed bundles: it reproduced the
// UB shape and omitted the trigger, so it was coverage in appearance only.
//
// `align_of::<Foo>() == 1` and `align_of::<[u8; 16]>() == 1`, so NO alignment obligation
// can fire for either bug harness -- extent is the only obligation that can be false,
// which is what makes this family distinct from the alignment duals.
//
// LIMITATION, stated rather than hidden: the `safe_` rows are green on the unfixed
// bundle too, because there the obligation is simply absent. At verdict granularity a
// DISCHARGED obligation and a MISSING one are indistinguishable; only the obligation
// listing separates them. The `bug_` rows are the discriminators.

#![allow(invalid_reference_casting, unused_variables)]

#[derive(kani::Arbitrary)]
struct Zero;

#[derive(kani::Arbitrary)]
struct Foo {
    a: u8,
}

#[derive(kani::Arbitrary)]
struct Wide {
    a: u64,
    b: u64,
    c: u64,
}

// ---- MUST FAIL: 1 byte read out of a 0-byte allocation. Reference deliberately unused:
// creating it is already UB, and a checker that only catches the later load is unsound on
// exactly the shape the corpus uses.
pub fn zst_deref(var_zst: &Zero) {
    let p0: *const Zero = var_zst;
    let p1: *const Foo = p0 as *const Foo;
    let r: &Foo = unsafe { &*p1 };
}

#[kani::proof]
pub fn bug_zst_alloc_read_as_sized_deref() {
    let z: Zero = kani::any();
    zst_deref(&z);
}

// ---- MUST FAIL: alignment-COMPATIBLE size increase (align 1 -> align 1), so alignment
// cannot substitute for extent the way it does for the i64 -> i128 casts.
pub fn align_compatible_deref(var: &Foo) {
    let p0: *const Foo = var;
    let p1: *const [u8; 16] = p0 as *const [u8; 16];
    let r: &[u8; 16] = unsafe { &*p1 };
}

#[kani::proof]
pub fn bug_align_compatible_size_increase_deref() {
    let f: Foo = kani::any();
    align_compatible_deref(&f);
}

// ---- MUST VERIFY: equal-size cast; the obligation must be PRESENT and DISCHARGED ----
pub fn equal_size_deref(var: &Foo) {
    let p0: *const Foo = var;
    let r: &Foo = unsafe { &*p0 };
}

#[kani::proof]
pub fn safe_equal_size_cast_deref() {
    let f: Foo = kani::any();
    equal_size_deref(&f);
}

// ---- MUST VERIFY: shrinking cast out of a larger allocation ----
pub fn shrinking_deref(var: &Wide) {
    let p0: *const Wide = var;
    let p1: *const Foo = p0 as *const Foo;
    let r: &Foo = unsafe { &*p1 };
}

#[kani::proof]
pub fn safe_shrinking_cast_deref() {
    let w: Wide = kani::any();
    shrinking_deref(&w);
}

// ---- MUST VERIFY: a ZST read AS a ZST (0 bytes out of 0 bytes) ----
pub fn zst_as_zst_deref(var_zst: &Zero) {
    let p0: *const Zero = var_zst;
    let r: &Zero = unsafe { &*p0 };
}

#[kani::proof]
pub fn safe_zst_read_as_zst_deref() {
    let z: Zero = kani::any();
    zst_as_zst_deref(&z);
}
