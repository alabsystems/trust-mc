// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- the F2 residual of design 2 Phase 0
//! (docs/chc-hole-fix-designs-2026-09-24.md; the tracker row is
//! walker_referent_write_dual.rs::bug_agg_ref_read): a reference held in a
//! BY-VALUE aggregate argument of a walked body, copied out of a field
//! (`_5 = deref_copy (_2.0)`) and read through (`(*_5)`), was read as its
//! address. The caller built the aggregate, and its reference field holds the
//! referent's address; F2 tagged reference PARAMETERS whose term has a
//! pointer's shape, but a reference copied out of a field of one was untagged,
//! so the walker's transparent `Deref` returned the address bits as the value.
//! Fixed by tagging such a copy address-bound (statement_exec.rs,
//! rvalue_reads_field_address): its read fails closed
//! (walker_deref_read_address_as_value). The rows reach the shape through a
//! struct field, a tuple field, a variant payload and a nested struct, all
//! through the dyn door with two candidates.
//!
//! The review of that fix found three residuals, present on main too, and
//! the second section's rows pin them:
//! - the tag first required the copied term to be an address or an extract of
//!   one, but a BV-flattened `Option<&T>` payload whose `T` is no bitvector
//!   (`bool`, a tuple, an array, an `Option`) is another term built from the
//!   address bits: the reference is now address-bound whatever its term;
//! - the rule applied only under the field-map resolver, so a closure's
//!   by-value aggregate ARGUMENT walked under the capture resolver was read
//!   as its address: now only the closure's environment is excluded;
//! - the tag did not follow a reference re-packed into an aggregate the walked
//!   body builds (`let pair = (w.k, w.r); *pair.1`), nor an aggregate a nested
//!   walk returned: such a local is now address-carrying, and a reference
//!   copied out of it is address-bound.
//!   `bug_closure_option_arg_read` also needed a fix of the Fn-trait argument
//!   unpacker (fn_trait_dispatch.rs): the one-element argument tuple arrives
//!   unwrapped, and peeling the `Some` off it handed the closure the payload
//!   bits as its `Option`, whose discriminant folded to `None`.
//!
//! The safe_ rows are the precision the fail-closed read costs: they were
//! wrong on main too (the bug rows prove the read was the address), and are
//! known-red false failures.
//!
//! Oracle: the corpus-rev Kani 4c0fce8c3 (Kani 0.67.0) FAILS every bug_ row on
//! the check it names and verifies every safe_ row (manifest entry).
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_agg_ref_read_dual.rs

#[inline(never)]
fn sink<T>(_v: T) {}

pub struct Wr<'a> {
    pub r: &'a u8,
    pub k: u8,
}

pub struct Outer<'a> {
    pub k: u8,
    pub w: Wr<'a>,
}

pub trait Rd {
    fn field(&self, w: Wr<'_>) -> u8;
    fn tuple(&self, t: (u8, &u8)) -> u8;
    fn payload(&self, o: Option<&u8>) -> u8;
    fn nested(&self, o: Outer<'_>) -> u8;
}

pub struct RA;
pub struct RB;

impl Rd for RA {
    fn field(&self, w: Wr<'_>) -> u8 {
        *w.r
    }
    fn tuple(&self, t: (u8, &u8)) -> u8 {
        *t.1
    }
    fn payload(&self, o: Option<&u8>) -> u8 {
        match o {
            Some(r) => *r,
            None => 0,
        }
    }
    fn nested(&self, o: Outer<'_>) -> u8 {
        *o.w.r
    }
}

impl Rd for RB {
    fn field(&self, w: Wr<'_>) -> u8 {
        *w.r
    }
    fn tuple(&self, t: (u8, &u8)) -> u8 {
        *t.1
    }
    fn payload(&self, o: Option<&u8>) -> u8 {
        match o {
            Some(r) => *r,
            None => 0,
        }
    }
    fn nested(&self, o: Outer<'_>) -> u8 {
        *o.w.r
    }
}

fn pick() -> Box<dyn Rd> {
    if kani::any() { Box::new(RA) } else { Box::new(RB) }
}

#[kani::proof]
fn bug_field_ref_read() {
    let x: u8 = 7;
    assert!(pick().field(Wr { r: &x, k: 1 }) == 8);
}

#[kani::proof]
fn safe_field_ref_read() {
    let x: u8 = 7;
    assert!(pick().field(Wr { r: &x, k: 1 }) == 7);
}

#[kani::proof]
fn bug_tuple_ref_read() {
    let x: u8 = 7;
    assert!(pick().tuple((1, &x)) == 8);
}

#[kani::proof]
fn safe_tuple_ref_read() {
    let x: u8 = 7;
    assert!(pick().tuple((1, &x)) == 7);
}

#[kani::proof]
fn bug_payload_ref_read() {
    let x: u8 = 7;
    assert!(pick().payload(Some(&x)) == 8);
}

#[kani::proof]
fn safe_payload_ref_read() {
    let x: u8 = 7;
    assert!(pick().payload(Some(&x)) == 7);
}

#[kani::proof]
fn bug_nested_ref_read() {
    let x: u8 = 7;
    assert!(pick().nested(Outer { k: 2, w: Wr { r: &x, k: 1 } }) == 8);
}

#[kani::proof]
fn safe_nested_ref_read() {
    let x: u8 = 7;
    assert!(pick().nested(Outer { k: 2, w: Wr { r: &x, k: 1 } }) == 7);
}

// The tracker's overflow shape with a value the assertion can see.
#[kani::proof]
fn bug_field_ref_overflow() {
    let x: u8 = 255;
    sink(pick().field(Wr { r: &x, k: 0 }).checked_add(1).unwrap());
}

// ---- residuals of the review of item 3 ----------------------------------------

pub trait Rd2 {
    fn payload_bool(&self, o: Option<&bool>) -> bool;
    fn payload_pair(&self, o: Option<&(u8, u8)>) -> u8;
    fn payload_array(&self, o: Option<&[u8; 2]>) -> u8;
    fn payload_option(&self, o: Option<&Option<u8>>) -> u8;
    fn reaggregate(&self, w: Wr<'_>) -> u8;
    fn swap_pair(&self, t: (&u8, &u8)) -> u8;
    fn returned_agg(&self, r: &u8) -> u8;
    fn nested_bool(&self, o: Option<&bool>) -> bool;
}

#[inline(never)]
fn mk_wr(r: &u8) -> Wr<'_> {
    Wr { r, k: 1 }
}

#[inline(never)]
fn inner_bool(o: Option<&bool>) -> bool {
    match o {
        Some(b) => *b,
        None => true,
    }
}

impl Rd2 for RA {
    fn payload_bool(&self, o: Option<&bool>) -> bool {
        match o {
            Some(b) => *b,
            None => true,
        }
    }
    fn payload_pair(&self, o: Option<&(u8, u8)>) -> u8 {
        match o {
            Some(p) => p.1,
            None => 0,
        }
    }
    fn payload_array(&self, o: Option<&[u8; 2]>) -> u8 {
        match o {
            Some(a) => a[1],
            None => 0,
        }
    }
    fn payload_option(&self, o: Option<&Option<u8>>) -> u8 {
        match o {
            Some(Some(v)) => *v,
            _ => 0,
        }
    }
    fn reaggregate(&self, w: Wr<'_>) -> u8 {
        let pair = (w.k, w.r);
        *pair.1
    }
    fn swap_pair(&self, t: (&u8, &u8)) -> u8 {
        let (a, b) = t;
        let s = (b, a);
        *s.0
    }
    fn returned_agg(&self, r: &u8) -> u8 {
        let w = mk_wr(r);
        *w.r
    }
    fn nested_bool(&self, o: Option<&bool>) -> bool {
        inner_bool(o)
    }
}

impl Rd2 for RB {
    fn payload_bool(&self, o: Option<&bool>) -> bool {
        match o {
            Some(b) => *b,
            None => true,
        }
    }
    fn payload_pair(&self, o: Option<&(u8, u8)>) -> u8 {
        match o {
            Some(p) => p.1,
            None => 0,
        }
    }
    fn payload_array(&self, o: Option<&[u8; 2]>) -> u8 {
        match o {
            Some(a) => a[1],
            None => 0,
        }
    }
    fn payload_option(&self, o: Option<&Option<u8>>) -> u8 {
        match o {
            Some(Some(v)) => *v,
            _ => 0,
        }
    }
    fn reaggregate(&self, w: Wr<'_>) -> u8 {
        let pair = (w.k, w.r);
        *pair.1 + 0
    }
    fn swap_pair(&self, t: (&u8, &u8)) -> u8 {
        let (a, b) = t;
        let s = (b, a);
        *s.0 + 0
    }
    fn returned_agg(&self, r: &u8) -> u8 {
        let w = mk_wr(r);
        *w.r + 0
    }
    fn nested_bool(&self, o: Option<&bool>) -> bool {
        inner_bool(o)
    }
}

fn pick2() -> Box<dyn Rd2> {
    if kani::any() { Box::new(RA) } else { Box::new(RB) }
}

#[kani::proof]
fn bug_payload_bool_read() {
    let b = false;
    assert!(pick2().payload_bool(Some(&b)));
}

#[kani::proof]
fn safe_payload_bool_read() {
    let b = false;
    assert!(!pick2().payload_bool(Some(&b)));
}

#[kani::proof]
fn bug_payload_bool_symbolic_read() {
    let b: bool = kani::any();
    assert!(pick2().payload_bool(Some(&b)));
}

#[kani::proof]
fn bug_payload_pair_read() {
    let v = (1u8, 7u8);
    assert!(pick2().payload_pair(Some(&v)) != 7);
}

#[kani::proof]
fn bug_payload_array_read() {
    let v = [1u8, 7u8];
    assert!(pick2().payload_array(Some(&v)) != 7);
}

#[kani::proof]
fn bug_payload_option_read() {
    let v = Some(7u8);
    assert!(pick2().payload_option(Some(&v)) != 7);
}

#[kani::proof]
fn bug_reaggregate_read() {
    let x = 7u8;
    assert!(pick2().reaggregate(Wr { r: &x, k: 1 }) != 7);
}

#[kani::proof]
fn safe_reaggregate_read() {
    let x = 7u8;
    assert!(pick2().reaggregate(Wr { r: &x, k: 1 }) == 7);
}

#[kani::proof]
fn bug_swap_pair_read() {
    let x = 7u8;
    let y = 3u8;
    assert!(pick2().swap_pair((&y, &x)) != 7);
}

#[kani::proof]
fn bug_returned_agg_read() {
    let x = 7u8;
    assert!(pick2().returned_agg(&x) != 7);
}

#[kani::proof]
fn safe_returned_agg_read() {
    let x = 7u8;
    assert!(pick2().returned_agg(&x) == 7);
}

#[kani::proof]
fn bug_nested_bool_read() {
    let b = false;
    assert!(pick2().nested_bool(Some(&b)));
}

// A closure's by-value aggregate argument, walked under the capture resolver.

#[kani::proof]
fn bug_closure_tuple_arg_read() {
    let c1 = |t: (u8, &u8)| *t.1;
    let c2 = |t: (u8, &u8)| *t.1 + 0;
    let f: &dyn Fn((u8, &u8)) -> u8 = if kani::any() { &c1 } else { &c2 };
    let x = 7u8;
    assert!(f((1, &x)) != 7);
}

#[kani::proof]
fn safe_closure_tuple_arg_read() {
    let c1 = |t: (u8, &u8)| *t.1;
    let c2 = |t: (u8, &u8)| *t.1 + 0;
    let f: &dyn Fn((u8, &u8)) -> u8 = if kani::any() { &c1 } else { &c2 };
    let x = 7u8;
    assert!(f((1, &x)) == 7);
}

#[kani::proof]
fn bug_closure_struct_arg_read() {
    let c1 = |w: Wr| *w.r;
    let c2 = |w: Wr| *w.r + 0;
    let f: &dyn Fn(Wr) -> u8 = if kani::any() { &c1 } else { &c2 };
    let x = 7u8;
    assert!(f(Wr { r: &x, k: 1 }) != 7);
}

#[kani::proof]
fn bug_closure_option_arg_read() {
    let c1 = |o: Option<&u8>| match o {
        Some(r) => *r,
        None => 0,
    };
    let c2 = |o: Option<&u8>| match o {
        Some(r) => *r + 0,
        None => 1,
    };
    let f: &dyn Fn(Option<&u8>) -> u8 = if kani::any() { &c1 } else { &c2 };
    let x = 7u8;
    assert!(f(Some(&x)) != 7);
}

#[kani::proof]
fn bug_closure_array_arg_read() {
    let c1 = |a: [&u8; 2]| *a[1];
    let c2 = |a: [&u8; 2]| *a[1] + 0;
    let f: &dyn Fn([&u8; 2]) -> u8 = if kani::any() { &c1 } else { &c2 };
    let x = 7u8;
    let y = 3u8;
    assert!(f([&y, &x]) != 7);
}

#[kani::proof]
fn bug_boxed_fnonce_tuple_arg_read() {
    let x = 7u8;
    let c: Box<dyn FnOnce((u8, &u8)) -> u8> =
        if kani::any() { Box::new(|t: (u8, &u8)| *t.1) } else { Box::new(|t: (u8, &u8)| *t.1 + 0) };
    assert!(c((1, &x)) != 7);
}

// The Fn-trait argument unpacker: a one-element argument tuple whose element
// is a one-field constructor.

#[kani::proof]
fn bug_closure_option_value_arg() {
    let c1 = |o: Option<u8>| match o {
        Some(v) => v,
        None => 0,
    };
    let c2 = |o: Option<u8>| match o {
        Some(v) => v + 0,
        None => 1,
    };
    let f: &dyn Fn(Option<u8>) -> u8 = if kani::any() { &c1 } else { &c2 };
    assert!(f(Some(7)) != 7);
}

#[kani::proof]
fn safe_closure_option_value_arg() {
    let c1 = |o: Option<u8>| match o {
        Some(v) => v,
        None => 0,
    };
    let c2 = |o: Option<u8>| match o {
        Some(v) => v + 0,
        None => 1,
    };
    let f: &dyn Fn(Option<u8>) -> u8 = if kani::any() { &c1 } else { &c2 };
    assert!(f(Some(7)) == 7);
}

fn opt_first(o: Option<u8>) -> u8 {
    match o {
        Some(v) => v,
        None => 0,
    }
}

fn opt_second(o: Option<u8>) -> u8 {
    match o {
        Some(v) => v + 0,
        None => 1,
    }
}

#[kani::proof]
fn bug_fn_item_option_value_arg() {
    let f: &dyn Fn(Option<u8>) -> u8 = if kani::any() { &opt_first } else { &opt_second };
    assert!(f(Some(7)) != 7);
}
