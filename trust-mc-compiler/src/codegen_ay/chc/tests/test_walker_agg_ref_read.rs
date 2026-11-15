// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The F2 residual of design 2 Phase 0 (`call/inline_walk_guard.rs`;
//! tools/soundness-duals/walker_agg_ref_read_dual.rs): a reference copied out
//! of a field of a BY-VALUE argument of a walked body (`_3 = copy (_2.0)`,
//! `_4 = copy ((_2 as Some).0)`) holds the caller's address, or bits of it
//! when the caller's aggregate types the field by its referent (the low byte
//! for `Option<&u8>`, another term built from them for `Option<&bool>`, a
//! tuple or an array). The walker's transparent `Deref` read those bits as the
//! referent; the read now fails closed (`walker_deref_read_address_as_value`,
//! `statement_exec.rs::rvalue_reads_field_address`), whatever the term's
//! shape, for a closure's arguments under the capture resolver too, and for a
//! reference re-packed into an aggregate the walked body builds itself.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

/// Spelled out, so the file compiles, and fails, against an encoder that never
/// records it.
const ADDRESS_AS_VALUE: &str = "walker_deref_read_address_as_value";

const AGG_REF_PROBE: &str = r#"
    #![allow(dead_code)]

    pub struct Wr<'a> { pub r: &'a u8, pub k: u8 }

    pub trait Rd {
        fn field(&self, w: Wr<'_>) -> u8;
        fn payload(&self, o: Option<&u8>) -> u8;
        fn plain(&self, w: Wr<'_>) -> u8;
        fn payload_bool(&self, o: Option<&bool>) -> bool;
        fn payload_pair(&self, o: Option<&(u8, u8)>) -> u8;
        fn reaggregate(&self, w: Wr<'_>) -> u8;
        fn returned_agg(&self, r: &u8) -> u8;
    }
    #[inline(never)]
    fn mk<'a>(r: &'a u8) -> Wr<'a> { Wr { r, k: 1 } }
    pub struct RA;
    pub struct RB;
    impl Rd for RA {
        fn field(&self, w: Wr<'_>) -> u8 { *w.r }
        fn payload(&self, o: Option<&u8>) -> u8 { match o { Some(r) => *r, None => 0 } }
        fn plain(&self, w: Wr<'_>) -> u8 { w.k }
        fn payload_bool(&self, o: Option<&bool>) -> bool { match o { Some(b) => *b, None => true } }
        fn payload_pair(&self, o: Option<&(u8, u8)>) -> u8 { match o { Some(p) => p.1, None => 0 } }
        #[inline(never)]
        fn reaggregate(&self, w: Wr<'_>) -> u8 { let pair = (w.k, w.r); *pair.1 }
        fn returned_agg(&self, r: &u8) -> u8 { let w = mk(r); *w.r }
    }
    impl Rd for RB {
        fn field(&self, w: Wr<'_>) -> u8 { *w.r }
        fn payload(&self, o: Option<&u8>) -> u8 { match o { Some(r) => *r, None => 0 } }
        fn plain(&self, w: Wr<'_>) -> u8 { w.k }
        fn payload_bool(&self, o: Option<&bool>) -> bool { match o { Some(b) => *b, None => true } }
        fn payload_pair(&self, o: Option<&(u8, u8)>) -> u8 { match o { Some(p) => p.1, None => 0 } }
        #[inline(never)]
        fn reaggregate(&self, w: Wr<'_>) -> u8 { let pair = (w.k, w.r); *pair.1 + 0 }
        fn returned_agg(&self, r: &u8) -> u8 { let w = mk(r); *w.r + 0 }
    }
    fn pick(c: u8) -> Box<dyn Rd> {
        if c > 3 { Box::new(RA) } else { Box::new(RB) }
    }

    pub fn probe_agg_field_ref_read(c: u8) -> u8 {
        let x: u8 = 7;
        pick(c).field(Wr { r: &x, k: 1 })
    }

    pub fn probe_agg_payload_ref_read(c: u8) -> u8 {
        let x: u8 = 7;
        pick(c).payload(Some(&x))
    }

    pub fn probe_agg_plain_field_read(c: u8) -> u8 {
        let x: u8 = 7;
        pick(c).plain(Wr { r: &x, k: 1 })
    }

    pub fn probe_agg_payload_bool_read(c: u8) -> bool {
        let b = false;
        pick(c).payload_bool(Some(&b))
    }

    pub fn probe_agg_payload_pair_read(c: u8) -> u8 {
        let v = (1u8, 7u8);
        pick(c).payload_pair(Some(&v))
    }

    pub fn probe_agg_reaggregate_read(c: u8) -> u8 {
        let x: u8 = 7;
        pick(c).reaggregate(Wr { r: &x, k: 1 })
    }

    pub fn probe_agg_returned_by_nested_call_read(c: u8) -> u8 {
        let x: u8 = 7;
        pick(c).returned_agg(&x)
    }

    pub fn probe_closure_arg_tuple_read(c: bool) -> u8 {
        let c1 = |t: (u8, &u8)| *t.1;
        let c2 = |t: (u8, &u8)| *t.1 + 0;
        let f: &dyn Fn((u8, &u8)) -> u8 = if c { &c1 } else { &c2 };
        let x = 7u8;
        f((1, &x))
    }
"#;

fn encode_probe(fn_name: &str) -> BTreeMap<String, usize> {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let ran = AtomicBool::new(false);
    with_test_ay_ctx_for_source(AGG_REF_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let config =
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };
        let _vc = mir_to_chc(ctx.tcx, &body, fn_name, config);
        ran.store(true, Ordering::SeqCst);
    });
    assert!(ran.load(Ordering::SeqCst), "the probe crate compiled and {fn_name} was encoded");
    crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(fn_name)
        .unwrap_or_default()
}

/// `*w.r` for a `Wr { r: &x, .. }` built by the caller: the copied reference
/// holds x's address, and its read fails closed.
#[test]
fn test_agg_field_ref_read_fails_closed() {
    let fn_name = "probe_agg_field_ref_read";
    let sites = encode_probe(fn_name);
    assert!(
        sites.get(ADDRESS_AS_VALUE).copied().unwrap_or(0) >= 1,
        "{fn_name}: the read through a reference copied out of a by-value argument must fail \
         closed, got sites {sites:?}"
    );
}

/// `match o { Some(r) => *r, .. }` for the caller's `Some(&x)`: the payload
/// slot is typed by the referent, so it holds the address's low byte, and its
/// read fails closed too.
#[test]
fn test_agg_payload_ref_read_fails_closed() {
    let fn_name = "probe_agg_payload_ref_read";
    let sites = encode_probe(fn_name);
    assert!(
        sites.get(ADDRESS_AS_VALUE).copied().unwrap_or(0) >= 1,
        "{fn_name}: the read through an Option<&u8> payload of a by-value argument must fail \
         closed, got sites {sites:?}"
    );
}

/// Reading a non-reference field of the same argument (`w.k`) is exact.
#[test]
fn test_agg_plain_field_read_records_nothing() {
    let fn_name = "probe_agg_plain_field_read";
    let sites = encode_probe(fn_name);
    assert!(
        !sites.contains_key(ADDRESS_AS_VALUE),
        "{fn_name}: a u8 field is no address, got sites {sites:?}"
    );
}

/// `match o { Some(b) => *b, .. }` for the caller's `Some(&b)`, `b: bool`, and
/// `Some(p) => p.1` for an `Option<&(u8, u8)>`: the payload term is built from
/// the address's bits but is neither an address nor an extract of one, so no
/// term shape tells it from the referent. The read fails closed.
#[test]
fn test_agg_payload_non_bitvector_referent_read_fails_closed() {
    let mut open = Vec::new();
    for fn_name in ["probe_agg_payload_bool_read", "probe_agg_payload_pair_read"] {
        let sites = encode_probe(fn_name);
        if sites.get(ADDRESS_AS_VALUE).copied().unwrap_or(0) == 0 {
            open.push((fn_name, sites));
        }
    }
    assert!(open.is_empty(), "each read must fail closed: {open:?}");
}

/// `let pair = (w.k, w.r); *pair.1`: the reference re-packed into an aggregate
/// the walked body builds keeps its address-ness (the aggregate is
/// address-carrying), and its read fails closed.
#[test]
fn test_agg_reaggregated_ref_read_fails_closed() {
    let fn_name = "probe_agg_reaggregate_read";
    let sites = encode_probe(fn_name);
    assert!(
        sites.get(ADDRESS_AS_VALUE).copied().unwrap_or(0) >= 1,
        "{fn_name}: a reference re-packed into a local tuple must stay address-bound, got sites \
         {sites:?}"
    );
}

/// `let w = mk(r); *w.r` where the walked `mk` packs its address-bound
/// parameter into the aggregate it returns: the call's destination is
/// address-carrying, and the read of the reference copied out of it fails
/// closed.
#[test]
fn test_agg_returned_by_nested_call_ref_read_fails_closed() {
    let fn_name = "probe_agg_returned_by_nested_call_read";
    let sites = encode_probe(fn_name);
    assert!(
        sites.get(ADDRESS_AS_VALUE).copied().unwrap_or(0) >= 1,
        "{fn_name}: a reference in an aggregate a nested walk returned must fail closed, got \
         sites {sites:?}"
    );
}

/// A closure behind `&dyn Fn((u8, &u8))`, walked under the capture resolver:
/// its argument `t` (local 2) is a by-value aggregate the caller built, so
/// `*t.1` fails closed like a method's argument does.
#[test]
fn test_closure_arg_ref_read_fails_closed() {
    let fn_name = "probe_closure_arg_tuple_read";
    let sites = encode_probe(fn_name);
    assert!(
        sites.get(ADDRESS_AS_VALUE).copied().unwrap_or(0) >= 1,
        "{fn_name}: a reference in a closure's by-value argument must fail closed, got sites \
         {sites:?}"
    );
}
