// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Phase 0 of the dyn-walker write/read design
//! (`docs/chc-hole-fix-designs-2026-09-24.md`, section 2;
//! `call/inline_walk_guard.rs`): a walked body that reads a place after
//! writing through a deref, reads an address as a value, or loses a write
//! records a reason that is NOT blessed, so its proof is demoted and its
//! counterexample never certified.
//!
//! Each probe is a shape from the tracker duals
//! (`tools/soundness-duals/walker_dyn_deref_write_dual.rs`,
//! `walker_dyn_heap_write_dual.rs`, `walker_referent_read_dual.rs`,
//! `walker_drop_redo_false_cert_dual.rs`, `walker_phase0_front_doors_dual.rs`),
//! where the driver measured the verdicts. The precision probes pin what must
//! stay clean.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

/// Spelled out rather than imported, so this file compiles, and fails, against
/// an encoder that never records them.
const READ_AFTER_WRITE: &str = "walker_deref_read_after_write";
const ADDRESS_AS_VALUE: &str = "walker_deref_read_address_as_value";
const SELF_MAP_STALE: &str = "walker_self_field_map_stale";
const STORE_IN_ARM: &str = "walker_store_in_branch_arm";
const ALIAS_SORT_MISMATCH: &str = "dyn_dispatch_alias_update_sort_mismatch";
const WRITEBACK_MEMORY_ONLY: &str = "walker_deref_writeback_memory_only";
const REGION_STALE: &str = "heap_region_stale_after_subsort_store";

const PHASE0_PROBE: &str = r#"
    #![allow(dead_code)]

    #[inline(never)]
    fn sink<T>(_value: T) {}

    static mut G: u8 = 0;

    // --- dyn: write through `*a`, then read it --------------------------------
    pub trait W {
        fn add_after_write(&self, a: &mut u8) -> u8;
        fn add_no_write(&self, a: &mut u8) -> u8;
        fn field(&mut self) -> u8;
    }
    pub struct A { x: u8 }
    pub struct B { x: u8 }
    impl W for A {
        fn add_after_write(&self, a: &mut u8) -> u8 { *a = 255; unsafe { (*a).unchecked_add(1) } }
        fn add_no_write(&self, a: &mut u8) -> u8 { unsafe { (*a).unchecked_add(1) } }
        fn field(&mut self) -> u8 { self.x = 200; self.x }
    }
    impl W for B {
        fn add_after_write(&self, a: &mut u8) -> u8 { *a = 255; unsafe { (*a).unchecked_add(1) } }
        fn add_no_write(&self, a: &mut u8) -> u8 { unsafe { (*a).unchecked_add(1) } }
        fn field(&mut self) -> u8 { self.x = 200; self.x }
    }
    fn pick(x: u8) -> Box<dyn W> {
        if x > 3 { Box::new(A { x }) } else { Box::new(B { x }) }
    }

    // `a`'s address escapes, so it lives in memory and the dyn door binds the
    // `&mut a` argument to its ADDRESS.
    pub fn probe_dyn_write_then_read(c: u8) -> u8 {
        let mut a: u8 = 0;
        sink(&mut a as *mut u8);
        pick(7).add_after_write(&mut a)
    }

    pub fn probe_dyn_read_param_no_write(c: u8) -> u8 {
        let mut a: u8 = 255;
        sink(&mut a as *mut u8);
        pick(7).add_no_write(&mut a)
    }

    pub fn probe_dyn_self_write_then_read(c: u8) -> u8 {
        let mut d = pick(c);
        d.field()
    }

    // --- dyn: one candidate stores a static -----------------------------------
    pub trait T {
        fn f(&self) -> u8;
    }
    pub struct SA;
    pub struct SB;
    impl T for SA {
        fn f(&self) -> u8 { unsafe { G = 200; } 0 }
    }
    impl T for SB {
        fn f(&self) -> u8 { 0 }
    }
    pub fn probe_dyn_candidate_stores_static(c: bool) -> u8 {
        let o: Box<dyn T> = if c { Box::new(SA) } else { Box::new(SB) };
        o.f()
    }

    // --- dyn + nested helper: the first parameter reassigned on one arm --------
    pub struct Span { pub lo: u8, pub hi: u8 }
    #[inline(never)]
    fn maybe_moved<'x>(mut cur: &'x Span, next: Option<&'x Span>, len: u8) -> u8 {
        if let Some(n) = next { cur = n; }
        if PartialOrd::lt(&cur.lo, &cur.hi) { len } else { unsafe { len.unchecked_sub(1) } }
    }
    pub trait MaybeCursor {
        fn maybe(&self, a: &Span, b: Option<&Span>, len: u8) -> u8;
    }
    pub struct MA;
    pub struct MB;
    impl MaybeCursor for MA {
        fn maybe(&self, a: &Span, b: Option<&Span>, len: u8) -> u8 { maybe_moved(a, b, len) }
    }
    impl MaybeCursor for MB {
        fn maybe(&self, a: &Span, b: Option<&Span>, len: u8) -> u8 { maybe_moved(a, b, len) }
    }
    pub fn probe_nested_first_param_reassigned(c: bool, l: u8, h: u8) -> u8 {
        let head = Span { lo: l, hi: h };
        let tail = Span { lo: h, hi: l };
        let o: Box<dyn MaybeCursor> = if c { Box::new(MA) } else { Box::new(MB) };
        o.maybe(&head, Some(&tail), 0)
    }

    // --- dyn: `&mut self` writer with two candidates of different types -------
    pub trait Tr {
        fn bump(&mut self, k: u8);
    }
    pub struct DA { a: u8, b: u8 }
    pub struct DB { a: u8, b: u8, c: u8 }
    impl Tr for DA {
        fn bump(&mut self, k: u8) { self.a = self.a.wrapping_add(k); }
    }
    impl Tr for DB {
        fn bump(&mut self, k: u8) { self.a = self.a.wrapping_add(k); }
    }
    pub fn probe_dyn_multi_bump(c: bool, a: u8) -> u8 {
        let mut o: Box<dyn Tr> = if c { Box::new(DA { a, b: 1 }) } else { Box::new(DB { a, b: 1, c: 2 }) };
        o.bump(250);
        core::mem::forget(o);
        0
    }

    // --- dyn: a write through `*a` that reaches memory only ------------------
    pub trait Wr {
        fn wr(&self, a: &mut u8);
    }
    pub struct RA;
    pub struct RB;
    impl Wr for RA {
        fn wr(&self, a: &mut u8) { *a = 200; }
    }
    impl Wr for RB {
        fn wr(&self, a: &mut u8) { *a = 200; }
    }
    pub fn probe_dyn_write_reaches_caller(c: bool) -> u8 {
        let mut a: u8 = 7;
        sink(&mut a as *mut u8);
        let o: Box<dyn Wr> = if c { Box::new(RA) } else { Box::new(RB) };
        o.wr(&mut a);
        a
    }

    // --- a field store, then a whole-object read of the Box payload ----------
    // (walker_drop_redo_false_cert_dual.rs: the dyn call is devirtualized and
    // `redo` runs on the statement path).
    pub trait Swap2 {
        fn redo(&mut self);
    }
    pub struct S2 { a: u8, b: u8, c: u8 }
    impl Drop for S2 {
        fn drop(&mut self) {
            sink(unsafe { self.a.unchecked_add(self.b) });
        }
    }
    impl Swap2 for S2 {
        fn redo(&mut self) {
            self.a = self.a.wrapping_add(self.c);
            let old = core::mem::replace(self, S2 { a: 0, b: 0, c: 0 });
            drop(old);
        }
    }
    pub fn probe_field_store_then_replace() {
        let mut o: Box<dyn Swap2> = Box::new(S2 { a: 254, b: 1, c: 1 });
        o.redo();
    }

    // --- a flattened receiver's hint map, written through then read -----------
    #[inline(never)]
    fn wr_then_read(p: &mut (u8, u8)) -> u8 {
        p.0 = 200;
        p.0
    }
    pub fn probe_fninline_hint_map_write_then_read() -> u8 {
        let mut p = (1u8, 2u8);
        wr_then_read(&mut p)
    }

    // --- precision: a value-bound `&mut u8` written then read in fn_inline ----
    #[inline(never)]
    fn wr_then_read_u8(x: &mut u8) -> u8 {
        *x = 200;
        *x
    }
    pub fn probe_fninline_value_write_then_read() -> u8 {
        let mut a = 1u8;
        wr_then_read_u8(&mut a)
    }

    // --- precision: a dyn method that only reads `self` -----------------------
    pub trait Get {
        fn get(&self) -> u8;
    }
    pub struct GA { a: u8 }
    pub struct GB { a: u8 }
    impl Get for GA {
        fn get(&self) -> u8 { self.a }
    }
    impl Get for GB {
        fn get(&self) -> u8 { self.a }
    }
    pub fn probe_dyn_self_read_only(c: bool, a: u8) -> u8 {
        let o: Box<dyn Get> = if c { Box::new(GA { a }) } else { Box::new(GB { a }) };
        o.get()
    }
"#;

/// Encode `fn_name` from the probe crate and return its translation-drop site
/// reasons.
fn encode_probe(fn_name: &str) -> BTreeMap<String, usize> {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let ran = AtomicBool::new(false);
    with_test_ay_ctx_for_source(PHASE0_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        // The driver's track level: memory-backed places are modelled.
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

fn assert_records(fn_name: &str, sites: &BTreeMap<String, usize>, reason: &str) {
    assert!(
        sites.get(reason).copied().unwrap_or(0) >= 1,
        "{fn_name}: must record {reason}, got sites {sites:?}"
    );
}

/// Every Phase 0 reason fails closed: none is on the blessed list.
#[test]
fn test_phase0_reasons_are_not_blessed() {
    for reason in [
        READ_AFTER_WRITE,
        ADDRESS_AS_VALUE,
        SELF_MAP_STALE,
        STORE_IN_ARM,
        ALIAS_SORT_MISMATCH,
        WRITEBACK_MEMORY_ONLY,
        REGION_STALE,
        "walker_self_field_unloaded",
        "walker_deref_write_dropped",
        "walker_set_discriminant_dropped",
        "walker_deref_write_rebind_lost",
        "walker_nested_alias_writeback_dropped",
        "walker_bailed_arm_may_write",
        "walker_fn_ptr_closure_alias_dropped",
    ] {
        assert_eq!(fallback_soundness(reason), FallbackSoundness::FailClose, "{reason}");
    }
}

/// `*a = 255; (*a).unchecked_add(1)` through a two-candidate dyn call: the read
/// after the memory-only write fails closed (F1), and the write, which reaches
/// memory only, too (F3).
#[test]
fn test_dyn_read_after_deref_write_fails_closed() {
    let fn_name = "probe_dyn_write_then_read";
    let sites = encode_probe(fn_name);
    assert_records(fn_name, &sites, READ_AFTER_WRITE);
    assert_records(fn_name, &sites, WRITEBACK_MEMORY_ONLY);
}

/// `*a` for an address-bound `&mut u8` parameter of the dyn door, with no write
/// at all: the transparent read of the address fails closed (F2).
#[test]
fn test_dyn_address_bound_param_read_fails_closed() {
    let fn_name = "probe_dyn_read_param_no_write";
    let sites = encode_probe(fn_name);
    assert_records(fn_name, &sites, ADDRESS_AS_VALUE);
    assert!(!sites.contains_key(READ_AFTER_WRITE), "{fn_name}: no write happened, got {sites:?}");
}

/// `self.x = 200; self.x`: the second read would be the entry snapshot.
#[test]
fn test_dyn_self_field_read_after_write_fails_closed() {
    let fn_name = "probe_dyn_self_write_then_read";
    let sites = encode_probe(fn_name);
    assert!(
        sites.get(READ_AFTER_WRITE).copied().unwrap_or(0)
            + sites.get(SELF_MAP_STALE).copied().unwrap_or(0)
            >= 1,
        "{fn_name}: the read after `self.x = 200` must fail closed, got {sites:?}"
    );
}

/// One of two candidates stores a static: the host applies the store on both
/// dispatch paths.
#[test]
fn test_dyn_candidate_store_fails_closed() {
    let fn_name = "probe_dyn_candidate_stores_static";
    let sites = encode_probe(fn_name);
    assert_records(fn_name, &sites, STORE_IN_ARM);
}

/// `cur = n` (a plain reassignment, no write through a deref) then a read of
/// `cur.lo`: the self-field snapshot of the old `cur` must not answer it.
#[test]
fn test_reassigned_first_param_snapshot_fails_closed() {
    let fn_name = "probe_nested_first_param_reassigned";
    let sites = encode_probe(fn_name);
    assert_records(fn_name, &sites, SELF_MAP_STALE);
}

/// Two candidates write `self` back with different sorts: the alias key is
/// havocked and recorded instead of dropped (F5).
#[test]
fn test_dispatch_alias_sort_mismatch_fails_closed() {
    let fn_name = "probe_dyn_multi_bump";
    let sites = encode_probe(fn_name);
    assert_records(fn_name, &sites, ALIAS_SORT_MISMATCH);
}

/// `*a = 200` through a dyn call reaches memory only; the caller's `a` gets no
/// alias update (F3).
#[test]
fn test_dyn_memory_only_write_back_fails_closed() {
    let fn_name = "probe_dyn_write_reaches_caller";
    let sites = encode_probe(fn_name);
    assert_records(fn_name, &sites, WRITEBACK_MEMORY_ONLY);
}

/// The drop-redo shape: `self.a = ..` then `mem::replace(self, ..)` reads the
/// whole object. In the driver the dyn call is devirtualized and the read is
/// a region select that misses the field store (F4, measured on the dual);
/// here `redo` is walked, and its reads after the write fail closed there.
#[test]
fn test_field_store_then_whole_object_read_fails_closed() {
    let fn_name = "probe_field_store_then_replace";
    let sites = encode_probe(fn_name);
    assert!(
        [REGION_STALE, READ_AFTER_WRITE, ADDRESS_AS_VALUE].iter().any(|reason| sites
            .get(*reason)
            .copied()
            .unwrap_or(0)
            >= 1),
        "{fn_name}: the whole-object read after the field store must fail closed, got {sites:?}"
    );
}

/// F4 directly: an object whose region array holds a 32-bit element takes an
/// 8-bit store, which only the type-indexed array sees. A region read of the
/// object after it, or before it in encoding order, fails closed; a region
/// read of an object with no such store records nothing.
#[test]
fn test_region_read_and_subsort_store_fail_closed_in_either_order() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_region_divergence(x: u32) -> u32 { x }
    "#;
    let fn_name = "probe_region_divergence";
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let ran = AtomicBool::new(false);
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let word = ay_bindings::Sort::bitvec(32);
        let byte = ay_bindings::Sort::bitvec(8);
        let addr = |obj: u32| {
            ay_bindings::Expr::bitvec_const(obj as u128, 32)
                .concat(ay_bindings::Expr::bitvec_const(0u128, 32))
        };
        let reasons = || {
            crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove(fn_name)
                .unwrap_or_default()
                .get(REGION_STALE)
                .copied()
                .unwrap_or(0)
        };

        // A region read with no divergent store records nothing.
        let clean: u32 = 31;
        let _ = chc_ctx.assign_region_array_to_relation(clean, word.clone());
        assert!(chc_ctx.try_load_from_region(&addr(clean), &word, Some(&word), "u32").is_some());
        assert_eq!(reasons(), 0, "a region read of an undiverged object must record nothing");

        // Store, then read.
        let later: u32 = 32;
        let _ = chc_ctx.assign_region_array_to_relation(later, word.clone());
        chc_ctx.try_store_to_region(
            &addr(later),
            &ay_bindings::Expr::bitvec_const(7u128, 8),
            &byte,
            false,
        );
        assert!(chc_ctx.heap_state.region_diverged.contains(&later), "the 8-bit store diverges");
        assert_eq!(reasons(), 0, "the divergence alone, before any region read, records nothing");
        assert!(chc_ctx.try_load_from_region(&addr(later), &word, Some(&word), "u32").is_some());
        assert_eq!(reasons(), 1, "a region read after the divergent store fails closed");

        // Read, then store (encoding order is not program order).
        let earlier: u32 = 33;
        let _ = chc_ctx.assign_region_array_to_relation(earlier, word.clone());
        assert!(chc_ctx.try_load_from_region(&addr(earlier), &word, Some(&word), "u32").is_some());
        chc_ctx.try_store_to_region(
            &addr(earlier),
            &ay_bindings::Expr::bitvec_const(7u128, 8),
            &byte,
            false,
        );
        assert_eq!(reasons(), 1, "a divergent store after a region read fails closed");

        // A store of the region's own sort is not a divergence.
        let same: u32 = 34;
        let _ = chc_ctx.assign_region_array_to_relation(same, word.clone());
        chc_ctx.try_store_to_region(
            &addr(same),
            &ay_bindings::Expr::bitvec_const(7u128, 32),
            &word,
            false,
        );
        assert!(!chc_ctx.heap_state.region_diverged.contains(&same));
        ran.store(true, Ordering::SeqCst);
    });
    assert!(ran.load(Ordering::SeqCst), "the probe crate compiled and the test body ran");
}

/// `p.0 = 200; p.0` where `p`'s fields are the caller's flattened state (the
/// fn_inline hint map): the write rebinds `p`, so the hint entry for `p.0`
/// (the caller's ENTRY value) is stale and must not answer. `p`'s term is now
/// the updated pair, an untagged value of the pointee's datatype, and no other
/// write happened: the read goes through the term, exactly, and records
/// nothing. Served from the snapshot, it returned 1.
#[test]
fn test_hint_map_read_after_rebind_reads_the_rebound_value() {
    let fn_name = "probe_fninline_hint_map_write_then_read";
    let sites = encode_probe(fn_name);
    for reason in [SELF_MAP_STALE, READ_AFTER_WRITE, ADDRESS_AS_VALUE] {
        assert!(!sites.contains_key(reason), "{fn_name}: must not record {reason}, got {sites:?}");
    }
}

/// Precision: a value-bound `&mut` written and then read through the SAME
/// root, with no other write, is exact (the F1 exemption); nothing is
/// recorded.
#[test]
fn test_value_bound_rebind_then_read_is_exempt() {
    let fn_name = "probe_fninline_value_write_then_read";
    let sites = encode_probe(fn_name);
    for reason in [READ_AFTER_WRITE, ADDRESS_AS_VALUE, SELF_MAP_STALE] {
        assert!(!sites.contains_key(reason), "{fn_name}: must not record {reason}, got {sites:?}");
    }
}

/// Precision: a dyn method that only reads `self` through the self-field map
/// records nothing.
#[test]
fn test_dyn_self_read_only_records_nothing() {
    let fn_name = "probe_dyn_self_read_only";
    let sites = encode_probe(fn_name);
    for reason in [READ_AFTER_WRITE, ADDRESS_AS_VALUE, SELF_MAP_STALE, STORE_IN_ARM] {
        assert!(!sites.contains_key(reason), "{fn_name}: must not record {reason}, got {sites:?}");
    }
}
