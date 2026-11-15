// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A reference loaded out of a reference-typed field (`_t = copy (*_r).p`)
//! points at `*h.p`, not at the slot `h.p`. Pass 1.5 records the copy as the
//! place `h.p` ("value-of"); Pass 2.5 repairs it only when the aggregate's
//! field was built from a pointer with an edge of its own, and the unrepaired
//! edge was read as points-at: `*r.p = 7` overwrote the POINTER field with 7
//! and the heap referent kept its value
//! (`drop_pointer_field_value_of_edges`,
//! tools/soundness-duals/modifies_frame_call_arg_escape_dual.rs and
//! pointer_field_value_edge_dual.rs). The bug probe must reach its error, and
//! each safe twin must prove.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

const FIELD_REF_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, _msg: &str) {
            let _ = cond;
        }
    }

    pub struct HM<'a> { pub n: u32, pub p: &'a mut u32 }

    pub fn probe_heap_field_ref_store_bug() {
        let mut bx: Box<u32> = Box::new(5);
        let mut h = HM { n: 0, p: &mut *bx };
        let r = &mut h;
        *r.p = 7;
        kani::assert(*bx == 5, "the heap referent was written");
    }

    pub fn probe_heap_field_ref_store_safe() {
        let mut bx: Box<u32> = Box::new(5);
        let mut h = HM { n: 0, p: &mut *bx };
        let r = &mut h;
        *r.p = 7;
        kani::assert(*bx == 7, "the heap referent was written");
    }

    pub fn probe_heap_field_ref_slot_kept_safe() {
        let mut bx: Box<u32> = Box::new(5);
        let mut h = HM { n: 0, p: &mut *bx };
        let r = &mut h;
        *r.p = 7;
        kani::assert(r.n == 0, "the sibling field is untouched");
        kani::assert(*h.p == 7, "the pointer field still points at the referent");
    }

    pub struct HR { pub n: u32, pub p: *mut u32 }

    pub fn probe_usize_rebind_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut h = HR { n: 0, p: &mut *bx };
        unsafe { *(core::ptr::addr_of_mut!(h.p) as *mut usize) = yp as usize; }
        let r = &mut h;
        unsafe { *r.p = 7; }
        kani::assert(*bx == 0, "the store went through the rebound pointer");
    }

    pub fn probe_stack_field_ref_store_safe() {
        let mut x: u32 = 5;
        let mut h = HM { n: 0, p: &mut x };
        let r = &mut h;
        *r.p = 7;
        kani::assert(x == 7, "the stack referent was written");
    }
"#;

fn solve_probe(fn_name: &str) -> String {
    solve_probe_with_reasons(fn_name).0
}

fn solve_probe_with_reasons(fn_name: &str) -> (String, std::collections::BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let mut verdict = None;
    with_test_ay_ctx_for_source(FIELD_REF_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        vc.propagate_constants();
        vc.prune_orphan_block_rules();
        vc.prune_dead_identity_scalars();
        vc.normalize_free_array_bases();
        crate::codegen_ay::chc::scalarize_vc(&mut vc);
        vc.prune_dead_vars_and_constraints();
        let smt = emit_chc(&vc).to_string();
        verdict = Some(
            run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30))
                .unwrap_or_else(|e| panic!("AY failed on {fn_name}: {e}")),
        );
    });
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(fn_name)
        .unwrap_or_default();
    (verdict.expect("the probe was encoded"), reasons)
}

#[test]
fn test_store_through_field_reference_reaches_the_heap_referent() {
    assert_eq!(solve_probe("probe_heap_field_ref_store_bug"), "sat");
}

#[test]
fn test_store_through_field_reference_safe_twin_proves() {
    assert_eq!(solve_probe("probe_heap_field_ref_store_safe"), "unsat");
}

#[test]
fn test_store_through_field_reference_keeps_the_pointer_field() {
    assert_eq!(solve_probe("probe_heap_field_ref_slot_kept_safe"), "unsat");
}

#[test]
fn test_store_through_field_reference_stack_referent_stays_exact() {
    assert_eq!(solve_probe("probe_stack_field_ref_store_safe"), "unsat");
}

/// A `usize` store through a pointer cast from `addr_of_mut!(h.p)` rebinds
/// the pointer field without a pointer store, so the aggregate's operand is
/// no longer the field's value: the store through `r.p` must stay unresolved
/// and fail closed. The first fix placed it on `*bx` and certified the safe
/// twin's failure (review of fix/chc-lost-writes, 2026-09-27).
#[test]
fn test_untyped_pointer_field_rebind_fails_closed() {
    let (_verdict, reasons) = solve_probe_with_reasons("probe_usize_rebind_safe");
    assert!(
        reasons.contains_key("deref_store_referent_unresolved")
            || reasons.contains_key("deref_store_stack_target_unresolved"),
        "the store through the rebound field must fail closed; got {reasons:?}"
    );
}
