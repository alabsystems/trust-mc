// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The stack Deref+Field read lane (`try_stack_deref_field_expr`,
//! `expr/codegen_expr_deref_field_offset.rs`) read a flattened owner's INPUT
//! variables whatever the block had written, and walked the MIR indices over
//! the sort tree, which names another leaf past an interior `(T,)`:
//! `r.t.0.y = v; let got = r.t.0.y;` read the pre-block `x.r1`, and
//! `assert!(got == 0)` was proved from a false error obligation
//! (tools/soundness-duals/nested_field_ref_write_dual.rs, the
//! interior-tuple write-then-read rows). A path with no faithful slot now
//! reads memory and records `stack_deref_field_path_unfaithful`.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use std::collections::BTreeMap;

const STACK_FIELD_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, _msg: &str) {
            let _ = cond;
        }
    }

    pub struct R2 { pub r0: u8, pub r1: u8 }
    pub struct QT { pub x: R2, pub y: u8 }
    pub struct QT1 { pub t: (QT,), pub k: u8 }
    pub struct P { pub a: u8, pub b: u8, pub c: u8 }
    pub struct W { pub p: P, pub z: u8 }

    #[inline(never)]
    fn mk_qt1() -> QT1 {
        QT1 { t: (QT { x: R2 { r0: 0, r1: 0 }, y: 0 },), k: 0 }
    }

    pub fn probe_interior_tuple_literal_write_read_bug(v: u8) {
        let mut o = QT1 { t: (QT { x: R2 { r0: 0, r1: 0 }, y: 0 },), k: 0 };
        let r = &mut o;
        r.t.0.y = v;
        let got = r.t.0.y;
        kani::assert(got == 0, "the written field is read back");
    }

    pub fn probe_interior_tuple_write_read_bug(v: u8) {
        let mut o = mk_qt1();
        let r = &mut o;
        r.t.0.y = v;
        let got = r.t.0.y;
        kani::assert(got == 0, "the written field is read back");
    }

    pub fn probe_plain_nested_write_read_safe(v: u8) {
        let mut o = W { p: P { a: 1, b: 2, c: 3 }, z: 4 };
        let r = &mut o;
        r.p.b = v;
        let got = r.p.b;
        kani::assert(got == v, "the written field is read back");
        kani::assert(r.p.c == 3, "the sibling is untouched");
    }
"#;

fn solve_probe(fn_name: &str) -> (String, BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let mut verdict = None;
    with_test_ay_ctx_for_source(STACK_FIELD_PROBE, |ctx| {
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
fn test_interior_tuple_write_then_read_through_reference_is_refutable() {
    let (verdict, reasons) = solve_probe("probe_interior_tuple_write_read_bug");
    assert_eq!(verdict, "sat", "the read must see the written value; reasons {reasons:?}");
}

#[test]
fn test_interior_tuple_literal_owner_write_then_read_is_refutable() {
    let (verdict, reasons) = solve_probe("probe_interior_tuple_literal_write_read_bug");
    assert_eq!(verdict, "sat", "the read must see the written value; reasons {reasons:?}");
}

#[test]
fn test_plain_nested_write_then_read_through_reference_stays_exact() {
    let (verdict, reasons) = solve_probe("probe_plain_nested_write_read_safe");
    assert_eq!(verdict, "unsat", "the written field must be read back; reasons {reasons:?}");
    assert!(
        !reasons.contains_key("stack_deref_field_path_unfaithful"),
        "a faithful path keeps the register lane, got {reasons:?}"
    );
}
