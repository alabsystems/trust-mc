// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Repair round 4 of fix/chc-walker-fail-closed, the class of walker
//! fail-closed review 6 round 3 finding 7 (docs/chc-hole-fix-designs-
//! 2026-09-24.md, "Walker fail-closed: repair round 4"): `mem::swap`
//! exchanges collection side state, `Vec::len` through a by-value field reads
//! the field, and a store through a reference of a value holding a
//! collection fails closed. The BMC half (derived field entries) is in
//! `statement/env/mod.rs`.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use super::common::*;

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

const PROBE: &str = r#"
    #![allow(dead_code, internal_features, unused)]

    pub struct S {
        pub v: Vec<u8>,
        pub n: u8,
    }

    pub fn probe_swap_vecs() -> usize {
        let mut v: Vec<u8> = Vec::new();
        let mut w = vec![1u8, 2];
        std::mem::swap(&mut v, &mut w);
        v.len() + w.len()
    }
    pub fn probe_deref_field_store() -> usize {
        let mut s = S { v: Vec::new(), n: 0 };
        {
            let r = &mut s;
            r.v = vec![1, 2, 3];
        }
        s.v.len()
    }
    pub fn probe_deref_scalar_field_store() -> u8 {
        let mut s = S { v: Vec::new(), n: 0 };
        {
            let r = &mut s;
            r.n = 7;
        }
        s.n
    }
    pub fn probe_field_types(s: &S, r: &&Vec<u8>) -> usize {
        s.v.len() + r.len()
    }
"#;

fn with_probe(test: impl for<'tcx> FnOnce(TyCtxt<'tcx>) + Send) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let ran = AtomicBool::new(false);
    with_test_ay_ctx_for_source(PROBE, |ctx| {
        test(ctx.tcx);
        ran.store(true, Ordering::SeqCst);
    });
    assert!(ran.load(Ordering::SeqCst), "the probe crate compiled and the test body ran");
}

fn reasons_of(ctx_name: &str) -> BTreeMap<String, usize> {
    crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(ctx_name)
        .unwrap_or_default()
}

/// Encode `probe` with `config` and return the VC and the fallback reasons
/// it recorded.
fn encode(
    tcx: TyCtxt<'_>,
    probe: &str,
    config: ChcConfig,
) -> (trust_mc_core::chc::ChcVc, BTreeMap<String, usize>) {
    let name = format!("walker_repair4_side_state__{probe}");
    let instance = find_instance_by_suffix(tcx, probe);
    let body = instance.body().expect("body");
    let vc = mir_to_chc_with_instance(tcx, &body, instance, name.as_str(), config);
    (vc, reasons_of(&name))
}


// ---------------------------------------------------------------------------
// (7) Collection side state
// ---------------------------------------------------------------------------

/// Is `expr` an equality between a collection length var's `__out` and
/// another length var's input?
fn is_len_exchange(expr: &Expr) -> bool {
    let ExprValue::Eq(lhs, rhs) = expr.value() else {
        return false;
    };
    let name = |e: &Expr| match e.value() {
        ExprValue::Var { name } => Some(name.to_string()),
        _ => None,
    };
    match (name(lhs), name(rhs)) {
        (Some(out), Some(input)) => {
            out.contains("_len_")
                && out.ends_with("__out")
                && input.contains("_len_")
                && !input.ends_with("__out")
                && out.trim_end_matches("__out") != input
        }
        _ => false,
    }
}

/// `mem::swap(&mut v, &mut w)` exchanged the two Vec datatypes but not their
/// length side state: `v.len() == 0` after swapping in `vec![1, 2]` verified
/// clean where Kani fails (`d3_mem_swap_len_bug`). The swap now writes each
/// local's length from the other's, and records no fail-closed reason.
#[test]
fn test_mem_swap_exchanges_collection_side_state() {
    with_probe(|tcx| {
        let (vc, reasons) = encode(tcx, "probe_swap_vecs", ChcConfig::default());
        assert!(
            !reasons.contains_key("typed_swap_collection_side_state_unmodelled"),
            "{reasons:?}"
        );
        let exchanges = vc
            .rules
            .iter()
            .flat_map(|rule| rule.body.constraints.iter())
            .filter(|c| constraint_tree_contains(c, &is_len_exchange))
            .count();
        assert!(exchanges >= 2, "both lengths are written from the other's: {exchanges}");
    });
}

/// A store through a reference into a field (`(*r).v = vec![1, 2, 3]`) writes
/// the target's memory image, while `s.v.len()` reads the struct's own state:
/// the bug row `s.v.len() == 0` verified clean once the length was read where
/// the field lives. A store through a reference of a value holding a
/// collection fails closed; a scalar field store does not.
#[test]
fn test_deref_store_of_a_value_holding_a_collection_fails_closed() {
    with_probe(|tcx| {
        let (_, reasons) = encode(tcx, "probe_deref_field_store", ChcConfig::default());
        assert!(reasons.contains_key("deref_store_collection_side_state_unmodelled"), "{reasons:?}");
        let (_, reasons) = encode(tcx, "probe_deref_scalar_field_store", ChcConfig::default());
        assert!(
            !reasons.contains_key("deref_store_collection_side_state_unmodelled"),
            "a scalar field: {reasons:?}"
        );
    });
}

/// `Vec::len` through a field took the length of ANY tracked local whose
/// reference target was that field: a borrow taken before a later store to
/// the field (a drop-glue reborrow of the old value), so `s.v = vec![1, 2];
/// s.v.len() == 0` verified clean (`s3_vec_field_direct_store_bug`). Only a
/// field that holds a reference (a closure's captured `&Vec`) is chased now.
#[test]
fn test_vec_len_ref_chase_only_through_a_reference_field() {
    use rustc_public::mir::ProjectionElem;
    with_probe(|tcx| {
        let body = find_instance_by_suffix(tcx, "probe_field_types").body().expect("body");
        let s_ty = body.locals()[1].ty;
        let TyKind::RigidTy(RigidTy::Ref(_, s_inner, _)) = s_ty.kind() else {
            panic!("&S");
        };
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = s_inner.kind() else {
            panic!("S");
        };
        let v_ty = def.variants()[0].fields()[0].ty_with_args(&args);
        let ref_vec_ty = {
            let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = body.locals()[2].ty.kind() else {
                panic!("&&Vec");
            };
            inner
        };
        let by_value = ProjectionElem::Field(0, v_ty);
        let by_ref = ProjectionElem::Field(0, ref_vec_ty);
        assert!(!ChcCtx::field_projection_holds_reference(Some(&by_value)), "a Vec by value");
        assert!(ChcCtx::field_projection_holds_reference(Some(&by_ref)), "a &Vec field");
        assert!(!ChcCtx::field_projection_holds_reference(None));
    });
}
