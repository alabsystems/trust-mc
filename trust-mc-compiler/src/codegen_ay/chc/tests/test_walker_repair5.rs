// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Repair round 5 of fix/chc-walker-fail-closed (docs/chc-hole-fix-designs-
//! 2026-09-24.md, "Walker fail-closed: repair round 5"): the exact range
//! count of `Vec::extend` (signed, `char`, a literal that is no longer
//! current, the capacity panic), Kani's `memcmp` loop behind `raw_eq` and
//! `compare_bytes`, and float sums left unmodelled. The duals are
//! `tools/soundness-duals/range_extend_kinds_dual.rs`,
//! `range_literal_stale_dual.rs`, `model_call_unwind_memcmp_dual.rs` and
//! `float_sum_dual.rs`.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use super::common::*;

use ay_bindings::ExprValue;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::codegen_ay::reduce_loop_rule::{SumModel, iter_sum_call_model};

const PROBE: &str = r#"
    #![allow(dead_code, internal_features, unused)]

    pub fn probe_extend_signed(a: i8, b: i8) -> usize {
        let mut v: Vec<i8> = Vec::new();
        v.extend(a..b);
        v.len()
    }
    pub fn probe_extend_char(a: char, b: char) -> usize {
        let mut v: Vec<char> = Vec::new();
        v.extend(a..b);
        v.len()
    }
    pub fn probe_extend_literal() -> usize {
        let r = 0u32..5;
        let mut v: Vec<u32> = Vec::new();
        v.extend(r);
        v.len()
    }
    pub fn probe_extend_advanced() -> usize {
        let mut r = 0u32..5;
        r.next();
        let mut v: Vec<u32> = Vec::new();
        v.extend(r);
        v.len()
    }
    pub fn probe_extend_u64(n: u64) -> usize {
        let mut v: Vec<u64> = Vec::new();
        v.extend(0..n);
        v.len()
    }
    pub fn probe_u32_array_eq(a: [u32; 2], b: [u32; 2]) -> bool {
        a == b
    }
    pub fn probe_str_eq(a: &str, b: &str) -> bool {
        a == b
    }
    pub fn probe_u32_eq(a: u32, b: u32) -> bool {
        PartialEq::eq(&a, &b)
    }
    pub fn probe_float_sum(a: [f32; 2]) -> f32 {
        a.iter().sum()
    }
    pub fn probe_int_sum(a: [u8; 2]) -> u8 {
        a.iter().sum()
    }

    #[derive(Clone, Copy)]
    #[repr(u8)]
    pub enum E3 { A = 0, B = 1, C = 2 }
    #[inline(never)]
    fn keep(_e: E3) {}
    pub fn probe_enum_built(k: u8) {
        let e = if k == 0 { E3::A } else if k == 1 { E3::B } else { E3::C };
        let f = e;
        keep(f);
    }
    pub fn probe_enum_forged(k: u8, b: u8) {
        let mut e = if k == 0 { E3::A } else { E3::B };
        unsafe { *(&mut e as *mut E3 as *mut u8) = b; }
        keep(e);
    }
    #[inline(never)]
    fn make() -> E3 { E3::C }
    pub fn probe_enum_from_call() {
        let e = make();
        keep(e);
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

fn encode(tcx: TyCtxt<'_>, probe: &str) -> (trust_mc_core::chc::ChcVc, BTreeMap<String, usize>) {
    let name = format!("walker_repair5__{probe}");
    let instance = find_instance_by_suffix(tcx, probe);
    let body = instance.body().expect("body");
    let vc = mir_to_chc_with_instance(tcx, &body, instance, name.as_str(), ChcConfig::default());
    (vc, reasons_of(&name))
}

fn vc_contains(vc: &trust_mc_core::chc::ChcVc, pred: impl Fn(&Expr) -> bool) -> bool {
    vc.rules.iter().any(|rule| rule_contains_expr(rule, &pred))
}

fn is_const(expr: &Expr, value: u64, width: u32) -> bool {
    matches!(expr.value(), ExprValue::BitVecConst { value: v, width: w } if *w == width && *v == value.into())
}

/// The callee instance of the call in `body` whose callee's name ends with
/// `suffix`.
fn callee_named(body: &Body, suffix: &str) -> Instance {
    body.blocks
        .iter()
        .find_map(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                return None;
            };
            let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func.ty(body.locals()).ok()?.kind() else {
                return None;
            };
            def.name().ends_with(suffix).then(|| Instance::resolve(def, &args).expect("resolves"))
        })
        .unwrap_or_else(|| panic!("the body calls `{suffix}`"))
}

// ---------------------------------------------------------------------------
// Finding 1 (a), (b): the count in the element type's own order
// ---------------------------------------------------------------------------

/// `-2i8..3` yielded no element and `2i8..-1` 253: the bounds were
/// zero-extended and compared unsigned. A signed range is compared signed.
#[test]
fn test_extend_signed_range_compares_signed() {
    with_probe(|tcx| {
        let (vc, reasons) = encode(tcx, "probe_extend_signed");
        assert!(vc_contains(&vc, |e| matches!(e.value(), ExprValue::BvSLt(..))), "start <s end: {reasons:?}");
        assert!(
            !vc_contains(&vc, |e| matches!(e.value(), ExprValue::BvULt(a, _) if matches!(a.value(), ExprValue::BvZeroExtend { .. }))),
            "no unsigned comparison of zero-extended bounds: {reasons:?}"
        );
    });
}

/// `'\u{D7FF}'..'\u{E001}'` counted the 0x800 surrogates.
#[test]
fn test_extend_char_range_skips_the_surrogates() {
    with_probe(|tcx| {
        let (vc, reasons) = encode(tcx, "probe_extend_char");
        assert!(vc_contains(&vc, |e| is_const(e, 0x800, 64)), "the surrogate gap: {reasons:?}");
        assert!(vc_contains(&vc, |e| is_const(e, 0xD800, 64)), "the gap's start: {reasons:?}");
    });
}

// ---------------------------------------------------------------------------
// Finding 1 (c): a literal answers only while it is current
// ---------------------------------------------------------------------------

/// `let mut r = 0..5; r.next(); v.extend(r)` extended by five: the bounds
/// were read from the literal. A range borrowed mutably reads its state; a
/// current literal still folds to its count.
#[test]
fn test_extend_reads_an_advanced_range_from_its_state() {
    with_probe(|tcx| {
        let adds_five = |e: &Expr| match e.value() {
            ExprValue::BvAdd(_, rhs) => is_const(rhs, 5, 64),
            _ => false,
        };
        let (vc, reasons) = encode(tcx, "probe_extend_literal");
        assert!(vc_contains(&vc, adds_five), "a current literal folds to 5: {reasons:?}");
        let (vc, reasons) = encode(tcx, "probe_extend_advanced");
        assert!(!vc_contains(&vc, adds_five), "an advanced range is not its literal: {reasons:?}");
    });
}

/// `v.extend(0u64..u64::MAX)` verified clean where Kani fails: the new length
/// was assumed not to wrap. `extend` reserves the count, which panics with
/// "capacity overflow" past `isize::MAX / size_of::<T>()` elements; the check
/// compares with that limit.
#[test]
fn test_extend_checks_the_capacity_overflow() {
    with_probe(|tcx| {
        let (vc, reasons) = encode(tcx, "probe_extend_u64");
        let max_cap = (i64::MAX as u64) / 8;
        assert!(vc_contains(&vc, |e| is_const(e, max_cap, 64)), "isize::MAX / 8: {reasons:?}");
    });
}

// ---------------------------------------------------------------------------
// Finding 4: Kani's memcmp loop
// ---------------------------------------------------------------------------

/// Kani runs `raw_eq` (array `==` of bytewise-comparable elements) and
/// `compare_bytes` (`str` / `[u8]` comparison) as CBMC's `memcmp`, a loop per
/// byte. The loop walk read both body-less intrinsics as loop-free.
#[test]
fn test_memcmp_backed_comparisons_loop() {
    with_probe(|tcx| {
        let stubs = crate::codegen_ay::obligation_free_walk::StubMap::default();
        let may_loop = |probe: &str, callee: &str| {
            let body = find_instance_by_suffix(tcx, probe).body().expect("probe body");
            crate::codegen_ay::obligation_free_walk::instance_may_loop(tcx, callee_named(&body, callee), &stubs)
        };
        assert!(may_loop("probe_u32_array_eq", "PartialEq::eq"), "[u32; 2] == runs raw_eq");
        assert!(may_loop("probe_str_eq", "PartialEq::eq"), "&str == runs compare_bytes");
        assert!(!may_loop("probe_u32_eq", "PartialEq::eq"), "u32 == runs no loop");
    });
}

// ---------------------------------------------------------------------------
// Finding 3: float sums
// ---------------------------------------------------------------------------

/// A float `sum` was modelled as checked integer addition of the bit patterns,
/// so repair round 5 left it unmodelled. Main's `Iterator::sum` rework
/// (`iter_sum_summand`, `SumSummand::Float`: IEEE addition of the elements,
/// folded on the host for constants, with Kani's NaN check under
/// `--nan-check`) models core's float `Sum` exactly in both lanes, so the
/// merge with main takes its rule again: a float target is core's `Sum`, and
/// the summand, not this model, says how it adds (`float_sum_dual.rs`, whose
/// BMC bug rows the exclusion had left undecided).
#[test]
fn test_float_sum_is_core_sum() {
    with_probe(|tcx| {
        let model = |probe: &str| {
            let body = find_instance_by_suffix(tcx, probe).body().expect("probe body");
            let func = body
                .blocks
                .iter()
                .find_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, .. }
                        if matches!(func.ty(body.locals()).ok().map(|t| t.kind()),
                            Some(TyKind::RigidTy(RigidTy::FnDef(def, _))) if def.name().ends_with("Iterator::sum")) =>
                    {
                        Some(func.clone())
                    }
                    _ => None,
                })
                .expect("a sum call");
            iter_sum_call_model(&func, body.locals())
        };
        assert_eq!(model("probe_float_sum"), Some(SumModel::Checked), "f32 sum");
        assert_eq!(model("probe_int_sum"), Some(SumModel::Checked), "u8 sum");
    });
}

// ---------------------------------------------------------------------------
// Finding 8: the enum pass-on cost (`walker_enum_pass_on_dual.rs` `f1`)
// ---------------------------------------------------------------------------

/// A host local of a fieldless enum holds only valid values when nothing
/// borrows it and each definition is a variant, a constant or a copy of such
/// a local; a raw-pointer write through its address, or a call result,
/// refuses. Passing such a value on to a havocked callee adds nothing to the
/// result's valid values.
#[test]
fn test_host_enum_local_built_valid() {
    use crate::codegen_ay::chc::call::codegen_call_virtual_inline::host_local_built_valid;
    with_probe(|tcx| {
        let verdicts = |probe: &str| {
            let body = find_instance_by_suffix(tcx, probe).body().expect("probe body");
            let enum_locals: Vec<(usize, rustc_public::ty::Ty)> = body
                .locals()
                .iter()
                .enumerate()
                .filter(|(_, decl)| {
                    matches!(decl.ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if def.name().ends_with("E3"))
                })
                .map(|(local, decl)| (local, decl.ty))
                .collect();
            assert!(!enum_locals.is_empty(), "{probe} has an E3 local");
            enum_locals
                .into_iter()
                .map(|(local, ty)| host_local_built_valid(&body, local, ty, &mut std::collections::HashSet::new()))
                .collect::<Vec<_>>()
        };
        assert!(verdicts("probe_enum_built").iter().all(|v| *v), "variants and copies of them");
        assert!(verdicts("probe_enum_forged").iter().any(|v| !*v), "a write through a cast pointer");
        assert!(verdicts("probe_enum_from_call").iter().all(|v| !*v), "a call result");
    });
}
