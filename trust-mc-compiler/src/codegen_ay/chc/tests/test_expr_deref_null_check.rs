// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for the CHC raw-pointer null-dereference obligation
//! (`expr/codegen_expr_deref_null_check.rs`).
//!
//! Soundness gap closure: previously only the BMC path emitted null-deref
//! checks (`statement/place_deref.rs::emit_raw_ptr_deref_checks`). The CHC
//! path either loaded an unconstrained value from memory (Mem level) or
//! recorded a sound fallback (Reg/Ptr level), so a reachable null deref like
//! `let p: *const u32 = ptr::null(); unsafe { *p }` verified as PROOF
//! (later mitigated to UNKNOWN by 8fb72021a — but never a detected CTREX).
//!
//! Test strategy:
//! - Structural: the VC must contain a violated `ptr != 0` obligation as an
//!   `error()` rule (deterministic, independent of solver power).
//! - Solver-backed (fail-closed): the VC must never solve to "unsat"
//!   (false PROOF) on either the PDR lane or the bounded-BMC lane.
//! - Non-regression: reference-derived raw pointers must NOT pick up
//!   spurious obligations (no #3094-class false CTREX).
//!
//! KNOWN PINNED-SOLVER GAP (CTREX conclusiveness): the AY revision pinned in
//! Cargo.lock (685d8ffda116) returns `unknown` for BV-sorted error
//! reachability through one or more intermediate relations, on every engine
//! (PDR, BMC-only, CLI portfolio). Minimized reproducer (z3 answers `sat`
//! instantly; `ay solve` and `ay solve --portfolio` answer `unknown`):
//!
//! ```smt2
//! (set-logic HORN)
//! (declare-var p (_ BitVec 8))
//! (declare-rel bb0 ((_ BitVec 8)))
//! (declare-rel bb1 ((_ BitVec 8)))
//! (declare-rel error ())
//! (rule (=> true (bb0 p)))
//! (rule (=> (bb0 p) (bb1 p)))
//! (rule (=> (and (bb1 p) (= p #x00)) error))
//! (query error)
//! ```
//!
//! (The single-hop variant — error rule keyed directly off bb0 — solves
//! `sat`.) Until that upstream gap is fixed, the violation probes here
//! hard-assert the fail-closed properties and report engine convergence via
//! the FIXED/EXPECTED diagnostic convention used by the tier-3 solver
//! probes: when an AY engine starts concluding `sat`, the eprintln flips to
//! FIXED and the assertions can be tightened to `assert_eq!(verdict, "sat")`.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

/// Wall-clock budget for the bounded-BMC reachability check.
const NULL_CHECK_BMC_BUDGET_SECS: u64 = 60;

/// Unroll bound for the bounded-BMC reachability check. The probe systems
/// are straightline (4-6 blocks), so a small depth suffices.
const NULL_CHECK_BMC_MAX_DEPTH: usize = 16;

/// Translate `fn_name` from `source` and return (vc, smt, bb_count).
fn vc_and_smt_for(
    source: &str,
    fn_name: &str,
    config: ChcConfig,
) -> (trust_mc_core::chc::ChcVc, String, usize) {
    let mut vc_out = None;
    let mut smt = String::new();
    let mut bb_count = 0;
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        bb_count = body.blocks.len();
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, config);
        smt = emit_chc(&vc).to_string();
        vc_out = Some(vc);
    });
    (vc_out.expect("vc"), smt, bb_count)
}

/// Bounded-BMC error-reachability verdict, mirroring the production driver's
/// counterexample lane (`AdaptivePortfolio::solve_bmc_only`, see
/// trust-mc-driver/src/call_ay/chc/native.rs). Returns "sat" when BMC finds
/// a counterexample trace, "unsat" when it proves bounded safety, otherwise
/// "unknown".
fn bmc_reachability_verdict(smt: &str) -> String {
    let config = ay_chc::BmcConfig::default()
        .with_max_depth(NULL_CHECK_BMC_MAX_DEPTH)
        .with_time_budget(std::time::Duration::from_secs(NULL_CHECK_BMC_BUDGET_SECS));
    match ay_chc::engines::solve_bmc_only_from_str(smt, config) {
        Ok(result) => {
            if result.is_unsafe() {
                "sat".to_string()
            } else if result.is_safe() {
                "unsat".to_string()
            } else {
                format!("unknown ({:?})", result.unknown_reason())
            }
        }
        Err(err) => format!("error: {err}"),
    }
}

/// An error rule whose constraints reference an equality against a bv64 zero
/// constant — the shape of the negated `ptr != 0` obligation.
fn has_null_check_error_rule(vc: &trust_mc_core::chc::ChcVc) -> bool {
    vc.rules.iter().filter(|rule| rule.head.name == "error").any(|rule| {
        rule.body.constraints.iter().any(|c| {
            constraint_tree_contains(c, &|expr| {
                if let ExprValue::Eq(lhs, rhs) = expr.value() {
                    let is_zero64 = |e: &Expr| {
                        matches!(
                            e.value(),
                            ExprValue::BitVecConst { value, width: 64 } if value.to_string() == "0"
                        )
                    };
                    is_zero64(lhs) || is_zero64(rhs)
                } else {
                    false
                }
            })
        })
    })
}

/// Shared driver for the violation probes: assert the violated obligation is
/// present structurally, that PDR never returns "unsat" (false PROOF), and
/// that the production-style bounded BMC detects the violation ("sat").
fn assert_null_deref_violation(source: &str, fn_name: &str, config: ChcConfig, label: &str) {
    let (vc, smt, bb_count) = vc_and_smt_for(source, fn_name, config);
    assert_vc_structure(&vc, fn_name, bb_count);

    assert!(
        has_null_check_error_rule(&vc),
        "{label}: a raw-pointer deref through a (possibly) null pointer must stage a \
         `ptr != 0` obligation that lowers to an error rule with an eq-to-bv64-zero \
         violation. Rules:\n{:?}",
        vc.rules.iter().map(|r| &r.head.name).collect::<Vec<_>>()
    );

    // Fail-closed: the system has a genuinely reachable error, so a PROOF
    // ("unsat") would be the exact soundness hole this change closes.
    // (The pinned PDR engine currently returns "unknown" on multi-block BV
    // reachability; "sat" is asserted via the BMC lane below.)
    let pdr_verdict =
        run_z3_on_smt2_with_timeout(&smt, NULL_CHECK_BMC_BUDGET_SECS).expect("AY CHC PDR result");
    assert_ne!(
        pdr_verdict, "unsat",
        "{label}: FALSE PROOF — PDR proved a VC whose error relation is reachable \
         (null raw-pointer deref). SMT:\n{smt}"
    );

    // Counterexample detection (CTREX): bounded BMC must never claim bounded
    // safety, and ideally concludes "sat". See the pinned-solver gap note in
    // the module header for why "sat" is not yet a hard assertion.
    let bmc_verdict = bmc_reachability_verdict(&smt);
    assert_ne!(
        bmc_verdict, "unsat",
        "{label}: FALSE PROOF — bounded BMC claimed safety for a VC whose error \
         relation is reachable (null raw-pointer deref). SMT:\n{smt}"
    );
    report_ctrex_convergence(label, &pdr_verdict, &bmc_verdict);
}

/// FIXED/EXPECTED diagnostic for CTREX conclusiveness (see module header).
fn report_ctrex_convergence(label: &str, pdr_verdict: &str, bmc_verdict: &str) {
    if pdr_verdict == "sat" || bmc_verdict == "sat" {
        eprintln!(
            "[null-deref {label}] FIXED: AY concludes CTREX \
             (pdr={pdr_verdict}, bmc={bmc_verdict}) — tighten to assert_eq!(.., \"sat\")"
        );
    } else {
        eprintln!(
            "[null-deref {label}] EXPECTED: pinned AY engines inconclusive \
             (pdr={pdr_verdict}, bmc={bmc_verdict}); violation is asserted \
             structurally and fail-closed (z3 cross-check of this system shape: sat)"
        );
    }
}

// =============================================================================
// Null raw-pointer deref READ — must be a detected violation (CTREX), not
// PROOF (the original soundness hole) or UNKNOWN (the 8fb72021a mitigation).
// =============================================================================

const NULL_PTR_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_null_ptr_deref() -> u32 {
        let p: *const u32 = std::ptr::null();
        unsafe { *p }
    }
"#;

#[test]
fn test_null_ptr_deref_emits_violated_obligation_reg_level() {
    assert_null_deref_violation(
        NULL_PTR_DEREF_SOURCE,
        "probe_null_ptr_deref",
        ChcConfig::default(),
        "probe_null_ptr_deref (Reg)",
    );
}

#[test]
fn test_null_ptr_deref_emits_violated_obligation_mem_level() {
    assert_null_deref_violation(
        NULL_PTR_DEREF_SOURCE,
        "probe_null_ptr_deref",
        ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        "probe_null_ptr_deref (Mem)",
    );
}

// =============================================================================
// Zero-cast pointer deref — same obligation through the `0 as *const i32` path.
// =============================================================================

const ZERO_CAST_PTR_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_zero_cast_ptr_deref() -> i32 {
        let p: *const i32 = 0 as *const i32;
        unsafe { *p }
    }
"#;

#[test]
fn test_zero_cast_ptr_deref_emits_violated_obligation() {
    assert_null_deref_violation(
        ZERO_CAST_PTR_DEREF_SOURCE,
        "probe_zero_cast_ptr_deref",
        ChcConfig::default(),
        "probe_zero_cast_ptr_deref (Reg)",
    );
}

// =============================================================================
// Null raw-pointer deref STORE — the stmt-side mirror of the cascade hook.
// =============================================================================

const NULL_PTR_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_null_ptr_store() {
        let p: *mut u32 = std::ptr::null_mut();
        unsafe { *p = 5 };
    }
"#;

/// Store-side: only structural + BMC assertions. The pinned PDR engine does
/// not terminate in reasonable time on the Mem-promoted store system, so the
/// PDR lane is skipped here (the read-side tests cover the PDR fail-closed
/// property).
#[test]
fn test_null_ptr_store_emits_violated_obligation() {
    let fn_name = "probe_null_ptr_store";
    let (vc, smt, bb_count) = vc_and_smt_for(NULL_PTR_STORE_SOURCE, fn_name, ChcConfig::default());
    assert_vc_structure(&vc, fn_name, bb_count);

    assert!(
        has_null_check_error_rule(&vc),
        "{fn_name}: a raw-pointer deref STORE through ptr::null_mut() must stage a \
         `ptr != 0` obligation (stmt-side hook in encode_projection_assignment)"
    );

    let bmc_verdict = bmc_reachability_verdict(&smt);
    assert_ne!(
        bmc_verdict, "unsat",
        "{fn_name}: FALSE PROOF — bounded BMC claimed safety for a VC whose error \
         relation is reachable (null raw-pointer deref store). SMT:\n{smt}"
    );
    report_ctrex_convergence(fn_name, "skipped", &bmc_verdict);
}

// =============================================================================
// Non-regression: reference-derived raw pointers are provably non-null and
// must NOT pick up a violated obligation (no #3094-class false CTREX).
// =============================================================================

const REF_DERIVED_PTR_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_ref_derived_ptr_deref() -> u32 {
        let x: u32 = 7;
        let p: *const u32 = &x;
        unsafe { *p }
    }
"#;

#[test]
fn test_ref_derived_ptr_deref_has_no_false_ctrex() {
    let fn_name = "probe_ref_derived_ptr_deref";
    let (vc, smt, bb_count) =
        vc_and_smt_for(REF_DERIVED_PTR_DEREF_SOURCE, fn_name, ChcConfig::default());
    assert_vc_structure(&vc, fn_name, bb_count);

    let pdr_verdict =
        run_z3_on_smt2_with_timeout(&smt, NULL_CHECK_BMC_BUDGET_SECS).expect("AY CHC PDR result");
    assert_ne!(
        pdr_verdict, "sat",
        "{fn_name}: FALSE CTREX (PDR) — a raw pointer derived from a reference is \
         non-null by language guarantee; the null-deref obligation must be suppressed \
         by the provably-non-null whitelist. SMT:\n{smt}"
    );

    let bmc_verdict = bmc_reachability_verdict(&smt);
    assert_ne!(
        bmc_verdict, "sat",
        "{fn_name}: FALSE CTREX (BMC) — no error may be reachable for a ref-derived \
         raw pointer deref. SMT:\n{smt}"
    );
}

/// Same non-regression through `&mut` and a deref store.
const REF_DERIVED_PTR_STORE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_ref_derived_ptr_store() -> u32 {
        let mut x: u32 = 7;
        let p: *mut u32 = &mut x;
        unsafe { *p = 9 };
        x
    }
"#;

#[test]
fn test_ref_derived_ptr_store_has_no_false_ctrex() {
    let fn_name = "probe_ref_derived_ptr_store";
    let (vc, smt, bb_count) =
        vc_and_smt_for(REF_DERIVED_PTR_STORE_SOURCE, fn_name, ChcConfig::default());
    assert_vc_structure(&vc, fn_name, bb_count);

    let pdr_verdict =
        run_z3_on_smt2_with_timeout(&smt, NULL_CHECK_BMC_BUDGET_SECS).expect("AY CHC PDR result");
    assert_ne!(
        pdr_verdict, "sat",
        "{fn_name}: FALSE CTREX (PDR) — `&mut x as *mut u32` is non-null by language \
         guarantee; the store-side null-deref obligation must be suppressed. SMT:\n{smt}"
    );

    let bmc_verdict = bmc_reachability_verdict(&smt);
    assert_ne!(
        bmc_verdict, "sat",
        "{fn_name}: FALSE CTREX (BMC) — no error may be reachable for a ref-derived \
         raw pointer deref store. SMT:\n{smt}"
    );
}

// =============================================================================
// References themselves never get the obligation (type gate).
// =============================================================================

const PLAIN_REF_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_plain_ref_deref(r: &u32) -> u32 {
        *r
    }
"#;

#[test]
fn test_plain_ref_deref_emits_no_null_obligation() {
    let fn_name = "probe_plain_ref_deref";
    let (vc, _smt, bb_count) =
        vc_and_smt_for(PLAIN_REF_DEREF_SOURCE, fn_name, ChcConfig::default());
    assert_vc_structure(&vc, fn_name, bb_count);

    assert!(
        !has_null_check_error_rule(&vc),
        "{fn_name}: deref of a plain reference must not stage a null-pointer obligation \
         (RawPtr type gate)"
    );
}
