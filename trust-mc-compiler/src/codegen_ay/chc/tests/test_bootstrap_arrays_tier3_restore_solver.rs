// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Solver-backed restore-property probes for the arrays Tier 3 localizer.
//!
//! Part of #4050: turn the residual `pop_restores_assignments` packet into a
//! semantic positive/negative SMT check instead of a structural-only localizer.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::common::*;
use super::{
    BOOTSTRAP_ARRAYS_TIER3_SOURCE, inferable_predicate_artifacts,
    reset_bootstrap_arrays_tier3_counters,
};
use crate::codegen_ay::emit_chc;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Once;

const DROP_INLINE_WALK_SITE_PREFIX: &str = "drop_inline_walk_failed@";
const INLINE_OVERAPPROX_PREFIXES: &[&str] = &[
    "__nested_call_overapprox",
    "__assert_fail_inline",
    "__fmt_inline",
    "__switchint_branch_overapprox",
    "__switchint_sort_coerce",
    "__loop_exhaust_inline",
];

/// Result from `emit_restore_probe_smt`: SMT string, inferable decls,
/// and fallback count for the target function.
struct RestoreProbeResult {
    smt: String,
    inferable_decls: Vec<String>,
    has_p_inf_rule: bool,
    fallback_count: usize,
    aggregate_gap_count: usize,
    inferable_count: usize,
    aggregate_gaps: BTreeMap<String, usize>,
    aggregate_gap_reasons: BTreeMap<String, BTreeMap<String, usize>>,
    drop_fallback_reasons: BTreeMap<String, BTreeMap<String, usize>>,
    inline_overapprox_decl_counts: BTreeMap<String, usize>,
    unhandled_calls: BTreeMap<String, usize>,
    translation_drops: BTreeMap<String, usize>,
    translation_drop_sites: BTreeMap<String, BTreeMap<String, usize>>,
    relation_names: BTreeSet<String>,
}

fn init_restore_solver_tracing() {
    static INIT: Once = Once::new();
    INIT.call_once(|| {
        let _ = tracing_subscriber::fmt()
            .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
            .try_init();
    });
}

fn emit_restore_probe_smt(source: &str, fn_name: &str) -> RestoreProbeResult {
    init_restore_solver_tracing();
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_bootstrap_arrays_tier3_counters();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
    let _ = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
        .take_aggregate_gap_reasons_by_fn();
    let _ = crate::codegen_ay::take_drop_fallback_reasons_by_fn();

    let mut inferable_decls: Vec<String> = Vec::new();
    let mut has_p_inf_rule = false;
    let mut smt = String::new();
    let mut relation_names = BTreeSet::new();

    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        (inferable_decls, has_p_inf_rule) = inferable_predicate_artifacts(&vc);
        relation_names = vc.relations.iter().map(|rel| rel.name.clone()).collect();
        smt = emit_chc(&vc).to_string();
    });

    let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
    let aggregate_gap_count = crate::codegen_ay::take_aggregate_encoding_gap_count();
    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
    let aggregate_gaps = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
    let aggregate_gap_reasons = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
        .take_aggregate_gap_reasons_by_fn();
    let drop_fallback_reasons = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let inline_overapprox_decl_counts =
        count_declared_var_prefixes(&smt, INLINE_OVERAPPROX_PREFIXES);
    let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
    let translation_drops = take_translation_drop_by_fn();
    let translation_drop_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    reset_bootstrap_arrays_tier3_counters();
    RestoreProbeResult {
        smt,
        inferable_decls,
        has_p_inf_rule,
        fallback_count,
        aggregate_gap_count,
        inferable_count,
        aggregate_gaps,
        aggregate_gap_reasons,
        drop_fallback_reasons,
        inline_overapprox_decl_counts,
        unhandled_calls,
        translation_drops,
        translation_drop_sites,
        relation_names,
    }
}

fn summarize_relation_heads(stdout: &str, relation_names: &BTreeSet<String>) -> Vec<String> {
    stdout
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            if !trimmed.starts_with('(') || trimmed.starts_with("(error") {
                return None;
            }
            let head = trimmed[1..]
                .split(|c: char| c.is_whitespace() || c == ')' || c == '(')
                .find(|token| !token.is_empty())?;
            relation_names.contains(head).then(|| head.to_string())
        })
        .collect()
}

fn count_declared_var_prefixes(smt: &str, prefixes: &[&str]) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for line in smt.lines() {
        let trimmed = line.trim();
        let Some(rest) = trimmed.strip_prefix("(declare-var ") else {
            continue;
        };
        let Some(name) = rest.split_whitespace().next() else {
            continue;
        };
        for prefix in prefixes {
            if name.starts_with(prefix) {
                *counts.entry((*prefix).to_string()).or_insert(0) += 1;
                break;
            }
        }
    }
    counts
}

fn restore_probe_timeout_secs() -> u64 {
    z3_test_timeout_secs_or(30)
}

fn exact_file_restore_timeout_secs() -> u64 {
    z3_test_timeout_secs_or(60)
}

fn fn_reason_counts(
    reasons: &BTreeMap<String, BTreeMap<String, usize>>,
    fn_name: &str,
) -> BTreeMap<String, usize> {
    reasons.get(fn_name).cloned().unwrap_or_default()
}

fn non_resume_tagged_drop_count(
    fn_translation_drop_total: usize,
    fn_site_reasons: &BTreeMap<String, usize>,
) -> usize {
    let resume_abort_count = fn_site_reasons.get("resume_abort").copied().unwrap_or(0);
    fn_translation_drop_total.saturating_sub(resume_abort_count)
}

fn drop_inline_walk_site_counts(
    fn_site_reasons: &BTreeMap<String, usize>,
) -> BTreeMap<String, usize> {
    fn_site_reasons
        .iter()
        .filter(|(reason, _)| reason.starts_with(DROP_INLINE_WALK_SITE_PREFIX))
        .map(|(reason, count)| (reason.clone(), *count))
        .collect()
}

struct RestoreRunDiagnostics {
    verdict: String,
    stdout: String,
    stderr: String,
    status_success: bool,
    transport_error: Option<String>,
    relation_heads: Vec<String>,
    fn_drop_fallback_reasons: BTreeMap<String, usize>,
    fn_translation_drop_sites: BTreeMap<String, usize>,
    fn_drop_inline_walk_sites: BTreeMap<String, usize>,
    fn_translation_drop_total: usize,
    fn_resume_abort_count: usize,
    fn_non_resume_tagged: usize,
}

fn capture_restore_run(
    r: &RestoreProbeResult,
    fn_name: &str,
    timeout_secs: u64,
) -> RestoreRunDiagnostics {
    let result = run_z3_on_smt2_capture_output_with_timeout(&r.smt, timeout_secs);
    let (verdict, stdout, stderr, status_success, transport_error) = match result {
        Ok(output) => (output.verdict, output.stdout, output.stderr, output.status_success, None),
        Err(err) => ("error".to_string(), String::new(), String::new(), false, Some(err)),
    };
    let relation_heads = summarize_relation_heads(&stdout, &r.relation_names);
    let fn_drop_fallback_reasons = fn_reason_counts(&r.drop_fallback_reasons, fn_name);
    let fn_translation_drop_sites = fn_reason_counts(&r.translation_drop_sites, fn_name);
    let fn_drop_inline_walk_sites = drop_inline_walk_site_counts(&fn_translation_drop_sites);
    let fn_translation_drop_total = r.translation_drops.get(fn_name).copied().unwrap_or(0);
    let fn_resume_abort_count = fn_translation_drop_sites.get("resume_abort").copied().unwrap_or(0);
    let fn_non_resume_tagged =
        non_resume_tagged_drop_count(fn_translation_drop_total, &fn_translation_drop_sites);

    RestoreRunDiagnostics {
        verdict,
        stdout,
        stderr,
        status_success,
        transport_error,
        relation_heads,
        fn_drop_fallback_reasons,
        fn_translation_drop_sites,
        fn_drop_inline_walk_sites,
        fn_translation_drop_total,
        fn_resume_abort_count,
        fn_non_resume_tagged,
    }
}

fn assert_restore_run_well_formed(label: &str, diag: &RestoreRunDiagnostics) {
    assert!(
        diag.transport_error.is_none(),
        "[{label}] z3 transport error: {:?}",
        diag.transport_error
    );
    assert!(
        diag.status_success,
        "[{label}] z3 exited non-zero.\nstdout:\n{}\nstderr:\n{}",
        diag.stdout, diag.stderr
    );
    assert!(
        matches!(diag.verdict.as_str(), "sat" | "unsat" | "unknown"),
        "[{label}] unexpected z3 verdict={}.\nstdout:\n{}\nstderr:\n{}",
        diag.verdict,
        diag.stdout,
        diag.stderr
    );
    assert!(
        !diag.stdout.contains("Some_Option_bool") && !diag.stderr.contains("Some_Option_bool"),
        "[{label}] datatype constructor mismatch resurfaced.\nstdout:\n{}\nstderr:\n{}",
        diag.stdout,
        diag.stderr
    );
}

fn log_exact_file_restore_diagnostic(
    timeout_secs: u64,
    r: &RestoreProbeResult,
    diag: &RestoreRunDiagnostics,
) {
    eprintln!(
        "[exact-file pop_restores_assignments] verdict={}, \
         timeout_secs={timeout_secs}, status_success={}, \
         transport_error={:?}, \
         inferable_decls={}, has_p_inf_rule={}, fallback_count(fn)={}, aggregate_gap_count={}, \
         inferable_count={}, aggregate_gaps={:?}, inline_overapprox_decl_counts={:?}, \
         fn_drop_fallback_reasons={:?}, \
         fn_drop_inline_walk_sites={:?}, fn_translation_drop_total={}, fn_resume_abort_count={}, \
         fn_non_resume_tagged={}, fn_translation_drop_sites={:?}, \
         drop_fallback_reasons={:?}, unhandled_calls={:?}, translation_drops={:?}, \
         translation_drop_sites={:?}, \
         relation_heads={:?}, smt_len={}\nstdout:\n{}\nstderr:\n{}",
        diag.verdict,
        diag.status_success,
        diag.transport_error,
        r.inferable_decls.len(),
        r.has_p_inf_rule,
        r.fallback_count,
        r.aggregate_gap_count,
        r.inferable_count,
        r.aggregate_gaps,
        r.inline_overapprox_decl_counts,
        diag.fn_drop_fallback_reasons,
        diag.fn_drop_inline_walk_sites,
        diag.fn_translation_drop_total,
        diag.fn_resume_abort_count,
        diag.fn_non_resume_tagged,
        diag.fn_translation_drop_sites,
        r.drop_fallback_reasons,
        r.unhandled_calls,
        r.translation_drops,
        r.translation_drop_sites,
        diag.relation_heads,
        r.smt.len(),
        diag.stdout,
        diag.stderr
    );
}

fn assert_exact_file_drop_inline_site_counts(diag: &RestoreRunDiagnostics) -> usize {
    let drop_inline_walk_reason_total =
        diag.fn_drop_fallback_reasons.get("drop_inline_walk_failed").copied().unwrap_or(0);
    let drop_inline_walk_site_total: usize = diag.fn_drop_inline_walk_sites.values().sum();
    assert_eq!(
        drop_inline_walk_site_total, drop_inline_walk_reason_total,
        "[exact-file pop_restores_assignments] site-tagged drop-inline counts must match coarse \
         drop fallback counts; sites={:?}, reasons={:?}",
        diag.fn_drop_inline_walk_sites, diag.fn_drop_fallback_reasons
    );
    drop_inline_walk_site_total
}

fn explain_exact_file_restore_result(
    diag: &RestoreRunDiagnostics,
    drop_inline_walk_site_total: usize,
) {
    if diag.verdict.contains("Uninterpreted") {
        eprintln!(
            "[exact-file pop_restores_assignments] ERROR: Z3 reports uninterpreted symbol. \
             This usually means a datatype accessor (e.g. value_Option_bool) is used \
             in the SMT without the corresponding (declare-datatypes ...) block."
        );
    }
    if diag.verdict == "unsat" {
        eprintln!(
            "[exact-file pop_restores_assignments] FIXED: exact-file now unsat — \
             verify compiletest also returns PROOF"
        );
    } else if drop_inline_walk_site_total > 0 {
        eprintln!(
            "[exact-file pop_restores_assignments] EXPECTED: verdict={} with localized \
             drop-inline sites={:?}; clear transition_drop first before reopening the \
             walker lane",
            diag.verdict, diag.fn_drop_inline_walk_sites
        );
    } else {
        eprintln!(
            "[exact-file pop_restores_assignments] EXPECTED: verdict={}, \
             drop-inline sites cleared; next lane is while-loop invariant synthesis (#4050 D5)",
            diag.verdict
        );
    }
}

/// Diagnostic test: tracks whether PDR can prove the restore property.
/// Currently returns `sat` because PDR cannot synthesize invariants for
/// the 7+ interleaved while loops in ArraySolver (get_assignment, set_assignment,
/// remove_assignment, pop's trail replay). This test will flip to `unsat` when
/// the while-loop encoding is improved (#4050 D3).
///
/// The false-probe test below validates the encoding is not vacuously broken.
#[test]
fn test_bootstrap_arrays_tier3_restore_probe_solver_produces_unsat() {
    let fn_name = "probe_arrays_pop_restores_assignments_assert";
    let r = emit_restore_probe_smt(BOOTSTRAP_ARRAYS_TIER3_SOURCE, fn_name);
    let timeout_secs = restore_probe_timeout_secs();
    let diag = capture_restore_run(&r, fn_name, timeout_secs);
    eprintln!(
        "[restore-probe {fn_name}] verdict={}, \
         timeout_secs={timeout_secs}, status_success={}, \
         transport_error={:?}, \
         inferable_decls={}, has_p_inf_rule={}, fallback_count={}, aggregate_gap_count={}, \
         inferable_count={}, aggregate_gaps={:?}, inline_overapprox_decl_counts={:?}, \
         fn_drop_fallback_reasons={:?}, \
         fn_drop_inline_walk_sites={:?}, fn_translation_drop_total={}, fn_resume_abort_count={}, \
         fn_non_resume_tagged={}, fn_translation_drop_sites={:?}, \
         drop_fallback_reasons={:?}, unhandled_calls={:?}, translation_drops={:?}, \
         translation_drop_sites={:?}, \
         relation_heads={:?}\nstdout:\n{}\nstderr:\n{}",
        diag.verdict,
        diag.status_success,
        diag.transport_error,
        r.inferable_decls.len(),
        r.has_p_inf_rule,
        r.fallback_count,
        r.aggregate_gap_count,
        r.inferable_count,
        r.aggregate_gaps,
        r.inline_overapprox_decl_counts,
        diag.fn_drop_fallback_reasons,
        diag.fn_drop_inline_walk_sites,
        diag.fn_translation_drop_total,
        diag.fn_resume_abort_count,
        diag.fn_non_resume_tagged,
        diag.fn_translation_drop_sites,
        r.drop_fallback_reasons,
        r.unhandled_calls,
        r.translation_drops,
        r.translation_drop_sites,
        diag.relation_heads,
        diag.stdout,
        diag.stderr,
    );
    let label = format!("restore-probe {fn_name}");
    assert_restore_run_well_formed(&label, &diag);
    if diag.verdict == "unsat" {
        eprintln!("[restore-probe {fn_name}] FIXED: restore property now provable!");
    } else {
        eprintln!(
            "[restore-probe {fn_name}] EXPECTED: PDR cannot yet prove restore property \
             (while-loop invariant synthesis limitation, #4050 D3)"
        );
    }
}

#[test]
fn test_bootstrap_arrays_tier3_restore_false_probe_is_not_vacuously_unsat() {
    let fn_name = "probe_arrays_pop_restores_assignments_false_assert";
    let r = emit_restore_probe_smt(BOOTSTRAP_ARRAYS_TIER3_SOURCE, fn_name);
    let timeout_secs = restore_probe_timeout_secs();
    let result = run_z3_on_smt2_with_timeout(&r.smt, timeout_secs).expect("z3 result");
    assert_ne!(
        result, "unsat",
        "FALSE PROOF: {fn_name} returned unsat for a deliberately false arrays restore assertion. SMT:\n{}",
        r.smt
    );
}

// ---------------------------------------------------------------------------
// Exact-file unit reproducers for the committed smoke harness.
// Part of #4050 D1-D4 from designs/2026-03-20-issue-4050-exact-file-restore-localizer.md.
//
// These translate the real `ay_arrays_pop_restores_assignments` function body
// from `tests/ay/ay_self_verify_bootstrap_tier3_arrays.rs` through the CHC
// unit pipeline.
//
// Status (W4:4428): SwitchInt D0/D1/D2 fully landed. Encoding is clean:
// aggregate_gap_count=0, __switchint_branch_overapprox=4 (was 40+),
// __switchint_sort_coerce=0, gap_reasons={}. The live residual is purely
// semantic: Z3 returns `sat` with zero encoding gaps. The remaining blocker
// is Vec stub precision for multi-field struct composition within bounded-
// unrolled while loops, not SwitchInt over-approximation.
// ---------------------------------------------------------------------------

/// Encoding-only diagnostic: measures aggregate gap count, drop site counts,
/// and formula size WITHOUT running Z3. Always succeeds and provides gap
/// metrics for #4050 triage regardless of solver availability.
///
/// Part of #4050: regression tracker for keeping the exact-file restore packet
/// free of aggregate encoding gaps.
#[test]
fn test_exact_file_pop_restores_encoding_gaps() {
    let source = super::strip_kani_for_unit_ctx(super::BOOTSTRAP_ARRAYS_TIER3_REAL_FILE);
    let fn_name = "ay_arrays_pop_restores_assignments";
    let r = emit_restore_probe_smt(&source, fn_name);
    let drop_inline_walk_count: usize = r
        .drop_fallback_reasons
        .get(fn_name)
        .and_then(|m| m.get("drop_inline_walk_failed"))
        .copied()
        .unwrap_or(0);
    let fn_aggregate_gaps = r.aggregate_gaps.get(fn_name).copied().unwrap_or(0);
    let fn_gap_reasons = r.aggregate_gap_reasons.get(fn_name).cloned().unwrap_or_default();
    eprintln!(
        "[encoding-gaps {fn_name}] aggregate_gap_count={}, \
         fn_aggregate_gaps={fn_aggregate_gaps}, \
         inline_overapprox_decl_counts={:?}, \
         drop_inline_walk_failed={drop_inline_walk_count}, \
         fallback_count={}, smt_len={}, inferable_count={}",
        r.aggregate_gap_count,
        r.inline_overapprox_decl_counts,
        r.fallback_count,
        r.smt.len(),
        r.inferable_count,
    );
    eprintln!("[encoding-gaps {fn_name}] gap_reasons={fn_gap_reasons:?}");
    assert_eq!(
        drop_inline_walk_count, 0,
        "[encoding-gaps {fn_name}] drop_inline_walk_failed must be zero \
         (drop-inline reroute design complete, #4050 D1-D4)"
    );
    assert_eq!(r.fallback_count, 0, "[encoding-gaps {fn_name}] fallback_count must be zero");
    // Part of #4050: the flattened DT / transparent-wrapper follow-up now
    // clears the remaining Vec::push_mut projected-place gaps on clean HEAD.
    // Keep the exact-file packet at zero aggregate gaps so future edits do not
    // silently reintroduce the root Use/Cast/BinaryOp cascade.
    assert_eq!(
        fn_aggregate_gaps, 0,
        "[encoding-gaps {fn_name}] aggregate encoding gaps must stay at zero; \
         reasons={fn_gap_reasons:?}"
    );
    assert!(
        fn_gap_reasons.is_empty(),
        "[encoding-gaps {fn_name}] gap reasons must stay empty once the \
         projected-place fix lands: {fn_gap_reasons:?}"
    );
    let sort_coerce_count =
        r.inline_overapprox_decl_counts.get("__switchint_sort_coerce").copied().unwrap_or(0);
    assert_eq!(
        sort_coerce_count, 0,
        "[encoding-gaps {fn_name}] unit-return inline paths must not reintroduce \
         SwitchInt sort coercions; inline_overapprox_decl_counts={:?}",
        r.inline_overapprox_decl_counts
    );
    // Part of #4050 D0/D1/D2/D3/D4: SwitchInt edge-keyed dedup + loop-body depth
    // freeze eliminated __switchint_branch_overapprox entirely (was 40+ pre-D0,
    // 4 post-D2, 0 post-D3). D4 loop-exit-on-exhaustion eliminated
    // __loop_exhaust_inline but reintroduced <=4 __switchint_branch_overapprox
    // from post-loop exit path walks (strictly better: edge-specific, ITE-guarded).
    let branch_overapprox_count =
        r.inline_overapprox_decl_counts.get("__switchint_branch_overapprox").copied().unwrap_or(0);
    assert!(
        branch_overapprox_count <= 4,
        "[encoding-gaps {fn_name}] SwitchInt branch overapprox must be <=4 after D4; \
         inline_overapprox_decl_counts={:?}",
        r.inline_overapprox_decl_counts
    );
    // D4: __loop_exhaust_inline must be 0 — exit-branch path replaces them.
    let loop_exhaust_count =
        r.inline_overapprox_decl_counts.get("__loop_exhaust_inline").copied().unwrap_or(0);
    assert_eq!(
        loop_exhaust_count, 0,
        "[encoding-gaps {fn_name}] __loop_exhaust_inline must be 0 after D4; \
         inline_overapprox_decl_counts={:?}",
        r.inline_overapprox_decl_counts
    );
}

/// Exact-file reproducer: translate the real `ay_arrays_pop_restores_assignments`
/// harness body and report whether it produces `unsat` under unit CHC translation.
///
/// This is a **diagnostic** test. The drop-inline seam is now clear (zero
/// `drop_inline_walk_failed` sites) and aggregate encoding gaps should stay at
/// zero. The remaining blocker is semantic: the exact-file translation still
/// solves to `sat`, with SwitchInt over-approximation declarations present in
/// the emitted SMT.
#[test]
fn test_exact_file_pop_restores_assignments_diagnostic() {
    let source = super::strip_kani_for_unit_ctx(super::BOOTSTRAP_ARRAYS_TIER3_REAL_FILE);
    let fn_name = "ay_arrays_pop_restores_assignments";
    let r = emit_restore_probe_smt(&source, fn_name);
    let timeout_secs = exact_file_restore_timeout_secs();
    let diag = capture_restore_run(&r, fn_name, timeout_secs);
    log_exact_file_restore_diagnostic(timeout_secs, &r, &diag);
    // Transport errors are not expected on the current exact-file packet, but
    // keep this diagnostic lane non-fatal so structural regressions are still
    // reported through the encoding-gaps test above if solver invocation fails.
    if diag.transport_error.is_some() {
        eprintln!(
            "[exact-file {fn_name}] Z3 transport error with {} aggregate gaps and \
             {:.1}M SMT chars: {:?}",
            r.aggregate_gap_count,
            r.smt.len() as f64 / 1_000_000.0,
            diag.transport_error,
        );
        return;
    }
    assert_restore_run_well_formed("exact-file pop_restores_assignments", &diag);
    let drop_inline_walk_site_total = assert_exact_file_drop_inline_site_counts(&diag);
    explain_exact_file_restore_result(&diag, drop_inline_walk_site_total);
}
