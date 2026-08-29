// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Two-lane retry for loop-contract harnesses.
//!
//! A loop contract asks two INDEPENDENT questions, and a single lane has to
//! answer both:
//!
//!   1. *Is the annotation valid?*  — invariant holds on entry (base case), is
//!      re-established by the body (inductive step), and the measure strictly
//!      decreases. These REQUIRE the abstraction; that is what the user asked
//!      to verify about their annotation.
//!   2. *Is the program correct?*   — assertions, memory safety, overflow,
//!      bounds. The user never asked for these to be proven *through* their
//!      invariant. They asked for them to be proven.
//!
//! Conflating them means a VALID but WEAK invariant makes a CORRECT program
//! report FAILED. That is the common case, not a corner: people write the
//! weakest invariant that is inductive. `decreases_binary_search` is simply
//! the row that exposed it — invariant `lo <= hi && hi <= arr.len()` is
//! perfectly inductive yet cannot carry `result == Some(2)`, because under the
//! abstraction the normal loop exit (`lo == hi` -> `None`) stays reachable.
//! PROVEN, not argued: `assert!(false)` after that loop fails in 0.63s.
//!
//! So answer each question with the strongest sound method:
//!
//! ```text
//! Lane 1 = today's run (rule ON, everything).  SUCCEEDS -> done, nothing else runs.
//!          ^ the no-regression net: a passing harness is never re-adjudicated.
//!
//! otherwise, if the harness carries loop-contract obligations:
//!   Lane O  rule ON  + --prove-safety-only     -> base / step / decreases
//!   Lane P  rule OFF + bounded unroll (d2, d3) -> assertions / memory safety
//!   SAFE iff Lane O discharges the obligations AND Lane P proves the properties.
//! ```
//!
//! # Why the lanes are separate PROCESSES
//!
//! Not a style choice — an in-process second lane is unsound here. The
//! unsoundness counters are PROCESS-GLOBAL (`snapshot_counters`), they
//! ACCUMULATE across harnesses (`absorb_fn_keyed_for_harness`), and the driver
//! demotes on `count > 0` over 17 categories (`demote_for_all_unsoundness`).
//! A second lane is by construction a coarser encoding, so it trips markers the
//! first lane never trips — and each one would flip a CLEAN first-lane PROOF
//! into a FAILURE, manufacturing false positives. A child process shares no
//! counter state.
//!
//! # Soundness
//!
//! * Lane P is FAIL-CLOSED under insufficient unrolling. Measured in this exact
//!   configuration: depth 1 on a loop needing 2 iterations reports FAILED
//!   ("CHC verification: error reachable"); depth 2 reports SUCCESSFUL. An
//!   insufficient depth can therefore never yield a false Safe — it can only
//!   cost us the retry.
//! * Lane O keeps the obligations: `--prove-safety-only` demotes
//!   `PropertyKind::Assertion` only, while the loop-contract obligations are
//!   registered through `hook_safety_check`. Measured: lane O reports the base
//!   case, the inductive step and the decreases checks, all SUCCESS.
//! * The merge requires the obligations to be PRESENT, not merely un-failed.
//!   "No failing checks" alone would let a lane whose obligations were dropped
//!   pass vacuously.

use std::path::Path;
use std::process::Command;
use std::time::Duration;

use crate::ay_parse::vc_artifact::{
    LOOP_CONTRACT_REPORT_MARKERS, LOOP_INVARIANT_BASE_REPORT_TEXT,
    LOOP_INVARIANT_STEP_REPORT_TEXT, artifact_has_loop_contract_obligations,
};

/// Set in every child so a lane can never spawn its own lanes.
pub(crate) const LANE_ENV: &str = "TRUST_MC_LOOP_LANE";

/// Unroll depths Lane P tries, in order. Measured cost on the motivating row:
/// d2 = 7.75-19.9s, d3 = 21.7s, d4 > 100s, d6 > 150s. Past d3 the encoding
/// blows the budget without ever answering, so deepening further only burns
/// wall-clock that the harness watchdog needs.
pub(crate) const LANE_P_DEPTHS: [u32; 2] = [2, 3];

/// Per-query solver budget handed to each lane, in seconds. This is NOT the
/// wall-clock cap (see `lane_budget`) — it is what the child passes on as
/// `--harness-timeout`, i.e. how long the solver may spend per query.
pub(crate) const LANE_SOLVER_BUDGET_SECS: u32 = 60;

/// The obligations that must be PRESENT in Lane O for the merge to trust it.
/// The decreases clause is deliberately NOT required: a loop may carry an
/// invariant without a measure, and demanding one would make every
/// invariant-only harness ineligible.
///
/// These are the RENDERED report texts, not the artifact's internal message
/// stems: `obligations_present_in_report` greps a lane's stdout, and the
/// driver rewrites both obligations into Kani's own wording before printing
/// (`ay_parse::violation::apply_loop_contract_naming`). Keeping the internal
/// stems here would make the guard find nothing and refuse EVERY merge.
const REQUIRED_OBLIGATIONS: [&str; 2] =
    [LOOP_INVARIANT_BASE_REPORT_TEXT, LOOP_INVARIANT_STEP_REPORT_TEXT];

/// Outcome of the two-lane retry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TwoLaneOutcome {
    /// Both lanes discharged what they own: the harness is SAFE.
    Proved,
    /// The retry did not establish safety. The first lane's verdict stands
    /// UNCHANGED — this never turns a verdict worse.
    Inconclusive(String),
}

/// Is this harness eligible for the retry?
///
/// Reads the RAW artifact for the loop-contract obligation MESSAGES.
/// Two traps this deliberately avoids:
/// * `kani_metadata`'s `has_loop_contracts` is hardwired `false`, so gating on
///   it yields a permanent no-op that still looks green.
/// * `load_chc_property_table` keeps only `error_p*` smt_vars, and every
///   loop-contract obligation is an `ay_violation_*` — so it returns EMPTY for
///   exactly the harnesses we want.
pub(crate) fn harness_is_eligible(vc_artifact: &Path) -> bool {
    if std::env::var(LANE_ENV).is_ok() {
        return false; // we ARE a lane; never recurse
    }
    artifact_has_loop_contract_obligations(vc_artifact)
}

/// Build one lane's argv from this process's own argv.
///
/// `extra` is appended; `drop_flags` are removed first so a caller-supplied
/// flag cannot conflict with the lane's own.
pub(crate) fn lane_argv(extra: &[String], drop_flags: &[&str]) -> Option<(String, Vec<String>)> {
    let mut it = std::env::args();
    let exe = it.next()?;
    let argv: Vec<String> = it.collect();
    let mut out: Vec<String> = Vec::with_capacity(argv.len() + extra.len());
    let mut skip_value = false;
    for a in argv {
        if skip_value {
            // The previous token was a dropped flag written in its two-token
            // form (`--flag value`); drop its value too or it is left orphaned
            // and clap rejects the child with a bare positional.
            skip_value = false;
            continue;
        }
        if let Some(d) = drop_flags.iter().find(|d| a == **d) {
            skip_value = TAKES_A_VALUE.contains(d);
            continue;
        }
        if drop_flags.iter().any(|d| a.starts_with(&format!("{d}="))) {
            continue;
        }
        out.push(a);
    }
    out.extend_from_slice(extra);
    Some((exe, out))
}

/// Dropped flags that carry a separate value token.
const TAKES_A_VALUE: [&str; 4] =
    ["--harness-timeout", "--harness", "--unwind", "--target-dir"];

/// Did a child driver run report a clean verification?
///
/// Deliberately strict: the summary line must be present AND positive. A child
/// that crashed, timed out, or printed nothing is NOT a proof.
pub(crate) fn child_proved(stdout: &str) -> bool {
    stdout.lines().any(|l| l.trim() == "VERIFICATION:- SUCCESSFUL")
}

/// Lane O: prove the CONTRACT OBLIGATIONS with the rule ON and user assertions
/// demoted to non-obligations, so the lane is not dragged down by the very
/// property the weak invariant cannot carry.
/// A private `--target-dir` for a lane.
///
/// The lanes run CONCURRENTLY and both inherit the parent's `--target-dir`
/// from argv. Sharing one directory makes two compilations race: MEASURED, the
/// obligations lane still reported SUCCESSFUL but its check list came back
/// without the loop-contract obligations, so the vacuity guard correctly
/// refused the merge. Isolate them.
fn lane_target_dir(tag: &str) -> String {
    let base = std::env::temp_dir().join(format!("trust-mc-lane-{tag}-{}", std::process::id()));
    base.to_string_lossy().into_owned()
}

pub(crate) fn lane_o_command(harness: &str) -> Option<Command> {
    let extra = vec![
        "--ay-chc".to_string(),
        "--prove-safety-only".to_string(),
        "--harness".to_string(),
        harness.to_string(),
        // The parent's per-harness budget is the child's PER-QUERY solver
        // budget. Inheriting a 15s parent starves this lane: MEASURED
        // `ay-chc inconclusive` at 15s, `SUCCESSFUL` in 44.2s at 60s.
        format!("--harness-timeout={LANE_SOLVER_BUDGET_SECS}s"),
        "--target-dir".to_string(),
        lane_target_dir("o"),
    ];
    // `--ay-chc-bounded-unroll` / `--unwind` belong to Lane P only.
    let (exe, argv) = lane_argv(
        &extra,
        &[
            "--ay-chc-bounded-unroll",
            "--unwind",
            "--harness",
            "--harness-timeout",
            "--target-dir",
        ],
    )?;
    let mut cmd = Command::new(exe);
    cmd.args(argv);
    cmd.env(LANE_ENV, "obligations");
    // The compound `a - b` measure lane: without it an `hi - lo` style measure
    // falls to the blanket fail-closed stub and Lane O can never discharge the
    // ranking it is responsible for.
    cmd.env("TRUST_MC_COMPOUND_DECREASES", "1");
    Some(cmd)
}

/// Lane P: prove the USER PROPERTIES precisely — rule off, loop unrolled to
/// `depth` with the unwinding assertion left ON (that is what keeps an
/// insufficient depth fail-closed).
///
/// `--ay-chc` is MANDATORY: `--ay-chc-bounded-unroll` is rejected by argument
/// validation without it, and the parent's argv does not necessarily carry it.
/// Omitting it makes every retry exit 2 at clap — a silent permanent no-op.
pub(crate) fn lane_p_command(harness: &str, depth: u32) -> Option<Command> {
    let extra = vec![
        "--ay-chc".to_string(),
        "--ay-chc-bounded-unroll".to_string(),
        "--unwind".to_string(),
        depth.to_string(),
        "--harness".to_string(),
        harness.to_string(),
        format!("--harness-timeout={LANE_SOLVER_BUDGET_SECS}s"),
        "--target-dir".to_string(),
        lane_target_dir("p"),
    ];
    let (exe, argv) = lane_argv(
        &extra,
        &["--prove-safety-only", "--harness", "--harness-timeout", "--target-dir"],
    )?;
    let mut cmd = Command::new(exe);
    cmd.args(argv);
    cmd.env(LANE_ENV, "properties");
    cmd.env("TRUST_MC_NO_LOOP_RULE", "1");
    cmd.env("TRUST_MC_COMPOUND_DECREASES", "1");
    Some(cmd)
}

/// Merge rule. SAFE requires ALL of:
///   * Lane O reported a clean verification, AND
///   * Lane O actually CONTAINED the base-case and inductive-step obligations
///     (present, not merely un-failed — otherwise a lane whose obligations were
///     dropped would pass on memory-safety checks alone), AND
///   * Lane P reported a clean verification at some tried depth.
/// Which required obligations does this lane's REPORT actually contain?
///
/// Read from the lane's own stdout, not from an artifact path: the lane runs in
/// a child process with its own out-dir, so the parent's artifact describes the
/// PARENT's run. Pointing the vacuity guard at the parent's artifact makes it
/// refuse every merge — measured.
pub(crate) fn obligations_present_in_report(stdout: &str) -> Vec<&'static str> {
    let mut found: Vec<&'static str> = Vec::new();
    for [canonical, also] in LOOP_CONTRACT_REPORT_MARKERS {
        if (stdout.contains(canonical) || stdout.contains(also)) && !found.contains(&canonical) {
            found.push(canonical);
        }
    }
    found
}

pub(crate) fn merge(
    lane_o_proved: bool,
    lane_o_stdout: &str,
    lane_p_proved: bool,
) -> TwoLaneOutcome {
    if !lane_o_proved {
        return TwoLaneOutcome::Inconclusive(
            "obligations lane did not discharge the loop contract".to_string(),
        );
    }
    let present = obligations_present_in_report(lane_o_stdout);
    let missing: Vec<&str> =
        REQUIRED_OBLIGATIONS.iter().copied().filter(|r| !present.contains(r)).collect();
    if !missing.is_empty() {
        return TwoLaneOutcome::Inconclusive(format!(
            "obligations lane is missing {missing:?} — refusing a vacuous pass"
        ));
    }
    if !lane_p_proved {
        return TwoLaneOutcome::Inconclusive(
            "properties lane did not prove the user properties at any tried depth".to_string(),
        );
    }
    TwoLaneOutcome::Proved
}

/// Wall-clock a single lane may consume.
/// Total wall-clock the WHOLE retry may consume.
///
/// The parent's own watchdog is `harness_timeout * 5 + 5` = 80s for the corpus's
/// 15s budget. If the lanes together outrun that, the PARENT is killed and the
/// row degrades to a timeout — turning this feature into a regression on every
/// failing loop-contract harness. Measured end-to-end cost on the motivating
/// row is 66.3s (Lane O 44.2s + Lane P d2 ~20s), so the cap has to leave the
/// parent room to finish reporting.
pub(crate) const RETRY_TOTAL_BUDGET: Duration = Duration::from_secs(70);

/// A lane may use whatever remains of `RETRY_TOTAL_BUDGET`, never more.
/// Returns `None` when too little is left for a lane to plausibly finish, so
/// the retry stops instead of starting work it cannot complete.
pub(crate) fn lane_budget(elapsed: Duration) -> Option<Duration> {
    let remaining = RETRY_TOTAL_BUDGET.checked_sub(elapsed)?;
    if remaining < Duration::from_secs(10) { None } else { Some(remaining) }
}

#[cfg(test)]
#[path = "loop_two_lane_tests.rs"]
mod tests;
