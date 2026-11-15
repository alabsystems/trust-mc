// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The loop-contract retry.
//!
//! A loop-contract harness whose single run did not succeed gets ONE more
//! attempt, in a child driver process, that checks the same harness under the
//! same loop-contract semantics with what the first run may have lacked: the
//! CHC lane (a `--backend`/BMC-lane parent gets it too), the compound `a - b`
//! measure encoding (`TRUST_MC_COMPOUND_DECREASES`), and a per-query solver
//! budget of [`LANE_SOLVER_BUDGET_SECS`].
//!
//! ```text
//! first run (everything)  SUCCEEDS -> done, nothing else runs.
//!          ^ a passing harness is never re-adjudicated.
//!
//! otherwise, if the harness carries loop-contract obligations:
//!   retry lane: rule ON + CHC + compound measures, every check the parent checks
//!   SAFE iff the lane checked exactly this harness, proved every check, and its
//!   report contains the base-case and inductive-step obligations.
//! ```
//!
//! # Why the retry proves the user's properties with the loop contract ON
//!
//! Kani's loop contracts REPLACE the loop by its invariant: what the invariant
//! does not say about the state after the loop is havocked, so a valid but WEAK
//! invariant fails a harness whose concrete program is correct. That is Kani's
//! verdict and therefore the oracle: `tools/soundness-duals/lc_dual_weak.rs`
//! pins it (MUST FAIL), and Kani 0.67.0 fails `lc_dual_retry_weak.rs` too, where
//! the loop runs at most twice.
//!
//! Until AY alignment review round 3 this retry had TWO lanes (since
//! `5ee9a418c`): an obligations lane (rule ON, `--prove-safety-only`) and a
//! properties lane that proved the user's assertions on a bounded unroll with
//! the loop rule OFF (`TRUST_MC_NO_LOOP_RULE=1`, `--ay-chc-bounded-unroll`,
//! depths 2 and 3), on the argument that the user "never asked" for the
//! properties to be proven through the invariant. Kani disagrees, and the
//! properties lane turned exactly the weak-invariant harnesses Kani fails into
//! `VERIFICATION:- SUCCESSFUL`: measured on `lc_dual_retry_weak.rs` in both
//! lanes on main's bundle and the branch, once with a first-run counterexample
//! certified Genuine (`weak_bounded`) and once with a first run that failed on
//! the compound-measure encoding gap (`weak_compound`). So the properties lane
//! is gone, and the one remaining lane proves every check with the rule ON.
//!
//! # Why the lane is a separate PROCESS
//!
//! Not a style choice — an in-process second run is unsound here. The
//! unsoundness counters are PROCESS-GLOBAL (`snapshot_counters`), they
//! ACCUMULATE across harnesses (`absorb_fn_keyed_for_harness`), and the driver
//! demotes on `count > 0` over 17 categories (`demote_for_all_unsoundness`).
//! A second encoding trips markers the first never trips — and each one would
//! flip a CLEAN first-run PROOF into a FAILURE, manufacturing false positives.
//! A child process shares no counter state.
//!
//! # Soundness
//!
//! * The lane checks the harness it retries and no other. `--harness` is a
//!   SUBSTRING filter, so the lane passes `--exact` beside it, and the parent
//!   accepts a child only if its stdout names exactly this harness
//!   ([`lane_checked_exactly`]). Before review round 3 neither held: in a file
//!   where the retried harness's name is a substring of another harness's name,
//!   the child checked both, and the parent credited the other harness's
//!   SUCCESSFUL line to the retried one (`lc_dual_retry_substring.rs`: a
//!   certified Genuine counterexample printed SUCCESSFUL).
//! * The lane reports in the regular format: [`filter_parent_argv`] drops the
//!   parent's `--output-format`, `--quiet` and `--jobs`, so the per-check lines
//!   the merge reads are printed and the child solves its one harness on a
//!   one-thread pool (its memory envelope is not divided a second time).
//! * The merge requires the obligations to be PRESENT, not merely un-failed.
//!   "No failing checks" alone would let a lane whose obligations were dropped
//!   pass vacuously.
//! * The retry can move a verdict only toward SUCCESS, and only through
//!   [`merge`]: a lane that fails, times out or prints something unexpected
//!   costs the retry and leaves the first run's verdict standing. A lane that
//!   wrongly SUCCEEDS is a missed bug, which is why every condition above is a
//!   precondition of the upgrade rather than a diagnostic.
//! * The retry never overturns a first-run VACUITY verdict ([`FailClosedGate`]):
//!   V4's "every check is unreachable" and V5's unsatisfiable or missing cover
//!   fail a harness closed because it proved NOTHING, and "every check is
//!   unreachable" is also the shape a mis-encoded guard leaves. The child is
//!   another lane with its own encoding and its own (weaker) reachability
//!   evidence, so its proof of the same mis-encoded program is no answer to
//!   that verdict. Before AY alignment review round 2 the retry ran on any
//!   non-success: in the BMC lane a harness whose only check sat behind a
//!   mis-encoded float guard was failed closed by V4, proved by the CHC child,
//!   and printed `VERIFICATION:- SUCCESSFUL` where Kani fails
//!   (`v4_retry_f32_bug`, every output format since the terse fix let the
//!   merge read the child's obligations under `--jobs`).
//! * `TRUST_MC_LOOP_LANE=properties` still makes the compiler waive design 5
//!   (`loop_contracts::is_two_lane_properties_lane`). The retry never sets it
//!   now, but nothing authenticates the variable, so a process that has it set
//!   by hand never prints its success as a proof
//!   ([`demote_properties_lane_success`]).

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use crate::ay_parse::vc_artifact::{
    LOOP_CONTRACT_REPORT_MARKERS, LOOP_INVARIANT_BASE_REPORT_TEXT,
    LOOP_INVARIANT_STEP_REPORT_TEXT, artifact_has_loop_contract_obligations,
};
use crate::verification_result::{ValidationStatus, VerificationResult};

/// Set in every child so a lane can never spawn its own lanes.
pub(crate) const LANE_ENV: &str = "TRUST_MC_LOOP_LANE";

/// The value [`retry_lane_command`] gives [`LANE_ENV`]. The compiler reacts only
/// to `properties` (never set by the retry any more); the driver reads the
/// variable's presence ([`is_lane_child`]).
const RETRY_LANE_VALUE: &str = "obligations";

/// The engine GENERATION KNOBS the retry lane sets on its child
/// ([`retry_lane_command`]).
///
/// One list, so the route check below and the lane command cannot drift: a
/// knob added to the lane but not here would make the retry spawn a child the
/// Trustc route refuses, which is exactly the defect the check closes.
/// `lane_commands_set_exactly_the_lane_engine_env_knobs` reads the command
/// back and compares. (`TRUST_MC_NO_LOOP_RULE` left this list with the
/// properties lane in review round 3.)
pub(crate) const LANE_ENGINE_ENV_KNOBS: [&str; 1] = ["TRUST_MC_COMPOUND_DECREASES"];

/// A capability the ACTIVE COMPILER ROUTE does not have, reported by name.
///
/// Not an error and not a refusal: the run produced its verdict, and this says
/// which OPTIONAL step the route could not take. `tools/kani-domination`
/// records [`Self::marker`]'s payload per row (`route_limitations`), so a
/// measurement can tell "this route cannot do it yet, and here is its name"
/// from "this route is broken" — the distinction the T1 S7 acceptance chain
/// could not make while the lanes were spawned and refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RouteLimitation {
    /// Stable identifier. Never reworded: a measurement keys on it.
    pub id: &'static str,
    /// The route that lacks the capability.
    pub route: &'static str,
    /// One sentence a human can act on.
    pub detail: String,
}

/// The id [`route_limitation`] reports. Kept although the retry has one lane
/// now: measurements key on it.
pub(crate) const TWO_LANE_ROUTE_LIMITATION_ID: &str = "two-lane-loop-contract-retry";

impl RouteLimitation {
    /// The machine-readable line: `[AY:ROUTE_LIMITATION:<id> route=<route>]`.
    pub(crate) fn marker(&self) -> String {
        format!("[AY:ROUTE_LIMITATION:{} route={}]", self.id, self.route)
    }

    /// The human line, printed beside the marker.
    pub(crate) fn explanation(&self) -> String {
        format!("[AY:LOOP_TWO_LANE] not run on the {} compiler route: {}", self.route, self.detail)
    }
}

/// The limitation that stops the retry on this compiler route, if any.
///
/// The lane is a child `trust-mc-driver` process that INHERITS the parent's
/// argv — `--compiler-route` included — and sets [`LANE_ENGINE_ENV_KNOBS`] in
/// its child's environment. The Trustc route removes every `TRUST_MC_*` and
/// `AY_*` variable from the trustc it starts, so a knob set here would be
/// silently dropped and the lane would compile something other than what it
/// asked for; rather than do that, the route refuses the child outright
/// (`TrustcRouteError::EngineEnvKnobs`).
///
/// Spawning a lane that route will refuse costs the run its retry AND prints
/// the child's refusal inside the parent's diagnostic, where a reader takes it
/// for the PARENT refusing: measured on the T1 S7 acceptance chain, four CHC
/// loop-contract units with attested route markers and real verdicts were
/// scored `route error` for a refusal that happened in a child
/// (`decreases_binary_search`, `fixme_decreases_struct_field`,
/// `fixme_decreases_with_modifies`, `fixme_multi_dim_decreases`).
///
/// So do not start a lane this route will refuse. Not running the retry leaves
/// the first run's verdict standing — the conservative answer, and the same one
/// a route with no eligible harness gives. Carrying the knobs through the
/// engine-argument channel instead is engine work (S2,
/// `docs/trust-lane-trustc-route.md`); until it lands the route says by name
/// what it cannot do.
pub(crate) fn route_limitation(is_trustc: bool) -> Option<RouteLimitation> {
    if !is_trustc {
        return None;
    }
    Some(RouteLimitation {
        id: TWO_LANE_ROUTE_LIMITATION_ID,
        route: "trustc",
        detail: format!(
            "the lanes need engine environment knob(s) {}, and that route carries no \
             engine knob to the engine (the engine-argument channel does not encode them yet, \
             T1 S2). The single-lane verdict stands unchanged.",
            LANE_ENGINE_ENV_KNOBS.join(", ")
        ),
    })
}

/// Printed by a lane child, beside its `VERIFICATION:- SUCCESSFUL (UNVALIDATED)`,
/// when the off-pin-solver demotion (`crate::ay_binary`) is the ONLY thing that
/// kept it from a clean `VERIFICATION:- SUCCESSFUL`. See [`child_proved`].
pub(crate) const UNPINNED_DEMOTION_ONLY_MARKER: &str =
    "[AY:LOOP_TWO_LANE:success-unvalidated-only-by-unpinned-ay]";

/// Printed by a lane child when it starts checking a harness, whatever its
/// output format, followed by the harness's pretty name and `]`
/// ([`lane_harness_marker`]). The parent accepts the child only when this is
/// the one harness it checked ([`lane_checked_exactly`]).
pub(crate) const LANE_HARNESS_MARKER_PREFIX: &str = "[AY:LOOP_TWO_LANE:lane-harness:";

/// The line a lane child prints for `harness` ([`LANE_HARNESS_MARKER_PREFIX`]).
pub(crate) fn lane_harness_marker(harness: &str) -> String {
    format!("{LANE_HARNESS_MARKER_PREFIX}{harness}]")
}

/// Is this process a loop-contract retry child?
pub(crate) fn is_lane_child() -> bool {
    std::env::var(LANE_ENV).is_ok()
}

/// Does this process carry `TRUST_MC_LOOP_LANE=properties`?
///
/// The compiler reads the same variable (`loop_contracts::is_two_lane_properties_lane`)
/// and waives design 5 there: that process runs the loop on the legacy encoding
/// and never checks the loop contract. The retry no longer starts such a
/// process, and nothing authenticates the variable, so its success is never
/// printed as a proof ([`demote_properties_lane_success`]).
pub(crate) fn is_properties_lane_child() -> bool {
    std::env::var(LANE_ENV).is_ok_and(|lane| lane == "properties")
}

/// Printed beside every success a properties-lane process demotes
/// ([`demote_properties_lane_success`]).
pub(crate) const PROPERTIES_LANE_NOT_A_PROOF_MARKER: &str =
    "[AY:LOOP_TWO_LANE:properties-lane-success-is-not-a-proof]";

/// A process with `TRUST_MC_LOOP_LANE=properties` in its environment proves
/// the user properties with the loop contract unchecked (the compiler waives
/// design 5 and the legacy latch check there), so its success is not a proof.
/// Such a process, set by hand with no parent, used to print a clean
/// `VERIFICATION:- SUCCESSFUL` for a loop whose invariant breaks. So every
/// such success is demoted to `SUCCESSFUL (UNVALIDATED)`, like the
/// off-pin-solver demotion.
///
/// Returns the marker to print when a success was demoted.
pub(crate) fn demote_properties_lane_success(
    result: &mut VerificationResult,
    should_panic: bool,
    properties_lane: bool,
) -> Option<&'static str> {
    if !properties_lane
        || !crate::demotion::is_effective_manual_success(
            result.status,
            should_panic,
            result.failed_properties,
        )
    {
        return None;
    }
    result.validation_status = ValidationStatus::Unvalidated;
    Some(PROPERTIES_LANE_NOT_A_PROOF_MARKER)
}

/// Would `result` print exactly `VERIFICATION:- SUCCESSFUL` as it stands?
///
/// Checked just before the off-pin-solver demotion, so a lane child can say
/// that the demotion was the only reason its success is unvalidated. A
/// `should_panic` harness never prints the bare line, and a success already
/// unvalidated for another reason (a non-linear logic tier) is not clean.
pub(crate) fn clean_success_before_unpinned_demotion(
    result: &VerificationResult,
    should_panic: bool,
) -> bool {
    !should_panic
        && result.validation_status == ValidationStatus::Validated
        && crate::demotion::is_effective_manual_success(
            result.status,
            should_panic,
            result.failed_properties,
        )
}

/// Per-query solver budget handed to the lane, in seconds. This is NOT the
/// wall-clock cap (see `lane_budget`) — it is what the child passes on as
/// `--harness-timeout`, i.e. how long the solver may spend per query.
pub(crate) const LANE_SOLVER_BUDGET_SECS: u32 = 60;

/// The obligations that must be PRESENT in the lane's report for the merge to
/// trust it. The decreases clause is deliberately NOT required: a loop may
/// carry an invariant without a measure, and demanding one would make every
/// invariant-only harness ineligible.
///
/// These are the RENDERED report texts, not the artifact's internal message
/// stems: `obligations_present_in_report` greps a lane's stdout, and the
/// driver rewrites both obligations into Kani's own wording before printing
/// (`ay_parse::violation::apply_loop_contract_naming`). Keeping the internal
/// stems here would make the guard find nothing and refuse EVERY merge.
const REQUIRED_OBLIGATIONS: [&str; 2] =
    [LOOP_INVARIANT_BASE_REPORT_TEXT, LOOP_INVARIANT_STEP_REPORT_TEXT];

/// Outcome of the retry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TwoLaneOutcome {
    /// The lane proved every check of exactly this harness, obligations
    /// included: the harness is SAFE.
    Proved,
    /// The retry did not establish safety. The first run's verdict stands
    /// UNCHANGED.
    Inconclusive(String),
}

/// A first-run gate that failed the harness closed because the run proved
/// NOTHING, not because a check failed. The retry exists for a check a WEAK
/// loop invariant failed; it is never an answer to one of these (see the
/// module's soundness notes).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FailClosedGate {
    /// V4, unsatisfiable assumptions: the harness cannot run.
    UnsatAssumption,
    /// V4, dead checks: the harness runs and every check it emitted is
    /// unreachable, which is also what a mis-encoded guard leaves.
    DeadChecks,
    /// V5 under `--strict-vacuity`: a declared cover is unsatisfiable.
    UnsatisfiableCover,
    /// V5 conformance: a conformance harness reached no satisfied cover.
    Conformance,
}

impl FailClosedGate {
    /// The vacuity marker id the gate printed (`[AY:VACUOUS:<id>]`).
    pub(crate) fn id(self) -> &'static str {
        match self {
            Self::UnsatAssumption => "unsat-assumption",
            Self::DeadChecks => "dead-checks",
            Self::UnsatisfiableCover => "cover",
            Self::Conformance => "conformance",
        }
    }

    /// The line printed instead of starting the retry.
    pub(crate) fn refusal_marker(self) -> String {
        format!(
            "[AY:LOOP_TWO_LANE] not started: the first run failed closed as vacuous \
             ([AY:VACUOUS:{}]), which a proof in the retry lane cannot overturn; \
             the first run's verdict stands",
            self.id()
        )
    }
}

/// What the loop-contract retry does after the first run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RetryDecision {
    /// The first run succeeded, or the harness carries no loop contract.
    NotNeeded,
    /// The first run failed closed through a vacuity gate: say so, do not retry.
    Refused(FailClosedGate),
    /// Start the retry lane.
    Start,
}

/// Decide the retry. `first_run_succeeded` is the effective manual success of
/// the first run; `eligible` is [`harness_is_eligible`]; `gate` is the vacuity
/// gate that failed the first run closed, if one did.
pub(crate) fn retry_decision(
    first_run_succeeded: bool,
    eligible: bool,
    gate: Option<FailClosedGate>,
) -> RetryDecision {
    if first_run_succeeded || !eligible {
        return RetryDecision::NotNeeded;
    }
    match gate {
        Some(gate) => RetryDecision::Refused(gate),
        None => RetryDecision::Start,
    }
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

/// Parent flags the lane never inherits, each with how its value is written.
///
/// * The lane's own replacements: `--harness` (and `--exact`), which the lane
///   sets to exactly the retried harness; `--harness-timeout` and
///   `--target-dir`, which it sets to its own.
/// * Flags that change what the lane REPORTS, which the merge reads:
///   `--output-format` (`terse` leaves out the per-check lines the obligation
///   guard needs, and `--jobs` requires it) and `--quiet` (no verdict line at
///   all). Review round 3: under `--jobs N` every retry ended "obligations lane
///   is missing [...]".
/// * `--jobs`: the lane solves ONE harness, so a pool would only divide its
///   memory envelope a second time (review round 3: the child of a `--jobs 2`
///   parent took half of its cap, and at `--jobs 20` a twentieth).
/// * Output destinations the parent owns: `--export-smtlib`,
///   `--export-chc-comp`, `--sarif`, `--proof-summary-json`,
///   `--concrete-playback`. Measured for `--export-smtlib` in review round 3:
///   the file named by the parent held a lane child's query, written after the
///   parent's. (The row export, `TRUST_MC_CHC_ROW_EXPORT_DIR`, is an
///   environment variable; [`retry_lane_command`] moves it.)
/// * `--ay-chc-bounded-unroll` and `--unwind`: the lane proves the loop through
///   its contract, never on an unroll.
const DROPPED_FLAGS: [(&str, FlagValue); 16] = [
    ("--harness", FlagValue::Required),
    ("--exact", FlagValue::None),
    ("--harness-timeout", FlagValue::Required),
    ("--target-dir", FlagValue::Required),
    ("--output-format", FlagValue::Required),
    ("--quiet", FlagValue::None),
    ("-q", FlagValue::None),
    ("--jobs", FlagValue::OptionalNumber),
    ("-j", FlagValue::OptionalNumber),
    ("--export-smtlib", FlagValue::Required),
    ("--export-chc-comp", FlagValue::Required),
    ("--sarif", FlagValue::Required),
    ("--proof-summary-json", FlagValue::Required),
    ("--concrete-playback", FlagValue::Required),
    ("--ay-chc-bounded-unroll", FlagValue::None),
    ("--unwind", FlagValue::Required),
];

/// How a dropped flag's value is written after it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FlagValue {
    /// A boolean flag.
    None,
    /// `--flag value` or `--flag=value`.
    Required,
    /// `--jobs` / `-j`: bare, `--jobs 3`, `--jobs=3`, `-j 3`, `-j3`, `-j=3`.
    OptionalNumber,
}

impl FlagValue {
    /// Is `token` this flag with its value attached (`--flag=value`, `-j3`)?
    fn attached(self, flag: &str, token: &str) -> bool {
        let Some(rest) = token.strip_prefix(flag) else { return false };
        match self {
            FlagValue::None => false,
            FlagValue::Required => flag.starts_with("--") && rest.starts_with('='),
            FlagValue::OptionalNumber => {
                let value = match rest.strip_prefix('=') {
                    Some(value) => value,
                    // Only a short flag takes its value unseparated (`-j3`).
                    None if !flag.starts_with("--") => rest,
                    None => return false,
                };
                is_number(value)
            }
        }
    }
}

/// The parent's argv (without the executable) less every flag in
/// [`DROPPED_FLAGS`] and its value, in every spelling clap accepts for it.
pub(crate) fn filter_parent_argv(parent: impl IntoIterator<Item = String>) -> Vec<String> {
    let mut out = Vec::new();
    let mut tokens = parent.into_iter().peekable();
    'tokens: while let Some(token) = tokens.next() {
        for (flag, value) in DROPPED_FLAGS {
            if token == flag {
                match value {
                    FlagValue::None => {}
                    // The two-token form: drop the value too, or it is left
                    // orphaned and clap rejects the child with a bare positional.
                    FlagValue::Required => {
                        tokens.next();
                    }
                    FlagValue::OptionalNumber => {
                        if tokens.peek().is_some_and(|next| is_number(next)) {
                            tokens.next();
                        }
                    }
                }
                continue 'tokens;
            }
            if value.attached(flag, &token) {
                continue 'tokens;
            }
        }
        out.push(token);
    }
    out
}

fn is_number(token: &str) -> bool {
    !token.is_empty() && token.bytes().all(|b| b.is_ascii_digit())
}

/// Did a child driver run report a clean verification?
///
/// Deliberately strict: the summary line must be present AND positive. A child
/// that crashed, timed out, or printed nothing is NOT a proof. The merge also
/// requires the child to have checked exactly one harness, the retried one
/// ([`lane_checked_exactly`]), so this line cannot be another harness's.
///
/// `parent_accepted_unpinned_ay`: this process already accepted an off-pin `ay`
/// under `--allow-unpinned-ay`. The child inherits its argv and environment,
/// so it demotes its own success to `VERIFICATION:- SUCCESSFUL (UNVALIDATED)`,
/// and the strict line alone would turn every rescued harness into FAILED. That
/// line counts only when the child also printed
/// [`UNPINNED_DEMOTION_ONLY_MARKER`] (clean apart from the solver pin) and only
/// when the parent accepted the solver too, because the parent's own demotion in
/// `check_harness` is what re-marks the merged verdict. A success unvalidated
/// for any other reason still does not count.
pub(crate) fn child_proved(stdout: &str, parent_accepted_unpinned_ay: bool) -> bool {
    let has_line = |wanted: &str| stdout.lines().any(|l| l.trim() == wanted);
    has_line("VERIFICATION:- SUCCESSFUL")
        || (parent_accepted_unpinned_ay
            && has_line(UNPINNED_DEMOTION_ONLY_MARKER)
            && has_line("VERIFICATION:- SUCCESSFUL (UNVALIDATED)"))
}

/// Did the lane child check `harness` and nothing else?
///
/// Every condition is required, so no line of the child's stdout can belong to
/// another harness:
/// * exactly one [`lane_harness_marker`], naming `harness` (printed whatever
///   the output format);
/// * every `Checking harness ...` / `Autoharness: Checking function ...` line
///   names `harness`;
/// * exactly one `VERIFICATION:- ` line.
pub(crate) fn lane_checked_exactly(stdout: &str, harness: &str) -> Result<(), String> {
    let lines: Vec<&str> = stdout.lines().map(str::trim).collect();
    let markers: Vec<&str> =
        lines.iter().copied().filter(|l| l.starts_with(LANE_HARNESS_MARKER_PREFIX)).collect();
    let want = lane_harness_marker(harness);
    if markers != [want.as_str()] {
        return Err(format!(
            "the lane did not check exactly `{harness}` (harness markers {markers:?})"
        ));
    }
    // `check_harness`'s own start lines, for this harness.
    let this_harness = [
        format!("Checking harness {harness}..."),
        format!("Autoharness: Checking function {harness} against all possible inputs..."),
        format!(
            "Autoharness: Checking function {harness}'s contract against all possible inputs..."
        ),
    ];
    let other = lines.iter().copied().find(|l| {
        (l.starts_with("Checking harness ") || l.starts_with("Autoharness: Checking function "))
            && !this_harness.iter().any(|mine| mine == l)
    });
    if let Some(line) = other {
        return Err(format!("the lane also checked another harness: {line:?}"));
    }
    let verdicts = lines.iter().filter(|l| l.starts_with("VERIFICATION:- ")).count();
    if verdicts != 1 {
        return Err(format!("the lane printed {verdicts} verdict lines, not one"));
    }
    Ok(())
}

/// A private `--target-dir` for a lane.
///
/// The lane inherits the parent's `--target-dir` from argv, and compiling into
/// the parent's directory races the parent's own artifacts. Per HARNESS as well
/// as per process: under `--jobs N` several harnesses run their retries at
/// once, and a directory keyed only by the process made their lanes compile
/// into one directory together. MEASURED (review round 2,
/// `negative/loop_decreases_ignored.rs` at `--jobs 2`, on main's bundle and the
/// branch alike): a lane failed with `error: No such file or directory (os
/// error 2)`. A failed lane costs only the retry; the merge never reads a
/// failed lane as a proof.
fn lane_target_dir(tag: &str, harness: &str) -> String {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    harness.hash(&mut hasher);
    let base = std::env::temp_dir().join(format!(
        "trust-mc-lane-{tag}-{}-{:016x}",
        std::process::id(),
        hasher.finish()
    ));
    base.to_string_lossy().into_owned()
}

/// The environment variable the CHC row export reads (`call_ay::chc::row_export`).
const ROW_EXPORT_DIR_ENV: &str = "TRUST_MC_CHC_ROW_EXPORT_DIR";

/// The subdirectory of a harness's row export that holds its retry lane's own
/// export (review round 3). The lane used to inherit the parent's export
/// directory and overwrite the parent's `source.smt2` and `manifest.json` with
/// its own query and environment.
pub(crate) const RETRY_LANE_EXPORT_SUBDIR: &str = "loop-contract-retry";

/// Where the retry lane of `harness` exports its rows, under an export root:
/// `<root>/<harness>/loop-contract-retry` (the child then writes its own
/// `<harness>/` below that). `harness_dir` is the export's own directory name
/// for the harness (`row_export::file_component`).
pub(crate) fn retry_lane_export_root(root: &Path, harness_dir: &str) -> PathBuf {
    root.join(harness_dir).join(RETRY_LANE_EXPORT_SUBDIR)
}

/// The retry lane: every check of exactly `harness`, with the loop rule ON, in
/// the CHC lane, with the compound-measure encoding, in the regular output
/// format, on one thread.
///
/// `--ay-chc` is MANDATORY: the lane is the CHC lane whatever the parent ran.
/// `--prove-safety-only` is neither added nor dropped: the lane checks the
/// property set the parent checks.
///
/// `export_dir`: the lane's own row-export directory when the parent exports
/// (`retry_lane_export_root`); `None` removes the variable from the child.
pub(crate) fn retry_lane_command(harness: &str, export_dir: Option<&Path>) -> Option<Command> {
    let mut args = std::env::args();
    let exe = args.next()?;
    let mut argv = filter_parent_argv(args);
    argv.extend([
        "--ay-chc".to_string(),
        // `--harness` is a filter over PRETTY names and matches substrings;
        // `--exact` makes it this harness alone (review round 3).
        "--harness".to_string(),
        harness.to_string(),
        "--exact".to_string(),
        // The parent's per-harness budget is the child's PER-QUERY solver
        // budget. Inheriting a 15s parent starves this lane: MEASURED
        // `ay-chc inconclusive` at 15s, `SUCCESSFUL` in 44.2s at 60s.
        format!("--harness-timeout={LANE_SOLVER_BUDGET_SECS}s"),
        "--target-dir".to_string(),
        lane_target_dir("o", harness),
    ]);
    let mut cmd = Command::new(exe);
    cmd.args(argv);
    cmd.env(LANE_ENV, RETRY_LANE_VALUE);
    // The compound `a - b` measure lane: without it an `hi - lo` style measure
    // falls to the blanket fail-closed stub and the lane can never discharge
    // the ranking.
    cmd.env("TRUST_MC_COMPOUND_DECREASES", "1");
    match export_dir {
        Some(dir) => cmd.env(ROW_EXPORT_DIR_ENV, dir),
        None => cmd.env_remove(ROW_EXPORT_DIR_ENV),
    };
    Some(cmd)
}

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

/// Merge rule. SAFE requires ALL of:
///   * the lane checked exactly `harness` ([`lane_checked_exactly`]), AND
///   * it reported a clean verification (`lane_proved`, [`child_proved`]), AND
///   * its report CONTAINED the base-case and inductive-step obligations
///     (present, not merely un-failed — otherwise a lane whose obligations were
///     dropped would pass on memory-safety checks alone).
pub(crate) fn merge(harness: &str, lane_proved: bool, lane_stdout: &str) -> TwoLaneOutcome {
    if let Err(why) = lane_checked_exactly(lane_stdout, harness) {
        return TwoLaneOutcome::Inconclusive(why);
    }
    if !lane_proved {
        return TwoLaneOutcome::Inconclusive(
            "the retry lane did not prove every check with the loop contract on".to_string(),
        );
    }
    let present = obligations_present_in_report(lane_stdout);
    let missing: Vec<&str> =
        REQUIRED_OBLIGATIONS.iter().copied().filter(|r| !present.contains(r)).collect();
    if !missing.is_empty() {
        return TwoLaneOutcome::Inconclusive(format!(
            "obligations lane is missing {missing:?} — refusing a vacuous pass"
        ));
    }
    TwoLaneOutcome::Proved
}

/// Total wall-clock the retry may consume.
///
/// The parent's own watchdog is `harness_timeout * 5 + 5` = 80s for the corpus's
/// 15s budget. If the lane outruns that, the PARENT is killed and the row
/// degrades to a timeout — turning this feature into a regression on every
/// failing loop-contract harness. Measured end-to-end cost of the obligations
/// lane on the motivating row was 44.2s, so the cap has to leave the parent
/// room to finish reporting.
pub(crate) const RETRY_TOTAL_BUDGET: Duration = Duration::from_secs(70);

/// The least the lane can plausibly finish in: below it the retry is not
/// started, and says so.
pub(crate) const LANE_MIN_BUDGET: Duration = Duration::from_secs(10);

/// The lane may use whatever remains of `RETRY_TOTAL_BUDGET` AND of the
/// harness's own deadline (`harness_remaining`), never more. Returns `None`
/// when too little is left for a lane to plausibly finish, so the retry
/// stops instead of starting work it cannot complete. The harness deadline
/// is the binding one in practice: it sits inside the parent's watchdog
/// with headroom, so a retry that honours it ends by a typed verdict
/// instead of the watchdog's hard exit.
pub(crate) fn lane_budget(elapsed: Duration, harness_remaining: Duration) -> Option<Duration> {
    let remaining = RETRY_TOTAL_BUDGET.checked_sub(elapsed)?.min(harness_remaining);
    if remaining < LANE_MIN_BUDGET { None } else { Some(remaining) }
}

#[cfg(test)]
#[path = "loop_two_lane_tests.rs"]
mod tests;
