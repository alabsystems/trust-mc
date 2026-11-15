// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use std::io::Write;

fn artifact_with(messages: &[&str]) -> tempfile::NamedTempFile {
    let props: Vec<String> = messages
        .iter()
        .enumerate()
        .map(|(i, m)| {
            format!(
                r#"{{"id":{{"id":{i},"description":null}},"kind":"assertion","message":"{m}","smt_var":"ay_violation_kani_assert_{i}"}}"#
            )
        })
        .collect();
    let body = format!(
        r#"{{"version":{{"major":0,"minor":1,"patch":0}},"mode":"bmc","harness":{{"mangled_name":"h","pretty_name":"h"}},"properties":[{}]}}"#,
        props.join(",")
    );
    let mut f = tempfile::NamedTempFile::new().unwrap();
    f.write_all(body.as_bytes()).unwrap();
    f.flush().unwrap();
    f
}

/// The obligations are `kind: assertion` with `ay_violation_*` smt_vars, so
/// only the MESSAGE identifies them. This is the case that made a
/// property-kind or `error_p*` based detector a silent no-op.
#[test]
fn eligibility_matches_on_message_not_kind() {
    let f = artifact_with(&[
        // The message as the instrumentation actually stamps it: stem plus the
        // `(loop N)` suffix the driver turns into Kani's own wording.
        "loop invariant base case: invariant must hold on loop entry (loop 0)",
        "assertion failed: result == Some(2)",
    ]);
    assert!(artifact_has_loop_contract_obligations(f.path()));
}

#[test]
fn eligibility_false_without_loop_contract_messages() {
    let f = artifact_with(&["assertion failed: x == 2", "attempt to add with overflow"]);
    assert!(!artifact_has_loop_contract_obligations(f.path()));
}

/// A missing artifact must mean "do not retry", never a changed verdict.
#[test]
fn eligibility_false_for_missing_artifact() {
    assert!(!artifact_has_loop_contract_obligations(Path::new("/nonexistent/x.vc.json")));
}

/// A lane REPORT, so the obligations appear in their rendered Kani form
/// (`apply_loop_contract_naming`), not as the artifact's internal stems, as a
/// retry child prints it for harness `h`.
const O_REPORT: &str = "[AY:LOOP_TWO_LANE:lane-harness:h]\nChecking harness h...\nCheck 1: h.loop_invariant_base.1\n - Description: \"Check invariant before entry for loop h.0\"\nCheck 2: h.loop_invariant_step.1\n - Description: \"Check invariant after step for loop h.0\"\nVERIFICATION:- SUCCESSFUL\n";

#[test]
fn merge_proves_when_the_lane_discharges_every_check_of_this_harness() {
    assert_eq!(merge("h", true, O_REPORT), TwoLaneOutcome::Proved);
}

/// The vacuity guard: a lane that reports "no failures" but never CONTAINED the
/// obligations must not be trusted.
#[test]
fn merge_refuses_a_vacuous_obligations_lane() {
    let report = "[AY:LOOP_TWO_LANE:lane-harness:h]\nCheck 1: h.assertion.0\n - Description: \"attempt to add with overflow\"\nVERIFICATION:- SUCCESSFUL\n";
    match merge("h", true, report) {
        TwoLaneOutcome::Inconclusive(why) => assert!(why.contains("vacuous"), "{why}"),
        other => panic!("expected refusal, got {other:?}"),
    }
}

/// Base case present but inductive step absent is still vacuous.
#[test]
fn merge_requires_both_base_and_step() {
    let report = "[AY:LOOP_TWO_LANE:lane-harness:h]\nDescription: \"Check invariant before entry for loop h.0\"\nVERIFICATION:- SUCCESSFUL\n";
    assert!(matches!(merge("h", true, report), TwoLaneOutcome::Inconclusive(_)));
}

#[test]
fn merge_inconclusive_when_the_lane_fails() {
    assert!(matches!(merge("h", false, O_REPORT), TwoLaneOutcome::Inconclusive(_)));
}

/// Review round 3, finding 1, with the child's own stdout
/// (`twin_substring_probe.rs`, `--harness skip_bug` without `--exact`): the
/// filter matched `skip_bug_twin_ok` too, the twin printed SUCCESSFUL, and
/// the parent credited it to `skip_bug`, whose own run was VACUOUS. Every
/// line of that stdout is kept below, with the harness markers a child now
/// prints; each guard alone refuses it.
#[test]
fn a_child_that_checked_another_harness_is_never_credited() {
    let twin = "\
Checking harness skip_bug_twin_ok...
[AY:PROOF] CHC verification: property proven (false error obligation)

RESULTS:
Check 1: skip_bug_twin_ok.loop_invariant_base.0
\t - Status: UNREACHABLE
\t - Description: \"Check invariant before entry for loop skip_bug_twin_ok.0\"

Check 2: skip_bug_twin_ok.loop_invariant_step.1
\t - Status: UNREACHABLE
\t - Description: \"Check invariant after step for loop skip_bug_twin_ok.0\"

VERIFICATION:- SUCCESSFUL
";
    let own = "\
Checking harness skip_bug...
[AY:VACUOUS:unsat-assumption] skip_bug: every check is provably UNREACHABLE
Check 1: skip_bug.loop_invariant_base.0
\t - Description: \"Check invariant before entry for loop skip_bug.0\"
Check 2: skip_bug.loop_invariant_step.1
\t - Description: \"Check invariant after step for loop skip_bug.0\"
VERIFICATION:- VACUOUS (proof discharged under unsatisfiable assumptions — nothing verified)
";
    let marker = |h: &str| lane_harness_marker(h);
    // As the old child printed it, and as a child printing markers would.
    let old_child = format!("{twin}{own}");
    let with_markers =
        format!("{}\n{twin}{}\n{own}", marker("skip_bug_twin_ok"), marker("skip_bug"));
    for stdout in [&old_child, &with_markers] {
        // `child_proved` alone reads any SUCCESSFUL line: exactly the defect.
        assert!(child_proved(stdout, false));
        match merge("skip_bug", child_proved(stdout, false), stdout) {
            TwoLaneOutcome::Inconclusive(why) => assert!(why.contains("skip_bug"), "{why}"),
            other => panic!("another harness's success was credited: {other:?}"),
        }
    }
    // Only the twin, even if it were the one harness checked: not `skip_bug`.
    let twin_only = format!("{}\n{twin}", marker("skip_bug_twin_ok"));
    assert!(matches!(merge("skip_bug", true, &twin_only), TwoLaneOutcome::Inconclusive(_)));
    // The right marker, but another harness's start line: refused.
    let spliced = format!("{}\n{twin}", marker("skip_bug"));
    assert!(lane_checked_exactly(&spliced, "skip_bug").is_err());
    // The right marker and start line, but two verdicts: refused.
    let two_verdicts = format!("{}\n{own}VERIFICATION:- SUCCESSFUL\n", marker("skip_bug"));
    assert!(lane_checked_exactly(&two_verdicts, "skip_bug").is_err());
    // No marker at all (a child that never reached `check_harness`): refused.
    assert!(lane_checked_exactly("VERIFICATION:- SUCCESSFUL\n", "skip_bug").is_err());
    // Exactly `skip_bug`: accepted by the scope guard, refused by the verdict.
    let exact = format!("{}\n{own}", marker("skip_bug"));
    assert_eq!(lane_checked_exactly(&exact, "skip_bug"), Ok(()));
    assert!(!child_proved(&exact, false));
}

/// Autoharness start lines name the function, and count as this harness.
#[test]
fn an_autoharness_start_line_for_this_harness_is_accepted() {
    for start in [
        "Autoharness: Checking function f against all possible inputs...",
        "Autoharness: Checking function f's contract against all possible inputs...",
    ] {
        let stdout = format!("{}\n{start}\nVERIFICATION:- SUCCESSFUL\n", lane_harness_marker("f"));
        assert_eq!(lane_checked_exactly(&stdout, "f"), Ok(()), "{start}");
        let other = stdout.replace("function f", "function g");
        assert!(lane_checked_exactly(&other, "f").is_err(), "{start}");
    }
}

/// Only an explicit positive summary line counts as a proof: a child that
/// crashed, timed out, or printed nothing must not be read as success.
#[test]
fn child_proved_requires_the_positive_summary_line() {
    for unpinned in [false, true] {
        assert!(child_proved("blah\nVERIFICATION:- SUCCESSFUL\n", unpinned));
        assert!(!child_proved("VERIFICATION:- FAILED\n", unpinned));
        assert!(!child_proved("VERIFICATION:- INCONCLUSIVE\n", unpinned));
        assert!(!child_proved("", unpinned));
        assert!(!child_proved(
            "error: The --ay-chc-bounded-unroll option requires --ay-chc.\n",
            unpinned
        ));
    }
}

/// Under --allow-unpinned-ay a lane child demotes its own success, so the
/// strict line never appears. The demoted line counts only when the child says
/// the solver pin was its only caveat AND the parent accepted the same solver
/// (the parent's demotion is what re-marks the merged verdict).
#[test]
fn child_proved_accepts_a_success_unvalidated_only_by_the_solver_pin() {
    let marker =
        "[AY:SOLVER_PIN_MISMATCH:found=dd4de9e94e0bb94a458641c7e5aa814c8aeadf59:pin=unavailable]";
    let demoted = format!(
        "{marker}\n{UNPINNED_DEMOTION_ONLY_MARKER}\n\nVERIFICATION:- SUCCESSFUL (UNVALIDATED)\n"
    );
    assert!(child_proved(&demoted, true));
    // The parent never accepted an off-pin solver: nothing would re-mark it.
    assert!(!child_proved(&demoted, false));
    // Unvalidated for another reason as well (no lane marker): not a proof.
    let also_tier_b = format!("{marker}\n\nVERIFICATION:- SUCCESSFUL (UNVALIDATED)\n");
    assert!(!child_proved(&also_tier_b, true));
    // The lane marker never stands in for the verdict line.
    assert!(!child_proved(
        &format!("{UNPINNED_DEMOTION_ONLY_MARKER}\nVERIFICATION:- FAILED\n"),
        true
    ));
    assert!(!child_proved(UNPINNED_DEMOTION_ONLY_MARKER, true));
    // A should_panic success carries a suffix and was never a lane proof.
    assert!(!child_proved(
        &format!(
            "{UNPINNED_DEMOTION_ONLY_MARKER}\nVERIFICATION:- SUCCESSFUL (UNVALIDATED) (encountered one or more panics as expected)\n"
        ),
        true
    ));
}

/// A properties-lane success is never a proof: the compiler waives design 5
/// there, so a hand-set `TRUST_MC_LOOP_LANE=properties` used to print a clean
/// SUCCESSFUL for a loop whose invariant breaks. Every such success is demoted;
/// nothing else is touched.
#[test]
fn a_properties_lane_success_is_demoted_and_nothing_else() {
    use crate::test_support::test_result;
    use crate::verification_result::{FailedProperties, ValidationStatus, VerificationStatus};

    let mut success = test_result(VerificationStatus::Success, FailedProperties::None);
    assert_eq!(
        demote_properties_lane_success(&mut success, false, true),
        Some(PROPERTIES_LANE_NOT_A_PROOF_MARKER)
    );
    assert_eq!(success.validation_status, ValidationStatus::Unvalidated);

    let mut panicked_as_expected =
        test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
    assert!(demote_properties_lane_success(&mut panicked_as_expected, true, true).is_some());
    assert_eq!(panicked_as_expected.validation_status, ValidationStatus::Unvalidated);

    let mut failure = test_result(VerificationStatus::Failure, FailedProperties::Other);
    assert_eq!(demote_properties_lane_success(&mut failure, false, true), None);
    assert_eq!(failure.validation_status, ValidationStatus::Validated);

    // Not the properties lane: untouched.
    let mut other_lane = test_result(VerificationStatus::Success, FailedProperties::None);
    assert_eq!(demote_properties_lane_success(&mut other_lane, false, false), None);
    assert_eq!(other_lane.validation_status, ValidationStatus::Validated);
}

/// The lane marker is printed only for a result that would otherwise have
/// printed exactly `VERIFICATION:- SUCCESSFUL`.
#[test]
fn only_a_clean_validated_success_is_clean_before_the_unpinned_demotion() {
    use crate::test_support::test_result;
    use crate::verification_result::{FailedProperties, ValidationStatus, VerificationStatus};

    let success = test_result(VerificationStatus::Success, FailedProperties::None);
    assert!(clean_success_before_unpinned_demotion(&success, false));

    let mut tier_b = test_result(VerificationStatus::Success, FailedProperties::None);
    tier_b.validation_status = ValidationStatus::Unvalidated;
    assert!(!clean_success_before_unpinned_demotion(&tier_b, false));

    let failure = test_result(VerificationStatus::Failure, FailedProperties::Other);
    assert!(!clean_success_before_unpinned_demotion(&failure, false));

    let panicked_as_expected =
        test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
    assert!(!clean_success_before_unpinned_demotion(&panicked_as_expected, true));
}

fn args_of(cmd: &std::process::Command) -> Vec<String> {
    cmd.get_args().map(|a| a.to_string_lossy().into_owned()).collect()
}

/// The lane is the CHC lane, checks exactly the retried harness, and proves
/// with the loop contract ON: no bounded unroll, no `TRUST_MC_NO_LOOP_RULE`
/// (review round 3: the properties lane that did both printed Kani's
/// weak-invariant failures SUCCESSFUL, `lc_dual_retry_weak.rs`).
#[test]
fn the_retry_lane_is_exact_and_proves_with_the_loop_contract_on() {
    let cmd = retry_lane_command("h", None).expect("argv");
    let args = args_of(&cmd);
    assert!(args.contains(&"--ay-chc".to_string()), "{args:?}");
    let at = args.iter().position(|a| a == "--harness").expect("--harness");
    assert_eq!(args[at + 1], "h");
    assert!(args.contains(&"--exact".to_string()), "{args:?}");
    assert_eq!(args.iter().filter(|a| *a == "--harness").count(), 1, "{args:?}");
    assert_eq!(args.iter().filter(|a| *a == "--exact").count(), 1, "{args:?}");
    assert!(!args.contains(&"--prove-safety-only".to_string()), "{args:?}");
    assert!(!args.contains(&"--ay-chc-bounded-unroll".to_string()), "{args:?}");
    assert!(!args.contains(&"--unwind".to_string()), "{args:?}");
    assert!(
        !cmd.get_envs().any(|(k, v)| k == "TRUST_MC_NO_LOOP_RULE" && v.is_some()),
        "the retry lane must keep the loop rule on"
    );
}

/// Every lane must be stamped so it cannot spawn lanes of its own.
#[test]
fn the_retry_lane_sets_the_recursion_guard() {
    let cmd = retry_lane_command("h", None).unwrap();
    let stamped = cmd.get_envs().any(|(k, v)| k == LANE_ENV && v.is_some_and(|v| !v.is_empty()));
    assert!(stamped, "lane is missing the {LANE_ENV} guard");
}

fn strings(tokens: &[&str]) -> Vec<String> {
    tokens.iter().map(|t| (*t).to_string()).collect()
}

/// Review round 3, findings 3 and 4: the lane inherited `--jobs N` (dividing
/// its memory envelope by N again) and `--output-format=terse` (no per-check
/// lines, so every merge under `--jobs` ended "missing [...]"). Every spelling
/// clap accepts is dropped, with its value and nothing else.
#[test]
fn the_parent_argv_filter_drops_every_spelling_of_the_dropped_flags() {
    let kept = ["unit.rs", "-Z", "unstable-options", "-Z", "loop-contracts", "--ay-chc"];
    for dropped in [
        &["--jobs"][..],
        &["--jobs", "3"],
        &["--jobs=3"],
        &["-j"],
        &["-j", "20"],
        &["-j20"],
        &["-j=2"],
        &["--output-format", "terse"],
        &["--output-format=terse"],
        &["--output-format=old"],
        &["-q"],
        &["--quiet"],
        &["--exact"],
        &["--harness", "a"],
        &["--harness=a"],
        &["--harness-timeout", "30s"],
        &["--harness-timeout=30s"],
        &["--target-dir", "/t"],
        &["--target-dir=/t"],
        &["--export-smtlib", "q.smt2"],
        &["--export-smtlib=q.smt2"],
        &["--export-chc-comp", "c.smt2"],
        &["--sarif", "o.sarif"],
        &["--proof-summary-json", "p.json"],
        &["--concrete-playback", "inplace"],
        &["--concrete-playback=print"],
        &["--ay-chc-bounded-unroll"],
        &["--unwind", "4"],
        &["--unwind=4"],
    ] {
        for at in 0..=kept.len() {
            let mut argv = strings(&kept);
            for (i, token) in dropped.iter().enumerate() {
                argv.insert(at + i, (*token).to_string());
            }
            assert_eq!(filter_parent_argv(argv.clone()), strings(&kept), "{argv:?}");
        }
    }
}

/// Only a number after a bare `--jobs` / `-j` is its value; anything else is
/// the next argument and stays. Flags that merely share a prefix stay too.
#[test]
fn the_parent_argv_filter_keeps_what_is_not_a_dropped_flag() {
    assert_eq!(filter_parent_argv(strings(&["-j", "unit.rs"])), strings(&["unit.rs"]));
    assert_eq!(filter_parent_argv(strings(&["--jobs", "--ay-chc"])), strings(&["--ay-chc"]));
    for kept in [
        &["--jobsx"][..],
        &["--harnessx", "v"],
        &["--prove-safety-only"],
        &["--default-unwind", "3"],
        &["--allow-vacuous"],
        &["-Z", "loop-contracts"],
        &["--ay-chc-engine=pdr"],
        &["--output-into-files"],
    ] {
        assert_eq!(filter_parent_argv(strings(kept)), strings(kept), "{kept:?}");
    }
}

/// Review round 2's `--jobs 2` lane children carried `--jobs=3
/// --output-format=terse` from the parent; the lane's own argv never does.
#[test]
fn the_retry_lane_argv_never_carries_jobs_output_format_or_quiet() {
    let parent = strings(&[
        "unit.rs",
        "--jobs=3",
        "--output-format=terse",
        "-q",
        "--harness",
        "skip_bug",
        "-Z",
        "loop-contracts",
    ]);
    let argv = filter_parent_argv(parent);
    for token in &argv {
        assert!(
            !(token.starts_with("--jobs")
                || token.starts_with("-j")
                || token.starts_with("--output-format")
                || token == "-q"
                || token == "--quiet"
                || token == "--harness"
                || token == "skip_bug"),
            "{argv:?}"
        );
    }
    let cmd = retry_lane_command("h", None).expect("argv");
    let args = args_of(&cmd);
    assert!(
        !args.iter().any(|a| a.starts_with("--jobs")
            || a == "-j"
            || a.starts_with("--output-format")
            || a == "-q"
            || a == "--quiet"),
        "{args:?}"
    );
}

/// Review round 3, finding 2: the lane inherited the parent's
/// `TRUST_MC_CHC_ROW_EXPORT_DIR`. It now gets its own directory below the
/// parent's harness directory, or none at all.
#[test]
fn the_retry_lane_exports_below_the_parent_or_not_at_all() {
    let root = Path::new("/exports");
    let lane_root = retry_lane_export_root(root, "demo__h");
    assert_eq!(lane_root, Path::new("/exports/demo__h/loop-contract-retry"));
    let cmd = retry_lane_command("demo::h", Some(&lane_root)).unwrap();
    let export = cmd
        .get_envs()
        .find(|(k, _)| *k == "TRUST_MC_CHC_ROW_EXPORT_DIR")
        .and_then(|(_, v)| v)
        .map(|v| v.to_string_lossy().into_owned());
    assert_eq!(export.as_deref(), Some("/exports/demo__h/loop-contract-retry"));
    let none = retry_lane_command("demo::h", None).unwrap();
    assert!(
        none.get_envs().any(|(k, v)| k == "TRUST_MC_CHC_ROW_EXPORT_DIR" && v.is_none()),
        "without an export the variable is removed from the child"
    );
}

/// The retry must never outrun the parent's watchdog: a kill degrades the row
/// to a timeout, which would make this feature a regression.
#[test]
fn lane_budget_never_exceeds_the_total_and_stops_when_spent() {
    let plenty = Duration::from_secs(3600);
    assert_eq!(lane_budget(Duration::from_secs(0), plenty), Some(RETRY_TOTAL_BUDGET));
    assert!(lane_budget(Duration::from_secs(30), plenty).unwrap() < RETRY_TOTAL_BUDGET);
    // Too little left to finish a lane -> do not start one.
    assert_eq!(lane_budget(Duration::from_secs(65), plenty), None);
    assert_eq!(lane_budget(Duration::from_secs(10_000), plenty), None);
    // Total must leave the parent room under its own 80s watchdog.
    assert!(RETRY_TOTAL_BUDGET < Duration::from_secs(80));
}

/// The harness's own deadline binds the retry: a lane never gets more than
/// what the harness has left, and below a lane's floor the retry is not
/// started at all — that is how the retry ends by a typed verdict instead
/// of the parent's watchdog.
#[test]
fn lane_budget_is_bounded_by_the_harness_deadline() {
    // Less harness time than the retry total: the harness remainder wins.
    assert_eq!(lane_budget(Duration::ZERO, Duration::from_secs(40)), Some(Duration::from_secs(40)));
    // Both bounds apply: 70 - 30 = 40 vs 25 left on the harness -> 25.
    assert_eq!(
        lane_budget(Duration::from_secs(30), Duration::from_secs(25)),
        Some(Duration::from_secs(25))
    );
    // Exactly the floor is usable; below it is a skip.
    assert_eq!(lane_budget(Duration::ZERO, LANE_MIN_BUDGET), Some(LANE_MIN_BUDGET));
    assert_eq!(lane_budget(Duration::ZERO, LANE_MIN_BUDGET - Duration::from_millis(1)), None);
    assert_eq!(lane_budget(Duration::ZERO, Duration::ZERO), None);
}



// ---------------------------------------------------------------------------
// The route limitation (T1 S7 acceptance: four CHC loop-contract units scored
// `route error` for a refusal that happened in a LANE CHILD).

/// The knobs a lane command actually sets, read back from the `Command`
/// (the row-export directory is a driver setting, not an engine knob).
fn lane_knobs(cmd: &std::process::Command) -> Vec<String> {
    let mut out: Vec<String> = cmd
        .get_envs()
        .filter(|(key, value)| value.is_some() && key.to_string_lossy().starts_with("TRUST_MC_"))
        .map(|(key, _)| key.to_string_lossy().into_owned())
        .filter(|key| key != LANE_ENV && key != "TRUST_MC_CHC_ROW_EXPORT_DIR")
        .collect();
    out.sort();
    out
}

/// The value a command passes for `--target-dir`.
fn target_dir_of(cmd: &std::process::Command) -> String {
    let args: Vec<String> = cmd.get_args().map(|a| a.to_string_lossy().into_owned()).collect();
    let at = args.iter().position(|a| a == "--target-dir").expect("--target-dir");
    args[at + 1].clone()
}

/// Review round 2: under `--jobs N` two harnesses' retries run at once, and
/// the lane directories were keyed only by the process, so both lanes compiled
/// into one directory (`No such file or directory` on
/// `negative/loop_decreases_ignored.rs` at `--jobs 2`). Every harness now gets
/// its own directory.
#[test]
fn concurrent_harnesses_get_their_own_lane_target_dirs() {
    let a = target_dir_of(&retry_lane_command("harness_a", None).unwrap());
    let b = target_dir_of(&retry_lane_command("harness_b", None).unwrap());
    assert_ne!(a, b, "two harnesses' lanes must not share a directory");
    assert_eq!(a, target_dir_of(&retry_lane_command("harness_a", None).unwrap()), "stable");
    assert!(a.contains(&std::process::id().to_string()));
}

/// The list the route check reads must be exactly what the lane sets. A knob
/// added to the lane and not to the list would make the retry spawn a child
/// the Trustc route refuses — the defect the check closes.
#[test]
fn lane_commands_set_exactly_the_lane_engine_env_knobs() {
    let lane = retry_lane_command("h", Some(Path::new("/exports/h/loop-contract-retry")))
        .expect("lane command");
    let mut want: Vec<String> = LANE_ENGINE_ENV_KNOBS.iter().map(|k| (*k).to_string()).collect();
    want.sort();
    assert_eq!(lane_knobs(&lane), want, "LANE_ENGINE_ENV_KNOBS is out of date with the lane");
}

/// Every knob a lane sets must be one the Trustc route actually refuses.
/// If it were not, the retry would be skipped on that route for no reason.
#[test]
fn every_lane_knob_is_one_the_trustc_route_refuses() {
    for knob in LANE_ENGINE_ENV_KNOBS {
        assert!(
            trust_mc_metadata::engine_args::ENGINE_ENV_KNOBS.contains(&knob),
            "{knob} is not an engine env knob, so the route would not refuse it"
        );
        assert!(
            !trust_mc_metadata::engine_args::set_engine_env_knobs([knob]).is_empty(),
            "{knob} is not reported as set by set_engine_env_knobs"
        );
    }
}

#[test]
fn the_dev_cli_route_has_no_limitation() {
    assert_eq!(route_limitation(false), None);
}

/// The reported limitation names the route, a stable id and every knob, so a
/// measurement can record WHY without re-reading this source.
#[test]
fn the_trustc_route_limitation_is_named_and_specific() {
    let l = route_limitation(true).expect("the trustc route cannot carry the lane knobs");
    assert_eq!(l.id, TWO_LANE_ROUTE_LIMITATION_ID);
    assert_eq!(l.route, "trustc");
    assert_eq!(l.marker(), "[AY:ROUTE_LIMITATION:two-lane-loop-contract-retry route=trustc]");
    for knob in LANE_ENGINE_ENV_KNOBS {
        assert!(l.detail.contains(knob), "the detail does not name {knob}");
    }
    assert!(l.explanation().contains("[AY:LOOP_TWO_LANE]"));
}

/// NEITHER line may look like a route REFUSAL. A refusal means the driver
/// produced no verdict; this run produced one, and a consumer that greps for
/// the refusal text would score an attested row as a route error — which is
/// precisely the measurement defect being fixed.
#[test]
fn the_limitation_lines_are_not_a_route_refusal() {
    let l = route_limitation(true).unwrap();
    for line in [l.marker(), l.explanation()] {
        assert!(!line.contains("compiler route trustc refused"), "{line}");
        assert!(!line.starts_with("error:"), "{line}");
        assert!(!line.contains('\n'), "a marker must be one line: {line}");
    }
}

/// AY alignment review round 2: a first run that a vacuity gate failed closed
/// is never retried. Before the gate, `v4_retry_f32_bug` [bmc] (every check
/// unreachable behind a mis-encoded guard, V4 dead-checks) reached the retry,
/// the CHC child proved the same mis-encoded program, and the merge printed
/// `VERIFICATION:- SUCCESSFUL` where Kani fails. Under the old rule
/// (`!first_run_succeeded && eligible` => retry) every row below but the last
/// two started the lane.
#[test]
fn a_vacuity_verdict_is_never_handed_to_the_retry() {
    for gate in [
        FailClosedGate::UnsatAssumption,
        FailClosedGate::DeadChecks,
        FailClosedGate::UnsatisfiableCover,
        FailClosedGate::Conformance,
    ] {
        assert_eq!(retry_decision(false, true, Some(gate)), RetryDecision::Refused(gate));
        let marker = gate.refusal_marker();
        assert!(marker.starts_with("[AY:LOOP_TWO_LANE] not started"), "{marker}");
        assert!(marker.contains(&format!("[AY:VACUOUS:{}]", gate.id())), "{marker}");
    }
    // A check-failure first run still gets its retry; a success or an
    // ineligible harness never does.
    assert_eq!(retry_decision(false, true, None), RetryDecision::Start);
    assert_eq!(retry_decision(true, true, None), RetryDecision::NotNeeded);
    assert_eq!(retry_decision(false, false, None), RetryDecision::NotNeeded);
    assert_eq!(
        retry_decision(false, false, Some(FailClosedGate::DeadChecks)),
        RetryDecision::NotNeeded
    );
}

/// The gate ids are the `[AY:VACUOUS:<id>]` ids the gates print, so a reader
/// can match the refusal to the gate's own line.
#[test]
fn fail_closed_gate_ids_match_the_vacuity_markers() {
    assert_eq!(FailClosedGate::UnsatAssumption.id(), "unsat-assumption");
    assert_eq!(FailClosedGate::DeadChecks.id(), "dead-checks");
    assert_eq!(FailClosedGate::UnsatisfiableCover.id(), "cover");
    assert_eq!(FailClosedGate::Conformance.id(), "conformance");
}
