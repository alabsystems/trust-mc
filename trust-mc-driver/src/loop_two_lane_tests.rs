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
/// (`apply_loop_contract_naming`), not as the artifact's internal stems.
const O_REPORT: &str = "Check 1: h.loop_invariant_base.1\n - Description: \"Check invariant before entry for loop h.0\"\nCheck 2: h.loop_invariant_step.1\n - Description: \"Check invariant after step for loop h.0\"\nVERIFICATION:- SUCCESSFUL\n";

#[test]
fn merge_proves_when_both_lanes_discharge() {
    assert_eq!(merge(true, O_REPORT, true), TwoLaneOutcome::Proved);
}

/// The vacuity guard: a lane that reports "no failures" but never CONTAINED the
/// obligations must not be trusted.
#[test]
fn merge_refuses_a_vacuous_obligations_lane() {
    let report = "Check 1: h.assertion.0\n - Description: \"attempt to add with overflow\"\nVERIFICATION:- SUCCESSFUL\n";
    match merge(true, report, true) {
        TwoLaneOutcome::Inconclusive(why) => assert!(why.contains("vacuous"), "{why}"),
        other => panic!("expected refusal, got {other:?}"),
    }
}

/// Base case present but inductive step absent is still vacuous.
#[test]
fn merge_requires_both_base_and_step() {
    let report = "Description: \"Check invariant before entry for loop h.0\"\nVERIFICATION:- SUCCESSFUL\n";
    assert!(matches!(merge(true, report, true), TwoLaneOutcome::Inconclusive(_)));
}

#[test]
fn merge_inconclusive_when_a_lane_fails() {
    assert!(matches!(merge(false, O_REPORT, true), TwoLaneOutcome::Inconclusive(_)));
    assert!(matches!(merge(true, O_REPORT, false), TwoLaneOutcome::Inconclusive(_)));
}

/// Only an explicit positive summary line counts as a proof: a child that
/// crashed, timed out, or printed nothing must not be read as success.
#[test]
fn child_proved_requires_the_positive_summary_line() {
    assert!(child_proved("blah\nVERIFICATION:- SUCCESSFUL\n"));
    assert!(!child_proved("VERIFICATION:- FAILED\n"));
    assert!(!child_proved("VERIFICATION:- INCONCLUSIVE\n"));
    assert!(!child_proved(""));
    assert!(!child_proved("error: The --ay-chc-bounded-unroll option requires --ay-chc.\n"));
}

/// `--ay-chc` is mandatory for Lane P; without it argument validation rejects
/// the child and the retry becomes a silent permanent no-op.
#[test]
fn lane_p_argv_carries_ay_chc_and_the_depth() {
    let cmd = lane_p_command("h", 2).expect("argv");
    let args: Vec<String> =
        cmd.get_args().map(|a| a.to_string_lossy().into_owned()).collect();
    assert!(args.contains(&"--ay-chc".to_string()), "{args:?}");
    assert!(args.contains(&"--ay-chc-bounded-unroll".to_string()), "{args:?}");
    assert!(args.contains(&"--unwind".to_string()), "{args:?}");
    assert!(args.contains(&"2".to_string()), "{args:?}");
    assert!(!args.contains(&"--prove-safety-only".to_string()), "{args:?}");
}

#[test]
fn lane_o_argv_is_safety_only_and_not_unrolled() {
    let cmd = lane_o_command("h").expect("argv");
    let args: Vec<String> =
        cmd.get_args().map(|a| a.to_string_lossy().into_owned()).collect();
    assert!(args.contains(&"--ay-chc".to_string()), "{args:?}");
    assert!(args.contains(&"--prove-safety-only".to_string()), "{args:?}");
    assert!(!args.contains(&"--ay-chc-bounded-unroll".to_string()), "{args:?}");
}

/// Every lane must be stamped so it cannot spawn lanes of its own.
#[test]
fn both_lanes_set_the_recursion_guard() {
    for cmd in [lane_o_command("h").unwrap(), lane_p_command("h", 2).unwrap()] {
        let stamped = cmd
            .get_envs()
            .any(|(k, v)| k == LANE_ENV && v.is_some_and(|v| !v.is_empty()));
        assert!(stamped, "lane is missing the {LANE_ENV} guard");
    }
}

/// The retry must never outrun the parent's watchdog: a kill degrades the row
/// to a timeout, which would make this feature a regression.
#[test]
fn lane_budget_never_exceeds_the_total_and_stops_when_spent() {
    assert_eq!(lane_budget(Duration::from_secs(0)), Some(RETRY_TOTAL_BUDGET));
    assert!(lane_budget(Duration::from_secs(30)).unwrap() < RETRY_TOTAL_BUDGET);
    // Too little left to finish a lane -> do not start one.
    assert_eq!(lane_budget(Duration::from_secs(65)), None);
    assert_eq!(lane_budget(Duration::from_secs(10_000)), None);
    // Total must leave the parent room under its own 80s watchdog.
    assert!(RETRY_TOTAL_BUDGET < Duration::from_secs(80));
}


