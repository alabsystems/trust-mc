// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

const ARTIFACT: &str = r#"{
  "schema_version": 1,
  "harnesses": [
    {"harness": "proofs::ttl_is_bounded", "status": "success",
     "effective_success": true, "property_counts": {"total": 1}},
    {"harness": "proofs::shard_divides_by_zero", "status": "failure",
     "effective_success": false,
     "failed_checks": [
       {"description": "division by zero", "file": "src/lib.rs",
        "line": "2", "column": "47"}]}
  ]
}"#;

#[test]
fn a_failing_harness_carries_its_reason_and_position() {
    let rows = parse(ARTIFACT).expect("artifact should parse");
    assert_eq!(rows.len(), 2);
    let failed = rows.iter().find(|r| !r.proved).expect("one failure");
    assert_eq!(failed.harness, "proofs::shard_divides_by_zero");
    // Reason AND position on one line is the whole point: the engine's own
    // closing block names the harness and nothing else.
    assert_eq!(failed.detail, vec!["division by zero  (src/lib.rs:2:47)"]);
    let proved = rows.iter().find(|r| r.proved).expect("one proof");
    assert_eq!(proved.harness, "proofs::ttl_is_bounded");
    assert!(proved.detail.is_empty(), "a proof needs no explanation");
}

#[test]
fn a_should_panic_pass_counts_as_proved() {
    // `effective_success` is the authority, not `status`: a should_panic
    // harness is a PASS whose status is `failure`. Reading `status` alone
    // would report a green run as broken.
    let text = r#"{"harnesses":[{"harness":"h","status":"failure",
        "effective_success":true}]}"#;
    let rows = parse(text).expect("parses");
    assert!(rows[0].proved, "effective_success must win over status");
}

#[test]
fn a_failure_with_no_recorded_checks_still_says_something() {
    // VACUOUS and no-checks runs fail with an empty `failed_checks`. A blank
    // line under FAILED would read as a rendering bug.
    let text = r#"{"harnesses":[{"harness":"h","status":"failure",
        "effective_success":false}]}"#;
    let rows = parse(text).expect("parses");
    assert!(!rows[0].proved);
    assert_eq!(rows[0].detail.len(), 1);
    assert!(!rows[0].detail[0].is_empty());
}

#[test]
fn a_long_failure_list_is_truncated_rather_than_flooding_the_terminal() {
    let checks: Vec<String> = (0..9)
        .map(|i| format!(r#"{{"description":"check {i}","file":"a.rs","line":"{i}"}}"#))
        .collect();
    let text = format!(
        r#"{{"harnesses":[{{"harness":"h","status":"failure","effective_success":false,
           "failed_checks":[{}]}}]}}"#,
        checks.join(",")
    );
    let rows = parse(&text).expect("parses");
    assert_eq!(rows[0].detail.len(), 5, "four checks plus an ellipsis");
    assert_eq!(rows[0].detail[4], "...");
}

#[test]
fn exactly_the_display_limit_is_shown_whole_with_no_elision_marker() {
    // Off-by-one guard: breaking AT the limit printed "..." under a harness
    // with exactly 4 failing checks and nothing hidden. A summary that claims
    // to be hiding something it is not is worse than one that shows it all.
    for n in 1..=4 {
        let checks: Vec<String> = (0..n)
            .map(|i| format!(r#"{{"description":"check {i}","file":"a.rs","line":"{i}"}}"#))
            .collect();
        let text = format!(
            r#"{{"harnesses":[{{"harness":"h","status":"failure","effective_success":false,
               "failed_checks":[{}]}}]}}"#,
            checks.join(",")
        );
        let rows = parse(&text).expect("parses");
        assert_eq!(rows[0].detail.len(), n, "{n} checks should show as {n} rows");
        assert!(!rows[0].detail.iter().any(|d| d == "..."), "nothing was elided at n={n}");
    }
    // Five is the first count that genuinely elides.
    let checks: Vec<String> = (0..5)
        .map(|i| format!(r#"{{"description":"check {i}","file":"a.rs","line":"{i}"}}"#))
        .collect();
    let text = format!(
        r#"{{"harnesses":[{{"harness":"h","status":"failure","effective_success":false,
           "failed_checks":[{}]}}]}}"#,
        checks.join(",")
    );
    let rows = parse(&text).expect("parses");
    assert_eq!(rows[0].detail.len(), 5);
    assert_eq!(rows[0].detail[4], "...");
}

#[test]
fn junk_is_declined_rather_than_half_rendered() {
    assert!(parse("not json at all").is_none());
    assert!(render(std::path::Path::new("/nonexistent/summary.json")) == false);
}

#[test]
fn the_summary_flag_is_taken_out_and_the_engines_own_flag_is_kept() {
    let argv: Vec<OsString> = ["--summary", "--timeout", "30s", "x.rs"]
        .iter()
        .map(OsString::from)
        .collect();
    let (req, rest) = take_summary_flag(&argv);
    assert!(req.wanted);
    assert!(req.existing.is_none());
    // The engine has never heard of --summary; forwarding it is a usage error.
    assert_eq!(rest, vec![OsString::from("--timeout"), OsString::from("30s"), OsString::from("x.rs")]);
}

#[test]
fn an_artifact_the_caller_already_asked_for_is_reused_not_duplicated() {
    for spelling in [
        vec!["--summary", "--proof-summary-json", "mine.json"],
        vec!["--summary", "--proof-summary-json=mine.json"],
    ] {
        let argv: Vec<OsString> = spelling.iter().map(OsString::from).collect();
        let (req, rest) = take_summary_flag(&argv);
        assert!(req.wanted);
        assert_eq!(req.existing, Some(OsString::from("mine.json")), "{spelling:?}");
        // ...and the engine still receives it, or the caller loses their file.
        assert!(rest.iter().any(|a| a.to_str().is_some_and(|s| s.contains("proof-summary-json"))));
    }
}

/// A row must say WHICH kind of red it is.
///
/// `FAILED` covered three different pieces of news — the solver never decided,
/// the assumptions were contradictory so nothing was verified, and a check
/// really can fail — and only the last is "your code is wrong".
#[test]
fn a_row_names_the_kind_of_failure_not_just_that_there_was_one() {
    let cases: [(&str, &str); 4] = [
        ("vacuous", "VACUOUS"),
        ("inconclusive_undecided", "UNDECIDED"),
        ("inconclusive_no_checks", "NO-CHECKS"),
        ("uncertified_counterexample", "UNCERTIFIED"),
    ];
    for (verdict, label) in cases {
        let text = format!(
            r#"{{"harnesses":[{{"harness":"h","status":"failure","verdict":"{verdict}",
               "verdict_description":"why it went this way","effective_success":false}}]}}"#
        );
        let rows = parse(&text).expect("parses");
        assert_eq!(rows[0].label, label, "{verdict}");
        assert!(!rows[0].proved, "{verdict} is not a proof");
        // ...and the sentence the engine shipped is what gets printed, so the
        // table keeps no vocabulary of its own to drift.
        assert_eq!(rows[0].detail, vec!["why it went this way"], "{verdict}");
    }

    // An ordinary refutation keeps the word it always had, and the caveat line
    // is NOT added — it would be noise on every failing run.
    let ordinary = r#"{"harnesses":[{"harness":"h","status":"failure","verdict":"failed",
        "verdict_description":"verification did not succeed","effective_success":false,
        "failed_checks":[{"description":"division by zero","file":"a.rs","line":"2"}]}]}"#;
    let rows = parse(ordinary).expect("parses");
    assert_eq!(rows[0].label, "FAILED");
    assert_eq!(rows[0].detail, vec!["division by zero  (a.rs:2)"]);
}

/// An uncertified counterexample shows its caveat ABOVE the checks: without it
/// the listed values read as a bug in the user's code.
#[test]
fn an_uncertified_row_puts_the_caveat_before_the_checks() {
    let text = r#"{"harnesses":[{"harness":"h","status":"failure",
        "verdict":"uncertified_counterexample","verdict_description":"NOT certified as genuine",
        "effective_success":false,
        "failed_checks":[{"description":"assertion failed","file":"a.rs","line":"9"}]}]}"#;
    let rows = parse(text).expect("parses");
    assert_eq!(rows[0].label, "UNCERTIFIED");
    assert_eq!(rows[0].detail[0], "NOT certified as genuine");
    assert_eq!(rows[0].detail[1], "assertion failed  (a.rs:9)");
}

/// A verdict this build has never heard of must still render as "not proved".
/// The field is additive by contract, so new tokens WILL show up here.
#[test]
fn an_unknown_verdict_token_degrades_to_plain_failed() {
    let text = r#"{"harnesses":[{"harness":"h","status":"failure",
        "verdict":"something_invented_later","effective_success":false}]}"#;
    let rows = parse(text).expect("parses");
    assert!(!rows[0].proved);
    assert_eq!(rows[0].label, "FAILED");
    // A proved harness is labelled by its outcome, never by the token.
    let ok = r#"{"harnesses":[{"harness":"h","status":"failure","verdict":"successful",
        "effective_success":true}]}"#;
    assert_eq!(parse(ok).unwrap()[0].label, "proved");
}
