// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for declaration extraction and HORN logic detection.

use super::super::classifier::smt_file_uses_horn_logic;
use super::super::datatypes;
use super::super::declarations::{
    build_cover_sat_query, extract_cover_declarations, extract_coverage_declarations_from_content,
    extract_violation_declarations, strip_cover_assertions_for_chc_solver,
};
use std::io::Write;
use tempfile::NamedTempFile;

#[test]
fn test_smt_file_has_datatypes_true() {
    // Create an SMT file with a datatype declaration
    let mut input = NamedTempFile::new().unwrap();
    let content = "(set-option :produce-models true)\n\
                   (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert!(
        datatypes::smt_file_has_datatypes(input.path()).unwrap(),
        "Should detect declare-datatype"
    );
}

#[test]
fn test_smt_file_has_datatypes_recursive() {
    // Create an SMT file with mutually recursive datatypes
    let mut input = NamedTempFile::new().unwrap();
    let content = "(set-option :produce-models true)\n\
                   (declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T)))))))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert!(
        datatypes::smt_file_has_datatypes(input.path()).unwrap(),
        "Should detect declare-datatypes"
    );
}

#[test]
fn test_smt_file_has_datatypes_false() {
    // Create an SMT file without datatypes
    let mut input = NamedTempFile::new().unwrap();
    let content = "(set-option :produce-models true)\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert!(
        !datatypes::smt_file_has_datatypes(input.path()).unwrap(),
        "Should not detect datatypes"
    );
}

#[test]
fn test_extract_violation_declarations() {
    let mut input = NamedTempFile::new().unwrap();
    let content = "(set-option :produce-models true)\n\
                   (declare-const ay_violation_kani_assert_0 Bool)\n\
                   (declare-const ay_violation_overflow_check_add_1 Bool)\n\
                   (declare-const ay_violation_bounds_check_2 Bool)\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    let violations = extract_violation_declarations(input.path()).unwrap();
    assert_eq!(violations.len(), 3);
    assert!(violations.contains(&"ay_violation_kani_assert_0".to_string()));
    assert!(violations.contains(&"ay_violation_overflow_check_add_1".to_string()));
    assert!(violations.contains(&"ay_violation_bounds_check_2".to_string()));
}

#[test]
fn test_extract_violation_declarations_empty() {
    // SMT file with no violations
    let mut input = NamedTempFile::new().unwrap();
    let content = "(set-option :produce-models true)\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    let violations = extract_violation_declarations(input.path()).unwrap();
    assert!(violations.is_empty());
}

#[test]
fn test_extract_cover_declarations() {
    // SMT file with cover declarations
    let mut input = NamedTempFile::new().unwrap();
    let content = "(set-option :produce-models true)\n\
                   (declare-const ay_cover_0 Bool)\n\
                   (declare-const ay_cover_1 Bool)\n\
                   (declare-const ay_cover_42 Bool)\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    let covers = extract_cover_declarations(input.path()).unwrap();
    assert_eq!(covers.len(), 3);
    assert!(covers.contains(&"ay_cover_0".to_string()));
    assert!(covers.contains(&"ay_cover_1".to_string()));
    assert!(covers.contains(&"ay_cover_42".to_string()));
}

#[test]
fn test_extract_cover_declarations_empty() {
    // SMT file with no covers
    let mut input = NamedTempFile::new().unwrap();
    let content = "(set-option :produce-models true)\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    let covers = extract_cover_declarations(input.path()).unwrap();
    assert!(covers.is_empty());
}

#[test]
fn test_extract_coverage_declarations_from_content() {
    let content = "(set-option :produce-models true)\n\
                   (declare-const ay_coverage_0 Bool)\n\
                   (declare-const ay_cover_1 Bool)\n\
                   (declare-const ay_coverage_42 Bool)\n\
                   (check-sat)\n";

    let coverage = extract_coverage_declarations_from_content(content);
    assert_eq!(coverage, vec!["ay_coverage_0".to_string(), "ay_coverage_42".to_string()]);
}

#[test]
fn test_smt_file_uses_horn_logic_true() {
    // Create a CHC file with HORN logic
    let mut input = NamedTempFile::new().unwrap();
    let content = "(set-logic HORN)\n\
                   (declare-rel P (Int))\n\
                   (declare-var x Int)\n\
                   (rule (P 0))\n\
                   (rule (=> (P x) (P (+ x 1))))\n\
                   (query P)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert!(smt_file_uses_horn_logic(input.path()).unwrap(), "Should detect HORN logic");
}

#[test]
fn test_smt_file_uses_horn_logic_false() {
    // Create a BMC file without HORN logic
    let mut input = NamedTempFile::new().unwrap();
    let content = "(set-logic QF_AUFBV)\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert!(
        !smt_file_uses_horn_logic(input.path()).unwrap(),
        "Should not detect HORN logic in BMC file"
    );
}

#[test]
fn test_smt_file_uses_horn_logic_no_logic() {
    // Create a file without any set-logic
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-const x Int)\n\
                   (assert (> x 0))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert!(
        !smt_file_uses_horn_logic(input.path()).unwrap(),
        "Should not detect HORN logic when no logic set"
    );
}

// Part of #1162: Tests for build_cover_sat_query

#[test]
fn test_build_cover_sat_query_basic() {
    let smt_content = "\
(set-logic ALL)
(declare-const x (_ BitVec 32))
(declare-const ay_violation_kani_assert_0 Bool)
(declare-const ay_cover_0 Bool)
(assert (= ay_violation_kani_assert_0 (bvult x (_ bv10 32))))
(assert (= ay_cover_0 (= x (_ bv5 32))))
(assert (or ay_violation_kani_assert_0))
(check-sat)
(get-value (ay_violation_kani_assert_0 ay_cover_0))
(exit)
";
    let cover_names = vec!["ay_cover_0".to_string()];
    let query = build_cover_sat_query(smt_content, &cover_names);

    // Should contain the declarations and constraint assertions
    assert!(query.contains("(set-logic ALL)"));
    assert!(query.contains("(declare-const x (_ BitVec 32))"));
    assert!(query.contains("(declare-const ay_cover_0 Bool)"));
    assert!(query.contains("(assert (= ay_cover_0 (= x (_ bv5 32))))"));

    // Should NOT contain the violation disjunction, check-sat, get-value
    assert!(
        !query.contains("(assert (or ay_violation_kani_assert_0))"),
        "should strip violation disjunction"
    );
    assert!(!query.contains("(get-value"), "should strip get-value");

    // Should contain push/pop cover check
    assert!(query.contains("(push 1)"));
    assert!(query.contains("(assert ay_cover_0)"));
    assert!(query.contains("(check-sat)"));
    assert!(query.contains("(pop 1)"));
    assert!(query.contains("(exit)"));
}

#[test]
fn test_build_cover_sat_query_multiple_covers() {
    let smt_content = "\
(set-logic ALL)
(declare-const ay_cover_0 Bool)
(declare-const ay_cover_1 Bool)
(assert (or ay_violation_kani_assert_0))
(check-sat)
(get-value (ay_cover_0 ay_cover_1))
";
    let cover_names = vec!["ay_cover_0".to_string(), "ay_cover_1".to_string()];
    let query = build_cover_sat_query(smt_content, &cover_names);

    // Should have two push/pop blocks
    let push_count = query.matches("(push 1)").count();
    let pop_count = query.matches("(pop 1)").count();
    let check_sat_count = query.matches("(check-sat)").count();
    assert_eq!(push_count, 2, "should have 2 push blocks");
    assert_eq!(pop_count, 2, "should have 2 pop blocks");
    assert_eq!(check_sat_count, 2, "should have 2 check-sat commands");

    assert!(query.contains("(assert ay_cover_0)"));
    assert!(query.contains("(assert ay_cover_1)"));
}

#[test]
fn test_build_cover_sat_query_strips_assert_false() {
    // When no violations exist, emit_bmc emits (assert false)
    let smt_content = "\
(set-logic ALL)
(declare-const ay_cover_0 Bool)
(assert false)
(check-sat)
";
    let cover_names = vec!["ay_cover_0".to_string()];
    let query = build_cover_sat_query(smt_content, &cover_names);

    assert!(!query.contains("(assert false)"), "should strip (assert false)");
    assert!(query.contains("(assert ay_cover_0)"));
}

#[test]
fn test_build_cover_sat_query_preserves_constraint_assertions() {
    let smt_content = "\
(set-logic ALL)
(declare-const x Int)
(assert (> x 0))
(assert (< x 100))
(assert (or ay_violation_kani_assert_0))
(check-sat)
";
    let cover_names = vec!["ay_cover_0".to_string()];
    let query = build_cover_sat_query(smt_content, &cover_names);

    // Program constraints should be preserved
    assert!(query.contains("(assert (> x 0))"));
    assert!(query.contains("(assert (< x 100))"));
    // Violation disjunction should be stripped
    assert!(!query.contains("(assert (or ay_violation_kani_assert_0))"));
}

#[test]
fn test_strip_cover_assertions_for_chc_solver_keeps_query_and_rules() {
    let smt_content = "\
(set-logic HORN)
(declare-rel P ())
(declare-rel error ())
(rule (=> true P))
(query error)
(declare-const ay_cover_0 Bool)
(assert (= ay_cover_0 true))
";
    let stripped = strip_cover_assertions_for_chc_solver(smt_content);

    assert!(stripped.contains("(query error)"));
    assert!(stripped.contains("(rule (=> true P))"));
    assert!(!stripped.contains("ay_cover_0"));
}
