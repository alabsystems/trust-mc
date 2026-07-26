// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for nonlinear arithmetic detection and numeric literal parsing.

use super::super::nonlinear::{
    check_division_by_var, check_nonlinear_args, detect_nonlinear_in_content, is_numeric_literal,
};
use std::collections::HashSet;

#[test]
fn test_is_numeric_literal() {
    // Decimal integers
    assert!(is_numeric_literal("123"));
    assert!(is_numeric_literal("0"));
    assert!(is_numeric_literal("-42"));

    // Decimal reals
    assert!(is_numeric_literal("3.14"));
    assert!(is_numeric_literal("-1.5"));

    // SMT-LIB2 hex literals
    assert!(is_numeric_literal("#x1A"));
    assert!(is_numeric_literal("#xFF"));
    assert!(is_numeric_literal("#x0"));

    // SMT-LIB2 binary literals
    assert!(is_numeric_literal("#b1010"));
    assert!(is_numeric_literal("#b0001"));
    assert!(is_numeric_literal("#b0"));

    // Not numeric
    assert!(!is_numeric_literal("x"));
    assert!(!is_numeric_literal("var_name"));
    assert!(!is_numeric_literal(""));
    assert!(!is_numeric_literal("_"));
    assert!(!is_numeric_literal("#x")); // Empty hex
    assert!(!is_numeric_literal("#b")); // Empty binary
}

#[test]
fn test_check_nonlinear_args_requires_known_vars() {
    let mut vars: HashSet<&str> = HashSet::new();

    assert!(
        !check_nonlinear_args("x y)", &vars),
        "Unknown identifiers should not count as non-linear without vars"
    );

    vars.insert("x");
    vars.insert("y");
    assert!(
        check_nonlinear_args("x y)", &vars),
        "Known variables should count as non-linear operands"
    );

    vars.remove("y");
    assert!(!check_nonlinear_args("x y)", &vars), "Single known variable is linear");

    vars.insert("y");
    assert!(
        check_nonlinear_args("x 5 y)", &vars),
        "Separated variables in a variadic multiplication are non-linear"
    );

    vars.remove("x");
    vars.remove("y");
    vars.insert("y");
    vars.insert("z");
    assert!(
        !check_nonlinear_args("2 (+ y z))", &vars),
        "Multiplying a constant by a linear expression stays linear"
    );
}

#[test]
fn test_check_division_by_var_requires_known_divisor() {
    let mut vars: HashSet<&str> = HashSet::new();

    assert!(
        !check_division_by_var("x y)", &vars),
        "Unknown divisor should not count as non-linear"
    );

    vars.insert("y");
    assert!(check_division_by_var("x y)", &vars), "Known divisor variable should be detected");

    vars.remove("y");
    vars.insert("x");
    assert!(
        !check_division_by_var("x y)", &vars),
        "Only divisor variable should trigger non-linear detection"
    );

    vars.remove("x");
    vars.insert("y");
    assert!(
        check_division_by_var("x (+ y 1))", &vars),
        "Divisor expressions containing variables should be detected"
    );

    vars.clear();
    vars.insert("x");
    vars.insert("y");
    assert!(
        !check_division_by_var("(* x y) 5)", &vars),
        "Numerator variables should not affect divisor classification"
    );
}

#[test]
fn test_detect_nonlinear_in_content_multiple_mults() {
    let vars: HashSet<&str> = HashSet::from(["x", "y", "z"]);

    let content = "(assert (+ (* x 5) (* y z)))\n(check-sat)\n";
    assert!(
        detect_nonlinear_in_content(content, &vars),
        "Should detect non-linear multiplication among multiple ops on a line"
    );
}

#[test]
fn test_detect_nonlinear_in_content_linear_only() {
    let vars: HashSet<&str> = HashSet::from(["x", "y"]);

    let content = "(assert (= (* x 5) 25))\n(assert (= (/ y 10) 3))\n(check-sat)\n";
    assert!(
        !detect_nonlinear_in_content(content, &vars),
        "Constant multiplication/division should remain linear"
    );
}
