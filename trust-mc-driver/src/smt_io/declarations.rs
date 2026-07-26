// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Violation and cover declaration extraction from SMT-LIB2 content.
//!
//! Parses `declare-const` lines to extract `ay_violation_*`, `ay_cover_*`,
//! and `ay_coverage_*` variable names used by the driver to enumerate checks
//! on UNSAT results.

#[cfg(test)]
use anyhow::{Context, Result};
#[cfg(test)]
use std::path::Path;

/// Extract violation variable names from an SMT file.
///
/// Parses lines like `(declare-const ay_violation_kani_assert_0 Bool)` to
/// extract the variable names. This is used on UNSAT to enumerate all
/// checks that passed (since the solver doesn't return get-value on UNSAT).
///
/// REQUIRES: smt_file exists and is readable
/// ENSURES: result.is_ok() implies result.all(|s| s.starts_with("ay_violation_"))
/// ENSURES: result contains exactly the violation declarations in file order
#[cfg(test)]
pub(crate) fn extract_violation_declarations(smt_file: &Path) -> Result<Vec<String>> {
    let content = std::fs::read_to_string(smt_file)
        .with_context(|| format!("Failed to read SMT file: {}", smt_file.display()))?;
    Ok(extract_violation_declarations_from_content(&content))
}

/// Extract violation variable names from SMT content string.
///
/// Part of #2942: content-based variant avoids redundant file reads when the
/// caller has already read the SMT file.
pub(crate) fn extract_violation_declarations_from_content(content: &str) -> Vec<String> {
    let mut violations = Vec::new();
    for line in content.lines() {
        let trimmed = line.trim();
        // Look for: (declare-const ay_violation_... Bool)
        if let Some(rest) = trimmed.strip_prefix("(declare-const ay_violation_") {
            // Extract the name (everything before the next space)
            if let Some(end) = rest.find(' ') {
                let name = &rest[..end];
                violations.push(format!("ay_violation_{}", name));
            }
        }
    }
    violations
}

/// Extract cover property variable names from an SMT file.
///
/// Parses lines like `(declare-const ay_cover_0 Bool)` to extract the
/// variable names. This is used on UNSAT to enumerate cover properties
/// (since the solver doesn't return get-value on UNSAT).
///
/// REQUIRES: smt_file exists and is readable
/// ENSURES: result.is_ok() implies result.all(|s| s.starts_with("ay_cover_"))
/// ENSURES: result contains exactly the cover declarations in file order
#[cfg(test)]
pub(crate) fn extract_cover_declarations(smt_file: &Path) -> Result<Vec<String>> {
    let content = std::fs::read_to_string(smt_file)
        .with_context(|| format!("Failed to read SMT file: {}", smt_file.display()))?;
    Ok(extract_cover_declarations_from_content(&content))
}

/// Extract cover property names from SMT content string.
///
/// Part of #2942: content-based variant avoids redundant file reads.
pub(crate) fn extract_cover_declarations_from_content(content: &str) -> Vec<String> {
    let mut covers = Vec::new();
    for line in content.lines() {
        let trimmed = line.trim();
        // Look for: (declare-const ay_cover_... Bool)
        if let Some(rest) = trimmed.strip_prefix("(declare-const ay_cover_") {
            // Extract the name (everything before the next space)
            if let Some(end) = rest.find(' ') {
                let name = &rest[..end];
                covers.push(format!("ay_cover_{}", name));
            }
        }
    }
    covers
}

/// Extract reachability flag names from SMT content string.
///
/// Parses lines like `(declare-const ay_reach_kani_assert_3 Bool)`. Each flag
/// pairs with the violation flag of the same suffix
/// (`ay_violation_kani_assert_3`) and is defined as that check's guard (path
/// condition ∧ ordered assumption context). The driver classifies a check as
/// UNREACHABLE when the solver proves its reach flag unsatisfiable. Checks
/// without a reach flag have a trivially-true guard (always reachable).
pub(crate) fn extract_reach_declarations_from_content(content: &str) -> Vec<String> {
    let mut reach_flags = Vec::new();
    for line in content.lines() {
        let trimmed = line.trim();
        // Look for: (declare-const ay_reach_... Bool)
        if let Some(rest) = trimmed.strip_prefix("(declare-const ay_reach_")
            && let Some(end) = rest.find(' ')
        {
            let name = &rest[..end];
            reach_flags.push(format!("ay_reach_{}", name));
        }
    }
    reach_flags
}

/// Extract source coverage property names from SMT content string.
pub(crate) fn extract_coverage_declarations_from_content(content: &str) -> Vec<String> {
    let mut coverage = Vec::new();
    for line in content.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("(declare-const ay_coverage_")
            && let Some(end) = rest.find(' ')
        {
            let name = &rest[..end];
            coverage.push(format!("ay_coverage_{}", name));
        }
    }
    coverage
}

/// Returns true for the violation disjunction line `(assert (or viol_1 ...))`.
///
/// The legacy and emit_bmc encoders both build the disjunction by left-folding
/// `Expr::or`, so with three or more checks the printed form is nested:
/// `(assert (or (or (or v0 v1) v2) v3))`. A plain
/// `starts_with("(assert (or ay_violation_")` check misses the nested form and
/// would leave the disjunction in secondary queries, wrongly constraining
/// cover/reach satisfiability checks (on an UNSAT primary query, every
/// secondary check-sat would come back unsat). Violation flag *definitions*
/// are `(assert (= ay_violation_...))` and never match.
fn is_violation_disjunction_line(trimmed: &str) -> bool {
    trimmed.starts_with("(assert ay_violation_")
        || (trimmed.starts_with("(assert (or") && trimmed.contains("ay_violation_"))
}

/// Build a secondary SMT query to check cover property satisfiability.
///
/// When the main verification query returns UNSAT (proof), cover properties
/// cannot be determined from the main query because no model is available.
/// This function constructs a secondary query that checks each cover property
/// individually using incremental solving (push/pop).
///
/// The secondary query:
/// 1. Retains all declarations and constraint assertions from the original
/// 2. Strips the violation disjunction assertion, check-sat, and get-value commands
/// 3. Adds a push/assert/check-sat/pop block for each cover variable
///
/// The solver output will contain one "sat" or "unsat" line per cover property.
/// - sat = SATISFIED (cover condition is reachable)
/// - unsat = UNSATISFIABLE (cover condition is never reachable)
///
/// REQUIRES: smt_content is valid SMT-LIB2 content
/// REQUIRES: cover_names are non-empty and match `ay_cover_*` declarations in smt_content
/// ENSURES: result contains push/pop blocks for each cover name
/// ENSURES: result does not contain the violation disjunction assertion
/// ENSURES: result does not contain get-value commands
pub(crate) fn build_cover_sat_query(smt_content: &str, cover_names: &[String]) -> String {
    let mut query = String::with_capacity(smt_content.len() + cover_names.len() * 40);

    for line in smt_content.lines() {
        let trimmed = line.trim();

        if is_violation_disjunction_line(trimmed) {
            continue;
        }
        if trimmed == "(assert false)" {
            continue;
        }
        if trimmed == "(check-sat)" {
            continue;
        }
        if trimmed.starts_with("(get-value") {
            continue;
        }
        if trimmed == "(exit)" {
            continue;
        }

        query.push_str(line);
        query.push('\n');
    }

    for name in cover_names {
        query.push_str("(push 1)\n");
        query.push_str(&format!("(assert {})\n", name));
        query.push_str("(check-sat)\n");
        query.push_str("(pop 1)\n");
    }

    query.push_str("(exit)\n");
    query
}

/// Build a secondary SMT query to check cover property satisfiability from CHC content.
///
/// CHC files use `(set-logic HORN)` with `(declare-rel)`, `(rule)`, and `(query)`
/// constructs that standard SMT solvers cannot process. This function extracts the
/// declarations and constraint assertions from the CHC file and builds a plain SMT
/// query that can be solved by any SMT solver (ay, CVC5, etc.).
///
/// Part of #1162: Cover semantics for CHC path.
///
/// REQUIRES: smt_content is valid CHC/HORN SMT-LIB2 content
/// REQUIRES: cover_names are non-empty and match `ay_cover_*` declarations in smt_content
/// ENSURES: result does NOT contain `(set-logic HORN)`, `(declare-rel)`, `(rule)`, `(query)`
/// ENSURES: result contains push/pop blocks for each cover name
pub(crate) fn build_cover_sat_query_for_chc(smt_content: &str, cover_names: &[String]) -> String {
    let mut query = String::with_capacity(smt_content.len() + cover_names.len() * 40);

    for line in smt_content.lines() {
        let trimmed = line.trim();

        // Replace HORN logic with ALL (plain SMT)
        if trimmed == "(set-logic HORN)" {
            query.push_str("(set-logic ALL)\n");
            continue;
        }
        // Strip CHC-specific constructs
        if trimmed.starts_with("(declare-rel ") {
            continue;
        }
        if trimmed.starts_with("(declare-var ") {
            continue;
        }
        if trimmed.starts_with("(rule ") || trimmed == "(rule" {
            continue;
        }
        if trimmed.starts_with("(query ") || trimmed == "(query" {
            continue;
        }
        // Skip violation disjunctions
        if is_violation_disjunction_line(trimmed) {
            continue;
        }
        if trimmed == "(assert false)" {
            continue;
        }
        if trimmed == "(check-sat)" {
            continue;
        }
        if trimmed.starts_with("(get-value") {
            continue;
        }
        if trimmed == "(exit)" {
            continue;
        }

        query.push_str(line);
        query.push('\n');
    }

    for name in cover_names {
        query.push_str("(push 1)\n");
        query.push_str(&format!("(assert {})\n", name));
        query.push_str("(check-sat)\n");
        query.push_str("(pop 1)\n");
    }

    query.push_str("(exit)\n");
    query
}

/// Remove CHC cover declarations/assertions from the SMT-LIB fed to the main
/// HORN solver.
///
/// Cover assertions are metadata for the driver's secondary satisfiability
/// checks. Keeping them in the main CHC script can perturb solvers that do not
/// treat post-`query` commands as inert for the already-issued query.
pub(crate) fn strip_cover_assertions_for_chc_solver(smt_content: &str) -> String {
    let mut stripped = String::with_capacity(smt_content.len());
    let mut changed = false;

    for line in smt_content.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("(declare-const ay_cover_")
            || trimmed.starts_with("(assert (= ay_cover_")
        {
            changed = true;
            continue;
        }
        stripped.push_str(line);
        stripped.push('\n');
    }

    if changed { stripped } else { smt_content.to_owned() }
}
