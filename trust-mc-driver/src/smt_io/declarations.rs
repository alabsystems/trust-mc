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

/// Build a secondary SMT query asking whether the harness is reachable at all —
/// i.e. whether the program constraints alone are satisfiable.
///
/// # Why this exists
///
/// The main query is `program_constraints ∧ (violation₁ ∨ … ∨ violationₙ)`, and
/// `unsat` is read as "no violation is possible" — a proof. But `unsat` also
/// results when `program_constraints` is *itself* contradictory, in which case
/// nothing was verified: every check passes vacuously. `kani::assume(false)`,
/// two assumptions that cannot both hold, or an unreachable harness body all
/// produce exactly that.
///
/// Per-check reach flags (`ay_reach_*`, see [`extract_reach_declarations_from_content`])
/// do not cover this: the compiler emits them only for checks whose *guard* is
/// non-trivial, so a harness whose contradiction lives in a top-level
/// `(assert …)` has no flag on any check and stays SUCCESS.
///
/// # Difference from [`build_cover_sat_query`]
///
/// That builder drops `(assert false)`, because a cover query asks "could this
/// cover point be hit in a *feasible* run" and the caller has already accepted
/// the program constraints. Here `(assert false)` is precisely the thing under
/// test, so **every constraint is preserved**; only the violation disjunction
/// and the trailing solver directives are removed.
///
/// REQUIRES: `smt_content` is the BMC query emitted for one harness
/// ENSURES: the result contains no violation disjunction and exactly one `(check-sat)`
pub(crate) fn build_harness_reachability_query(smt_content: &str) -> String {
    let mut query = String::with_capacity(smt_content.len() + 64);
    let mut has_assume_final = false;

    for line in smt_content.lines() {
        let trimmed = line.trim();

        // The violation disjunction is the *question* of the main query, not a
        // program constraint — asking it here would defeat the probe.
        if is_violation_disjunction_line(trimmed) {
            continue;
        }
        if trimmed == "(check-sat)" || trimmed.starts_with("(get-value") || trimmed == "(exit)" {
            continue;
        }
        if trimmed.starts_with("(declare-const ay_assume_final ") {
            has_assume_final = true;
        }

        query.push_str(line);
        query.push('\n');
    }

    // `kani::assume` joins the compiler's ORDERED assumption context (suffix
    // semantics — a later assume must not mask an earlier check), so the
    // assumes are no longer top-level asserts. The whole-trace conjunction the
    // vacuity question is about arrives instead as the unasserted flag
    // `ay_assume_final` (defined `= final_context` by the compiler); asserting
    // it here restores exactly what this probe asked when assumes were global.
    // Absent flag = the harness has no assumptions = nothing extra to assert.
    if has_assume_final {
        query.push_str("(assert ay_assume_final)\n");
    }

    query.push_str("(check-sat)\n");
    query.push_str("(exit)\n");
    query
}

/// Split an SMT-LIB2 script into its top-level S-expressions.
///
/// The CHC cover-query builder has to keep or drop whole commands, and a
/// line-based filter cannot do that: the SMT printer wraps a `(rule ...)`
/// across several lines, so dropping only the line that starts with `(rule `
/// leaves its continuation lines behind as free-floating garbage. Tracking
/// paren depth — outside `"strings"`, `|quoted symbols|` and `; comments` —
/// makes each command an indivisible unit.
///
/// A trailing unbalanced form is returned verbatim rather than dropped, so a
/// truncated file degrades into a solver parse error instead of a silently
/// altered query.
fn top_level_forms(content: &str) -> Vec<&str> {
    let bytes = content.as_bytes();
    let mut forms = Vec::new();
    let mut depth: usize = 0;
    let mut start: Option<usize> = None;
    let mut i = 0usize;

    while i < bytes.len() {
        match bytes[i] {
            b';' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'"' => {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'"' {
                        // `""` is an escaped quote inside an SMT-LIB string.
                        if bytes.get(i + 1) == Some(&b'"') {
                            i += 2;
                            continue;
                        }
                        break;
                    }
                    i += 1;
                }
                i += 1;
            }
            b'|' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'|' {
                    i += 1;
                }
                i += 1;
            }
            b'(' => {
                if depth == 0 {
                    start = Some(i);
                }
                depth += 1;
                i += 1;
            }
            b')' => {
                i += 1;
                depth = depth.saturating_sub(1);
                if depth == 0
                    && let Some(s) = start.take()
                {
                    forms.push(&content[s..i]);
                }
            }
            _ => i += 1,
        }
    }

    if let Some(s) = start {
        forms.push(&content[s..]);
    }
    forms
}

/// Read the leading token of `s` (a symbol, possibly `|quoted|`), plus the rest.
fn split_token(s: &str) -> Option<(&str, &str)> {
    let s = s.trim_start();
    if let Some(rest) = s.strip_prefix('|') {
        let end = rest.find('|')?;
        return Some((&s[..end + 2], &rest[end + 1..]));
    }
    if s.is_empty() {
        return None;
    }
    let end = s.find(|c: char| c.is_whitespace() || c == '(' || c == ')').unwrap_or(s.len());
    if end == 0 {
        return None;
    }
    Some((&s[..end], &s[end..]))
}

/// The command name of a top-level form: `(declare-var x S)` -> `declare-var`.
fn form_head(form: &str) -> &str {
    form.strip_prefix('(')
        .and_then(split_token)
        .map(|(head, _)| head)
        .unwrap_or("")
}

/// The declared symbol of a `declare-*` form: `(declare-var x S)` -> `x`.
fn declared_symbol(form: &str) -> Option<&str> {
    let (_, rest) = split_token(form.strip_prefix('(')?)?;
    split_token(rest).map(|(name, _)| name)
}

/// Build a secondary SMT query to check cover property satisfiability from CHC content.
///
/// CHC files use `(set-logic HORN)` with `(declare-rel)`, `(rule)`, and `(query)`
/// constructs that standard SMT solvers cannot process. This function keeps every
/// declaration and constraint the cover assertion can refer to, drops the Horn
/// constructs, and appends one push/assert/check-sat/pop block per cover.
///
/// Part of #1162: Cover semantics for CHC path.
///
/// # `declare-var` becomes `declare-const`
///
/// The cover assertion the compiler emits — `(assert (= ay_cover_0 <cond>))` —
/// is written over the Horn program's `(declare-var ...)` symbols. Stripping
/// those lines (as this builder used to) left the assertion referring to
/// undeclared names, so the solver answered `(error "unknown constant ...")`,
/// nothing parsed as sat/unsat, and EVERY cover landed UNDETERMINED. A Horn
/// `declare-var` is a rule-local universal; in a plain query asking "can this
/// condition hold", the same symbol is an existentially quantified unknown —
/// exactly `declare-const`. Names already declared by the program's own
/// `declare-const`/`declare-fun` are not re-declared (a duplicate declaration
/// is a hard solver error).
///
/// # What this query can and cannot decide — read before trusting a `sat`
///
/// Plain SMT cannot express Horn reachability, so the `(rule ...)`s stay out;
/// and the emitted cover record carries the cover's CONDITION but never the
/// program point it guards, so nothing in the file ties the condition to the
/// path constraints and `kani::assume`s that bound it. The query therefore
/// ranges over ALL states, reachable or not — an over-approximation. Only one
/// direction of its answer survives that:
///
/// * `unsat` — no state anywhere satisfies the condition, so a fortiori no
///   *reachable* one does. Sound: the cover really is unsatisfiable.
/// * `sat` — some state satisfies it, with no evidence that state is reachable.
///   `assume(x < 10); cover!(x > 200)` answers sat here, and so does
///   `assume(false); cover!(true)`. Reading that as SATISFIED is fail-open.
///
/// `KaniSession::check_cover_satisfiability_for_chc` is where that asymmetry is
/// applied; this builder only guarantees the query is well-formed.
///
/// REQUIRES: smt_content is valid CHC/HORN SMT-LIB2 content
/// REQUIRES: cover_names are non-empty and match `ay_cover_*` declarations in smt_content
/// ENSURES: result does NOT contain `(set-logic HORN)`, `(declare-rel)`, `(rule)`, `(query)`
/// ENSURES: every `(declare-var n s)` appears as `(declare-const n s)`
/// ENSURES: result contains push/pop blocks for each cover name
pub(crate) fn build_cover_sat_query_for_chc(smt_content: &str, cover_names: &[String]) -> String {
    let mut query = String::with_capacity(smt_content.len() + cover_names.len() * 40);
    let mut declared: std::collections::HashSet<&str> = std::collections::HashSet::new();

    for form in top_level_forms(smt_content) {
        match form_head(form) {
            // Horn logic has no plain-SMT decision procedure; ALL does.
            "set-logic" => query.push_str("(set-logic ALL)\n"),
            // Horn-only constructs: unrepresentable in a plain query.
            "declare-rel" | "rule" | "query" => {}
            // Solver directives: this builder appends its own.
            "check-sat" | "check-sat-assuming" | "get-value" | "get-model" | "exit" => {}
            "declare-var" => {
                if let Some(name) = declared_symbol(form)
                    && declared.insert(name)
                {
                    query.push_str(&form.replacen("(declare-var", "(declare-const", 1));
                    query.push('\n');
                }
            }
            "declare-const" | "declare-fun" => {
                if let Some(name) = declared_symbol(form) {
                    declared.insert(name);
                }
                query.push_str(form);
                query.push('\n');
            }
            "assert" => {
                let trimmed = form.trim();
                // A cover asks "could this point be hit in a FEASIBLE run", and
                // the caller has already accepted the program constraints — so
                // `(assert false)` is dropped here, exactly as in
                // `build_cover_sat_query`. The violation disjunction is the
                // main query's question, not a constraint.
                if trimmed == "(assert false)" || is_violation_disjunction_line(trimmed) {
                    continue;
                }
                query.push_str(form);
                query.push('\n');
            }
            // set-option, set-info, declare-datatypes, define-fun, ... — every
            // one of these can be referenced by a cover condition, so keep it.
            _ => {
                query.push_str(form);
                query.push('\n');
            }
        }
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
    // Depth still owed by a cover assertion whose printed form wrapped across
    // lines. Dropping only its first line would leave the continuation lines
    // behind as free-floating garbage that the HORN parser rejects — which
    // turns a cover into a whole-harness solver error. Line-exactness is kept
    // for every line this does NOT drop, because callers compare the returned
    // length against the input to decide whether to write a separate file.
    let mut owed: i32 = 0;

    for line in smt_content.lines() {
        if owed > 0 {
            owed += paren_delta(line);
            continue;
        }
        let trimmed = line.trim();
        if trimmed.starts_with("(declare-const ay_cover_")
            || trimmed.starts_with("(assert (= ay_cover_")
        {
            changed = true;
            owed = paren_delta(line).max(0);
            continue;
        }
        stripped.push_str(line);
        stripped.push('\n');
    }

    if changed { stripped } else { smt_content.to_owned() }
}

/// Net paren depth one line contributes, ignoring `"strings"`, `|quoted
/// symbols|` and `; comments`.
fn paren_delta(line: &str) -> i32 {
    let bytes = line.as_bytes();
    let mut delta = 0i32;
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b';' => break,
            b'"' => {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'"' {
                        if bytes.get(i + 1) == Some(&b'"') {
                            i += 2;
                            continue;
                        }
                        break;
                    }
                    i += 1;
                }
                i += 1;
            }
            b'|' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'|' {
                    i += 1;
                }
                i += 1;
            }
            b'(' => {
                delta += 1;
                i += 1;
            }
            b')' => {
                delta -= 1;
                i += 1;
            }
            _ => i += 1,
        }
    }
    delta
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "a panicking assertion is the point in tests")]
mod vacuity_query_tests {
    use super::*;

    /// The BMC query shape trust-mc emits for `kani::assume(false); assert!(x == 42)`.
    const VACUOUS_QUERY: &str = "\
(set-logic QF_AUFBV)
(declare-const ay_any_0 (_ BitVec 8))
(assert false)
(declare-const ay_violation_kani_assert_0 Bool)
(assert (= ay_violation_kani_assert_0 (not (= ay_any_0 #x2a))))
(assert ay_violation_kani_assert_0)
(check-sat)
(get-value (ay_violation_kani_assert_0))
";

    #[test]
    fn reachability_query_keeps_the_contradiction_that_makes_a_proof_vacuous() {
        let query = build_harness_reachability_query(VACUOUS_QUERY);
        // `(assert false)` IS the thing under test here — losing it would make
        // every vacuous harness look reachable. Note `build_cover_sat_query`
        // deliberately drops it, which is why this needs its own builder.
        assert!(query.contains("(assert false)"), "{query}");
        assert!(
            !build_cover_sat_query(VACUOUS_QUERY, &["c".to_string()]).contains("(assert false)")
        );
    }

    #[test]
    fn reachability_query_drops_the_violation_question_and_asks_once() {
        let query = build_harness_reachability_query(VACUOUS_QUERY);
        // The violation disjunction is the main query's question, not a program
        // constraint; asking it again here would defeat the probe.
        assert!(!query.contains("(assert ay_violation_kani_assert_0)"), "{query}");
        // The *definition* of the violation flag is a constraint and stays.
        assert!(
            query.contains("(= ay_violation_kani_assert_0 (not (= ay_any_0 #x2a))))"),
            "{query}"
        );
        assert_eq!(query.matches("(check-sat)").count(), 1, "{query}");
        assert!(!query.contains("(get-value"), "{query}");
    }

    #[test]
    fn reachability_query_preserves_declarations_and_a_feasible_harness() {
        let feasible = "\
(set-logic QF_AUFBV)
(declare-const ay_any_0 (_ BitVec 8))
(assert (bvult ay_any_0 #x0a))
(declare-const ay_violation_kani_assert_0 Bool)
(assert (or ay_violation_kani_assert_0))
(check-sat)
";
        let query = build_harness_reachability_query(feasible);
        assert!(query.contains("(declare-const ay_any_0 (_ BitVec 8))"), "{query}");
        assert!(query.contains("(assert (bvult ay_any_0 #x0a))"), "{query}");
        assert!(!query.contains("(assert (or ay_violation_kani_assert_0))"), "{query}");
    }

    /// `kani::assume` joins the compiler's ordered assumption context (suffix
    /// semantics), so the whole-trace assumption conjunction reaches this probe
    /// as the UNASSERTED flag `ay_assume_final`. The probe must assert it —
    /// otherwise `assume(x < 10); assume(x > 200)` would look feasible and the
    /// vacuity gate would blame dead code instead of the assumptions.
    #[test]
    fn reachability_query_asserts_the_assume_final_flag_when_declared() {
        let with_flag = "\
(set-logic QF_AUFBV)
(declare-const ay_any_0 (_ BitVec 8))
(declare-const ay_assume_ctx_0 Bool)
(assert (= ay_assume_ctx_0 (and (bvult ay_any_0 #x0a) (bvugt ay_any_0 #xc8))))
(declare-const ay_assume_final Bool)
(assert (= ay_assume_final ay_assume_ctx_0))
(declare-const ay_violation_kani_assert_0 Bool)
(assert (= ay_violation_kani_assert_0 (and ay_assume_ctx_0 (not (= ay_any_0 #x2a)))))
(assert ay_violation_kani_assert_0)
(check-sat)
";
        let query = build_harness_reachability_query(with_flag);
        assert!(query.contains("(assert ay_assume_final)"), "{query}");
        // The definition stays too — asserting the flag without it would be free.
        assert!(query.contains("(assert (= ay_assume_final ay_assume_ctx_0))"), "{query}");

        // Control: a harness with no assumptions has no flag and gains no assert.
        let query = build_harness_reachability_query(VACUOUS_QUERY);
        assert!(!query.contains("(assert ay_assume_final)"), "{query}");
    }
}
