// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Violation and cover property parsing from SMT solver output.

use std::borrow::Cow;
use std::collections::BTreeMap;

use crate::coverage::cov_results::{CoverageCheck, CoverageRegion, CoverageResults};
use crate::property_model::{CheckStatus, Property, PropertyId, RawSourceLocation, TraceItem};
use crate::verification_result::{FailedProperties, VerificationStatus};

use super::vc_artifact::{
    LOOP_INVARIANT_BASE_CLASS, LOOP_INVARIANT_BASE_REPORT_TEXT, LOOP_INVARIANT_STEP_CLASS,
    LOOP_INVARIANT_STEP_REPORT_TEXT, VcLocationMap,
};

/// Mirrors `trust-mc-compiler`'s
/// `kani_middle::transform::loop_contracts::rule::{LOOP_INVARIANT_BASE_MSG,
/// LOOP_INVARIANT_STEP_MSG, LOOP_ID_MARKER}`; the two crates share no code, so
/// the stems are duplicated here on purpose (as `LOOP_CONTRACT_OBLIGATION_PREFIXES`
/// already duplicates their prefixes).
const LOOP_INVARIANT_BASE_MSG: &str = "loop invariant base case: invariant must hold on loop entry";
const LOOP_INVARIANT_STEP_MSG: &str =
    "loop invariant inductive step: invariant must be re-established by the loop body";
const LOOP_ID_MARKER: &str = "(loop ";

/// Parse SMT solver output and extract verification results.
///
/// SMT solver semantics for verification:
/// - "unsat" = no counterexample found = verification SUCCESS
/// - "sat" = counterexample exists = verification FAILURE
/// - "unknown" = solver could not determine = treat as FAILURE (conservative)
///
/// REQUIRES: output is UTF-8 text from an SMT solver (ay, CVC5, etc.)
/// REQUIRES: output contains one of "sat", "unsat", "unknown" on its own line (or is malformed)
/// ENSURES: Returns Success iff output contains "unsat" line
/// ENSURES: Returns Failure with FailedProperties::None only on Success
/// ENSURES: Returns Failure with FailedProperties::Other for sat/unknown/malformed
pub(crate) fn parse_solver_output(output: &str) -> (VerificationStatus, FailedProperties) {
    // Parse line by line to find the solver result.
    // SMT solvers output "sat", "unsat", or "unknown" on their own line.
    for line in output.lines() {
        let trimmed = line.trim();
        if trimmed == "unsat" {
            return (VerificationStatus::Success, FailedProperties::None);
        } else if trimmed == "sat" {
            return (VerificationStatus::Failure, FailedProperties::Other);
        }
        // "unknown" falls through to default failure case
    }
    // Unknown or empty result - treat as failure for safety
    (VerificationStatus::Failure, FailedProperties::Other)
}

/// Build a property list from violation declarations for UNSAT (success) cases.
///
/// When the solver returns UNSAT, all checks passed. This function builds
/// the property list from the SMT file's violation declarations so we can
/// report "N of N checks passed" instead of "0 of 0".
///
/// REQUIRES: violation_names contains names in format "ay_violation_<label>_<id>" or just "<label>_<id>"
/// REQUIRES: each name has a numeric suffix after the last underscore (or defaults to id=0)
/// ENSURES: result.len() == violation_names.len()
/// ENSURES: all returned properties have status == CheckStatus::Success
/// ENSURES: property_id.id matches the parsed numeric suffix from the name
/// ENSURES: source_location is populated from location_map when available
pub(crate) fn build_success_properties(
    violation_names: &[String],
    location_map: Option<&VcLocationMap>,
) -> Vec<Property> {
    build_declared_properties(violation_names, location_map, CheckStatus::Success)
}

/// Build a property list from violation declarations with every check
/// UNDETERMINED — the undecided-solver counterpart of
/// [`build_success_properties`].
///
/// When the solver answers `unknown` (or returns a model that names no
/// violation), there is no per-check verdict to read out of the solver, so the
/// model-derived list is empty and the report used to print an EMPTY check
/// table under a "0 of 0 failed" summary — indistinguishable from a harness
/// that genuinely emitted no obligations. Kani prints every check it emitted
/// with `Status: UNDETERMINED` and the real description; this rebuilds that
/// list from the SMT declarations.
///
/// SOUNDNESS: `Undetermined` is the fail-closed status. It claims nothing —
/// not proved, not violated — so no obligation is dropped and no undecided
/// check is upgraded. The only thing that changes is that the obligations the
/// harness actually emitted become VISIBLE instead of silently absent.
///
/// REQUIRES: violation_names in the same format `build_success_properties` takes
/// ENSURES: result.len() == violation_names.len()
/// ENSURES: all returned properties have status == CheckStatus::Undetermined
pub(crate) fn build_undetermined_properties(
    violation_names: &[String],
    location_map: Option<&VcLocationMap>,
) -> Vec<Property> {
    build_declared_properties(violation_names, location_map, CheckStatus::Undetermined)
}

/// Shared body of [`build_success_properties`] and
/// [`build_undetermined_properties`]: identical name parsing, location lookup
/// and description recovery, differing only in the status stamped on each check.
fn build_declared_properties(
    violation_names: &[String],
    location_map: Option<&VcLocationMap>,
    status: CheckStatus,
) -> Vec<Property> {
    violation_names
        .iter()
        .map(|name| {
            // Strip "ay_violation_" prefix and parse
            let trimmed = name.strip_prefix("ay_violation_").unwrap_or(name);
            let (label, id) = parse_violation_name(trimmed);
            let (class, fallback_description) = classify_violation(&label);

            // Look up source location and message from artifact map if available
            let info = location_map.and_then(|map| map.get(name));
            let source_location = info.map(|i| i.location.clone()).unwrap_or(RawSourceLocation {
                column: None,
                file: None,
                function: None,
                line: None,
            });
            // Prefer the captured message (e.g. "assertion failed: foo() == None")
            // over the generic label-derived fallback.
            let description = info
                .and_then(|i| i.message.clone())
                .map(Cow::Owned)
                .unwrap_or(Cow::Borrowed(fallback_description));

            Property {
                description,
                property_id: PropertyId { fn_name: None, class: Cow::Borrowed(class), id },
                source_location,
                status,

                trace: None,
            }
        })
        .collect()
}

/// Build cover properties with Undetermined status (fallback).
///
/// Returns cover properties with Undetermined status. Used as a fallback when
/// secondary SAT checks cannot be performed (e.g., CHC path, solver errors).
/// See `build_cover_properties_from_sat_checks` for the primary path (#1162)
/// that computes SATISFIED/UNSATISFIABLE semantics.
///
/// #1164: Supports location mapping via `smt_var` in the VC artifact.
///
/// REQUIRES: cover_names contains names in format "ay_cover_<id>"
/// ENSURES: result.len() == cover_names.len()
/// ENSURES: all returned properties have status == CheckStatus::Undetermined
/// ENSURES: all returned properties have class == "cover"
/// ENSURES: source_location is populated from location_map when available
#[cfg(test)]
fn build_cover_properties_undetermined(
    cover_names: &[String],
    location_map: Option<&VcLocationMap>,
) -> Vec<Property> {
    cover_names
        .iter()
        .map(|name| {
            // Parse the cover ID from the name
            let id =
                name.strip_prefix("ay_cover_").and_then(|s| s.parse::<u32>().ok()).unwrap_or(0);

            // #1164: Look up location from map if available
            let source_location =
                location_map.and_then(|map| map.get(name)).map(|i| i.location.clone()).unwrap_or(
                    RawSourceLocation { column: None, file: None, function: None, line: None },
                );

            Property {
                description: Cow::Owned(format!("cover property {}", id)),
                property_id: PropertyId { fn_name: None, class: Cow::Borrowed("cover"), id },
                source_location,
                status: CheckStatus::Undetermined,

                trace: None,
            }
        })
        .collect()
}

/// Build cover properties from secondary satisfiability check results.
///
/// When the main verification query returns UNSAT, a secondary query checks
/// each cover property individually. This function converts the solver's
/// per-cover results into Property structs with correct cover semantics:
/// - sat -> SATISFIED (cover condition is reachable)
/// - unsat -> UNSATISFIABLE (cover condition is never reachable)
/// - other -> UNDETERMINED (solver could not determine)
///
/// REQUIRES: cover_names in format "ay_cover_<id>"
/// REQUIRES: sat_results.len() == cover_names.len()
/// REQUIRES: each sat_result is one of: Some(true)=SAT, Some(false)=UNSAT, None=unknown
/// ENSURES: result.len() == cover_names.len()
/// ENSURES: all returned properties have class == "cover"
/// ENSURES: source_location is populated from location_map when available
pub(crate) fn build_cover_properties_from_sat_checks(
    cover_names: &[String],
    sat_results: &[Option<bool>],
    location_map: Option<&VcLocationMap>,
) -> Vec<Property> {
    cover_names
        .iter()
        .zip(sat_results.iter())
        .map(|(name, sat_result)| {
            let id =
                name.strip_prefix("ay_cover_").and_then(|s| s.parse::<u32>().ok()).unwrap_or(0);

            let info = location_map.and_then(|map| map.get(name));
            let source_location = info.map(|i| i.location.clone()).unwrap_or(RawSourceLocation {
                column: None,
                file: None,
                function: None,
                line: None,
            });

            let status = match sat_result {
                Some(true) => CheckStatus::Satisfied,
                Some(false) => CheckStatus::Unsatisfiable,
                None => CheckStatus::Undetermined,
            };

            // Kani parity: the artifact message carries the text the user wrote
            // (`cover condition: <expr>` from `kani::cover!(expr)`, or the custom
            // message). Only without one fall back to the numbered placeholder.
            let description = info
                .and_then(|i| i.message.clone())
                .map(Cow::Owned)
                .unwrap_or_else(|| Cow::Owned(format!("cover property {}", id)));

            Property {
                description,
                property_id: PropertyId { fn_name: None, class: Cow::Borrowed("cover"), id },
                source_location,
                status,
                trace: None,
            }
        })
        .collect()
}

/// Parse the output of a secondary cover satisfiability query.
///
/// The secondary query uses push/pop blocks, producing one "sat" or "unsat"
/// per cover property. This function parses the output to extract per-cover results.
///
/// REQUIRES: output contains one result line per cover property
/// REQUIRES: num_covers is the expected number of cover results
/// ENSURES: result.len() == num_covers
/// ENSURES: each element is Some(true) for "sat", Some(false) for "unsat", None for other
pub(crate) fn parse_cover_sat_check_output(output: &str, num_covers: usize) -> Vec<Option<bool>> {
    let mut results = Vec::with_capacity(num_covers);

    for line in output.lines() {
        let trimmed = line.trim();
        if trimmed == "sat" {
            results.push(Some(true));
        } else if trimmed == "unsat" {
            results.push(Some(false));
        } else if trimmed == "unknown" {
            // An undecided probe must occupy its OWN slot. Skipping it and
            // padding `None` at the end is correct only when every `unknown`
            // is at the tail, which is the truncation case. It is not the only
            // case: ay also answers `unknown` from incompleteness mid-file
            // (`(:reason-unknown incomplete)`) and then decides later probes.
            // Dropping the slot shifts every later verdict up by one, and the
            // shifted values are acted on — `Some(false)` promotes a check to
            // CheckStatus::Unreachable, which is treated as dead code and NOT
            // verified. That is a wrong answer in the direction that hides
            // work, so a probe that was never decided must never inherit a
            // neighbour's verdict.
            results.push(None);
        }
        // Skip other lines (errors, warnings, empty lines)

        if results.len() == num_covers {
            break;
        }
    }

    // Pad with None if solver produced fewer results than expected
    while results.len() < num_covers {
        results.push(None);
    }

    results
}

/// Build success properties for violations plus undetermined cover properties.
///
/// This is a convenience function that combines `build_success_properties` and
/// `build_cover_properties_undetermined` for the UNSAT (verification success) case.
///
/// REQUIRES: violation_names in format "ay_violation_<label>_<id>" (see build_success_properties)
/// REQUIRES: cover_names in format "ay_cover_<id>" (see build_cover_properties_undetermined)
/// ENSURES: result.len() == violation_names.len() + cover_names.len()
/// ENSURES: first violation_names.len() properties have Success status
/// ENSURES: last cover_names.len() properties have Undetermined status
/// ENSURES: source_location is populated from location_map when available
#[cfg(test)]
pub(crate) fn build_success_and_cover_properties(
    violation_names: &[String],
    cover_names: &[String],
    location_map: Option<&VcLocationMap>,
) -> Vec<Property> {
    let mut properties = build_success_properties(violation_names, location_map);
    let cover_properties = build_cover_properties_undetermined(cover_names, location_map);
    properties.extend(cover_properties);
    properties
}

/// Parse violation properties from solver output.
///
/// The output format from SMT get-value is:
/// ```text
/// ((ay_violation_kani_assert_0 true)
///  (ay_violation_overflow_check_add_1 false))
/// ```
/// REQUIRES: output is solver output containing (ay_violation_* true|false) entries (may be empty)
/// REQUIRES: is_sat correctly reflects whether solver returned SAT (for status interpretation)
/// REQUIRES: any_trace is None when is_sat is false (no trace for UNSAT)
/// ENSURES: returned properties have status==Failure only when is_sat && violation value is "true"
/// ENSURES: returned properties have trace populated only when is_sat is true
/// ENSURES: each ay_violation entry in output produces exactly one Property in result
/// ENSURES: source_location is populated from location_map when available
pub(crate) fn parse_violation_properties(
    output: &str,
    is_sat: bool,
    any_trace: Option<&[TraceItem]>,
    location_map: Option<&VcLocationMap>,
) -> Vec<Property> {
    let mut properties = Vec::new();
    let trace_items = if is_sat { Some(any_trace.unwrap_or(&[])) } else { None };

    for (violation_name, value_token) in scan_violation_entries(output) {
        let is_violated = is_sat && value_token == "true";

        // Build full variable name for location lookup
        let full_var_name = format!("ay_violation_{}", violation_name);

        // Parse the label and id from the violation name
        let (label, id) = parse_violation_name(violation_name);

        // Determine the status
        let status = if is_violated { CheckStatus::Failure } else { CheckStatus::Success };

        // Classify the violation to get property class and fallback description
        let (class, fallback_description) = classify_violation(&label);

        // Look up source location and message from artifact map if available
        let info = location_map.and_then(|map| map.get(&full_var_name));
        let source_location = info.map(|i| i.location.clone()).unwrap_or(RawSourceLocation {
            column: None,
            file: None,
            function: None,
            line: None,
        });
        // Prefer the captured message (e.g. "assertion failed: foo() == None")
        // over the generic label-derived fallback.
        let description = info
            .and_then(|i| i.message.clone())
            .map(Cow::Owned)
            .unwrap_or(Cow::Borrowed(fallback_description));

        // Create the property
        let property = Property {
            description,
            property_id: PropertyId { fn_name: None, class: Cow::Borrowed(class), id },
            source_location,
            status,

            trace: trace_items.map(|items| items.to_vec()),
        };

        properties.push(property);
    }

    properties
}

/// Scan `(ay_violation_<name> <value>)` entries from get-value output.
///
/// Returns `(name, value_token)` pairs (name without the `ay_violation_`
/// prefix) in output order. This is the single scanner backing
/// `parse_violation_properties` and `parse_violation_entry_names`, keeping
/// their per-entry alignment exact.
fn scan_violation_entries(output: &str) -> Vec<(&str, &str)> {
    let mut entries = Vec::new();
    let prefix = "ay_violation_";
    let mut idx = 0;
    let bytes = output.as_bytes();

    while idx < output.len() {
        let haystack = &output[idx..];
        let Some(rel_pos) = haystack.find(prefix) else {
            break;
        };
        let start = idx + rel_pos;
        let mut cursor = start + prefix.len();

        // Extract the violation name (until space or parenthesis)
        let name_start = cursor;
        while cursor < bytes.len() && bytes[cursor] != b' ' && bytes[cursor] != b')' {
            cursor += 1;
        }
        let violation_name = &output[name_start..cursor];

        // Determine true/false value: skip whitespace, then read the value token
        while cursor < bytes.len() && bytes[cursor] == b' ' {
            cursor += 1;
        }
        let value_start = cursor;
        while cursor < bytes.len() && bytes[cursor] != b')' && bytes[cursor] != b' ' {
            cursor += 1;
        }
        let value_token = &output[value_start..cursor];

        entries.push((violation_name, value_token));

        // Advance past this entry
        idx = cursor;
    }

    entries
}

/// Full violation variable names from get-value output, in output order.
///
/// Index-aligned with the properties returned by `parse_violation_properties`
/// for the same output (both are driven by `scan_violation_entries`). Used by
/// the driver to re-query individual violation flags after a SAT result.
pub(crate) fn parse_violation_entry_names(output: &str) -> Vec<String> {
    scan_violation_entries(output)
        .into_iter()
        .map(|(name, _)| format!("ay_violation_{}", name))
        .collect()
}

/// Parse cover entries from solver output.
fn parse_cover_entries(output: &str) -> Vec<(u32, bool)> {
    let mut entries = Vec::new();
    let bytes = output.as_bytes();
    let mut idx = 0;

    while idx < bytes.len() {
        let haystack = &output[idx..];
        let Some(rel_pos) = haystack.find("ay_cover_") else {
            break;
        };
        let start = idx + rel_pos;
        let mut cursor = start + "ay_cover_".len();

        // Parse the numeric id.
        let id_start = cursor;
        while cursor < bytes.len() && bytes[cursor].is_ascii_digit() {
            cursor += 1;
        }
        if id_start == cursor {
            idx = cursor.saturating_add(1);
            continue;
        }
        let id = match output[id_start..cursor].parse::<u32>() {
            Ok(id) => id,
            Err(_) => {
                idx = cursor.saturating_add(1);
                continue;
            }
        };

        // Skip whitespace before the value.
        while cursor < bytes.len() && bytes[cursor].is_ascii_whitespace() {
            cursor += 1;
        }

        let remainder = &output[cursor..];
        let (is_satisfied, consumed) = if remainder.starts_with("true") {
            (true, "true".len())
        } else if remainder.starts_with("false") {
            (false, "false".len())
        } else {
            idx = cursor.saturating_add(1);
            continue;
        };

        entries.push((id, is_satisfied));
        idx = cursor + consumed;
    }

    entries
}

fn parse_named_bool_entries(output: &str, prefix: &str) -> Vec<(String, bool)> {
    let mut entries = Vec::new();
    let bytes = output.as_bytes();
    let mut idx = 0;

    while idx < bytes.len() {
        let haystack = &output[idx..];
        let Some(rel_pos) = haystack.find(prefix) else {
            break;
        };
        let start = idx + rel_pos;
        let mut cursor = start + prefix.len();

        while cursor < bytes.len() && bytes[cursor] != b' ' && bytes[cursor] != b')' {
            cursor += 1;
        }
        let name = &output[start..cursor];

        while cursor < bytes.len() && bytes[cursor].is_ascii_whitespace() {
            cursor += 1;
        }

        let remainder = &output[cursor..];
        let (value, consumed) = if remainder.starts_with("true") {
            (true, "true".len())
        } else if remainder.starts_with("false") {
            (false, "false".len())
        } else {
            idx = cursor.saturating_add(1);
            continue;
        };

        entries.push((name.to_string(), value));
        idx = cursor + consumed;
    }

    entries
}

fn coverage_counter_from_name(name: &str) -> u32 {
    name.strip_prefix("ay_coverage_").and_then(|suffix| suffix.parse().ok()).unwrap_or(0)
}

fn coverage_check_from_location(
    name: &str,
    is_covered: bool,
    location: Option<RawSourceLocation>,
) -> (String, CoverageCheck) {
    let location = location.unwrap_or(RawSourceLocation {
        column: None,
        file: None,
        function: None,
        line: None,
    });
    let file = location.file.unwrap_or_else(|| "<unknown>".to_string());
    let line = location.line.and_then(|line| line.parse::<u32>().ok()).unwrap_or(0);
    let column = location.column.and_then(|column| column.parse::<u32>().ok()).unwrap_or(0);
    let function = location.function.unwrap_or_else(|| "<unknown>".to_string());
    let status = if is_covered { CheckStatus::Covered } else { CheckStatus::Uncovered };
    let region = CoverageRegion { file: file.clone(), start: (line, column), end: (line, column) };
    let check = CoverageCheck::counter(function, coverage_counter_from_name(name), region, status);
    (file, check)
}

pub(crate) fn build_coverage_results_from_sat_checks(
    coverage_names: &[String],
    sat_results: &[Option<bool>],
    location_map: Option<&VcLocationMap>,
) -> CoverageResults {
    let mut data: BTreeMap<String, Vec<CoverageCheck>> = BTreeMap::new();
    for (name, sat_result) in coverage_names.iter().zip(sat_results.iter()) {
        let (file, check) = coverage_check_from_location(
            name,
            sat_result.unwrap_or(false),
            location_map.and_then(|map| map.get(name)).map(|i| i.location.clone()),
        );
        data.entry(file).or_default().push(check);
    }
    CoverageResults { data }
}

pub(crate) fn parse_coverage_results(
    output: &str,
    location_map: Option<&VcLocationMap>,
) -> CoverageResults {
    let mut data: BTreeMap<String, Vec<CoverageCheck>> = BTreeMap::new();
    for (name, is_covered) in parse_named_bool_entries(output, "ay_coverage_") {
        let (file, check) = coverage_check_from_location(
            &name,
            is_covered,
            location_map.and_then(|map| map.get(&name)).map(|i| i.location.clone()),
        );
        data.entry(file).or_default().push(check);
    }
    CoverageResults { data }
}

pub(crate) fn parse_cover_properties(
    output: &str,
    is_sat: bool,
    any_trace: Option<&[TraceItem]>,
    location_map: Option<&VcLocationMap>,
) -> Vec<Property> {
    let mut properties = Vec::new();

    if !is_sat {
        // For UNSAT, we can't determine cover reachability from the main query.
        // The cover properties would need a separate satisfiability check.
        // For now, return no cover results when UNSAT.
        return properties;
    }

    // Parse cover flags from get-value output
    // Format: (ay_cover_N true|false)
    for (id, is_satisfied) in parse_cover_entries(output) {
        // Determine the status
        // Cover semantics: true = SATISFIED, false = UNSATISFIABLE
        let status = if is_satisfied { CheckStatus::Satisfied } else { CheckStatus::Unsatisfiable };

        // Attach trace for satisfied covers to enable concrete playback (#1272)
        // Only satisfied covers need traces - unsatisfied covers have no
        // concrete values to replay
        let trace = if is_satisfied { any_trace.map(|items| items.to_vec()) } else { None };

        // Kani parity: prefer the artifact's message (`cover condition: <expr>`
        // or the user's custom message) and location over the numbered
        // placeholder, exactly as build_cover_properties_from_sat_checks does.
        let full_var_name = format!("ay_cover_{}", id);
        let info = location_map.and_then(|map| map.get(&full_var_name));
        let source_location = info.map(|i| i.location.clone()).unwrap_or(RawSourceLocation {
            column: None,
            file: None,
            function: None,
            line: None,
        });
        let description = info
            .and_then(|i| i.message.clone())
            .map(Cow::Owned)
            .unwrap_or_else(|| Cow::Owned(format!("cover property {}", id)));

        // Create the cover property
        let property = Property {
            description,
            property_id: PropertyId { fn_name: None, class: Cow::Borrowed("cover"), id },
            source_location,
            status,

            trace,
        };

        properties.push(property);
    }

    properties
}

/// Kani-parity naming for the two loop-invariant obligations.
///
/// The instrumentation registers both through `hook_safety_check`, so they
/// reach the driver as class `assertion` carrying the compiler's internal
/// message stem plus a `(loop N)` suffix (see
/// `trust-mc-compiler`'s `loop_contracts::rule::LOOP_INVARIANT_BASE_MSG`).
/// Kani/CBMC lists them under their own classes with a different description:
///
/// ```text
/// main.loop_invariant_base.1
///  - Status: SUCCESS
///  - Description: "Check invariant before entry for loop main.0"
/// ```
///
/// Display only: nothing maps these ids back to solver variables (the
/// SMT-name correlation is finished by the time this runs), and the STATUS is
/// never touched — an UNREACHABLE base case stays UNREACHABLE under its new
/// name. The function name in the description is taken from the check's own
/// source location, the same source `apply_kani_property_naming` uses for the
/// check-id prefix, so the two can never disagree.
///
/// A property whose message lacks the `(loop N)` suffix is left ALONE: without
/// the index there is no honest loop id to print, and a made-up one would be
/// worse than the internal wording.
///
/// REQUIRES: runs before `apply_kani_property_naming` (it renumbers per class)
/// ENSURES: `prop.status` is unchanged for every property
pub(crate) fn apply_loop_contract_naming(properties: &mut [Property]) {
    for prop in properties.iter_mut() {
        let (stem, class, text) = if prop.description.starts_with(LOOP_INVARIANT_BASE_MSG) {
            (LOOP_INVARIANT_BASE_MSG, LOOP_INVARIANT_BASE_CLASS, LOOP_INVARIANT_BASE_REPORT_TEXT)
        } else if prop.description.starts_with(LOOP_INVARIANT_STEP_MSG) {
            (LOOP_INVARIANT_STEP_MSG, LOOP_INVARIANT_STEP_CLASS, LOOP_INVARIANT_STEP_REPORT_TEXT)
        } else {
            continue;
        };
        // `<stem> (loop N)` -> N. Anything else keeps the internal wording.
        let Some(idx) = prop.description[stem.len()..]
            .trim_start()
            .strip_prefix(LOOP_ID_MARKER)
            .and_then(|rest| rest.strip_suffix(')'))
            .and_then(|n| n.parse::<u32>().ok())
        else {
            continue;
        };
        let Some(fn_name) = prop
            .property_id
            .fn_name
            .clone()
            .or_else(|| prop.source_location.function.clone())
        else {
            continue;
        };
        prop.description = Cow::Owned(format!("{text}{fn_name}.{idx}"));
        prop.property_id.class = Cow::Borrowed(class);
    }
}

/// Kani-parity check naming: rewrite each property id to
/// `<function>.<class>.<counter>` with a 1-based counter per
/// (function, class) pair, in listing order.
///
/// Kani (via CBMC) names every check after the function that contains it and
/// numbers checks 1-based within that function and class
/// (e.g. `main.assertion.1`, `check_foo.cover.2`). Our AY-native properties
/// arrive with a harness-global 0-based id parsed from the SMT variable name
/// and no function prefix (`assertion.0`). The SMT-name correlation (location
/// map lookups, cover sat-check zips) is finished by the time the property
/// list is assembled, so this is a display-only rename: nothing maps the
/// rewritten ids back to solver variables.
///
/// Runs `apply_loop_contract_naming` first: that step MOVES the two
/// loop-invariant obligations out of the `assertion` class, and the per-class
/// counters below have to see the final classes or every id is wrong.
///
/// ENSURES: fn_name is populated from the source location's function when absent
/// ENSURES: ids are 1-based and consecutive per (fn_name, class), in input order
pub(crate) fn apply_kani_property_naming(properties: &mut [Property]) {
    apply_loop_contract_naming(properties);
    let mut counters: BTreeMap<(Option<String>, String), u32> = BTreeMap::new();
    for prop in properties.iter_mut() {
        if prop.property_id.fn_name.is_none() {
            prop.property_id.fn_name = prop.source_location.function.clone();
        }
        let key = (prop.property_id.fn_name.clone(), prop.property_id.class.to_string());
        let counter = counters.entry(key).or_insert(0);
        *counter += 1;
        prop.property_id.id = *counter;
    }
}

/// Determine the FailedProperties classification from a list of properties.
///
/// Classifies the failure mode based on which property types failed:
/// - None: All properties passed (no Failure status)
/// - PanicsOnly: Only assertion failures (kani::assert, panic)
/// - Other: Non-assertion failures (overflow, bounds, etc.)
///
/// REQUIRES: properties contains valid Property structs with status field set
/// REQUIRES: property_id.class is "assertion" for kani::assert failures
/// ENSURES: Returns None iff no property has status == Failure
/// ENSURES: Returns Other if any non-assertion property has Failure status
/// ENSURES: Returns PanicsOnly only when assertion failures exist and no other failures exist
pub(crate) fn determine_failed_from_properties(properties: &[Property]) -> FailedProperties {
    let mut has_panic_failure = false;
    let mut has_other_failure = false;

    for prop in properties {
        if prop.status == CheckStatus::Failure {
            // A Rust panic reaches trust-mc as an "assertion", "panic", or
            // "unreachable" class check (see `classify_violation` and the CHC
            // `kind_class` mapping). All three count as a panic for
            // should_panic; every other class (memory_safety, null_pointer,
            // pointer_overflow, undefined_behavior, bounds, overflow, …) is a
            // non-panic failure.
            if matches!(prop.property_id.class.as_ref(), "assertion" | "panic" | "unreachable") {
                has_panic_failure = true;
            } else {
                has_other_failure = true;
            }
        }
    }

    if has_other_failure {
        FailedProperties::Other
    } else if has_panic_failure {
        FailedProperties::PanicsOnly
    } else {
        FailedProperties::None
    }
}

/// Parse a violation name like "kani_assert_0" or "overflow_check_add_1"
/// into (label, id).
fn parse_violation_name(name: &str) -> (&str, u32) {
    if let Some(last_underscore) = name.rfind('_') {
        let after_underscore = &name[last_underscore + 1..];
        if let Ok(id) = after_underscore.parse::<u32>() {
            let label = &name[..last_underscore];
            return (label, id);
        }
    }
    (name, 0)
}

/// Classify a violation label into (class, description).
fn classify_violation(label: &str) -> (&'static str, &'static str) {
    match label {
        "kani_assert" => ("assertion", "assertion failed"),
        "panic" | "panic_stub" => ("assertion", "panic reached"),
        // TerminatorKind::Unreachable — reaching it is UB, and Kani reports it
        // as class `unreachable` with description "unreachable code" (e.g.
        // `test_trivial_bounds.unreachable.1`). Rendering it as a panic hid
        // which kind of check fired. `determine_failed_from_properties` already
        // counts class "unreachable" in the panic family for should_panic.
        "unreachable" => ("unreachable", "unreachable code"),
        // BMC loop-unrolling bound. The unroller plants this check on the cut
        // back-edge of the last unrolled copy, so a FAILURE means the loop asked
        // for an iteration past `--unwind N` / `#[kani::unwind(N)]`. That is a
        // statement about the BOUND, never about the program, so it deliberately
        // does NOT join the panic classes above — three consumers key off that:
        //   * `determine_failed_from_properties` counts it as a non-panic
        //     failure, so a `should_panic` harness cannot bank an exhausted
        //     bound as "panicked as expected";
        //   * `extract_harness_values` already skips class "unwind", so no
        //     concrete-playback `#[test]` is minted for a bug that was never
        //     found;
        //   * `has_unwinding_assertion_failures` matches the "unwinding
        //     assertion loop" prefix of this description and appends the
        //     raise-the-bound tip (`UNWINDING_ASSERT_DESC`) — keep that prefix
        //     verbatim if this wording is ever revised.
        // Worded neutrally on purpose: when the bound IS sufficient this very
        // string renders as a SUCCESS check in the RESULTS listing, so it has to
        // read as an obligation rather than as a complaint. The "raise it"
        // advice lives in the tip and in `[AY:CTREX_NOT_CERTIFIED]`, both of
        // which fire only on the failing case.
        "unwind_assert" => {
            ("unwind", "unwinding assertion loop: the loop must exit within the --unwind bound")
        }
        // Kani-identical descriptions (commit c6746cbd6 direction): these render
        // in RESULTS listings and `Failed Checks:` lines, and the corpus expected
        // files pin Kani's exact wording. `div` vs `mod` matters: Rust (and Kani)
        // word `%` by zero as a remainder error, not a division error.
        "div_by_zero_check" => ("division-by-zero", "attempt to divide by zero"),
        "mod_by_zero_check" => {
            ("division-by-zero", "attempt to calculate the remainder with a divisor of zero")
        }
        // Generic/SIMD/bigint division-by-zero sites keep the neutral wording:
        // they are not the scalar `/` or `%` operator, so Kani's operator-specific
        // phrasing would be a false claim (and simd expected files pin this text).
        "division_by_zero" | "bigint_div_by_zero" | "bigint_mod_by_zero" => {
            ("division-by-zero", "division by zero")
        }
        "overflow_check_add" => ("overflow", "attempt to add with overflow"),
        "overflow_check_sub" => ("overflow", "attempt to subtract with overflow"),
        "overflow_check_mul" => ("overflow", "attempt to multiply with overflow"),
        "overflow_check_neg" => ("overflow", "attempt to negate with overflow"),
        // Signed INT_MIN / -1 overflow — Kani words `/` and `%` differently
        // (rustc's AssertKind texts), and the corpus pins both wordings.
        "overflow_check_div" => ("overflow", "attempt to divide with overflow"),
        "overflow_check_rem" => {
            ("overflow", "attempt to calculate the remainder with overflow")
        }
        "bounds_check" => {
            ("array_bounds", "index out of bounds: the length is less than or equal to the given index")
        }
        // Name WHICH intrinsic went out of bounds. The corpus expected files
        // (intrinsics/simd-{extract,insert}-out-of-bounds) pin the intrinsic
        // name on the line after `Status: FAILURE`, i.e. in this description —
        // and a user staring at a lane-index CTREX needs the callee, since the
        // check's Location points at the call site of an opaque intrinsic.
        "simd_extract" => ("array_bounds", "simd_extract: SIMD index out of bounds"),
        "simd_insert" => ("array_bounds", "simd_insert: SIMD index out of bounds"),
        "null_pointer_check" => ("pointer_dereference", "dereference failure: pointer NULL"),
        "alignment_check" => ("pointer_dereference", "dereference failure: pointer misaligned"),
        // Raw-pointer dereference validity — Kani instruments `*ptr` / `&*ptr`
        // with its own `safety_check`-class checks and these exact texts
        // (rustc's AssertKind wordings); the corpus pins them (zst, issue-3571,
        // ptr_to_ref_cast/alignment). The CBMC-flavored labels above keep their
        // "dereference failure: ..." texts for every other site.
        "raw_ptr_deref_null" => ("safety_check", "null pointer dereference occurred"),
        "raw_ptr_deref_misaligned" => (
            "safety_check",
            "misaligned pointer dereference: address must be a multiple of its type's alignment",
        ),
        "pointer_invalid" => ("pointer_dereference", "dereference failure: pointer invalid"),
        "dead_object" => ("pointer_dereference", "dereference failure: dead object"),
        "use_after_free_check" => ("pointer_dereference", "dereference failure: use after free"),
        // Part of #2740: Heap deallocation safety labels from context/heap.
        // The freed pointer is not the base of a live heap allocation — freeing
        // a stack address, an interior pointer, or a foreign address. CBMC (and
        // so Kani) words this "free argument must be dynamic object", and the
        // corpus pins that text (dealloc/stack, vec, vecdq); nothing pinned the
        // old "dealloc base pointer mismatch" wording.
        "dealloc_base_pointer_check" => {
            ("pointer_dereference", "free argument must be dynamic object")
        }
        "dealloc_size_mismatch" => {
            ("pointer_dereference", "dereference failure: dealloc size mismatch")
        }
        "double_free_check" => ("pointer_dereference", "dereference failure: double free"),
        "offset_value_overflow" | "offset_bytes_overflow" | "offset_result_overflow" => {
            ("pointer-overflow", "pointer arithmetic overflow")
        }
        "shift_distance_check" => ("undefined-shift", "shift distance too large"),
        "shift_distance_check_negative" => ("undefined-shift", "shift distance is negative"),
        "bigint_shl_negative_shift"
        | "bigint_shr_negative_shift"
        | "bigint_shl_assign_negative_shift"
        | "bigint_shr_assign_negative_shift" => ("undefined-shift", "negative shift amount"),
        "exact_div_zero" => ("division-by-zero", "exact_div division by zero"),
        "exact_div_not_exact" => ("undefined-behavior", "exact_div remainder is nonzero"),
        "exact_div_overflow" => ("overflow", "exact_div signed overflow"),
        "div_euclid_zero" | "rem_euclid_zero" => ("division-by-zero", "euclidean division by zero"),
        "div_euclid_overflow" | "rem_euclid_overflow" => {
            ("overflow", "euclidean division signed overflow")
        }
        "step_unchecked_overflow" => ("overflow", "step unchecked overflow"),
        // FC-06 (BMC): contract modifies-clause enforcement. The class name
        // must contain "assigns" — corpus expectations match the CBMC DFCC
        // check-id line ("assigns") immediately above the FAILURE status.
        "assigns_check" => ("assigns", "assigns clause violation"),
        "enum_check" => ("enum-range-check", "enum range check"),
        "coroutine_check" | "ctlz_nonzero_ub" | "cttz_nonzero_ub" | "biguint_neg_positive" => {
            ("undefined-behavior", "undefined behavior")
        }
        "iterator_sort_mismatch_unsound" => {
            ("unsoundness", "iterator sort mismatch over-approximation")
        }
        "unsound_enum_variant_0_default" => {
            ("unsoundness", "enum variant-0 defaulting for multi-variant enum")
        }
        "unsound_enum_discriminant_positional_fallback" => {
            ("unsoundness", "enum discriminant positional fallback")
        }
        "unsound_interior_mutable_read" => {
            ("unsoundness", "interior-mutable read over-approximation")
        }
        "kani_assert_no_args" => ("assertion", "kani::assert missing condition"),
        // Compile-time type-validity assertion (`assert_inhabited` / `assert_zero_valid`
        // / `assert_mem_uninitialized_valid`) that rustc definitively proves violated.
        // A Kani-style `assert!`-family check, classified with the assertion siblings.
        "assert_type_validity" => ("assertion", "type validity assertion failed"),
        "untranslatable_kani_assert" => ("assertion", "kani::assert condition untranslatable"),
        "untranslatable_assert_operand" => ("assertion", "assert condition operand untranslatable"),
        "untranslatable_assert_bv_width" => {
            ("assertion", "assert condition bitvector width unavailable")
        }
        "untranslatable_assert_sort" => ("assertion", "assert condition sort unsupported"),
        "untranslatable_overflow_assert" => ("overflow", "overflow check operands untranslatable"),
        "unsupported_cfg_cycle" | "unsupported_check" | "unsupported_shadow_memory" => {
            ("unsupported_construct", "unsupported construct")
        }
        "unsupported_oversized_object" => (
            "unsupported_construct",
            "unsupported construct: object larger than the 1MB heap region stride",
        ),
        _ if label.ends_with("_non_finite_lhs") || label.ends_with("_non_finite_rhs") => {
            ("undefined-behavior", "fast-math operand is non-finite")
        }
        _ if label.starts_with("overflow") => ("overflow", "arithmetic overflow"),
        _ => ("assertion", "property check failed"),
    }
}

#[cfg(test)]
mod taxonomy_tests;
#[cfg(test)]
mod tests {
    use super::super::vc_artifact::VcPropertyInfo;
    use super::*;
    use crate::property_model::TraceData;
    use crate::property_model::TraceValue;

    #[test]
    fn test_parse_solver_output_unsat() {
        let (status, failed) = parse_solver_output("unsat\n");
        assert_eq!(status, VerificationStatus::Success);
        assert!(matches!(failed, FailedProperties::None));
    }

    #[test]
    fn test_success_property_uses_artifact_message_as_description() {
        // Stream A: when the VC artifact carries a message (the assertion
        // expression text), it must be used as the check description instead of
        // the generic "assertion failed" fallback derived from the label.
        let names = vec!["ay_violation_kani_assert_0".to_string()];
        let mut map = std::collections::HashMap::new();
        map.insert(
            "ay_violation_kani_assert_0".to_string(),
            VcPropertyInfo {
                location: RawSourceLocation {
                    column: None,
                    file: None,
                    function: None,
                    line: None,
                },
                message: Some("assertion failed: foo() == None".to_string()),
            },
        );
        let props = build_success_properties(&names, Some(&map));
        assert_eq!(props.len(), 1);
        assert_eq!(props[0].description, "assertion failed: foo() == None");
    }

    #[test]
    fn test_success_property_falls_back_when_no_message() {
        // Without a message, the generic label-derived description is used.
        let names = vec!["ay_violation_kani_assert_0".to_string()];
        let props = build_success_properties(&names, None);
        assert_eq!(props.len(), 1);
        assert_eq!(props[0].description, "assertion failed");
    }

    #[test]
    fn test_parse_solver_output_sat() {
        let (status, failed) = parse_solver_output("sat\n((ay_violation_test true))\n");
        assert_eq!(status, VerificationStatus::Failure);
        assert!(matches!(failed, FailedProperties::Other));
    }

    #[test]
    fn test_parse_solver_output_unknown() {
        // #3374: `unknown` (solver incompleteness) must map to the undecided
        // signal FailedProperties::Other — NOT None — so the driver can later
        // classify it as CtrexCategory::Unknown instead of a Genuine bug.
        // This mirrors real `ay` output: "unknown\n(:reason-unknown incomplete)".
        let (status, failed) = parse_solver_output("unknown\n(:reason-unknown incomplete)\n");
        assert_eq!(status, VerificationStatus::Failure);
        assert!(
            matches!(failed, FailedProperties::Other),
            "unknown must yield the undecided `Other` signal, got {failed:?}"
        );
    }

    #[test]
    fn test_parse_solver_output_empty_is_undecided() {
        // Empty/malformed output is treated conservatively as undecided (Other),
        // never as Success and never as a decided failure.
        let (status, failed) = parse_solver_output("");
        assert_eq!(status, VerificationStatus::Failure);
        assert!(matches!(failed, FailedProperties::Other));
    }

    #[test]
    fn test_parse_violation_name() {
        assert_eq!(parse_violation_name("kani_assert_0"), ("kani_assert", 0));
        assert_eq!(parse_violation_name("overflow_check_add_42"), ("overflow_check_add", 42));
        assert_eq!(parse_violation_name("no_number"), ("no_number", 0));
    }

    #[test]
    fn test_classify_violation() {
        assert_eq!(classify_violation("kani_assert"), ("assertion", "assertion failed"));
        assert_eq!(
            classify_violation("div_by_zero_check"),
            ("division-by-zero", "attempt to divide by zero")
        );
        assert_eq!(
            classify_violation("mod_by_zero_check"),
            ("division-by-zero", "attempt to calculate the remainder with a divisor of zero")
        );
        assert_eq!(
            classify_violation("division_by_zero"),
            ("division-by-zero", "division by zero")
        );
        assert_eq!(
            classify_violation("overflow_check_add"),
            ("overflow", "attempt to add with overflow")
        );
        assert_eq!(
            classify_violation("bounds_check"),
            ("array_bounds", "index out of bounds: the length is less than or equal to the given index")
        );
        assert_eq!(
            classify_violation("null_pointer_check"),
            ("pointer_dereference", "dereference failure: pointer NULL")
        );
        assert_eq!(
            classify_violation("alignment_check"),
            ("pointer_dereference", "dereference failure: pointer misaligned")
        );
        assert_eq!(
            classify_violation("pointer_invalid"),
            ("pointer_dereference", "dereference failure: pointer invalid")
        );
        assert_eq!(
            classify_violation("dead_object"),
            ("pointer_dereference", "dereference failure: dead object")
        );
        // Shift checks - both variants
        assert_eq!(
            classify_violation("shift_distance_check"),
            ("undefined-shift", "shift distance too large")
        );
        assert_eq!(
            classify_violation("shift_distance_check_negative"),
            ("undefined-shift", "shift distance is negative")
        );
        // Enum and coroutine checks
        assert_eq!(classify_violation("enum_check"), ("enum-range-check", "enum range check"));
        assert_eq!(
            classify_violation("coroutine_check"),
            ("undefined-behavior", "undefined behavior")
        );
    }

    #[test]
    fn test_build_success_properties() {
        let names = vec![
            "ay_violation_kani_assert_0".to_string(),
            "ay_violation_overflow_check_add_1".to_string(),
        ];
        let props = build_success_properties(&names, None);
        assert_eq!(props.len(), 2);
        assert_eq!(props[0].status, CheckStatus::Success);
        assert_eq!(props[1].status, CheckStatus::Success);
    }

    /// The undecided-path builder must produce the SAME table the UNSAT path
    /// produces — same checks, same classes, same descriptions — differing only
    /// in the status. That is the whole point: an undecided run was hiding the
    /// obligations it had, and a table that disagreed with the UNSAT one about
    /// what those obligations ARE would just be a second wrong answer.
    #[test]
    fn undetermined_properties_mirror_the_success_table_except_for_status() {
        let names = vec![
            "ay_violation_kani_assert_0".to_string(),
            "ay_violation_overflow_check_add_1".to_string(),
        ];
        let success = build_success_properties(&names, None);
        let undetermined = build_undetermined_properties(&names, None);

        assert_eq!(undetermined.len(), success.len());
        for (u, s) in undetermined.iter().zip(success.iter()) {
            assert_eq!(u.status, CheckStatus::Undetermined, "the fail-closed status");
            assert_eq!(s.status, CheckStatus::Success);
            assert_eq!(u.description, s.description);
            assert_eq!(u.property_id.class, s.property_id.class);
            assert_eq!(u.property_id.id, s.property_id.id);
        }
        // An empty declaration list stays empty: a harness with no obligation
        // must NOT grow a phantom UNDETERMINED check.
        assert!(build_undetermined_properties(&[], None).is_empty());
    }

    #[test]
    fn test_build_cover_properties_undetermined() {
        let names =
            vec!["ay_cover_0".to_string(), "ay_cover_1".to_string(), "ay_cover_42".to_string()];
        let props = build_cover_properties_undetermined(&names, None);
        assert_eq!(props.len(), 3);
        // All should have Undetermined status
        assert_eq!(props[0].status, CheckStatus::Undetermined);
        assert_eq!(props[1].status, CheckStatus::Undetermined);
        assert_eq!(props[2].status, CheckStatus::Undetermined);
        // All should have "cover" class
        assert_eq!(props[0].property_id.class, "cover");
        assert_eq!(props[1].property_id.class, "cover");
        assert_eq!(props[2].property_id.class, "cover");
        // IDs should be parsed correctly
        assert_eq!(props[0].property_id.id, 0);
        assert_eq!(props[1].property_id.id, 1);
        assert_eq!(props[2].property_id.id, 42);
    }

    #[test]
    fn test_build_cover_properties_undetermined_empty() {
        let names: Vec<String> = vec![];
        let props = build_cover_properties_undetermined(&names, None);
        assert_eq!(props.len(), 0);
    }

    #[test]
    fn test_build_success_and_cover_properties() {
        let violations = vec!["ay_violation_kani_assert_0".to_string()];
        let covers = vec!["ay_cover_0".to_string(), "ay_cover_1".to_string()];
        let props = build_success_and_cover_properties(&violations, &covers, None);
        assert_eq!(props.len(), 3);
        // First property is violation (Success)
        assert_eq!(props[0].status, CheckStatus::Success);
        assert_eq!(props[0].property_id.class, "assertion");
        // Remaining are covers (Undetermined)
        assert_eq!(props[1].status, CheckStatus::Undetermined);
        assert_eq!(props[1].property_id.class, "cover");
        assert_eq!(props[2].status, CheckStatus::Undetermined);
        assert_eq!(props[2].property_id.class, "cover");
    }

    #[test]
    fn test_parse_cover_properties_with_trace() {
        // Test that satisfied cover properties get trace attached for concrete playback (#1272)
        let output = "sat\n((ay_cover_0 true)\n (ay_cover_1 false))\n";
        let trace_items = vec![TraceItem {
            step_type: Cow::Borrowed("assignment"),
            lhs: Some("goto_symex$$return_value0".to_string()),
            source_location: Some(RawSourceLocation {
                column: None,
                file: None,
                function: Some("kani::any_raw_internal::<ay>".to_string()),
                line: None,
            }),
            value: Some(TraceValue {
                binary: Some("01010101".to_string()),
                data: Some(TraceData::NonBool("85".to_string())),
                width: Some(8),
                elements: None,
            }),
        }];

        let props = parse_cover_properties(output, true, Some(&trace_items), None);
        assert_eq!(props.len(), 2);

        // First cover is satisfied - should have trace
        assert_eq!(props[0].status, CheckStatus::Satisfied);
        assert!(
            props[0].trace.is_some(),
            "Satisfied cover should have trace for concrete playback"
        );
        let trace = props[0].trace.as_ref().unwrap();
        assert_eq!(trace.len(), 1);
        assert_eq!(trace[0].step_type, "assignment");

        // Second cover is unsatisfied - should NOT have trace
        assert_eq!(props[1].status, CheckStatus::Unsatisfiable);
        assert!(props[1].trace.is_none(), "Unsatisfied cover should not have trace");
    }

    #[test]
    fn test_parse_cover_properties_no_trace() {
        // Test that cover properties work without trace (backwards compatibility)
        let output = "sat\n((ay_cover_0 true))\n";
        let props = parse_cover_properties(output, true, None, None);
        assert_eq!(props.len(), 1);
        assert_eq!(props[0].status, CheckStatus::Satisfied);
        assert!(props[0].trace.is_none(), "Cover without trace param should have no trace");
    }

    #[test]
    fn test_parse_cover_properties_unsat() {
        // UNSAT case: cover properties cannot be determined
        let output = "unsat\n";
        let props = parse_cover_properties(output, false, None, None);
        assert!(props.is_empty(), "UNSAT should return no cover properties");
    }

    #[test]
    fn test_parse_cover_properties_empty_trace() {
        // Empty trace slice should still attach (empty) trace to satisfied covers
        let output = "sat\n((ay_cover_0 true))\n";
        let empty_trace: Vec<TraceItem> = vec![];
        let props = parse_cover_properties(output, true, Some(&empty_trace), None);
        assert_eq!(props.len(), 1);
        assert_eq!(props[0].status, CheckStatus::Satisfied);
        // Empty trace is still Some([]), not None
        assert!(props[0].trace.is_some(), "Should have trace (even if empty)");
        assert!(props[0].trace.as_ref().unwrap().is_empty(), "Trace should be empty");
    }

    #[test]
    fn test_parse_cover_properties_single_line_multiple_entries() {
        // Single-line get-value output should still parse all cover entries.
        let output = "sat\n((ay_cover_0 true) (ay_cover_1 false) (ay_cover_2 true))\n";
        let props = parse_cover_properties(output, true, None, None);
        assert_eq!(props.len(), 3);
        assert_eq!(props[0].status, CheckStatus::Satisfied);
        assert_eq!(props[1].status, CheckStatus::Unsatisfiable);
        assert_eq!(props[2].status, CheckStatus::Satisfied);
    }

    #[test]
    fn test_build_coverage_results_from_sat_checks_uses_locations() {
        let coverage_names = vec!["ay_coverage_7".to_string(), "ay_coverage_8".to_string()];
        let sat_results = vec![Some(true), Some(false)];
        let mut locations = std::collections::HashMap::new();
        locations.insert(
            "ay_coverage_7".to_string(),
            VcPropertyInfo {
                location: RawSourceLocation {
                    column: Some("5".to_string()),
                    file: Some("src/lib.rs".to_string()),
                    function: Some("crate::covered".to_string()),
                    line: Some("12".to_string()),
                },
                message: None,
            },
        );
        locations.insert(
            "ay_coverage_8".to_string(),
            VcPropertyInfo {
                location: RawSourceLocation {
                    column: Some("9".to_string()),
                    file: Some("src/lib.rs".to_string()),
                    function: Some("crate::uncovered".to_string()),
                    line: Some("18".to_string()),
                },
                message: None,
            },
        );

        let results =
            build_coverage_results_from_sat_checks(&coverage_names, &sat_results, Some(&locations));
        let rendered = results.to_string();

        assert!(rendered.contains("src/lib.rs (crate::covered)"));
        assert!(rendered.contains("12:5 - 12:5 COVERED"));
        assert!(rendered.contains("src/lib.rs (crate::uncovered)"));
        assert!(rendered.contains("18:9 - 18:9 UNCOVERED"));
    }

    #[test]
    fn test_parse_violation_properties_sat() {
        let output =
            "sat\n((ay_violation_kani_assert_0 true)\n (ay_violation_overflow_check_1 false))\n";
        let props = parse_violation_properties(output, true, None, None);
        assert_eq!(props.len(), 2);
        // First one is violated (true)
        assert!(props.iter().any(|p| p.status == CheckStatus::Failure));
        // Second one is not violated (false)
        assert!(props.iter().any(|p| p.status == CheckStatus::Success));
    }

    #[test]
    fn test_parse_violation_properties_single_line() {
        // AY solver emits all get-value results on a single line
        let output =
            "sat\n((ay_violation_unsupported_check_0 false) (ay_violation_kani_assert_1 false))\n";
        let props = parse_violation_properties(output, true, None, None);
        assert_eq!(props.len(), 2, "should parse both violations from single line");
        assert!(props.iter().all(|p| p.status == CheckStatus::Success));
    }

    #[test]
    fn test_parse_violation_properties_single_line_mixed() {
        // One true, one false on same line
        let output =
            "sat\n((ay_violation_kani_assert_0 true) (ay_violation_overflow_check_1 false))\n";
        let props = parse_violation_properties(output, true, None, None);
        assert_eq!(props.len(), 2, "should parse both violations from single line");
        assert_eq!(props[0].status, CheckStatus::Failure);
        assert_eq!(props[1].status, CheckStatus::Success);
    }

    /// Build one property as `hook_safety_check` delivers it: class
    /// `assertion`, description = the instrumentation's message.
    fn loop_obligation(desc: &'static str, function: Option<&str>, status: CheckStatus) -> Property {
        Property {
            description: Cow::Borrowed(desc),
            property_id: PropertyId { fn_name: None, class: Cow::Borrowed("assertion"), id: 0 },
            source_location: RawSourceLocation {
                column: None,
                file: None,
                function: function.map(str::to_string),
                line: None,
            },
            status,
            trace: None,
        }
    }

    /// The rename, end to end: Kani's class and Kani's description text, with
    /// the loop id read from the `(loop N)` suffix and the function name spliced
    /// from the check's own location.
    #[test]
    fn loop_contract_naming_renders_the_kani_text() {
        let mut props = vec![
            loop_obligation(
                "loop invariant base case: invariant must hold on loop entry (loop 0)",
                Some("f"),
                CheckStatus::Success,
            ),
            loop_obligation(
                "loop invariant inductive step: invariant must be re-established by the loop \
                 body (loop 1)",
                Some("f"),
                CheckStatus::Success,
            ),
        ];
        apply_loop_contract_naming(&mut props);
        assert_eq!(props[0].property_id.class, "loop_invariant_base");
        assert_eq!(props[0].description, "Check invariant before entry for loop f.0");
        assert_eq!(props[1].property_id.class, "loop_invariant_step");
        assert_eq!(props[1].description, "Check invariant after step for loop f.1");
    }

    /// The rename is DISPLAY ONLY. An UNREACHABLE base case keeps its status;
    /// silently promoting one would be a fabricated proof.
    #[test]
    fn loop_contract_naming_never_touches_status() {
        let mut props = vec![loop_obligation(
            "loop invariant base case: invariant must hold on loop entry (loop 0)",
            Some("f"),
            CheckStatus::Unreachable,
        )];
        apply_loop_contract_naming(&mut props);
        assert_eq!(props[0].status, CheckStatus::Unreachable);
    }

    /// No `(loop N)` suffix means no honest loop id to print, so the property is
    /// left exactly as it arrived rather than renamed with a made-up index.
    #[test]
    fn loop_contract_naming_leaves_a_message_without_a_loop_id_alone() {
        let raw = "loop invariant base case: invariant must hold on loop entry";
        let mut props = vec![loop_obligation(raw, Some("f"), CheckStatus::Success)];
        apply_loop_contract_naming(&mut props);
        assert_eq!(props[0].property_id.class, "assertion");
        assert_eq!(props[0].description, raw);
    }

    /// Every other check is untouched — the pass must not reclassify user
    /// assertions that happen to sit next to a loop obligation.
    #[test]
    fn loop_contract_naming_ignores_unrelated_checks() {
        let mut props = vec![loop_obligation(
            "assertion failed: x == 2",
            Some("f"),
            CheckStatus::Success,
        )];
        apply_loop_contract_naming(&mut props);
        assert_eq!(props[0].property_id.class, "assertion");
        assert_eq!(props[0].description, "assertion failed: x == 2");
    }

    /// The renamed checks leave the `assertion` class, so the per-class counters
    /// must number what REMAINS from 1 — the corpus pins `main.assertion.1` for
    /// the user assertion that used to be numbered after the obligations.
    #[test]
    fn kani_naming_numbers_the_remaining_assertions_after_the_rename() {
        let mut props = vec![
            loop_obligation("panic reached", Some("f"), CheckStatus::Success),
            loop_obligation(
                "loop invariant base case: invariant must hold on loop entry (loop 0)",
                Some("f"),
                CheckStatus::Success,
            ),
            loop_obligation("assertion failed: x == 2", Some("f"), CheckStatus::Success),
        ];
        apply_kani_property_naming(&mut props);
        assert_eq!(props[0].property_id.id, 1);
        assert_eq!(props[1].property_id.class, "loop_invariant_base");
        assert_eq!(props[1].property_id.id, 1);
        assert_eq!(props[2].property_id.class, "assertion");
        assert_eq!(props[2].property_id.id, 2);
    }

    #[test]
    fn test_determine_failed_from_properties_all_success() {
        let props = vec![Property {
            description: Cow::Borrowed("test"),
            property_id: PropertyId { fn_name: None, class: Cow::Borrowed("assertion"), id: 0 },
            source_location: RawSourceLocation {
                column: None,
                file: None,
                function: None,
                line: None,
            },
            status: CheckStatus::Success,
            trace: None,
        }];
        assert!(matches!(determine_failed_from_properties(&props), FailedProperties::None));
    }

    #[test]
    fn test_determine_failed_from_properties_panics_only() {
        let props = vec![
            Property {
                description: Cow::Borrowed("assertion failed"),
                property_id: PropertyId { fn_name: None, class: Cow::Borrowed("assertion"), id: 0 },
                source_location: RawSourceLocation {
                    column: None,
                    file: None,
                    function: None,
                    line: None,
                },
                status: CheckStatus::Failure,
                trace: None,
            },
            Property {
                description: Cow::Borrowed("assertion ok"),
                property_id: PropertyId { fn_name: None, class: Cow::Borrowed("assertion"), id: 1 },
                source_location: RawSourceLocation {
                    column: None,
                    file: None,
                    function: None,
                    line: None,
                },
                status: CheckStatus::Success,
                trace: None,
            },
        ];
        assert!(matches!(determine_failed_from_properties(&props), FailedProperties::PanicsOnly));
    }

    #[test]
    fn test_determine_failed_from_properties_other() {
        let props = vec![Property {
            description: Cow::Borrowed("overflow check"),
            property_id: PropertyId {
                fn_name: None,
                class: Cow::Borrowed("overflow_check"),
                id: 0,
            },
            source_location: RawSourceLocation {
                column: None,
                file: None,
                function: None,
                line: None,
            },
            status: CheckStatus::Failure,
            trace: None,
        }];
        assert!(matches!(determine_failed_from_properties(&props), FailedProperties::Other));
    }

    #[test]
    fn test_determine_failed_from_properties_mixed_prefers_other() {
        // When both assertion and non-assertion failures exist, Other takes priority
        let props = vec![
            Property {
                description: Cow::Borrowed("assertion failed"),
                property_id: PropertyId { fn_name: None, class: Cow::Borrowed("assertion"), id: 0 },
                source_location: RawSourceLocation {
                    column: None,
                    file: None,
                    function: None,
                    line: None,
                },
                status: CheckStatus::Failure,
                trace: None,
            },
            Property {
                description: Cow::Borrowed("overflow check"),
                property_id: PropertyId {
                    fn_name: None,
                    class: Cow::Borrowed("overflow_check"),
                    id: 1,
                },
                source_location: RawSourceLocation {
                    column: None,
                    file: None,
                    function: None,
                    line: None,
                },
                status: CheckStatus::Failure,
                trace: None,
            },
        ];
        assert!(matches!(determine_failed_from_properties(&props), FailedProperties::Other));
    }

    // Part of #1162: Tests for cover satisfiability check parsing

    #[test]
    /// An undecided probe must not hand its slot to the next one.
    ///
    /// The parser used to count only `sat`/`unsat` lines and pad `None` at the
    /// end, which is right only when every `unknown` sits at the tail. A
    /// mid-stream `unknown` — which ay emits from incompleteness, not just on a
    /// deadline — shifted every later verdict up by one. Probe 1 then inherited
    /// probe 2's answer, and `Some(false)` promotes a check to UNREACHABLE,
    /// i.e. dead code that is never verified. Wrong answer, in the direction
    /// that hides work.
    #[test]
    fn an_undecided_probe_keeps_its_own_slot() {
        let out = "sat\nunknown\nunsat\n";
        assert_eq!(
            parse_cover_sat_check_output(out, 3),
            vec![Some(true), None, Some(false)],
            "a mid-stream `unknown` must occupy slot 1, not be skipped"
        );
    }

    /// The tail case the old code did handle stays handled.
    #[test]
    fn a_truncated_batch_still_pads_undecided() {
        assert_eq!(
            parse_cover_sat_check_output("unsat\nunsat\n", 4),
            vec![Some(false), Some(false), None, None]
        );
    }

    fn test_parse_cover_sat_check_output_all_sat() {
        let output = "sat\nsat\nsat\n";
        let results = parse_cover_sat_check_output(output, 3);
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], Some(true));
        assert_eq!(results[1], Some(true));
        assert_eq!(results[2], Some(true));
    }

    #[test]
    fn test_parse_cover_sat_check_output_all_unsat() {
        let output = "unsat\nunsat\n";
        let results = parse_cover_sat_check_output(output, 2);
        assert_eq!(results.len(), 2);
        assert_eq!(results[0], Some(false));
        assert_eq!(results[1], Some(false));
    }

    #[test]
    fn test_parse_cover_sat_check_output_mixed() {
        let output = "sat\nunsat\nsat\n";
        let results = parse_cover_sat_check_output(output, 3);
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], Some(true));
        assert_eq!(results[1], Some(false));
        assert_eq!(results[2], Some(true));
    }

    #[test]
    fn test_parse_cover_sat_check_output_with_noise() {
        // Solver may output warnings or other text between results
        let output = "(error \"some warning\")\nsat\n(model ...)\nunsat\n";
        let results = parse_cover_sat_check_output(output, 2);
        assert_eq!(results.len(), 2);
        assert_eq!(results[0], Some(true));
        assert_eq!(results[1], Some(false));
    }

    #[test]
    fn test_parse_cover_sat_check_output_too_few_results() {
        // Solver produced fewer results than expected (timeout, crash)
        let output = "sat\n";
        let results = parse_cover_sat_check_output(output, 3);
        assert_eq!(results.len(), 3);
        assert_eq!(results[0], Some(true));
        assert_eq!(results[1], None); // padded with None
        assert_eq!(results[2], None);
    }

    #[test]
    fn test_parse_cover_sat_check_output_empty() {
        let output = "";
        let results = parse_cover_sat_check_output(output, 2);
        assert_eq!(results.len(), 2);
        assert_eq!(results[0], None);
        assert_eq!(results[1], None);
    }

    #[test]
    fn test_build_cover_properties_from_sat_checks_satisfied() {
        let names = vec!["ay_cover_0".to_string(), "ay_cover_1".to_string()];
        let sat_results = vec![Some(true), Some(true)];
        let props = build_cover_properties_from_sat_checks(&names, &sat_results, None);
        assert_eq!(props.len(), 2);
        assert_eq!(props[0].status, CheckStatus::Satisfied);
        assert_eq!(props[1].status, CheckStatus::Satisfied);
        assert_eq!(props[0].property_id.class, "cover");
    }

    #[test]
    fn test_build_cover_properties_from_sat_checks_unsatisfiable() {
        let names = vec!["ay_cover_0".to_string()];
        let sat_results = vec![Some(false)];
        let props = build_cover_properties_from_sat_checks(&names, &sat_results, None);
        assert_eq!(props.len(), 1);
        assert_eq!(props[0].status, CheckStatus::Unsatisfiable);
    }

    #[test]
    fn test_build_cover_properties_from_sat_checks_mixed() {
        let names =
            vec!["ay_cover_0".to_string(), "ay_cover_1".to_string(), "ay_cover_2".to_string()];
        let sat_results = vec![Some(true), Some(false), None];
        let props = build_cover_properties_from_sat_checks(&names, &sat_results, None);
        assert_eq!(props.len(), 3);
        assert_eq!(props[0].status, CheckStatus::Satisfied);
        assert_eq!(props[1].status, CheckStatus::Unsatisfiable);
        assert_eq!(props[2].status, CheckStatus::Undetermined);
    }

    #[test]
    fn test_build_cover_properties_from_sat_checks_ids() {
        let names = vec!["ay_cover_42".to_string()];
        let sat_results = vec![Some(true)];
        let props = build_cover_properties_from_sat_checks(&names, &sat_results, None);
        assert_eq!(props[0].property_id.id, 42);
        assert_eq!(props[0].description.as_ref(), "cover property 42");
    }
}
