// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Per-property CHC verdict expansion (BSEM-18).
//!
//! The CHC encoder emits one `error_p{id}` relation per distinct check site and
//! records its metadata (kind, message, location) in the VC artifact. AY's
//! portfolio solves a single `(query error)` and returns one aggregate verdict
//! plus (on a counterexample) a trace naming the specific `error_p{id}` that
//! was violated. This module turns that aggregate verdict + the artifact table
//! into a list of per-property [`Property`] report lines:
//!
//! - **Aggregate PROOF** (`error` unreachable) ⇒ every `error_p{id}` is
//!   individually unreachable, so every property is `Success` (VERIFIED). Sound.
//! - **Aggregate COUNTEREXAMPLE** ⇒ at least one property fails. The ones named
//!   by the counterexample are `Failure`; the rest are `Unknown` (undetermined)
//!   — never `Success`, because an UNSAFE run does not prove them safe. Sound:
//!   a real failure can never be reported as verified.

use std::borrow::Cow;
use std::collections::HashSet;
use std::path::Path;

use trust_mc_core::violation::PropertyKind;
use trust_mc_metadata::HarnessMetadata;

use crate::ay_parse::{ChcArtifactProperty, load_chc_property_table, vc_artifact_path_for_smt};
use crate::property_model::{CheckStatus, Property, PropertyId};

/// Property-id class string for a check kind (used in `fn.class.id` names).
fn kind_class(kind: PropertyKind) -> &'static str {
    match kind {
        PropertyKind::Assertion => "assertion",
        PropertyKind::Assumption => "assume",
        PropertyKind::Cover => "cover",
        PropertyKind::ArithmeticOverflow => "arithmetic_overflow",
        PropertyKind::DivisionByZero => "division_by_zero",
        PropertyKind::OutOfBounds => "bounds",
        PropertyKind::NullPointer => "null_pointer",
        PropertyKind::MemorySafety => "memory_safety",
        PropertyKind::LoopDecreases => "loop_decreases",
        PropertyKind::PointerOverflow => "pointer_overflow",
        PropertyKind::Unreachable => "unreachable",
        PropertyKind::Panic => "panic",
        PropertyKind::UndefinedBehavior => "undefined_behavior",
        PropertyKind::Precondition => "precondition",
        PropertyKind::Postcondition => "postcondition",
        PropertyKind::LoopInvariant => "loop_invariant",
        PropertyKind::Other => "check",
    }
}

/// Build one report [`Property`] from a CHC artifact entry with the given status.
fn build_property(
    entry: &ChcArtifactProperty,
    harness: &HarnessMetadata,
    status: CheckStatus,
) -> Property {
    let description = match &entry.message {
        Some(message) => Cow::Owned(message.clone()),
        None => Cow::Owned(format!("CHC verification: {}", entry.kind.description())),
    };
    Property {
        description,
        property_id: PropertyId {
            fn_name: Some(harness.pretty_name.clone()),
            class: Cow::Borrowed(kind_class(entry.kind)),
            id: entry.id,
        },
        source_location: entry.location.clone(),
        status,
        trace: None,
    }
}

/// Per-property `Success` list for a proven-safe CHC harness (BSEM-18).
///
/// Returns `None` when the artifact carries no per-property CHC table (e.g. a
/// harness with no checks, or a pre-BSEM-18 artifact), so callers can keep the
/// legacy single aggregate property.
pub(super) fn chc_success_properties(
    smt_file: &Path,
    harness: &HarnessMetadata,
) -> Option<Vec<Property>> {
    let table = load_chc_property_table(&vc_artifact_path_for_smt(smt_file));
    if table.is_empty() {
        return None;
    }
    Some(table.iter().map(|e| build_property(e, harness, CheckStatus::Success)).collect())
}

/// Per-property list for a failing CHC harness (BSEM-18).
///
/// Properties whose relation appears in `failing_relations` are reported as
/// `Failure`; all others as `Unknown` (undetermined — an UNSAFE run does not
/// prove them safe). Returns `None` if the artifact carries no per-property
/// table, or if `failing_relations` names none of the table's relations (so the
/// caller keeps the legacy single aggregate failure rather than emitting a list
/// with no identified failure).
pub(super) fn chc_failure_properties(
    smt_file: &Path,
    harness: &HarnessMetadata,
    failing_relations: &HashSet<String>,
) -> Option<Vec<Property>> {
    let table = load_chc_property_table(&vc_artifact_path_for_smt(smt_file));
    if table.is_empty() {
        return None;
    }
    let any_identified = table.iter().any(|e| failing_relations.contains(&e.relation));
    if !any_identified {
        return None;
    }
    Some(
        table
            .iter()
            .map(|e| {
                let status = if failing_relations.contains(&e.relation) {
                    CheckStatus::Failure
                } else {
                    CheckStatus::Unknown
                };
                build_property(e, harness, status)
            })
            .collect(),
    )
}
