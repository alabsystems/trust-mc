// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Verdict classification policy for CHC solver results.
//!
//! Pure decision functions: no solver invocation or I/O. Extracted from
//! `chc.rs` for testability and to separate policy from orchestration.

use crate::property_model::Property;
use crate::verification_result::{FailedProperties, VerificationStatus};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ChcOutcomeKind {
    Proof,
    SolverUnknown,
    ConservativeUnknown,
    Counterexample,
}

pub(crate) fn classify_chc_outcome(
    solver_unknown: bool,
    status: VerificationStatus,
    failed_props: FailedProperties,
) -> ChcOutcomeKind {
    if status == VerificationStatus::Success {
        ChcOutcomeKind::Proof
    } else if solver_unknown {
        ChcOutcomeKind::SolverUnknown
    } else if matches!(failed_props, FailedProperties::Other) {
        ChcOutcomeKind::ConservativeUnknown
    } else {
        ChcOutcomeKind::Counterexample
    }
}

/// Part of #4058 D3: construct a recursion unwinding assertion property.
///
/// When the compiler emits `; RECURSIVE_UNWIND_ASSERTION:` and the solver
/// returns a non-PROOF result, the driver relabels the user-visible failure
/// as a recursion unwinding assertion instead of generic CHC failure.
pub(crate) fn recursion_unwind_property(harness_name: Option<&str>) -> Property {
    let fn_name = harness_name.map(|n| {
        // Strip the harness suffix to get the function name.
        // Harness names look like `harness_function` — use as-is if no
        // better information is available.
        n.to_string()
    });
    Property {
        description: std::borrow::Cow::Borrowed("recursion unwinding assertion"),
        property_id: crate::property_model::PropertyId {
            fn_name,
            class: std::borrow::Cow::Borrowed("recursion"),
            id: 1,
        },
        source_location: crate::property_model::RawSourceLocation {
            column: None,
            file: None,
            function: None,
            line: None,
        },
        status: crate::property_model::CheckStatus::Failure,
        trace: None,
    }
}

/// Part of #4058: apply the recursive unwind failure policy to solver results.
///
/// When the compiler emits `; RECURSIVE_UNWIND_ASSERTION:`, recursive inline
/// exhausted the active harness unwind bound while unwinding assertions were
/// enabled. The user-visible result must therefore be a recursion unwinding
/// failure, even if the backend solver otherwise returns PROOF or UNKNOWN.
pub(crate) fn apply_recursion_unwind_verdict(
    has_recursive_unwind: bool,
    outcome: ChcOutcomeKind,
    status: VerificationStatus,
    failed_props: FailedProperties,
    properties: Vec<Property>,
    harness_name: Option<&str>,
) -> (VerificationStatus, FailedProperties, Vec<Property>, ChcOutcomeKind) {
    if !has_recursive_unwind {
        return (status, failed_props, properties, outcome);
    }

    (
        VerificationStatus::Failure,
        FailedProperties::Other,
        vec![recursion_unwind_property(harness_name)],
        ChcOutcomeKind::Counterexample,
    )
}
