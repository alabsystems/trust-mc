// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::{AuditFailure, object_field, required_u64};
use serde_json::{Map, Value};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct HarnessCounts {
    pub(crate) total: u64,
    pub(crate) pass: u64,
    pub(crate) proof: u64,
    pub(crate) known_fp: u64,
    pub(crate) trusted_proof: u64,
    pub(crate) ctrex: u64,
    pub(crate) fail: u64,
    pub(crate) unknown: u64,
    pub(crate) error: u64,
    pub(crate) skip: u64,
    pub(crate) xfail: u64,
    pub(crate) bmc: u64,
}

pub(crate) fn validate_summary(
    path: &str,
    report: &Map<String, Value>,
    counts: &HarnessCounts,
    failures: &mut Vec<AuditFailure>,
) {
    let Some(summary) = object_field(path, report, "summary", failures) else {
        return;
    };

    match required_u64(path, summary, "summary.total", failures) {
        Some(0) => failures.push(AuditFailure::new(path, "summary.total must be greater than 0")),
        Some(value) if value != counts.total => failures.push(AuditFailure::new(
            path,
            format!("summary.total is {value}, expected {} from rows", counts.total),
        )),
        Some(_) | None => {}
    }

    validate_required_summary_count(path, summary, "pass", counts.pass, failures);
    validate_required_summary_count(path, summary, "proof", counts.proof, failures);
    validate_required_summary_count(path, summary, "known_fp", counts.known_fp, failures);
    validate_required_summary_count(path, summary, "trusted_proof", counts.trusted_proof, failures);
    validate_required_summary_count(path, summary, "ctrex", counts.ctrex, failures);
    validate_required_summary_count(path, summary, "fail", counts.fail, failures);
    validate_required_summary_count(path, summary, "unknown", counts.unknown, failures);
    validate_required_summary_count(path, summary, "error", counts.error, failures);
    validate_required_summary_count(path, summary, "bmc", counts.bmc, failures);
    validate_required_summary_count(path, summary, "xfail", counts.xfail, failures);
    validate_required_summary_count(path, summary, "skip", counts.skip, failures);
}

fn validate_required_summary_count(
    path: &str,
    summary: &Map<String, Value>,
    field: &str,
    expected: u64,
    failures: &mut Vec<AuditFailure>,
) {
    let label = format!("summary.{field}");
    match required_u64(path, summary, &label, failures) {
        Some(value) if value == expected => {}
        Some(value) => failures.push(AuditFailure::new(
            path,
            format!("{label} is {value}, expected {expected} from rows"),
        )),
        None => {}
    }
}
