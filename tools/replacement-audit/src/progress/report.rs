// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::{
    authority::ProgressAuthority,
    inventory_view::{HarnessKey, ProgressInventory},
    report_authority::{authority_metadata_failures, top_string},
};
use crate::proof_quality::proof_qualifier_non_quality_reason;
use serde_json::{Map, Value};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

const AUTHORITY_FIELDS: &[&str] =
    &["report_status", "tree_state", "commit", "ay_pin", "tree_fingerprint"];
const MAX_AUTHORITY_VALUE_EXAMPLES: usize = 12;
const MAX_KEY_EXAMPLES: usize = 12;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReportProgress {
    pub(crate) path: PathBuf,
    pub(crate) paths: Vec<PathBuf>,
    pub(crate) sources: Vec<ReportSource>,
    pub(crate) total: u64,
    pub(crate) proof_seen: u64,
    pub(crate) proof_quality: u64,
    pub(crate) authority_metadata: bool,
    pub(crate) authority_failures: Vec<String>,
    pub(crate) report_status: String,
    pub(crate) tree_state: String,
    pub(crate) commit: String,
    pub(crate) ay_pin: String,
    pub(crate) tree_fingerprint: String,
    pub(crate) status_counts: BTreeMap<String, u64>,
    pub(crate) verdict_counts: BTreeMap<String, u64>,
    pub(crate) non_quality_categories: BTreeMap<String, u64>,
    pub(crate) non_quality_reasons: BTreeMap<String, u64>,
    pub(crate) non_quality_examples: Vec<String>,
    pub(crate) missing_categories: BTreeMap<String, u64>,
    pub(crate) missing_examples: Vec<String>,
    pub(crate) duplicate_examples: Vec<String>,
    pub(crate) duplicate_keys: u64,
    pub(crate) row_sha256: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReportSource {
    pub(crate) path: PathBuf,
    pub(crate) rows: u64,
    pub(crate) file_sha256: String,
    pub(crate) row_sha256: String,
}

struct ReportScan {
    status_counts: BTreeMap<String, u64>,
    verdict_counts: BTreeMap<String, u64>,
    seen_proof_keys: BTreeSet<HarnessKey>,
    quality_proof_keys: BTreeSet<HarnessKey>,
    non_quality_reasons: BTreeMap<String, u64>,
    duplicate_keys: BTreeSet<HarnessKey>,
}

pub(crate) fn load_report_progresses(
    paths: &[PathBuf],
    proof_inventory: &ProgressInventory,
    authority: &ProgressAuthority,
) -> Result<ReportProgress, String> {
    if paths.is_empty() {
        return Err("at least one report path is required".to_string());
    }
    let mut scan = ReportScan::new();
    let mut seen_report_keys = BTreeSet::new();
    let mut total = 0u64;
    let mut authority_failures = Vec::new();
    let mut authority_values: BTreeMap<&'static str, BTreeSet<String>> = BTreeMap::new();
    let mut sources = Vec::new();
    let mut merged_rows = Vec::new();

    for path in paths {
        let text = fs::read_to_string(path)
            .map_err(|err| format!("failed to read report {}: {err}", path.display()))?;
        let value: Value = serde_json::from_str(&text)
            .map_err(|err| format!("invalid report JSON {}: {err}", path.display()))?;
        let report = report_object(path, &value)?;
        let harnesses = report_harnesses(path, report)?;
        sources.push(ReportSource {
            path: path.clone(),
            rows: harnesses.len() as u64,
            file_sha256: sha256_hex(text.as_bytes()),
            row_sha256: rows_sha256(harnesses)?,
        });
        merged_rows.extend(harnesses.iter().cloned());
        total += harnesses.len() as u64;
        scan_report_harnesses_into(harnesses, proof_inventory, &mut scan, &mut seen_report_keys);
        for failure in authority_metadata_failures(report, authority) {
            authority_failures.push(format!("{}: {failure}", path.display()));
        }
        for &field in AUTHORITY_FIELDS {
            authority_values.entry(field).or_default().insert(top_string(report, field));
        }
    }

    for (field, values) in &authority_values {
        if values.len() > 1 {
            let joined = authority_value_sample(values);
            authority_failures.push(format!("merged reports disagree on {field}: {joined}"));
        }
    }

    let proof_keys = proof_inventory.proof_keys();
    let non_quality_keys = keys_for_difference(&scan.seen_proof_keys, &scan.quality_proof_keys);
    let missing_keys = keys_for_difference(&proof_keys, &scan.seen_proof_keys);
    let non_quality_categories = categories_for_keys(&non_quality_keys);
    let missing_categories = categories_for_keys(&missing_keys);

    Ok(ReportProgress {
        path: report_path_label(paths),
        paths: paths.to_vec(),
        sources,
        total,
        proof_seen: scan.seen_proof_keys.len() as u64,
        proof_quality: scan.quality_proof_keys.len() as u64,
        authority_metadata: authority_failures.is_empty(),
        authority_failures,
        report_status: common_authority_value(&authority_values, "report_status"),
        tree_state: common_authority_value(&authority_values, "tree_state"),
        commit: common_authority_value(&authority_values, "commit"),
        ay_pin: common_authority_value(&authority_values, "ay_pin"),
        tree_fingerprint: common_authority_value(&authority_values, "tree_fingerprint"),
        status_counts: scan.status_counts,
        verdict_counts: scan.verdict_counts,
        non_quality_categories,
        non_quality_reasons: scan.non_quality_reasons,
        non_quality_examples: format_key_examples(&non_quality_keys),
        missing_categories,
        missing_examples: format_key_examples(&missing_keys),
        duplicate_examples: format_key_examples(&scan.duplicate_keys),
        duplicate_keys: scan.duplicate_keys.len() as u64,
        row_sha256: rows_sha256(&merged_rows)?,
    })
}

fn report_path_label(paths: &[PathBuf]) -> PathBuf {
    if paths.len() == 1 {
        return paths[0].clone();
    }
    PathBuf::from(format!("<{} reports>", paths.len()))
}

fn common_authority_value(
    authority_values: &BTreeMap<&'static str, BTreeSet<String>>,
    field: &'static str,
) -> String {
    let Some(values) = authority_values.get(field) else {
        return "missing".to_string();
    };
    if values.len() == 1 {
        return values.iter().next().cloned().unwrap_or_else(|| "missing".to_string());
    }
    "mixed".to_string()
}

fn authority_value_sample(values: &BTreeSet<String>) -> String {
    let sample =
        values.iter().take(MAX_AUTHORITY_VALUE_EXAMPLES).cloned().collect::<Vec<_>>().join(",");
    if values.len() <= MAX_AUTHORITY_VALUE_EXAMPLES {
        return sample;
    }
    format!("{sample},...(+{} more)", values.len() - MAX_AUTHORITY_VALUE_EXAMPLES)
}

fn report_object<'a>(path: &Path, value: &'a Value) -> Result<&'a Map<String, Value>, String> {
    value.as_object().ok_or_else(|| format!("report {} must be a JSON object", path.display()))
}

fn report_harnesses<'a>(
    path: &Path,
    report: &'a Map<String, Value>,
) -> Result<&'a Vec<Value>, String> {
    report
        .get("harnesses")
        .and_then(Value::as_array)
        .ok_or_else(|| format!("report {} missing harnesses array", path.display()))
}

fn scan_report_harnesses_into(
    harnesses: &[Value],
    proof_inventory: &ProgressInventory,
    scan: &mut ReportScan,
    seen_report_keys: &mut BTreeSet<HarnessKey>,
) {
    for harness in harnesses {
        let Some(row) = harness.as_object() else { continue };
        scan_row(row, proof_inventory, scan, seen_report_keys);
    }
}

fn scan_row(
    row: &Map<String, Value>,
    proof_inventory: &ProgressInventory,
    scan: &mut ReportScan,
    seen_report_keys: &mut BTreeSet<HarnessKey>,
) {
    let status = string_value(row, "status");
    let verdict = string_value(row, "verdict");
    add_count(&mut scan.status_counts, &status);
    add_count(&mut scan.verdict_counts, &verdict);

    let file = string_value(row, "file");
    let harness_name = string_value(row, "harness");
    let key = (file.clone(), harness_name.clone());
    if !seen_report_keys.insert(key.clone()) {
        scan.duplicate_keys.insert(key.clone());
    }
    if proof_inventory.expected_for(&file, &harness_name) == Some("PROOF") {
        scan.seen_proof_keys.insert(key.clone());
        let quality_failures = replacement_quality_failures(row);
        if quality_failures.is_empty() {
            scan.quality_proof_keys.insert(key);
        } else {
            for reason in quality_failures {
                add_count(&mut scan.non_quality_reasons, reason);
            }
        }
    }
}

impl ReportScan {
    fn new() -> Self {
        Self {
            status_counts: BTreeMap::new(),
            verdict_counts: BTreeMap::new(),
            seen_proof_keys: BTreeSet::new(),
            quality_proof_keys: BTreeSet::new(),
            non_quality_reasons: BTreeMap::new(),
            duplicate_keys: BTreeSet::new(),
        }
    }
}

fn keys_for_difference(
    expected: &BTreeSet<HarnessKey>,
    actual: &BTreeSet<HarnessKey>,
) -> BTreeSet<HarnessKey> {
    expected.difference(actual).cloned().collect()
}

fn categories_for_keys(keys: &BTreeSet<HarnessKey>) -> BTreeMap<String, u64> {
    let mut categories = BTreeMap::new();
    for key in keys {
        add_count(&mut categories, &category_from_file(&key.0));
    }
    categories
}

fn format_key_examples(keys: &BTreeSet<HarnessKey>) -> Vec<String> {
    keys.iter().take(MAX_KEY_EXAMPLES).map(format_key).collect()
}

fn format_key(key: &HarnessKey) -> String {
    format!("{}::{}", key.0, key.1)
}

fn replacement_quality_failures(row: &Map<String, Value>) -> Vec<&'static str> {
    let mut failures = Vec::new();
    if string_value(row, "status") != "PASS" {
        failures.push("status_not_pass");
    }
    if string_value(row, "expected") != "PROOF" {
        failures.push("expected_not_proof");
    }
    if string_value(row, "verdict") != "PROOF" {
        failures.push("verdict_not_proof");
    }
    if string_value(row, "execution_state") != "complete" {
        failures.push("execution_state_not_complete");
    }
    if string_value(row, "execution_details") != "final_marker=PROOF" {
        failures.push("execution_details_not_final_proof");
    }
    match row.get("proof_qualifiers").and_then(Value::as_str) {
        Some(qualifiers) => {
            if let Some(reason) = proof_qualifier_non_quality_reason(qualifiers) {
                failures.push(reason);
            }
        }
        None => failures.push("proof_qualifiers_missing"),
    }
    if row.get("trusted_proof").and_then(Value::as_bool) != Some(true) {
        failures.push("trusted_proof_not_true");
    }
    if row.get("known_fp").and_then(Value::as_bool) == Some(true) {
        failures.push("known_fp_true");
    }
    if row.get("sound_fallback_count").and_then(Value::as_u64) != Some(0) {
        failures.push("sound_fallback_count_not_zero");
    }
    if row.get("demotion_reasons").is_some_and(|value| !empty_array(value)) {
        failures.push("demotion_reasons_nonempty");
    }
    if row.get("translation_drop_reasons").is_some_and(|value| !empty_object(value)) {
        failures.push("translation_drop_reasons_nonempty");
    }
    if has_retry_metadata(row) {
        failures.push("retry_metadata_present");
    }
    failures
}

fn has_retry_metadata(row: &Map<String, Value>) -> bool {
    [
        "retried",
        "retry_attempts",
        "retry_resolved_by",
        "retry_final",
        "retry_recursive",
        "retry_relation_count",
    ]
    .iter()
    .any(|field| row.contains_key(*field))
}

fn empty_array(value: &Value) -> bool {
    value.as_array().is_some_and(Vec::is_empty)
}

fn empty_object(value: &Value) -> bool {
    value.as_object().is_some_and(Map::is_empty)
}

fn string_value(row: &Map<String, Value>, field: &str) -> String {
    row.get(field).and_then(Value::as_str).unwrap_or("missing").to_string()
}

fn add_count(counts: &mut BTreeMap<String, u64>, key: &str) {
    *counts.entry(key.to_string()).or_insert(0) += 1;
}

fn category_from_file(file: &str) -> String {
    file.split('/').nth(1).unwrap_or(file).to_string()
}

fn rows_sha256(rows: &[Value]) -> Result<String, String> {
    serde_json::to_vec(&Value::Array(rows.to_vec()))
        .map(|bytes| sha256_hex(&bytes))
        .map_err(|err| format!("failed to serialize report rows for digest: {err}"))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(64);
    for byte in digest {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}
