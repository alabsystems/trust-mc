// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::{AuditFailure, json_type};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

type ExpectedByKey = BTreeMap<HarnessKey, String>;
type DigestRows = Vec<BTreeMap<String, String>>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct HarnessKey {
    pub file: String,
    pub harness: String,
}

impl HarnessKey {
    pub(crate) fn new(file: impl Into<String>, harness: impl Into<String>) -> Self {
        Self { file: file.into(), harness: harness.into() }
    }

    pub(crate) fn label(&self) -> String {
        format!("{}::{}", self.file, self.harness)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Inventory {
    pub path: String,
    pub denominator: u64,
    pub row_sha256: String,
    expected_by_key: ExpectedByKey,
}

impl Inventory {
    pub fn from_manifest_text(path: impl Into<String>, text: &str) -> Result<Self, String> {
        let path = path.into();
        let value = parse_manifest_json(&path, text)?;
        let manifest = manifest_object(&path, &value)?;
        validate_manifest_header(&path, manifest)?;

        let denominator = manifest_denominator(&path, manifest)?;
        let rows = manifest_rows(&path, manifest)?;
        let (expected_by_key, digest_rows) = parse_inventory_rows(&path, rows)?;
        validate_manifest_denominator(&path, denominator, expected_by_key.len())?;
        let row_sha256 = validate_manifest_digest(&path, manifest, &digest_rows)?;

        Ok(Self { path, denominator, row_sha256, expected_by_key })
    }

    pub(crate) fn non_proof_expected_by_key(&self) -> BTreeMap<HarnessKey, String> {
        self.expected_by_key
            .iter()
            .filter(|(_, expected)| expected.as_str() != "PROOF")
            .map(|(key, expected)| (key.clone(), expected.clone()))
            .collect()
    }

    pub fn non_proof_denominator(&self) -> u64 {
        self.expected_by_key.values().filter(|expected| expected.as_str() != "PROOF").count() as u64
    }

    pub(crate) fn validate_report_keys(
        &self,
        report_path: &str,
        report_keys: &BTreeSet<HarnessKey>,
        report_expected_by_key: &BTreeMap<HarnessKey, String>,
        proof_keys: &BTreeSet<HarnessKey>,
        expected_harnesses: Option<u64>,
        failures: &mut Vec<AuditFailure>,
    ) {
        if let Some(expected) = expected_harnesses
            && expected != self.denominator
        {
            failures.push(AuditFailure::new(
                report_path,
                format!(
                    "expected_harnesses {expected} != inventory denominator {} ({})",
                    self.denominator, self.path
                ),
            ));
        }

        if report_keys.len() as u64 != self.denominator {
            failures.push(AuditFailure::new(
                report_path,
                format!(
                    "report has {} unique harness keys; inventory {} has {}",
                    report_keys.len(),
                    self.path,
                    self.denominator
                ),
            ));
        }

        let inventory_keys = self.expected_by_key.keys().cloned().collect::<BTreeSet<_>>();

        for key in inventory_keys.difference(report_keys).take(20) {
            failures.push(AuditFailure::new(
                report_path,
                format!("missing inventory harness {}", key.label()),
            ));
        }
        for key in report_keys.difference(&inventory_keys).take(20) {
            failures.push(AuditFailure::new(
                report_path,
                format!("report harness not in inventory {}", key.label()),
            ));
        }
        for (key, expected) in self.expected_by_key.iter() {
            if let Some(report_expected) = report_expected_by_key.get(key)
                && report_expected != expected
            {
                failures.push(AuditFailure::new(
                    report_path,
                    format!(
                        "report expected {report_expected:?} does not match inventory expected {expected:?} for {}",
                        key.label()
                    ),
                ));
            }
            if expected == "PROOF" && report_keys.contains(key) && !proof_keys.contains(key) {
                failures.push(AuditFailure::new(
                    report_path,
                    format!("inventory PROOF harness is not replacement-quality {}", key.label()),
                ));
            }
        }
    }
}

fn parse_manifest_json(path: &str, text: &str) -> Result<Value, String> {
    serde_json::from_str(text).map_err(|err| format!("{path}: invalid JSON: {err}"))
}

fn manifest_object<'a>(
    path: &str,
    value: &'a Value,
) -> Result<&'a serde_json::Map<String, Value>, String> {
    value.as_object().ok_or_else(|| format!("{path}: expected top-level JSON object"))
}

fn validate_manifest_header(
    path: &str,
    manifest: &serde_json::Map<String, Value>,
) -> Result<(), String> {
    match manifest.get("schema_version") {
        Some(Value::Number(version)) if version.as_u64() == Some(1) => {}
        Some(other) => {
            return Err(format!("{path}: schema_version must be 1, got {}", json_type(other)));
        }
        None => return Err(format!("{path}: missing schema_version")),
    }

    match manifest.get("suite") {
        Some(Value::String(suite)) if suite == "tests/trust-mc" => Ok(()),
        Some(Value::String(suite)) => Err(format!("{path}: suite {suite:?} != \"tests/trust-mc\"")),
        Some(other) => Err(format!("{path}: suite must be a string, got {}", json_type(other))),
        None => Err(format!("{path}: missing suite")),
    }
}

fn manifest_denominator(
    path: &str,
    manifest: &serde_json::Map<String, Value>,
) -> Result<u64, String> {
    match manifest.get("denominator") {
        Some(value) => {
            value.as_u64().ok_or_else(|| format!("{path}: denominator must be an unsigned integer"))
        }
        None => Err(format!("{path}: missing denominator")),
    }
}

fn manifest_rows<'a>(
    path: &str,
    manifest: &'a serde_json::Map<String, Value>,
) -> Result<&'a Vec<Value>, String> {
    match manifest.get("rows") {
        Some(Value::Array(rows)) => Ok(rows),
        _ => Err(format!("{path}: rows must be an array")),
    }
}

fn parse_inventory_rows(path: &str, rows: &[Value]) -> Result<(ExpectedByKey, DigestRows), String> {
    let mut expected_by_key = BTreeMap::new();
    let mut digest_rows = Vec::new();
    for (index, row) in rows.iter().enumerate() {
        parse_inventory_row(path, index, row, &mut expected_by_key, &mut digest_rows)?;
    }
    Ok((expected_by_key, digest_rows))
}

fn parse_inventory_row(
    path: &str,
    index: usize,
    row: &Value,
    expected_by_key: &mut BTreeMap<HarnessKey, String>,
    digest_rows: &mut Vec<BTreeMap<String, String>>,
) -> Result<(), String> {
    let Some(row) = row.as_object() else {
        return Err(format!("{path}: rows[{index}] must be an object"));
    };
    let file = required_nonempty_string(row.get("file"))
        .ok_or_else(|| format!("{path}: rows[{index}].file is missing or empty"))?;
    let harness = required_nonempty_string(row.get("harness"))
        .ok_or_else(|| format!("{path}: rows[{index}].harness is missing or empty"))?;
    let lane = required_nonempty_string(row.get("lane"))
        .ok_or_else(|| format!("{path}: rows[{index}].lane is missing or empty"))?;
    let expected = validate_inventory_expected(path, index, row.get("expected"))?;

    let key = HarnessKey::new(file, harness);
    if expected_by_key.insert(key.clone(), expected.clone()).is_some() {
        return Err(format!("{path}: duplicate inventory row {}", key.label()));
    }
    digest_rows.push(BTreeMap::from([
        ("expected".to_string(), expected),
        ("file".to_string(), key.file),
        ("harness".to_string(), key.harness),
        ("lane".to_string(), lane),
    ]));
    Ok(())
}

fn validate_inventory_expected(
    path: &str,
    index: usize,
    value: Option<&Value>,
) -> Result<String, String> {
    match value {
        Some(Value::String(expected)) if is_inventory_expected(expected) => Ok(expected.clone()),
        Some(Value::String(expected)) => Err(format!(
            "{path}: rows[{index}].expected {expected:?} is not an accepted replacement expected value"
        )),
        Some(other) => Err(format!(
            "{path}: rows[{index}].expected must be a string, got {}",
            json_type(other),
        )),
        None => Err(format!("{path}: rows[{index}].expected is missing")),
    }
}

fn is_inventory_expected(expected: &str) -> bool {
    matches!(expected, "PROOF" | "CTREX" | "UNKNOWN" | "BMC_SAFE" | "ERROR")
}

fn validate_manifest_denominator(path: &str, denominator: u64, rows: usize) -> Result<(), String> {
    if denominator == rows as u64 {
        Ok(())
    } else {
        Err(format!("{path}: denominator {denominator} != {rows} inventory rows"))
    }
}

fn validate_manifest_digest(
    path: &str,
    manifest: &serde_json::Map<String, Value>,
    digest_rows: &[BTreeMap<String, String>],
) -> Result<String, String> {
    let Some(Value::String(row_sha256)) = manifest.get("row_sha256") else {
        return Err(format!("{path}: missing row_sha256"));
    };
    let actual_sha256 = row_sha256_for_rows(digest_rows)?;
    if row_sha256 == &actual_sha256 {
        Ok(row_sha256.clone())
    } else {
        Err(format!("{path}: row_sha256 {row_sha256} != computed {actual_sha256}"))
    }
}

fn required_nonempty_string(value: Option<&Value>) -> Option<String> {
    match value {
        Some(Value::String(value)) if !value.trim().is_empty() => Some(value.clone()),
        _ => None,
    }
}

fn row_sha256_for_rows(rows: &[BTreeMap<String, String>]) -> Result<String, String> {
    let rendered = serde_json::to_string(rows)
        .map_err(|err| format!("failed to serialize inventory rows: {err}"))?;
    let digest = Sha256::digest(rendered.as_bytes());
    let mut out = String::with_capacity(64);
    for byte in digest {
        out.push_str(&format!("{byte:02x}"));
    }
    Ok(out)
}
