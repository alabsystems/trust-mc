// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::inventory::Inventory;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

pub(crate) type HarnessKey = (String, String);

#[derive(Debug, Clone)]
pub(crate) struct ProgressInventory {
    audit_inventory: Inventory,
    expected_by_key: BTreeMap<HarnessKey, String>,
    expected_counts: BTreeMap<String, u64>,
}

impl ProgressInventory {
    pub(crate) fn load(path: &Path) -> Result<Self, String> {
        let text = fs::read_to_string(path)
            .map_err(|err| format!("failed to read inventory {}: {err}", path.display()))?;
        let audit_inventory = Inventory::from_manifest_text(path.display().to_string(), &text)?;
        let expected_by_key = parse_expected_rows(path, &text)?;
        let expected_counts = count_expected_rows(&expected_by_key);
        Ok(Self { audit_inventory, expected_by_key, expected_counts })
    }

    pub(crate) fn audit_inventory(&self) -> &Inventory {
        &self.audit_inventory
    }

    pub(crate) fn denominator(&self) -> u64 {
        self.audit_inventory.denominator
    }

    pub(crate) fn row_sha256(&self) -> &str {
        &self.audit_inventory.row_sha256
    }

    pub(crate) fn expected_counts(&self) -> &BTreeMap<String, u64> {
        &self.expected_counts
    }

    pub(crate) fn count_expected(&self, expected: &str) -> u64 {
        self.expected_counts.get(expected).copied().unwrap_or(0)
    }

    pub(crate) fn expected_for(&self, file: &str, harness: &str) -> Option<&str> {
        self.expected_by_key.get(&(file.to_string(), harness.to_string())).map(String::as_str)
    }

    pub(crate) fn proof_keys(&self) -> BTreeSet<HarnessKey> {
        self.expected_by_key
            .iter()
            .filter(|(_, expected)| expected.as_str() == "PROOF")
            .map(|(key, _)| key.clone())
            .collect()
    }
}

fn parse_expected_rows(path: &Path, text: &str) -> Result<BTreeMap<HarnessKey, String>, String> {
    let value: Value = serde_json::from_str(text)
        .map_err(|err| format!("invalid inventory JSON {}: {err}", path.display()))?;
    let manifest = value
        .as_object()
        .ok_or_else(|| format!("inventory {} must be a JSON object", path.display()))?;
    let rows = manifest
        .get("rows")
        .and_then(Value::as_array)
        .ok_or_else(|| format!("inventory {} missing rows array", path.display()))?;
    rows.iter().enumerate().map(|(index, row)| parse_expected_row(path, index, row)).collect()
}

fn parse_expected_row(
    path: &Path,
    index: usize,
    row: &Value,
) -> Result<(HarnessKey, String), String> {
    let row = row
        .as_object()
        .ok_or_else(|| format!("{}: rows[{index}] must be an object", path.display()))?;
    let file = required_string(path, index, row, "file")?;
    let harness = required_string(path, index, row, "harness")?;
    let expected = required_string(path, index, row, "expected")?;
    Ok(((file, harness), expected))
}

fn required_string(
    path: &Path,
    index: usize,
    row: &serde_json::Map<String, Value>,
    field: &str,
) -> Result<String, String> {
    row.get(field)
        .and_then(Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| format!("{}: rows[{index}].{field} must be a string", path.display()))
}

fn count_expected_rows(rows: &BTreeMap<HarnessKey, String>) -> BTreeMap<String, u64> {
    let mut counts = BTreeMap::new();
    for expected in rows.values() {
        *counts.entry(expected.clone()).or_insert(0) += 1;
    }
    counts
}
