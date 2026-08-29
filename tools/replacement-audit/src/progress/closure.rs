// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::{inventory::Inventory, non_proof_closure::validate_non_proof_closure_text};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fs;
use std::path::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ClosureProgress {
    pub(crate) rows: u64,
    pub(crate) valid: bool,
    pub(crate) sha256: String,
    pub(crate) failures: Vec<String>,
}

pub(crate) fn load_closure(path: &Path, inventory: &Inventory) -> Result<ClosureProgress, String> {
    let text = fs::read_to_string(path)
        .map_err(|err| format!("failed to read non-proof closure {}: {err}", path.display()))?;
    let sha256 = sha256_hex(text.as_bytes());
    let rows = closure_row_count(path, &text)?;
    let failures = validate_non_proof_closure_text(&path.display().to_string(), &text, inventory)
        .into_iter()
        .map(|failure| failure.to_string())
        .collect::<Vec<_>>();
    Ok(ClosureProgress { rows, valid: failures.is_empty(), sha256, failures })
}

fn closure_row_count(path: &Path, text: &str) -> Result<u64, String> {
    let value: Value = serde_json::from_str(text)
        .map_err(|err| format!("invalid non-proof closure JSON {}: {err}", path.display()))?;
    Ok(value.get("rows").and_then(Value::as_array).map(|rows| rows.len() as u64).unwrap_or(0))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(64);
    for byte in digest {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}
