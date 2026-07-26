// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::collections::{BTreeSet, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct SoundnessLedger {
    entry: Vec<SoundnessLedgerEntry>,
}

#[derive(Debug, Deserialize)]
struct SoundnessLedgerEntry {
    issues: Vec<u64>,
    kind: SoundnessLedgerKind,
    file: String,
    harnesses: Vec<String>,
    accepted_verdicts: Vec<String>,
    notes: String,
}

#[derive(Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum SoundnessLedgerKind {
    FalseProof,
}

struct SeedExpectation {
    issues: &'static [u64],
    file: &'static str,
}

const REQUIRED_SEED_ENTRIES: &[SeedExpectation] = &[
    SeedExpectation { issues: &[129], file: "tests/ay/soundness_129_fail_expected.rs" },
    SeedExpectation { issues: &[155], file: "tests/ay/soundness_155_stale_ssa_fail.rs" },
    SeedExpectation { issues: &[2055], file: "tests/ay/soundness_2055_intermediate_read_fail.rs" },
    SeedExpectation { issues: &[1032], file: "tests/ay/memory_safety_uaf_fail.rs" },
    SeedExpectation { issues: &[1034], file: "tests/ay/memory_safety_double_free_fail.rs" },
    SeedExpectation { issues: &[3636, 3728], file: "tests/ay/realloc_stale_pointer_fail.rs" },
];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("trust-mc-driver should live under the workspace root")
        .to_path_buf()
}

fn ledger_path() -> PathBuf {
    repo_root().join("tests/ay/soundness_ledger.toml")
}

fn load_ledger() -> SoundnessLedger {
    let path = ledger_path();
    let raw = fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read soundness ledger {}: {err}", path.display()));
    toml::from_str(&raw)
        .unwrap_or_else(|err| panic!("failed to parse soundness ledger {}: {err}", path.display()))
}

fn read_source(relative_path: &str) -> String {
    let full_path = repo_root().join(relative_path);
    fs::read_to_string(&full_path).unwrap_or_else(|err| {
        panic!("failed to read soundness source {}: {err}", full_path.display())
    })
}

fn assert_entry_metadata(entry: &SoundnessLedgerEntry, seen_entries: &mut HashSet<String>) {
    assert!(
        !entry.issues.is_empty(),
        "ledger entry for {} must list at least one issue",
        entry.file
    );
    assert!(
        entry.kind == SoundnessLedgerKind::FalseProof,
        "ledger entry for {} must use the supported false-proof kind",
        entry.file
    );
    assert!(
        entry.file.starts_with("tests/ay/") && entry.file.ends_with(".rs"),
        "ledger entry path {} must stay under tests/ay/*.rs",
        entry.file
    );
    let entry_key = format!("{:?}|{}", entry.issues, entry.file);
    assert!(
        seen_entries.insert(entry_key),
        "duplicate soundness ledger entry for issues {:?} at {}",
        entry.issues,
        entry.file
    );
    assert!(
        !entry.harnesses.is_empty(),
        "ledger entry for {} must list at least one harness",
        entry.file
    );
    assert!(
        !entry.accepted_verdicts.is_empty(),
        "ledger entry for {} must list at least one accepted verdict",
        entry.file
    );
    assert!(
        !entry.notes.trim().is_empty(),
        "ledger entry for {} must explain why it is tracked",
        entry.file
    );
}

fn assert_tracked_harnesses(entry: &SoundnessLedgerEntry, source: &str) {
    let mut seen_harnesses = HashSet::new();
    for harness in &entry.harnesses {
        assert!(
            seen_harnesses.insert(harness),
            "{} lists tracked harness `{}` more than once",
            entry.file,
            harness
        );
        let signature = format!("fn {harness}(");
        let signature_count = source.match_indices(&signature).count();
        assert!(
            signature_count == 1,
            "{} must define tracked harness `{}` exactly once (found {})",
            entry.file,
            harness,
            signature_count
        );
    }
}

fn gate_script_path() -> PathBuf {
    repo_root().join("scripts/ay-soundness-gate.sh")
}

fn read_gate_script() -> String {
    let path = gate_script_path();
    fs::read_to_string(&path).unwrap_or_else(|err| {
        panic!("failed to read soundness gate script {}: {err}", path.display())
    })
}

fn gate_script_soundness_files() -> Vec<String> {
    let script = read_gate_script();
    let mut files = Vec::new();
    let mut in_array = false;
    let mut found_end = false;

    for line in script.lines() {
        let trimmed = line.trim();
        if !in_array {
            if trimmed == "SOUNDNESS_FILES=(" {
                in_array = true;
            }
            continue;
        }

        if trimmed == ")" {
            found_end = true;
            break;
        }

        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }

        let file = trimmed.trim_matches('"').trim_matches('\'').to_owned();
        assert!(
            file.starts_with("tests/ay/") && file.ends_with(".rs"),
            "scripts/ay-soundness-gate.sh SOUNDNESS_FILES entry must stay under tests/ay/*.rs: {file}"
        );
        files.push(file);
    }

    assert!(in_array, "scripts/ay-soundness-gate.sh must define SOUNDNESS_FILES=(");
    assert!(found_end, "scripts/ay-soundness-gate.sh SOUNDNESS_FILES array must close with `)`");
    assert!(
        !files.is_empty(),
        "scripts/ay-soundness-gate.sh SOUNDNESS_FILES array must keep at least one tracked file"
    );
    files
}

fn assert_accepted_verdicts(entry: &SoundnessLedgerEntry, source: &str) {
    let mut seen_verdicts = HashSet::new();
    for verdict in &entry.accepted_verdicts {
        assert!(
            seen_verdicts.insert(verdict),
            "{} lists accepted verdict `{}` more than once",
            entry.file,
            verdict
        );
        let directive = format!("kani-expect: {verdict}");
        let fail_closed_directive = format!("soundness-accepted-verdict: {verdict}");
        assert!(
            source.contains(&directive) || source.contains(&fail_closed_directive),
            "{} no longer advertises accepted verdict `{}` via `{}` or `{}`",
            entry.file,
            verdict,
            directive,
            fail_closed_directive
        );
    }
}

#[test]
fn test_soundness_ledger_covers_seed_false_proof_corpus() {
    let ledger = load_ledger();
    for expected in REQUIRED_SEED_ENTRIES {
        let entry = ledger
            .entry
            .iter()
            .find(|entry| entry.issues == expected.issues && entry.file == expected.file)
            .unwrap_or_else(|| {
                panic!(
                    "soundness ledger is missing required seed entry for issues {:?} at {}",
                    expected.issues, expected.file
                )
            });
        assert_eq!(
            entry.kind,
            SoundnessLedgerKind::FalseProof,
            "seed entry {:?} must remain classified as false-proof",
            expected.issues
        );
        assert!(
            entry.accepted_verdicts.iter().all(|v| v == "CTREX" || v == "UNKNOWN" || v == "ERROR"),
            "seed entry {:?} accepted_verdicts must stay non-PROOF (CTREX/UNKNOWN/ERROR), got {:?}",
            expected.issues,
            entry.accepted_verdicts,
        );
    }
}

#[test]
fn test_soundness_ledger_entries_reference_existing_fail_harnesses() {
    let ledger = load_ledger();
    assert!(!ledger.entry.is_empty(), "soundness ledger must keep at least one tracked entry");
    let mut seen_entries = HashSet::new();

    for entry in &ledger.entry {
        assert_entry_metadata(entry, &mut seen_entries);
        let source = read_source(&entry.file);
        assert!(
            source.contains("kani-verify-fail"),
            "{} is listed in the soundness ledger but no longer carries `kani-verify-fail`",
            entry.file
        );
        assert_tracked_harnesses(entry, &source);
        assert_accepted_verdicts(entry, &source);
    }
}

#[test]
fn test_soundness_gate_script_covers_all_ledgered_files() {
    let ledger = load_ledger();
    let script_files = gate_script_soundness_files();
    let mut seen_script_files = HashSet::new();
    for file in &script_files {
        assert!(
            seen_script_files.insert(file),
            "scripts/ay-soundness-gate.sh lists `{file}` more than once in SOUNDNESS_FILES"
        );
    }

    let ledger_files =
        ledger.entry.iter().map(|entry| entry.file.as_str()).collect::<BTreeSet<_>>();
    let script_file_set = script_files.iter().map(String::as_str).collect::<BTreeSet<_>>();
    let missing = ledger_files.difference(&script_file_set).copied().collect::<Vec<_>>();
    let unexpected = script_file_set.difference(&ledger_files).copied().collect::<Vec<_>>();

    assert!(
        missing.is_empty() && unexpected.is_empty(),
        "scripts/ay-soundness-gate.sh SOUNDNESS_FILES must match tests/ay/soundness_ledger.toml exactly; missing={missing:?}, unexpected={unexpected:?}"
    );
}

#[test]
fn test_soundness_gate_script_is_executable() {
    let path = gate_script_path();
    assert!(path.exists(), "scripts/ay-soundness-gate.sh must exist");

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let meta = fs::metadata(&path)
            .unwrap_or_else(|err| panic!("failed to stat {}: {err}", path.display()));
        let mode = meta.permissions().mode();
        assert!(
            mode & 0o111 != 0,
            "scripts/ay-soundness-gate.sh must be executable (mode: {mode:o})"
        );
    }
}
