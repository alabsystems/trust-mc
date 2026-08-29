// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! VC artifact loading and path helpers.

use std::collections::HashMap;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;

use crate::property_model::RawSourceLocation;
use trust_mc_core::artifact::VcArtifact;

/// Per-property metadata recovered from the VC artifact sidecar.
///
/// Carries the source location and the optional human-readable message
/// (e.g. the assertion expression text `assertion failed: foo() == None`).
#[derive(Debug, Clone)]
pub(crate) struct VcPropertyInfo {
    pub location: RawSourceLocation,
    pub message: Option<String>,
}

/// Type alias for mapping violation variable names to property metadata.
///
/// The key is the full violation variable name (e.g., "ay_violation_assertion_0")
/// and the value is the location + message from the VC artifact.
pub(crate) type VcLocationMap = HashMap<String, VcPropertyInfo>;

/// A per-property CHC check recovered from the VC artifact (BSEM-18).
///
/// Each entry corresponds to one `error_p{id}` relation the CHC encoder emitted
/// for a distinct check site (bounds, overflow, assert, …). The driver expands
/// the single aggregate CHC verdict into one report line per entry.
#[derive(Debug, Clone)]
pub(crate) struct ChcArtifactProperty {
    /// The per-property error relation name (`error_p{id}`); equals `smt_var`.
    pub relation: String,
    /// The property's deterministic per-harness id.
    pub id: u32,
    /// The check kind (assertion, overflow, bounds, …).
    pub kind: trust_mc_core::violation::PropertyKind,
    /// Optional human-readable message.
    pub message: Option<String>,
    /// Source location (fields may be `None` when not recorded).
    pub location: RawSourceLocation,
}

/// Task #78: approximation-identity evidence recovered from the VC artifact,
/// used by the driver to soundly certify a tainted SAT counterexample Genuine.
#[derive(Debug, Clone, Default)]
pub(crate) struct ApproximationEvidence {
    /// Compiler-side (local best-effort) completeness flag: every
    /// sound-approximation the encoder saw recorded its freed-var identity.
    pub complete: bool,
    /// Number of sound-approximation events whose freed-var identity was
    /// recorded. The driver cross-checks this against the harness taint total.
    pub accounted: usize,
    /// The base SMT-var identities freed by recorded approximations (evidence).
    pub approximated_vars: Vec<String>,
    /// Per-property (`error_p{id}`) data-dependence verdict, keyed by property
    /// id. `Some(false)` means the check is independent of every freed var.
    pub dependent_by_id: HashMap<u32, Option<bool>>,
}

/// Load [`ApproximationEvidence`] from a VC artifact sidecar (Task #78).
///
/// Returns `None` when the artifact is missing/unreadable — the driver then
/// keeps the counterexample OverApproximation (fail-closed).
pub(crate) fn load_approximation_evidence(path: &Path) -> Option<ApproximationEvidence> {
    if !path.exists() {
        return None;
    }
    let file = File::open(path).ok()?;
    let reader = BufReader::new(file);
    let artifact: VcArtifact = serde_json::from_reader(reader).ok()?;

    let mut dependent_by_id = HashMap::new();
    for prop in &artifact.properties {
        if prop.smt_var.as_deref().is_some_and(|v| v.starts_with("error_p")) {
            dependent_by_id.insert(prop.id.id, prop.approximation_dependent);
        }
    }
    Some(ApproximationEvidence {
        complete: artifact.approximation_identity_complete,
        accounted: artifact.accounted_approximations,
        approximated_vars: artifact.approximated_vars,
        dependent_by_id,
    })
}

/// Load the per-property CHC check table from a VC artifact (BSEM-18).
///
/// Returns only properties whose SMT variable names a per-property CHC error
/// relation (`error_p{id}`). Empty if the artifact is missing, unreadable, or
/// carries no such properties (e.g. a BMC-mode artifact). The returned order
/// matches the artifact order, which is the deterministic MIR emission order.
/// Whether this harness's artifact is readable AND registers NO obligations.
///
/// [`load_chc_property_table`] returns an empty vector for four different
/// situations — missing file, unreadable file, unparseable file, and a harness
/// that genuinely emitted no checks — and only the last one means "there was
/// nothing to verify". The CHC success path fabricates a synthetic `Success`
/// property whenever the table is empty, which makes the V4b no-checks gate
/// (`harness_runner`) unable to fire: a harness that compiled to zero
/// obligations reported `VERIFICATION:- SUCCESSFUL` under `--ay-chc` while BMC
/// correctly reported `INCONCLUSIVE (no checks)`.
///
/// Deliberately narrow: anything other than "parsed cleanly, zero properties"
/// answers `false` and leaves the existing behaviour alone, so a missing or
/// relocated artifact cannot turn a whole run inconclusive.
pub(crate) fn artifact_registers_no_obligations(path: &Path) -> bool {
    if !path.exists() {
        return false;
    }
    let Ok(file) = File::open(path) else {
        return false;
    };
    let Ok(artifact): Result<VcArtifact, _> = serde_json::from_reader(BufReader::new(file)) else {
        return false;
    };
    artifact.properties.is_empty()
}

/// The message prefixes the loop-contract instrumentation stamps on its
/// obligations. These are the ONLY reliable marker at the artifact level:
/// the obligations are registered through `hook_safety_check`, so their
/// `kind` is `assertion`/`memory_safety` — indistinguishable from a user
/// assertion — and their `smt_var` is an `ay_violation_*` name, so
/// `load_chc_property_table` (which keeps only `error_p*`) filters every one
/// of them out. Matching the text is what c63470f59 made possible.
pub(crate) const LOOP_CONTRACT_OBLIGATION_PREFIXES: [&str; 3] = [
    "loop invariant base case:",
    "loop invariant inductive step:",
    "loop decreases clause:",
];

/// The Kani/CBMC-identical description text the RENDERED report carries for the
/// two invariant obligations, and the check classes they are listed under.
///
/// Mirrors `trust-mc-compiler`'s
/// `kani_middle::transform::loop_contracts::rule::{LOOP_INVARIANT_BASE_MSG,
/// LOOP_INVARIANT_STEP_MSG, LOOP_ID_MARKER}` — the compiler stamps the internal
/// stem plus a `(loop N)` suffix onto the artifact, and
/// `violation::apply_loop_contract_naming` rewrites it into these forms for
/// display. Two different consumers therefore need two different markers:
/// `LOOP_CONTRACT_OBLIGATION_PREFIXES` reads the ARTIFACT (still the internal
/// stem), while the two-lane vacuity guard reads a lane's rendered STDOUT and
/// must look for the texts below.
pub(crate) const LOOP_INVARIANT_BASE_CLASS: &str = "loop_invariant_base";

/// Check class of the inductive-step obligation. See `LOOP_INVARIANT_BASE_CLASS`.
pub(crate) const LOOP_INVARIANT_STEP_CLASS: &str = "loop_invariant_step";

/// Rendered description of the base-case obligation, up to the loop id
/// (`<fn>.<N>`, appended by `apply_loop_contract_naming`).
pub(crate) const LOOP_INVARIANT_BASE_REPORT_TEXT: &str = "Check invariant before entry for loop ";

/// Rendered description of the inductive-step obligation, up to the loop id.
pub(crate) const LOOP_INVARIANT_STEP_REPORT_TEXT: &str = "Check invariant after step for loop ";

/// The same three obligations as `LOOP_CONTRACT_OBLIGATION_PREFIXES`, but as
/// they appear in the RENDERED report: `[canonical, also-accepted]`.
///
/// Both spellings are listed because the rename is a display step, and a
/// report is only guaranteed to carry the canonical form on paths that ran it.
/// The guard that uses this is a VACUITY check ("did this lane actually contain
/// the obligation?"), so accepting the instrumentation's internal stem as well
/// can only prevent a false "missing" — the stem cannot appear unless the
/// obligation is genuinely there. The decreases obligation is never renamed, so
/// both of its entries are the same stem.
pub(crate) const LOOP_CONTRACT_REPORT_MARKERS: [[&str; 2]; 3] = [
    [LOOP_INVARIANT_BASE_REPORT_TEXT, "loop invariant base case:"],
    [LOOP_INVARIANT_STEP_REPORT_TEXT, "loop invariant inductive step:"],
    ["loop decreases clause:", "loop decreases clause:"],
];

/// Does this harness carry loop-contract obligations?
///
/// Deliberately reads the RAW artifact rather than `load_chc_property_table`:
/// see the note on the prefixes above. Answers `false` for a missing or
/// unparseable artifact, so a relocated file can only mean "do not retry" —
/// never a changed verdict.
///
/// `kani_metadata`'s `has_loop_contracts` is NOT usable here: it is hardwired
/// `false` (trust-mc-compiler/src/kani_middle/metadata.rs:52,177).
pub(crate) fn artifact_has_loop_contract_obligations(path: &Path) -> bool {
    if !path.exists() {
        return false;
    }
    let Ok(file) = File::open(path) else {
        return false;
    };
    let Ok(artifact): Result<VcArtifact, _> = serde_json::from_reader(BufReader::new(file))
    else {
        return false;
    };
    artifact.properties.iter().any(is_loop_contract_property)
}

/// A property belongs to the loop contract if EITHER its kind says so, OR its
/// message carries one of the instrumentation's prefixes.
///
/// Both channels are needed, and which one fires depends on the configuration:
/// * With `--ay-chc` on a harness whose measure is unsupported, the run
///   short-circuits on the fail-closed decreases stub and the artifact holds
///   exactly ONE property — `PropertyKind::LoopDecreases`, message "loop
///   `decreases` ranking not proven". No prefix matches it.
/// * In bmc mode the obligations arrive through `hook_safety_check`, so their
///   kind is `assertion` and only the MESSAGE identifies them.
/// Matching one channel only makes the detector a silent no-op on exactly the
/// rows that need it — measured both ways.
fn is_loop_contract_property(p: &trust_mc_core::artifact::PropertyMetadata) -> bool {
    if matches!(
        p.kind,
        trust_mc_core::violation::PropertyKind::LoopInvariant
            | trust_mc_core::violation::PropertyKind::LoopDecreases
    ) {
        return true;
    }
    p.message.as_deref().is_some_and(|m| {
        LOOP_CONTRACT_OBLIGATION_PREFIXES.iter().any(|pre| m.starts_with(pre))
    })
}

/// The loop-contract obligation messages present in an artifact, deduplicated
/// by prefix. The two-lane merge uses this to require that the obligations were
/// actually PRESENT in the obligations lane — "no failing checks" alone would
/// let a lane whose obligations were dropped pass vacuously.
/// Did the compiler certify that this harness's body has NO obligation site?
///
/// Positive evidence for the vacuity decision: an encoded body with no `Call`
/// and no `Assert` terminator cannot have HAD an obligation to drop, so zero
/// checks is the `fn check() {}` shape Kani reports as a clean `0 of 0 failed`.
/// Anything that can panic — including `Option::unwrap`, which stays a `Call`
/// because the inliner preserves the boundary — is never certified.
///
/// Fail-closed: a missing, unreadable, or unmarked artifact answers `false`.
pub(crate) fn artifact_body_is_obligation_free(path: &Path) -> bool {
    if !path.exists() {
        return false;
    }
    let Ok(file) = File::open(path) else {
        return false;
    };
    let Ok(artifact): Result<VcArtifact, _> = serde_json::from_reader(BufReader::new(file))
    else {
        return false;
    };
    artifact.metadata.as_ref().and_then(|m| m.obligation_free_body).unwrap_or(false)
}

pub(crate) fn artifact_loop_obligation_kinds(path: &Path) -> Vec<&'static str> {
    let mut found: Vec<&'static str> = Vec::new();
    if !path.exists() {
        return found;
    }
    let Ok(file) = File::open(path) else {
        return found;
    };
    let Ok(artifact): Result<VcArtifact, _> = serde_json::from_reader(BufReader::new(file))
    else {
        return found;
    };
    for p in &artifact.properties {
        let Some(msg) = p.message.as_deref() else { continue };
        for pre in LOOP_CONTRACT_OBLIGATION_PREFIXES {
            if msg.starts_with(pre) && !found.contains(&pre) {
                found.push(pre);
            }
        }
    }
    found
}

pub(crate) fn load_chc_property_table(path: &Path) -> Vec<ChcArtifactProperty> {
    if !path.exists() {
        return Vec::new();
    }
    let Ok(file) = File::open(path) else {
        return Vec::new();
    };
    let reader = BufReader::new(file);
    let Ok(artifact): Result<VcArtifact, _> = serde_json::from_reader(reader) else {
        return Vec::new();
    };

    let mut out = Vec::new();
    for prop in artifact.properties {
        let Some(var) = prop.smt_var.clone() else {
            continue;
        };
        if !var.starts_with("error_p") {
            continue;
        }
        let location = match prop.location {
            Some(loc) => RawSourceLocation {
                file: Some(loc.file),
                line: Some(loc.line.to_string()),
                column: loc.column.map(|c| c.to_string()),
                function: loc.function,
            },
            None => RawSourceLocation { file: None, line: None, column: None, function: None },
        };
        out.push(ChcArtifactProperty {
            relation: var,
            id: prop.id.id,
            kind: prop.kind,
            message: prop.message,
            location,
        });
    }
    out
}

/// Load a VC artifact sidecar file and build a location map.
///
/// The VC artifact contains property metadata including source locations keyed by
/// SMT variable names. This allows the driver to populate source locations
/// in verification results.
///
/// #1164: Prefers `smt_var` (unified field for all property types) over
/// `violation_var` (deprecated, violations only) for forward compatibility.
///
/// REQUIRES: path points to a valid .vc.json file (or doesn't exist)
/// ENSURES: Returns Some(map) on successful load, with map containing all properties
///          that have smt_var or violation_var set (location may be None/empty)
/// ENSURES: Returns None if the file doesn't exist or cannot be parsed
#[allow(deprecated)] // Reads deprecated violation_var for backward compatibility
pub(crate) fn load_vc_artifact(path: &Path) -> Option<VcLocationMap> {
    if !path.exists() {
        return None;
    }

    let file = File::open(path).ok()?;
    let reader = BufReader::new(file);
    let artifact: VcArtifact = serde_json::from_reader(reader).ok()?;

    let mut map = HashMap::new();
    for prop in artifact.properties {
        // #1164: Prefer smt_var (unified), fall back to violation_var (deprecated)
        let var_name = prop.smt_var.or(prop.violation_var);
        if let Some(var_name) = var_name {
            // Convert trust_mc_core::SourceLocation to property_model::RawSourceLocation
            // Note: trust_mc_core uses u32 for line/column, property_model uses Option<String>
            let location = if let Some(loc) = prop.location {
                RawSourceLocation {
                    file: Some(loc.file),
                    line: Some(loc.line.to_string()),
                    column: loc.column.map(|c| c.to_string()),
                    function: loc.function,
                }
            } else {
                // Property exists but has no location - store empty location
                // so we know the property exists even without location data
                RawSourceLocation { file: None, line: None, column: None, function: None }
            };
            map.insert(var_name, VcPropertyInfo { location, message: prop.message });
        }
    }

    Some(map)
}

/// Load loop invariant hints from a VC artifact file.
///
/// Part of #972: Extracts `LoopInvariantHint` structures from the VcArtifact
/// for conversion to ay LemmaHints in CHC solving.
///
/// REQUIRES: path points to a valid .vc.json file (or doesn't exist)
/// ENSURES: Returns Vec of hints on successful load (may be empty)
/// ENSURES: Returns empty Vec if file doesn't exist or has no hints
#[cfg(feature = "ay-chc-native")]
pub(crate) fn load_loop_hints(path: &Path) -> Vec<trust_mc_core::LoopInvariantHint> {
    if !path.exists() {
        return Vec::new();
    }

    let Ok(file) = File::open(path) else {
        return Vec::new();
    };
    let reader = BufReader::new(file);
    let Ok(artifact): Result<VcArtifact, _> = serde_json::from_reader(reader) else {
        return Vec::new();
    };

    artifact.metadata.map(|m| m.loop_hints).unwrap_or_default()
}

/// Get the VC artifact path for a given SMT file.
///
/// The artifact is a sidecar file with the final extension replaced by `.vc.json`.
/// Examples:
/// - `foo.smt2` -> `foo.vc.json`
/// - `foo.symtab.smt2` -> `foo.symtab.vc.json`
///
/// REQUIRES: smt_path is a path to an SMT file
/// ENSURES: Returns path with final extension replaced by `.vc.json`
pub(crate) fn vc_artifact_path_for_smt(smt_path: &Path) -> std::path::PathBuf {
    smt_path.with_extension("vc.json")
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "ay-chc-native")]
    use super::load_loop_hints;

    /// End-to-end test: loop hints roundtrip through VcArtifact serialization.
    ///
    /// Verifies the full integration path:
    /// 1. Create VcArtifact with loop_hints in metadata
    /// 2. Serialize to JSON file
    /// 3. Load via load_loop_hints (with ay-chc-native feature)
    /// 4. Verify hints match original
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn test_loop_hint_e2e_artifact_roundtrip() {
        use tempfile::NamedTempFile;
        use trust_mc_core::LoopInvariantHint;
        use trust_mc_core::artifact::{ArtifactMetadata, VcArtifact, VerificationMode};
        use trust_mc_core::ident::HarnessId;

        // Create realistic loop hints for a simple_while_loop harness
        // Include formula_smt2 to test the new field serialization (#1562)
        let hints = vec![
            LoopInvariantHint::new("simple_while_loop__bb3", 3)
                .with_captured_vars(vec![0, 1])
                .with_captured_state_indices(vec![0, 1])
                .with_priority(50)
                .with_formula_smt2("(and (>= i 0) (< i 10))"),
            LoopInvariantHint::new("simple_while_loop__bb7", 7)
                .with_captured_vars(vec![2])
                .with_captured_state_indices(vec![3])
                .with_priority(25),
            // Third hint without formula to test None serialization
        ];

        // Create VcArtifact with metadata containing loop_hints
        let harness = HarnessId::new("test::simple_while_loop", "simple_while_loop");
        let metadata = ArtifactMetadata { loop_hints: hints, ..ArtifactMetadata::default() };

        let mut artifact = VcArtifact::new(harness)
            .with_mode(VerificationMode::Chc)
            .with_smt_file("simple_while_loop.smt2");
        artifact.metadata = Some(metadata);

        // Write to temp file
        let temp_file = NamedTempFile::with_suffix(".vc.json").expect("create temp file");
        let json = serde_json::to_string_pretty(&artifact).expect("serialize artifact");
        std::fs::write(temp_file.path(), &json).expect("write temp file");

        // Load hints via the driver's load_loop_hints function
        let loaded = load_loop_hints(temp_file.path());

        // Verify roundtrip
        assert_eq!(loaded.len(), 2, "Should load 2 loop hints");
        assert_eq!(loaded[0].relation_name, "simple_while_loop__bb3");
        assert_eq!(loaded[0].loop_head_bb, 3);
        assert_eq!(loaded[0].captured_vars, vec![0, 1]);
        assert_eq!(loaded[0].captured_state_indices, Some(vec![0, 1]));
        assert_eq!(loaded[0].priority, 50);
        // Verify formula_smt2 roundtrip (#1562)
        assert_eq!(
            loaded[0].formula_smt2,
            Some("(and (>= i 0) (< i 10))".to_string()),
            "First hint should have formula_smt2"
        );
        assert_eq!(loaded[1].relation_name, "simple_while_loop__bb7");
        assert_eq!(loaded[1].loop_head_bb, 7);
        assert_eq!(loaded[1].captured_vars, vec![2]);
        assert_eq!(loaded[1].captured_state_indices, Some(vec![3]));
        assert_eq!(loaded[1].priority, 25);
        // Second hint should have no formula (None)
        assert_eq!(loaded[1].formula_smt2, None, "Second hint should have no formula_smt2");
    }

    /// Test that load_loop_hints returns empty vec for non-existent file.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn test_loop_hint_e2e_missing_file() {
        use tempfile::TempDir;
        // Use tempdir to create a path that definitely doesn't exist
        let temp_dir = TempDir::new().expect("create temp dir");
        let nonexistent = temp_dir.path().join("does_not_exist.vc.json");
        let loaded = load_loop_hints(&nonexistent);
        assert!(loaded.is_empty(), "Missing file should return empty hints");
    }

    /// Test that load_loop_hints returns empty vec for artifact without metadata.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn test_loop_hint_e2e_no_metadata() {
        use tempfile::NamedTempFile;
        use trust_mc_core::artifact::{VcArtifact, VerificationMode};
        use trust_mc_core::ident::HarnessId;

        // Create artifact WITHOUT metadata (no loop_hints)
        let harness = HarnessId::new("test::no_hints", "no_hints");
        let artifact = VcArtifact::new(harness)
            .with_mode(VerificationMode::Bmc)
            .with_smt_file("no_hints.smt2");

        let temp_file = NamedTempFile::with_suffix(".vc.json").expect("create temp file");
        let json = serde_json::to_string(&artifact).expect("serialize artifact");
        std::fs::write(temp_file.path(), &json).expect("write temp file");

        let loaded = load_loop_hints(temp_file.path());
        assert!(loaded.is_empty(), "Artifact without metadata should return empty hints");
    }

    /// Test that load_loop_hints returns empty vec for artifact with empty hints array.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn test_loop_hint_e2e_empty_hints() {
        use tempfile::NamedTempFile;
        use trust_mc_core::artifact::{ArtifactMetadata, VcArtifact, VerificationMode};
        use trust_mc_core::ident::HarnessId;

        // Create artifact with metadata but EMPTY loop_hints
        let harness = HarnessId::new("test::empty_hints", "empty_hints");
        let metadata = ArtifactMetadata::default(); // default has empty loop_hints vec

        let mut artifact = VcArtifact::new(harness)
            .with_mode(VerificationMode::Chc)
            .with_smt_file("empty_hints.smt2");
        artifact.metadata = Some(metadata);

        let temp_file = NamedTempFile::with_suffix(".vc.json").expect("create temp file");
        let json = serde_json::to_string(&artifact).expect("serialize artifact");
        std::fs::write(temp_file.path(), &json).expect("write temp file");

        let loaded = load_loop_hints(temp_file.path());
        assert!(loaded.is_empty(), "Artifact with empty hints array should return empty hints");
    }

    /// Test that load_loop_hints handles malformed JSON gracefully.
    #[test]
    #[cfg(feature = "ay-chc-native")]
    fn test_loop_hint_e2e_malformed_json() {
        use tempfile::NamedTempFile;

        let temp_file = NamedTempFile::with_suffix(".vc.json").expect("create temp file");
        std::fs::write(temp_file.path(), "{ invalid json }").expect("write malformed json");

        let loaded = load_loop_hints(temp_file.path());
        assert!(loaded.is_empty(), "Malformed JSON should return empty hints");
    }
}
