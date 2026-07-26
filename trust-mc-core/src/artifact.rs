// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Serializable VC IR artifact format.
//!
//! This module defines the serializable representation of verification conditions
//! that can be emitted as a structured artifact alongside `.smt2` files.
//!
//! ## Design
//!
//! The artifact contains metadata about the verification problem:
//! - Harness information
//! - Property metadata (kind, location, description)
//! - Violation structure
//!
//! Actual SMT expressions remain in `.smt2` files; this artifact provides
//! structured metadata for the driver to correlate results with properties.
//!
//! ## Versioning
//!
//! The artifact format is versioned to support evolution:
//! - `version`: Semantic version of the format
//! - Readers should check version compatibility before parsing
//!
//! ## Usage
//!
//! ```text
//! use trust_mc_core::artifact::{VcArtifact, VerificationMode};
//! use trust_mc_core::ident::HarnessId;
//!
//! let harness = HarnessId::new("my_crate::my_harness", "my_harness");
//! let artifact = VcArtifact::new(harness)
//!     .with_mode(VerificationMode::Bmc)
//!     .with_smt_file("harness.smt2");
//!
//! // Serialize to JSON
//! let json = serde_json::to_string_pretty(&artifact).unwrap();
//! assert!(json.contains("my_harness"));
//! ```

use crate::ident::{HarnessId, PropertyId, SourceLocation};
use crate::violation::PropertyKind;
use serde::{Deserialize, Serialize};

/// Current artifact format version.
pub const CURRENT_VERSION: ArtifactVersion = ArtifactVersion { major: 0, minor: 1, patch: 0 };

/// Semantic version for the artifact format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ArtifactVersion {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
}

impl ArtifactVersion {
    /// Creates a new version.
    pub const fn new(major: u32, minor: u32, patch: u32) -> Self {
        Self { major, minor, patch }
    }

    /// Returns true if this version can read artifacts written by `other` version.
    ///
    /// Compatible means same major version with equal or greater minor.
    /// Example: version 0.2.0 can read artifacts from 0.1.0 (backward compatible).
    #[must_use]
    pub fn is_compatible_with(&self, other: &ArtifactVersion) -> bool {
        self.major == other.major && self.minor >= other.minor
    }
}

impl std::fmt::Display for ArtifactVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

/// A serializable verification condition artifact.
///
/// This is the root type for the structured VC artifact format.
/// It contains metadata about the verification problem without
/// the actual SMT expressions (which remain in `.smt2`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcArtifact {
    /// Format version for compatibility checking.
    pub version: ArtifactVersion,

    /// The verification mode.
    pub mode: VerificationMode,

    /// The harness being verified.
    pub harness: HarnessId,

    /// Properties being checked.
    pub properties: Vec<PropertyMetadata>,

    /// Path to the corresponding `.smt2` file (relative or absolute).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub smt_file: Option<String>,

    /// Additional metadata.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<ArtifactMetadata>,

    /// Task #78: base SMT-var identities freed by RECORDED sound approximations.
    ///
    /// Provenance/evidence for the driver's Genuine-certification of a tainted
    /// SAT counterexample: each name is a value whose defining constraint a
    /// sound approximation deleted (normalized without the `__out` suffix). The
    /// per-property [`approximation_dependent`](PropertyMetadata::approximation_dependent)
    /// verdicts are derived from these against the CHC rules.
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub approximated_vars: Vec<String>,

    /// Task #78: number of sound-approximation events whose freed-var identity
    /// was recorded (see [`ChcVc::accounted_approximations`]).
    ///
    /// The driver certifies Genuine only when this equals the harness's
    /// sound-approximation taint total MINUS its `unhandled_calls` count (which
    /// double-labels the same `chc_translation_drop` events) — i.e. every
    /// approximation on the harness was accounted. Absent/zero in legacy
    /// artifacts ⇒ never certifies (fail-closed).
    ///
    /// [`ChcVc::accounted_approximations`]: crate::chc::ChcVc
    #[serde(skip_serializing_if = "is_zero_usize", default)]
    pub accounted_approximations: usize,

    /// Task #78: compiler-side (local best-effort) approximation-identity
    /// completeness flag. `true` iff every sound-approximation the encoder saw
    /// locally recorded its freed-var identity. The driver additionally
    /// re-derives completeness from `accounted_approximations` vs its own taint
    /// total; both must hold to certify. Defaults `false` (fail-closed).
    #[serde(skip_serializing_if = "is_false", default)]
    pub approximation_identity_complete: bool,
}

fn is_zero_usize(n: &usize) -> bool {
    *n == 0
}

fn is_false(b: &bool) -> bool {
    !*b
}

impl VcArtifact {
    /// Creates a new artifact for a harness.
    pub fn new(harness: HarnessId) -> Self {
        Self {
            version: CURRENT_VERSION,
            mode: VerificationMode::Bmc,
            harness,
            properties: Vec::new(),
            smt_file: None,
            metadata: None,
            approximated_vars: Vec::new(),
            accounted_approximations: 0,
            approximation_identity_complete: false,
        }
    }

    /// Sets the verification mode.
    #[must_use]
    pub fn with_mode(mut self, mode: VerificationMode) -> Self {
        self.mode = mode;
        self
    }

    /// Sets the SMT file path.
    #[must_use]
    pub fn with_smt_file(mut self, path: impl Into<String>) -> Self {
        self.smt_file = Some(path.into());
        self
    }

    /// Adds a property.
    pub fn add_property(&mut self, property: PropertyMetadata) {
        self.properties.push(property);
    }

    /// Returns the number of properties.
    #[must_use]
    pub fn property_count(&self) -> usize {
        self.properties.len()
    }
}

/// The verification mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VerificationMode {
    /// Bounded Model Checking.
    Bmc,
    /// Constrained Horn Clauses.
    Chc,
}

/// Metadata about a property being checked.
///
/// This captures everything about a property except the actual
/// SMT expression (which is in the `.smt2` file).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PropertyMetadata {
    /// The property identifier.
    pub id: PropertyId,

    /// The kind of property.
    pub kind: PropertyKind,

    /// Source location where the check occurs.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,

    /// Human-readable description or message.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,

    /// The name of the SMT variable representing this violation (deprecated).
    ///
    /// Use [`smt_var`](Self::smt_var) for new code.
    #[deprecated(since = "0.2.0", note = "use `smt_var` for new code")]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub violation_var: Option<String>,

    /// Generic SMT variable name for this property (violations and covers).
    ///
    /// Replaces `violation_var` to support all property kinds uniformly.
    /// Readers should prefer `smt_var` when present; fall back to `violation_var`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub smt_var: Option<String>,

    /// SMT variable name of the per-check reachability flag (BMC violations).
    ///
    /// Defined in the SMT payload as the check's guard (path condition ∧
    /// ordered assumption context). The driver reports UNREACHABLE when the
    /// solver proves this flag unsatisfiable. `None` means the guard is
    /// trivially `true`.
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub reach_var: Option<String>,

    /// Task #78: whether this check's reachability is DATA-DEPENDENT on a
    /// sound-approximation-freed SMT var (see [`VcArtifact::approximated_vars`]).
    ///
    /// `Some(false)` — the check's reachability is independent of every freed
    /// var, so a tainted SAT counterexample here MAY be certified Genuine (given
    /// approximation-identity completeness). `Some(true)` / `None` — the check
    /// reads a freed value (or the analysis did not run): STAY OverApproximation.
    /// Absent in legacy artifacts (defaults to `None` ⇒ fail-closed).
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub approximation_dependent: Option<bool>,
}

impl PropertyMetadata {
    /// Creates new property metadata.
    #[allow(deprecated)] // violation_var field is deprecated but still initialized
    pub fn new(id: PropertyId, kind: PropertyKind) -> Self {
        Self {
            id,
            kind,
            location: None,
            message: None,
            violation_var: None,
            smt_var: None,
            reach_var: None,
            approximation_dependent: None,
        }
    }

    /// Sets the source location.
    #[must_use]
    pub fn with_location(mut self, location: SourceLocation) -> Self {
        self.location = Some(location);
        self
    }

    /// Sets the message.
    #[must_use]
    pub fn with_message(mut self, message: impl Into<String>) -> Self {
        self.message = Some(message.into());
        self
    }

    /// Sets the violation variable name.
    #[deprecated(since = "0.2.0", note = "use `with_smt_var` for new code")]
    #[must_use]
    pub fn with_violation_var(mut self, var: impl Into<String>) -> Self {
        #[allow(deprecated)]
        {
            self.violation_var = Some(var.into());
        }
        self
    }

    /// Sets the SMT variable name (works for any property kind).
    #[must_use]
    pub fn with_smt_var(mut self, var: impl Into<String>) -> Self {
        self.smt_var = Some(var.into());
        self
    }

    /// Sets the reachability flag variable name.
    #[must_use]
    pub fn with_reach_var(mut self, var: impl Into<String>) -> Self {
        self.reach_var = Some(var.into());
        self
    }

    /// Task #78: sets the approximation-dependence verdict for this check.
    #[must_use]
    pub fn with_approximation_dependent(mut self, dependent: bool) -> Self {
        self.approximation_dependent = Some(dependent);
        self
    }
}

/// Additional artifact metadata.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArtifactMetadata {
    /// The compiler version that generated this artifact.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compiler_version: Option<String>,

    /// Timestamp when the artifact was generated.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timestamp: Option<String>,

    /// Git commit of the source being verified.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_commit: Option<String>,

    /// SMT logic used.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub logic: Option<String>,

    /// Timeout configuration in milliseconds.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timeout_ms: Option<u64>,

    /// Loop invariant hints extracted from user annotations.
    ///
    /// Part of #972: These are converted to ay LemmaHints in the driver.
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub loop_hints: Vec<LoopInvariantHint>,

    /// Unsoundness counters detected during codegen.
    ///
    /// Part of #1929: Iterator sort mismatches and other unsound stubs
    /// are counted here so the driver can emit warnings.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unsoundness: Option<UnsoundnessCounters>,
}

/// Counters for unsoundness detected during codegen.
///
/// Part of #1929: These counters track when codegen encounters situations
/// that cannot be precisely modeled, potentially leading to unsound results.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnsoundnessCounters {
    /// Number of CHC iterator sort mismatches skipped.
    ///
    /// Incremented when CHC stubs encounter non-datatype iterator sorts
    /// and return false constraints instead of precise modeling.
    #[serde(skip_serializing_if = "is_zero", default)]
    pub chc_iterator_skips: usize,

    /// Number of BMC iterator sort mismatches skipped.
    ///
    /// Incremented when BMC stubs encounter sort mismatches and record
    /// property violations instead of precise modeling.
    #[serde(skip_serializing_if = "is_zero", default)]
    pub bmc_iterator_skips: usize,
}

fn is_zero(n: &usize) -> bool {
    *n == 0
}

impl UnsoundnessCounters {
    /// Creates new counters with given values.
    pub fn new(chc_iterator_skips: usize, bmc_iterator_skips: usize) -> Self {
        Self { chc_iterator_skips, bmc_iterator_skips }
    }

    /// Returns true if any unsoundness was detected.
    pub fn has_unsoundness(&self) -> bool {
        self.chc_iterator_skips > 0 || self.bmc_iterator_skips > 0
    }

    /// Returns total number of unsound operations.
    pub fn total(&self) -> usize {
        self.chc_iterator_skips + self.bmc_iterator_skips
    }
}

/// A serializable loop invariant hint.
///
/// This represents a hint extracted from `#[kani::loop_invariant]` annotations.
/// The driver converts these to ay `LemmaHint` structures for CHC solving.
///
/// Part of #972: Loop invariant extraction infrastructure.
/// Part of #1562: Added formula_smt2 for actual constraint extraction.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LoopInvariantHint {
    /// The CHC relation name for the loop head (e.g., "harness_fn__bb5").
    pub relation_name: String,

    /// The basic block index of the loop head.
    pub loop_head_bb: usize,

    /// The local variable indices captured by the invariant closure.
    ///
    /// These are MIR local indices that the invariant references.
    pub captured_vars: Vec<usize>,

    /// The CHC predicate argument indices corresponding to captured_vars.
    ///
    /// When present, this provides the canonical state index for each captured
    /// variable in the same order as `captured_vars`. This avoids relying on
    /// MIR local indices matching CHC argument positions.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub captured_state_indices: Option<Vec<usize>>,

    /// Priority hint for solver (lower = higher priority).
    /// Default: 50 (user hints are medium-high priority).
    #[serde(default = "default_hint_priority")]
    pub priority: u16,

    /// The invariant formula in SMT-LIB2 format.
    ///
    /// When present, this contains the actual constraint extracted from the
    /// closure body (e.g., "(and (>= i 0) (< i n))"). When None, the driver
    /// falls back to a placeholder "true" hint.
    ///
    /// Part of #1562: Formula extraction from closure bodies.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub formula_smt2: Option<String>,
}

fn default_hint_priority() -> u16 {
    50
}

impl LoopInvariantHint {
    /// Creates a new loop invariant hint.
    pub fn new(relation_name: impl Into<String>, loop_head_bb: usize) -> Self {
        Self {
            relation_name: relation_name.into(),
            loop_head_bb,
            captured_vars: Vec::new(),
            captured_state_indices: None,
            priority: default_hint_priority(),
            formula_smt2: None,
        }
    }

    /// Sets the captured variables.
    #[must_use]
    pub fn with_captured_vars(mut self, vars: Vec<usize>) -> Self {
        self.captured_vars = vars;
        self
    }

    /// Sets the captured state indices (CHC argument positions).
    #[must_use]
    pub fn with_captured_state_indices(mut self, indices: Vec<usize>) -> Self {
        self.captured_state_indices = Some(indices);
        self
    }

    /// Sets the priority.
    #[must_use]
    pub fn with_priority(mut self, priority: u16) -> Self {
        self.priority = priority;
        self
    }

    /// Sets the formula in SMT-LIB2 format.
    ///
    /// Part of #1562: Formula extraction from closure bodies.
    #[must_use]
    pub fn with_formula_smt2(mut self, formula: impl Into<String>) -> Self {
        self.formula_smt2 = Some(formula.into());
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version_compatibility() {
        let v010 = ArtifactVersion::new(0, 1, 0);
        let v011 = ArtifactVersion::new(0, 1, 1);
        let v020 = ArtifactVersion::new(0, 2, 0);
        let v100 = ArtifactVersion::new(1, 0, 0);

        // Same version is compatible
        assert!(v010.is_compatible_with(&v010));

        // Higher patch is compatible
        assert!(v011.is_compatible_with(&v010));

        // Higher minor is compatible
        assert!(v020.is_compatible_with(&v010));

        // Lower minor is not compatible
        assert!(!v010.is_compatible_with(&v020));

        // Different major is not compatible
        assert!(!v100.is_compatible_with(&v010));
        assert!(!v010.is_compatible_with(&v100));
    }

    #[test]
    #[allow(deprecated)] // Test uses deprecated with_violation_var for coverage
    fn test_artifact_serialization() {
        let harness = HarnessId::new("test::my_harness", "my_harness");
        let mut artifact =
            VcArtifact::new(harness).with_mode(VerificationMode::Bmc).with_smt_file("test.smt2");

        let prop = PropertyMetadata::new(PropertyId::new(1), PropertyKind::Assertion)
            .with_message("should not panic")
            .with_violation_var("v_1");
        artifact.add_property(prop);

        // Should serialize to JSON
        let json = serde_json::to_string(&artifact).expect("serialization failed");
        assert!(json.contains("\"version\""));
        assert!(json.contains("\"mode\":\"bmc\""));
        assert!(json.contains("\"assertion\""));

        // Should deserialize
        let parsed: VcArtifact = serde_json::from_str(&json).expect("deserialization failed");
        assert_eq!(parsed.version, CURRENT_VERSION);
        assert_eq!(parsed.properties.len(), 1);
    }
}
