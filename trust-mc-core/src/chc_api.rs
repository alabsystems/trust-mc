// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Typed CHC/PDR library API for MIR-derived obligations.
//!
//! This module is the narrow boundary tRust can use without encoding proof
//! metadata as SMT-LIB strings. Callers provide a typed [`ChcVc`] plus MIR
//! obligation identity; solvers return typed verdicts and evidence metadata.

use std::time::Duration;

use crate::chc::ChcVc;
use crate::evidence::{
    ChcPdrProofKind, ChcPdrStats, MirObligationKind, NativeTypedChcObligationMetadata,
    ObligationOrigin,
};

/// MIR-derived CHC/PDR obligation carried across the library boundary.
#[derive(Debug, Clone)]
pub struct MirChcPdrObligation {
    /// Stable identifier for this obligation in the producer.
    pub obligation_id: String,
    /// Display name for the function or harness that produced the obligation.
    pub function_name: String,
    /// Source-level obligation category.
    pub kind: MirObligationKind,
    /// Whether this is real MIR-derived input or a non-proving placeholder.
    pub origin: ObligationOrigin,
    /// Optional native bundle metadata for trust_ir request/proof-lineage consumers.
    pub native_metadata: Option<NativeTypedChcObligationMetadata>,
    /// Typed CHC verification condition.
    pub vc: ChcVc,
}

impl MirChcPdrObligation {
    /// Create a MIR-derived typed CHC/PDR obligation.
    #[must_use]
    pub fn new(
        obligation_id: impl Into<String>,
        function_name: impl Into<String>,
        kind: MirObligationKind,
        vc: ChcVc,
    ) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            function_name: function_name.into(),
            kind,
            origin: ObligationOrigin::MirDerived,
            native_metadata: None,
            vc,
        }
    }

    /// Create a typed placeholder. Placeholders validate as non-proof input.
    #[must_use]
    pub fn router_placeholder(
        obligation_id: impl Into<String>,
        function_name: impl Into<String>,
        kind: MirObligationKind,
        vc: ChcVc,
    ) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            function_name: function_name.into(),
            kind,
            origin: ObligationOrigin::RouterPlaceholder,
            native_metadata: None,
            vc,
        }
    }

    /// Attach typed native-bundle provenance to this CHC/PDR obligation.
    #[must_use]
    pub fn with_native_metadata(mut self, metadata: NativeTypedChcObligationMetadata) -> Self {
        self.native_metadata = Some(metadata);
        self
    }

    /// Validate the typed obligation shape before solving.
    pub fn validate(&self) -> Result<(), MirChcPdrObligationError> {
        if self.obligation_id.trim().is_empty() {
            return Err(MirChcPdrObligationError::EmptyObligationId);
        }
        if self.function_name.trim().is_empty() {
            return Err(MirChcPdrObligationError::EmptyFunctionName);
        }
        if self.origin != ObligationOrigin::MirDerived {
            return Err(MirChcPdrObligationError::NotMirDerived);
        }
        if self.vc.relations.is_empty() {
            return Err(MirChcPdrObligationError::NoRelations);
        }
        if self.vc.rules.is_empty() {
            return Err(MirChcPdrObligationError::NoRules);
        }
        let Some(target) = self.vc.query.target.as_deref() else {
            return Err(MirChcPdrObligationError::MissingQueryTarget);
        };
        if !self.vc.relations.iter().any(|rel| rel.name == target) {
            return Err(MirChcPdrObligationError::UndeclaredQueryTarget {
                target: target.to_string(),
            });
        }
        Ok(())
    }

    /// Return the query target relation, defaulting to the conventional `error`.
    #[must_use]
    pub fn query_target(&self) -> &str {
        self.vc.query.target.as_deref().unwrap_or("error")
    }

    /// Stable CHC/PDR statistics available without serializing the VC.
    #[must_use]
    pub fn stats(&self) -> ChcPdrStats {
        ChcPdrStats { relation_count: self.vc.relations.len(), clause_count: self.vc.rules.len() }
    }

    /// Returns true if no Horn rule derives the queried relation.
    #[must_use]
    pub fn is_trivially_safe(&self) -> bool {
        let target = self.query_target();
        !self.vc.rules.iter().any(|rule| rule.head.name == target)
    }
}

/// Validation failures for typed MIR-derived CHC/PDR obligations.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum MirChcPdrObligationError {
    EmptyObligationId,
    EmptyFunctionName,
    NotMirDerived,
    NoRelations,
    NoRules,
    MissingQueryTarget,
    UndeclaredQueryTarget { target: String },
}

impl std::fmt::Display for MirChcPdrObligationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyObligationId => write!(f, "obligation id must not be empty"),
            Self::EmptyFunctionName => write!(f, "function name must not be empty"),
            Self::NotMirDerived => write!(f, "obligation is not MIR-derived"),
            Self::NoRelations => write!(f, "CHC obligation has no relation declarations"),
            Self::NoRules => write!(f, "CHC obligation has no Horn rules"),
            Self::MissingQueryTarget => write!(f, "CHC obligation has no query target"),
            Self::UndeclaredQueryTarget { target } => {
                write!(f, "query target `{target}` has no relation declaration")
            }
        }
    }
}

impl std::error::Error for MirChcPdrObligationError {}

/// CHC/PDR engine selection for typed solves.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum ChcPdrEngine {
    /// Let trust_mc pick the production CHC/PDR portfolio.
    #[default]
    Auto,
    /// Force PDR/IC3 proof solving.
    Pdr,
    /// Force the adaptive CHC portfolio.
    AdaptivePortfolio,
}

/// Options for a typed CHC/PDR solve request.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct ChcPdrSolveOptions {
    pub engine: ChcPdrEngine,
    pub timeout: Option<Duration>,
    pub produce_proof_certificate: bool,
}

impl ChcPdrSolveOptions {
    /// Select a CHC/PDR engine.
    #[must_use]
    pub fn with_engine(mut self, engine: ChcPdrEngine) -> Self {
        self.engine = engine;
        self
    }

    /// Set a wall-clock timeout for the solve.
    #[must_use]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// Request proof-certificate production when the backend supports it.
    #[must_use]
    pub fn with_proof_certificate(mut self, produce: bool) -> Self {
        self.produce_proof_certificate = produce;
        self
    }
}

/// Typed request passed from tRust or another MIR producer to trust_mc.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ChcPdrSolveRequest {
    pub obligation: MirChcPdrObligation,
    pub options: ChcPdrSolveOptions,
}

impl ChcPdrSolveRequest {
    /// Build a typed CHC/PDR solve request with default options.
    #[must_use]
    pub fn new(obligation: MirChcPdrObligation) -> Self {
        Self { obligation, options: ChcPdrSolveOptions::default() }
    }

    /// Attach solve options.
    #[must_use]
    pub fn with_options(mut self, options: ChcPdrSolveOptions) -> Self {
        self.options = options;
        self
    }
}

/// How a typed CHC/PDR refutation counterexample was machine-checked by the
/// producer before it was attached to a [`ChcPdrRefutationWitness`].
///
/// This is deliberately a typed enum, not a boolean: consumers accept only the
/// verification kinds they recognize and must treat any future variant as
/// unvalidated (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ChcPdrCexVerification {
    /// ay-chc replay-verified the counterexample derivation against the exact
    /// lowered CHC problem (`ay_chc::VerifiedChcResult::Unsafe` carries a
    /// replay-checked trace, never a bare solver claim).
    AyChcReplayVerified {
        /// Number of steps in the replay-verified counterexample trace.
        step_count: u64,
    },
    /// The acyclic direct-SMT decision procedure exhaustively composed a
    /// satisfiable derivation of the query target and returned its concrete
    /// witness model.
    DirectSmtModel,
}

/// Producer attestation about the concreteness (havoc-freedom) of the encoding
/// trust_mc itself performed for a refuted typed obligation.
///
/// Direction of soundness: sound over-approximation (fresh universally
/// quantified havoc values, dropped constraints) is sound for PROOFS but makes
/// REFUTATIONS potentially spurious. A refutation witness is therefore only
/// admissible when the encoding stage it covers performed ZERO drops and ZERO
/// havocs of any kind, including "sound" ones.
///
/// SCOPE: this attests the translation trust_mc performed on the submitted
/// typed `ChcVc` (the `ChcVc` -> native solver-problem lowering, which is
/// exact-or-reject by construction). It cannot and does not attest how the
/// submitted `ChcVc` itself was produced from source/MIR semantics; that stage
/// belongs to the producer of the obligation, and consumers must account for
/// it on their own side of the boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ChcPdrEncodingConcreteness {
    /// The trust_mc encoding stage was exact. All counts must be zero for the
    /// witness to be admissible; they are carried explicitly (instead of an
    /// attestation-by-omission boolean) so consumers can check them and so a
    /// future lossy lowering fallback that increments them is visible.
    ExactEncoding {
        /// Constructs dropped by the translation (must be 0).
        translation_drops: u64,
        /// Values havoc'd by the translation, including "sound" havoc (must be 0).
        havocs: u64,
        /// Undef-as-diagnostic-havoc translations (must be 0).
        undef_diagnostic_havocs: u64,
    },
}

impl ChcPdrEncodingConcreteness {
    /// True iff this is an exact-encoding attestation with all-zero counts.
    #[must_use]
    pub fn is_exact_with_zero_counts(&self) -> bool {
        matches!(
            self,
            Self::ExactEncoding { translation_drops: 0, havocs: 0, undef_diagnostic_havocs: 0 }
        )
    }
}

/// Refutation witness for a typed CHC/PDR `Refuted` verdict.
///
/// The witness binds a machine-checked counterexample to the exact obligation
/// identity, the exact normalized encoded formula, and the semantic
/// configuration of the solve, and carries a typed concreteness attestation
/// for the trust_mc encoding stage. A bare transport flag is not admissible
/// evidence (it can be forged, replayed, or detached from the formula it
/// claims to certify); consumers must independently recompute the digests from
/// their OWN retained input and refuse the witness on any mismatch.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcPdrRefutationWitness {
    /// Producer obligation identity the counterexample refutes.
    pub obligation_id: String,
    /// Lowercase-hex SHA-256 of the exact normalized CHC input that was solved
    /// (the `normalized_typed_chc_pdr_input` identity). Consumers recompute
    /// this from their own retained request and require equality.
    pub encoded_formula_sha256: String,
    /// Lowercase-hex SHA-256 of the canonical semantic-configuration
    /// serialization the driver used for the solve. Consumers recompute this
    /// from their own configuration and require equality.
    pub semantic_config_sha256: String,
    /// The counterexample payload, serialized as the existing
    /// `trust_mc.typed-chc-pdr-counterexample/v1` JSON artifact schema.
    pub counterexample_json: String,
    /// How the counterexample was machine-checked by the producer.
    pub verification: ChcPdrCexVerification,
    /// Typed concreteness attestation for the trust_mc encoding stage.
    pub concreteness: ChcPdrEncodingConcreteness,
}

impl ChcPdrRefutationWitness {
    /// Build a refutation witness.
    #[must_use]
    pub fn new(
        obligation_id: impl Into<String>,
        encoded_formula_sha256: impl Into<String>,
        semantic_config_sha256: impl Into<String>,
        counterexample_json: impl Into<String>,
        verification: ChcPdrCexVerification,
        concreteness: ChcPdrEncodingConcreteness,
    ) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            encoded_formula_sha256: encoded_formula_sha256.into(),
            semantic_config_sha256: semantic_config_sha256.into(),
            counterexample_json: counterexample_json.into(),
            verification,
            concreteness,
        }
    }
}

/// Solver verdict for the typed CHC/PDR library boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ChcPdrSolveStatus {
    Proved {
        proof_kind: ChcPdrProofKind,
    },
    /// The solver refuted the encoded VC.
    ///
    /// `witness` is `Some` only when the producer can attach a machine-checked
    /// counterexample bound to the exact obligation/formula/semantic-config
    /// identity together with an exact-encoding concreteness attestation (see
    /// [`ChcPdrRefutationWitness`]). `None` preserves the historical fieldless
    /// behavior: a refutation of the encoded VC with nothing that certifies
    /// the encoding's concreteness, which consumers must not surface as a
    /// program-level failure.
    Refuted {
        witness: Option<Box<ChcPdrRefutationWitness>>,
    },
    Unknown {
        reason: String,
    },
}

/// Typed CHC/PDR solve outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcPdrSolveOutcome {
    pub obligation_id: String,
    pub status: ChcPdrSolveStatus,
    pub stats: ChcPdrStats,
    pub diagnostics: Vec<String>,
}

impl ChcPdrSolveOutcome {
    /// Build a proved outcome for typed CHC/PDR solving.
    #[must_use]
    pub fn proved(
        obligation_id: impl Into<String>,
        proof_kind: ChcPdrProofKind,
        stats: ChcPdrStats,
    ) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            status: ChcPdrSolveStatus::Proved { proof_kind },
            stats,
            diagnostics: Vec::new(),
        }
    }

    /// Build a refuted outcome for typed CHC/PDR solving with no witness.
    ///
    /// This preserves the historical fieldless `Refuted` behavior: the
    /// refutation applies to the encoded VC only and carries nothing that
    /// certifies the encoding's concreteness.
    #[must_use]
    pub fn refuted(obligation_id: impl Into<String>, stats: ChcPdrStats) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            status: ChcPdrSolveStatus::Refuted { witness: None },
            stats,
            diagnostics: Vec::new(),
        }
    }

    /// Build a refuted outcome carrying a machine-checked refutation witness.
    #[must_use]
    pub fn refuted_with_witness(
        obligation_id: impl Into<String>,
        witness: Box<ChcPdrRefutationWitness>,
        stats: ChcPdrStats,
    ) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            status: ChcPdrSolveStatus::Refuted { witness: Some(witness) },
            stats,
            diagnostics: Vec::new(),
        }
    }

    /// Build an inconclusive outcome for typed CHC/PDR solving.
    #[must_use]
    pub fn unknown(
        obligation_id: impl Into<String>,
        reason: impl Into<String>,
        stats: ChcPdrStats,
    ) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            status: ChcPdrSolveStatus::Unknown { reason: reason.into() },
            stats,
            diagnostics: Vec::new(),
        }
    }

    /// Attach a diagnostic line.
    #[must_use]
    pub fn with_diagnostic(mut self, diagnostic: impl Into<String>) -> Self {
        self.diagnostics.push(diagnostic.into());
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chc::{ChcQuery, RelationApp, RelationDecl, Rule, RuleBody};
    use ay_bindings::{Expr, Sort};

    fn typed_obligation_with_error_rule() -> MirChcPdrObligation {
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("entry", vec![Sort::int()]));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.query = ChcQuery::new().with_target("error");
        let x = Expr::var("x", Sort::int());
        vc.add_rule(Rule::new(RuleBody::empty(), RelationApp::new("entry", vec![x.clone()])));
        vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::new("entry", vec![x])), vec![Expr::bool_const(true)]),
            RelationApp::nullary("error"),
        ));
        MirChcPdrObligation::new("obl-1", "crate::harness", MirObligationKind::Assertion, vc)
    }

    #[test]
    fn typed_chc_pdr_obligation_validates_without_normalized_input_string() {
        let obligation = typed_obligation_with_error_rule();

        obligation.validate().expect("typed CHC obligation should validate");
        assert_eq!(obligation.query_target(), "error");
        assert_eq!(obligation.stats(), ChcPdrStats { relation_count: 2, clause_count: 2 });
        assert!(!obligation.is_trivially_safe());
    }

    #[test]
    fn router_placeholder_is_not_proof_input() {
        let placeholder = MirChcPdrObligation::router_placeholder(
            "obl-1",
            "crate::harness",
            MirObligationKind::Assertion,
            typed_obligation_with_error_rule().vc,
        );

        assert_eq!(placeholder.validate(), Err(MirChcPdrObligationError::NotMirDerived));
    }

    #[test]
    fn missing_query_target_fails_closed() {
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::new(RuleBody::empty(), RelationApp::nullary("error")));
        let obligation =
            MirChcPdrObligation::new("obl-1", "crate::harness", MirObligationKind::Assertion, vc);

        assert_eq!(obligation.validate(), Err(MirChcPdrObligationError::MissingQueryTarget));
    }

    #[test]
    fn typed_request_preserves_engine_options() {
        let request = ChcPdrSolveRequest::new(typed_obligation_with_error_rule())
            .with_options(ChcPdrSolveOptions::default().with_engine(ChcPdrEngine::Pdr));

        assert_eq!(request.options.engine, ChcPdrEngine::Pdr);
        assert_eq!(request.obligation.obligation_id, "obl-1");
    }

    fn sample_refutation_witness() -> ChcPdrRefutationWitness {
        ChcPdrRefutationWitness::new(
            "obl-1",
            "aa".repeat(32),
            "bb".repeat(32),
            r#"{"schema":"trust_mc.typed-chc-pdr-counterexample/v1"}"#,
            ChcPdrCexVerification::AyChcReplayVerified { step_count: 3 },
            ChcPdrEncodingConcreteness::ExactEncoding {
                translation_drops: 0,
                havocs: 0,
                undef_diagnostic_havocs: 0,
            },
        )
    }

    #[test]
    fn refuted_outcome_defaults_to_witnessless_refutation() {
        let outcome = ChcPdrSolveOutcome::refuted("obl-1", ChcPdrStats::default());

        assert_eq!(outcome.status, ChcPdrSolveStatus::Refuted { witness: None });
    }

    #[test]
    fn refuted_with_witness_carries_the_bound_witness() {
        let witness = sample_refutation_witness();
        let outcome = ChcPdrSolveOutcome::refuted_with_witness(
            "obl-1",
            Box::new(witness.clone()),
            ChcPdrStats::default(),
        );

        let ChcPdrSolveStatus::Refuted { witness: Some(carried) } = &outcome.status else {
            panic!("witnessed refutation must carry Some witness: {:?}", outcome.status);
        };
        assert_eq!(carried.as_ref(), &witness);
        assert_eq!(carried.obligation_id, "obl-1");
        assert_eq!(carried.encoded_formula_sha256, "aa".repeat(32));
        assert_eq!(carried.semantic_config_sha256, "bb".repeat(32));
    }

    #[test]
    fn exact_encoding_concreteness_requires_all_zero_counts() {
        let exact = ChcPdrEncodingConcreteness::ExactEncoding {
            translation_drops: 0,
            havocs: 0,
            undef_diagnostic_havocs: 0,
        };
        assert!(exact.is_exact_with_zero_counts());

        for (translation_drops, havocs, undef_diagnostic_havocs) in
            [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
        {
            let dirty = ChcPdrEncodingConcreteness::ExactEncoding {
                translation_drops,
                havocs,
                undef_diagnostic_havocs,
            };
            assert!(
                !dirty.is_exact_with_zero_counts(),
                "nonzero counts must not attest exactness: {dirty:?}"
            );
        }
    }
}
