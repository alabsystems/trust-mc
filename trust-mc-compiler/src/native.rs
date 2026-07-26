// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native compiler facade for producing trust_mc verification artifacts.
//!
//! This module is intentionally conservative: it defines the public boundary
//! that tRust-owned inputs can target, supports owned SMT-LIB BMC payloads, and
//! supports a small typed Trust MIR lowering envelope. Unsupported Trust MIR
//! constructs fail closed instead of being erased.

use std::error::Error;
use std::fmt;

const SMTLIB_BMC_PAYLOAD_VERSION: u32 = 1;
const SMTLIB_BMC_PAYLOAD_FORMAT: &str = "trust_mc.native.smtlib-bmc";
const TRUST_MIR_BMC_PAYLOAD_VERSION: u32 = 1;
const TRUST_MIR_BMC_PAYLOAD_FORMAT: &str = "trust_mc.native.trust-mir-bmc";
const TRUST_MIR_SUBSET: &str = "control-flow-v0";

/// Result alias for native compiler facade operations.
pub type NativeEncodeResult<T> = Result<T, NativeEncodeError>;

/// Verification input owned by a native caller.
///
/// These variants avoid exposing rustc arena lifetimes or `TyCtxt` references
/// across the facade. Future implementation work can lower these owned inputs
/// into the existing trust_mc MIR/CHC/BMC encoders.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeInput {
    /// Typed Rust MIR body owned by the native caller.
    #[cfg(feature = "ay")]
    RustMir(NativeRustMirInput),
    /// Typed trust_ir module owned by the native caller.
    #[cfg(feature = "ay")]
    TrustIrModule(NativeTrustIrModuleInput),
    /// A serialized tRust MIR extraction owned by the caller.
    TrustMir { format: String, bytes: Vec<u8> },
    /// An already-materialized textual verification condition.
    ///
    /// This is useful for compatibility probes and tests, but is not proof
    /// grade by itself unless paired with trustworthy provenance.
    SmtLib { script: String },
}

/// Source span preserved at the native compiler boundary.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeSourceSpan {
    pub file: String,
    pub line_start: u32,
    pub column_start: u32,
    pub line_end: u32,
    pub column_end: u32,
}

/// Type layout data carried with MIR/trust_ir locals.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeTypeLayout {
    pub size_bits: Option<u64>,
    pub align_bits: Option<u64>,
    pub abi: Option<String>,
}

/// Stable type reference for compiler-owned inputs.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeTypeRef {
    pub stable_name: String,
    pub layout: Option<NativeTypeLayout>,
}

/// Local/place metadata preserved for diagnostics and counterexample mapping.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeLocal {
    pub index: u32,
    pub name: Option<String>,
    pub ty: NativeTypeRef,
    pub span: Option<NativeSourceSpan>,
}

/// Contract metadata carried by hash, without making text predicates a product boundary.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeContractRef {
    pub id: String,
    pub kind: String,
    pub payload_hash: trust_mc_core::EvidenceHash,
    pub span: Option<NativeSourceSpan>,
}

/// Verification obligation metadata preserved at the compiler boundary.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeObligationRef {
    pub id: String,
    pub kind: String,
    pub span: Option<NativeSourceSpan>,
    pub local_indices: Vec<u32>,
}

/// Typed Rust MIR input for direct compiler integration.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeRustMirInput {
    pub crate_name: String,
    pub def_path: String,
    pub rustc_revision: String,
    pub body_hash: trust_mc_core::EvidenceHash,
    pub locals: Vec<NativeLocal>,
    pub contracts: Vec<NativeContractRef>,
    pub obligations: Vec<NativeObligationRef>,
}

/// Typed trust_ir function input for direct compiler integration.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeTrustIrFunctionInput {
    pub id: String,
    pub name: String,
    pub body_hash: trust_mc_core::EvidenceHash,
    pub span: Option<NativeSourceSpan>,
    pub locals: Vec<NativeLocal>,
    pub obligations: Vec<NativeObligationRef>,
}

/// Typed trust_ir module input for direct compiler integration.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeTrustIrModuleInput {
    pub module_name: String,
    pub trust_ir_version: String,
    pub snapshot_hash: trust_mc_core::EvidenceHash,
    pub functions: Vec<NativeTrustIrFunctionInput>,
    pub contracts: Vec<NativeContractRef>,
}

/// Proof mode requested by the native caller.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum NativeProofMode {
    /// Ordinary bounded model checking.
    #[default]
    Bmc,
    /// BMC over a finite acyclic transition system.
    ///
    /// Producers may use this only when acyclicity makes the BMC unrolling
    /// exhaustive for the analyzed transition system.
    FiniteAcyclicBmc,
    /// Constrained Horn Clause solving.
    Chc,
    /// Property-directed reachability / IC3.
    PdrIc3,
}

impl NativeProofMode {
    /// Returns true when this mode is ordinary depth-bounded evidence.
    pub fn is_bounded(self) -> bool {
        matches!(self, Self::Bmc)
    }

    /// Returns true when BMC is complete because the state graph is finite and acyclic.
    pub fn is_finite_acyclic_bmc(self) -> bool {
        matches!(self, Self::FiniteAcyclicBmc)
    }
}

/// Kind of encoded verification condition emitted by the compiler facade.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeVcKind {
    /// Bounded model checking artifact.
    Bmc,
    /// Constrained Horn Clause artifact.
    Chc,
}

/// Provenance attached to compiler-produced native artifacts.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeProofProvenance {
    /// Proof mode the artifact is intended to support.
    pub proof_mode: NativeProofMode,
    /// BMC depth when the mode is bounded or finite-acyclic BMC.
    pub bmc_depth: Option<u32>,
    /// Whether the producer established an acyclic finite transition system.
    pub finite_acyclic: bool,
    /// Human-readable producer name, for diagnostics and audit logs.
    pub producer: String,
}

impl NativeProofProvenance {
    /// Create provenance for an ordinary bounded BMC artifact.
    pub fn bmc(depth: u32) -> Self {
        Self {
            proof_mode: NativeProofMode::Bmc,
            bmc_depth: Some(depth),
            finite_acyclic: false,
            producer: String::from("trust_mc-compiler-native"),
        }
    }

    /// Create provenance for exhaustive finite acyclic BMC.
    pub fn finite_acyclic_bmc(depth: u32) -> Self {
        Self {
            proof_mode: NativeProofMode::FiniteAcyclicBmc,
            bmc_depth: Some(depth),
            finite_acyclic: true,
            producer: String::from("trust_mc-compiler-native"),
        }
    }

    /// Create provenance for CHC/PDR-style unbounded evidence.
    pub fn unbounded(proof_mode: NativeProofMode) -> Self {
        Self {
            proof_mode,
            bmc_depth: None,
            finite_acyclic: false,
            producer: String::from("trust_mc-compiler-native"),
        }
    }
}

/// Request to encode one obligation into a native trust_mc artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeEncodeRequest {
    /// Stable identifier for the obligation being encoded.
    pub obligation_id: String,
    /// Display name of the function or harness being encoded.
    pub function_name: String,
    /// Caller-owned verification input.
    pub input: NativeInput,
    /// Requested proof mode.
    pub proof_mode: NativeProofMode,
    /// Requested BMC depth for bounded modes.
    pub bmc_depth: Option<u32>,
}

impl NativeEncodeRequest {
    /// Construct a new native encode request.
    pub fn new(
        obligation_id: impl Into<String>,
        function_name: impl Into<String>,
        input: NativeInput,
        proof_mode: NativeProofMode,
    ) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            function_name: function_name.into(),
            input,
            proof_mode,
            bmc_depth: None,
        }
    }

    /// Set the requested BMC depth.
    pub fn with_bmc_depth(mut self, bmc_depth: u32) -> Self {
        self.bmc_depth = Some(bmc_depth);
        self
    }
}

/// Tool identity included in native verifier cache keys.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeToolIdentity {
    pub name: String,
    pub revision: String,
    pub binary_hash: Option<trust_mc_core::EvidenceHash>,
}

/// Snapshot identity for typed frontend IR such as trust_ir.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeSnapshotIdentity {
    pub name: String,
    pub revision: String,
    pub content_hash: trust_mc_core::EvidenceHash,
}

/// Resource limits that affect native verifier results and cache identity.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct NativeResourceLimits {
    pub timeout_ms: Option<u64>,
    pub memory_bytes: Option<u64>,
    pub fuel: Option<u64>,
}

/// Proof options requested through the direct native verifier API.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeVerifierOptions {
    pub proof_mode: NativeProofMode,
    pub bmc_depth: Option<u32>,
    pub extra_options_hash: Option<trust_mc_core::EvidenceHash>,
    pub resource_limits: NativeResourceLimits,
}

/// Native verifier environment included in deterministic cache identity.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeVerifierEnvironment {
    pub trust_mc_revision: String,
    pub ay: NativeToolIdentity,
    pub trust_compiler: NativeToolIdentity,
    pub trust_ir_snapshot: Option<NativeSnapshotIdentity>,
}

/// Direct verifier request prepared from typed compiler-owned data.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeVerifyRequest {
    pub input: NativeInput,
    pub options: NativeVerifierOptions,
    pub environment: NativeVerifierEnvironment,
    pub artifact_dir: Option<String>,
}

/// Prepared native verification metadata before solver execution is wired in.
#[cfg(feature = "ay")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct PreparedNativeVerification {
    pub input_hash: trust_mc_core::EvidenceHash,
    pub obligation_set_hash: trust_mc_core::EvidenceHash,
    pub cache_key: trust_mc_core::EvidenceHash,
    pub manifest: trust_mc_core::ContentAddressedEvidenceManifest,
}

/// Encoded native verification condition returned by the compiler facade.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct EncodedNativeVc {
    /// Obligation identifier copied from the request.
    pub obligation_id: String,
    /// Function or harness name copied from the request.
    pub function_name: String,
    /// Artifact kind.
    pub kind: NativeVcKind,
    /// Opaque artifact payload.
    pub payload: Vec<u8>,
    /// Proof provenance for downstream solver and router decisions.
    pub provenance: NativeProofProvenance,
}

/// Native facade operation that failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeOperation {
    /// Encoding caller-owned input into a trust_mc verification artifact.
    Encode,
}

impl NativeOperation {
    fn as_str(self) -> &'static str {
        match self {
            Self::Encode => "encode",
        }
    }
}

/// Structured unsupported-operation payload.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeEncodeUnsupported {
    /// Operation that is not implemented yet.
    pub operation: NativeOperation,
    /// Stable machine-readable reason.
    pub reason: String,
    /// Human-readable detail.
    pub detail: String,
}

/// Errors returned by the native compiler facade.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeEncodeError {
    /// The API shape exists, but the implementation is not lifted yet.
    Unsupported(NativeEncodeUnsupported),
    /// Request validation failed before encoding.
    InvalidInput { field: String, detail: String },
}

impl fmt::Display for NativeEncodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported(unsupported) => write!(
                f,
                "native {} is unsupported: {} ({})",
                unsupported.operation.as_str(),
                unsupported.reason,
                unsupported.detail
            ),
            Self::InvalidInput { field, detail } => {
                write!(f, "invalid native encode input `{field}`: {detail}")
            }
        }
    }
}

impl Error for NativeEncodeError {}

/// Encode caller-owned input into a native trust_mc verification artifact.
///
/// SMT-LIB BMC input is accepted for compatibility. Trust MIR input is parsed
/// through a narrow typed subset and emitted as a native Trust MIR payload; any
/// unsupported MIR or contract semantics fail closed.
pub fn encode_native(request: NativeEncodeRequest) -> NativeEncodeResult<EncodedNativeVc> {
    validate_encode_request(&request)?;
    match &request.input {
        #[cfg(feature = "ay")]
        NativeInput::RustMir(_) => Err(unsupported_native(
            "rust_mir_encode_not_lifted_yet",
            "typed Rust MIR inputs use the direct native verifier preparation API",
        )),
        #[cfg(feature = "ay")]
        NativeInput::TrustIrModule(_) => Err(unsupported_native(
            "trust_ir_module_encode_not_lifted_yet",
            "typed trust_ir module inputs use the direct native verifier preparation API",
        )),
        NativeInput::SmtLib { script } => encode_smtlib_native(request.clone(), script.clone()),
        NativeInput::TrustMir { format, bytes } => {
            encode_trust_mir_native(request.clone(), format.clone(), bytes.clone())
        }
    }
}

fn validate_encode_request(request: &NativeEncodeRequest) -> NativeEncodeResult<()> {
    if request.obligation_id.trim().is_empty() {
        return Err(NativeEncodeError::InvalidInput {
            field: String::from("obligation_id"),
            detail: String::from("must not be empty"),
        });
    }
    if request.function_name.trim().is_empty() {
        return Err(NativeEncodeError::InvalidInput {
            field: String::from("function_name"),
            detail: String::from("must not be empty"),
        });
    }
    match request.proof_mode {
        NativeProofMode::Bmc | NativeProofMode::FiniteAcyclicBmc => {
            if request.bmc_depth.is_none() {
                return Err(NativeEncodeError::InvalidInput {
                    field: String::from("bmc_depth"),
                    detail: String::from("must be set for BMC proof modes"),
                });
            }
        }
        NativeProofMode::Chc | NativeProofMode::PdrIc3 => {}
    }
    match &request.input {
        NativeInput::TrustMir { format, bytes } => {
            if format.trim().is_empty() {
                return Err(NativeEncodeError::InvalidInput {
                    field: String::from("input.format"),
                    detail: String::from("must not be empty"),
                });
            }
            if bytes.is_empty() {
                return Err(NativeEncodeError::InvalidInput {
                    field: String::from("input.bytes"),
                    detail: String::from("must not be empty"),
                });
            }
        }
        #[cfg(feature = "ay")]
        NativeInput::RustMir(input) => validate_rust_mir_input(input)?,
        #[cfg(feature = "ay")]
        NativeInput::TrustIrModule(input) => validate_trust_ir_module_input(input)?,
        NativeInput::SmtLib { script } => {
            if script.trim().is_empty() {
                return Err(NativeEncodeError::InvalidInput {
                    field: String::from("input.script"),
                    detail: String::from("must not be empty"),
                });
            }
        }
    }
    Ok(())
}

/// Prepare typed native verification metadata without routing through SMT-LIB text.
#[cfg(feature = "ay")]
pub fn prepare_native_verification(
    request: NativeVerifyRequest,
) -> NativeEncodeResult<PreparedNativeVerification> {
    validate_native_verify_request(&request)?;

    let input_hash = native_input_hash(&request.input)?;
    let obligation_set_hash = native_obligation_set_hash(&request.input)?;
    let options_hash = native_options_and_environment_hash(&request.options, &request.environment);
    let resource_hash = native_resource_limits_hash(&request.options.resource_limits);
    let input_kind = native_input_kind_name(&request.input)?;
    let artifact_root = request.artifact_dir.as_deref().unwrap_or("trust_mc://native");

    let solver_binary = request.environment.ay.binary_hash.clone().map(|hash| {
        trust_mc_core::FullVerificationArtifact::new(
            trust_mc_core::FullVerificationArtifactKind::SolverBinary,
            format!("{artifact_root}/solver/ay"),
        )
        .with_digest(hash)
    });

    let manifest = trust_mc_core::ContentAddressedEvidenceManifest::from_parts(
        trust_mc_core::ContentAddressedEvidenceManifestParts {
            input: trust_mc_core::FullVerificationArtifact::new(
                trust_mc_core::FullVerificationArtifactKind::CompilerInput,
                format!("{artifact_root}/input/{input_kind}"),
            )
            .with_digest(input_hash.clone()),
            obligation_set: trust_mc_core::FullVerificationArtifact::new(
                trust_mc_core::FullVerificationArtifactKind::ObligationSet,
                format!("{artifact_root}/obligations"),
            )
            .with_digest(obligation_set_hash.clone()),
            typed_problem: None,
            smt_rendering: None,
            solver_binary,
            solver_transcript: None,
            replay_log: None,
            checked_report: None,
            invariants: Vec::new(),
            counterexamples: Vec::new(),
            options: trust_mc_core::FullVerificationArtifact::new(
                trust_mc_core::FullVerificationArtifactKind::VerificationOptions,
                format!("{artifact_root}/options-and-environment"),
            )
            .with_digest(options_hash),
            resource_limits: trust_mc_core::FullVerificationArtifact::new(
                trust_mc_core::FullVerificationArtifactKind::ResourceLimits,
                format!("{artifact_root}/resource-limits"),
            )
            .with_digest(resource_hash),
        },
    );
    manifest.validate().map_err(|errors| NativeEncodeError::InvalidInput {
        field: String::from("manifest"),
        detail: errors.join("; "),
    })?;

    Ok(PreparedNativeVerification {
        input_hash,
        obligation_set_hash,
        cache_key: manifest.cache_key.clone(),
        manifest,
    })
}

#[cfg(feature = "ay")]
fn validate_native_verify_request(request: &NativeVerifyRequest) -> NativeEncodeResult<()> {
    match &request.input {
        NativeInput::RustMir(input) => validate_rust_mir_input(input)?,
        NativeInput::TrustIrModule(input) => validate_trust_ir_module_input(input)?,
        NativeInput::TrustMir { .. } | NativeInput::SmtLib { .. } => {
            return Err(unsupported_native(
                "typed_native_input_required",
                "direct native verification requires RustMir or TrustIrModule input",
            ));
        }
    }

    if request.environment.trust_mc_revision.trim().is_empty() {
        return Err(NativeEncodeError::InvalidInput {
            field: String::from("environment.trust_mc_revision"),
            detail: String::from("must not be empty"),
        });
    }
    validate_tool_identity("environment.ay", &request.environment.ay)?;
    validate_tool_identity("environment.trust_compiler", &request.environment.trust_compiler)?;
    if let Some(snapshot) = &request.environment.trust_ir_snapshot {
        validate_snapshot_identity("environment.trust_ir_snapshot", snapshot)?;
    }
    match request.options.proof_mode {
        NativeProofMode::Bmc | NativeProofMode::FiniteAcyclicBmc => {
            if request.options.bmc_depth.is_none() {
                return Err(NativeEncodeError::InvalidInput {
                    field: String::from("options.bmc_depth"),
                    detail: String::from("must be set for BMC proof modes"),
                });
            }
        }
        NativeProofMode::Chc | NativeProofMode::PdrIc3 => {}
    }
    if let Some(hash) = &request.options.extra_options_hash {
        validate_evidence_hash("options.extra_options_hash", hash)?;
    }
    Ok(())
}

#[cfg(feature = "ay")]
fn validate_rust_mir_input(input: &NativeRustMirInput) -> NativeEncodeResult<()> {
    if input.crate_name.trim().is_empty() {
        return invalid_native_field("input.crate_name", "must not be empty");
    }
    if input.def_path.trim().is_empty() {
        return invalid_native_field("input.def_path", "must not be empty");
    }
    if input.rustc_revision.trim().is_empty() {
        return invalid_native_field("input.rustc_revision", "must not be empty");
    }
    validate_evidence_hash("input.body_hash", &input.body_hash)?;
    validate_locals("input.locals", &input.locals)?;
    validate_contracts("input.contracts", &input.contracts)?;
    validate_obligations("input.obligations", &input.obligations)?;
    Ok(())
}

#[cfg(feature = "ay")]
fn validate_trust_ir_module_input(input: &NativeTrustIrModuleInput) -> NativeEncodeResult<()> {
    if input.module_name.trim().is_empty() {
        return invalid_native_field("input.module_name", "must not be empty");
    }
    if input.trust_ir_version.trim().is_empty() {
        return invalid_native_field("input.trust_ir_version", "must not be empty");
    }
    validate_evidence_hash("input.snapshot_hash", &input.snapshot_hash)?;
    if input.functions.is_empty() {
        return invalid_native_field("input.functions", "must contain at least one function");
    }
    for (idx, function) in input.functions.iter().enumerate() {
        let prefix = format!("input.functions[{idx}]");
        if function.id.trim().is_empty() {
            return invalid_native_field(format!("{prefix}.id"), "must not be empty");
        }
        if function.name.trim().is_empty() {
            return invalid_native_field(format!("{prefix}.name"), "must not be empty");
        }
        validate_evidence_hash(format!("{prefix}.body_hash"), &function.body_hash)?;
        validate_locals(format!("{prefix}.locals"), &function.locals)?;
        validate_obligations(format!("{prefix}.obligations"), &function.obligations)?;
    }
    validate_contracts("input.contracts", &input.contracts)?;
    Ok(())
}

#[cfg(feature = "ay")]
fn invalid_native_field<T>(
    field: impl Into<String>,
    detail: impl Into<String>,
) -> NativeEncodeResult<T> {
    Err(NativeEncodeError::InvalidInput { field: field.into(), detail: detail.into() })
}

#[cfg(feature = "ay")]
fn validate_tool_identity(prefix: &str, tool: &NativeToolIdentity) -> NativeEncodeResult<()> {
    if tool.name.trim().is_empty() {
        return invalid_native_field(format!("{prefix}.name"), "must not be empty");
    }
    if tool.revision.trim().is_empty() {
        return invalid_native_field(format!("{prefix}.revision"), "must not be empty");
    }
    if let Some(hash) = &tool.binary_hash {
        validate_evidence_hash(format!("{prefix}.binary_hash"), hash)?;
    }
    Ok(())
}

#[cfg(feature = "ay")]
fn validate_snapshot_identity(
    prefix: &str,
    snapshot: &NativeSnapshotIdentity,
) -> NativeEncodeResult<()> {
    if snapshot.name.trim().is_empty() {
        return invalid_native_field(format!("{prefix}.name"), "must not be empty");
    }
    if snapshot.revision.trim().is_empty() {
        return invalid_native_field(format!("{prefix}.revision"), "must not be empty");
    }
    validate_evidence_hash(format!("{prefix}.content_hash"), &snapshot.content_hash)
}

#[cfg(feature = "ay")]
fn validate_locals(prefix: impl AsRef<str>, locals: &[NativeLocal]) -> NativeEncodeResult<()> {
    for (idx, local) in locals.iter().enumerate() {
        let field = format!("{}[{idx}]", prefix.as_ref());
        if local.ty.stable_name.trim().is_empty() {
            return invalid_native_field(format!("{field}.ty.stable_name"), "must not be empty");
        }
    }
    Ok(())
}

#[cfg(feature = "ay")]
fn validate_contracts(
    prefix: impl AsRef<str>,
    contracts: &[NativeContractRef],
) -> NativeEncodeResult<()> {
    for (idx, contract) in contracts.iter().enumerate() {
        let field = format!("{}[{idx}]", prefix.as_ref());
        if contract.id.trim().is_empty() {
            return invalid_native_field(format!("{field}.id"), "must not be empty");
        }
        if contract.kind.trim().is_empty() {
            return invalid_native_field(format!("{field}.kind"), "must not be empty");
        }
        validate_evidence_hash(format!("{field}.payload_hash"), &contract.payload_hash)?;
    }
    Ok(())
}

#[cfg(feature = "ay")]
fn validate_obligations(
    prefix: impl AsRef<str>,
    obligations: &[NativeObligationRef],
) -> NativeEncodeResult<()> {
    if obligations.is_empty() {
        return invalid_native_field(prefix.as_ref(), "must contain at least one obligation");
    }
    for (idx, obligation) in obligations.iter().enumerate() {
        let field = format!("{}[{idx}]", prefix.as_ref());
        if obligation.id.trim().is_empty() {
            return invalid_native_field(format!("{field}.id"), "must not be empty");
        }
        if obligation.kind.trim().is_empty() {
            return invalid_native_field(format!("{field}.kind"), "must not be empty");
        }
    }
    Ok(())
}

#[cfg(feature = "ay")]
fn validate_evidence_hash(
    field: impl Into<String>,
    hash: &trust_mc_core::EvidenceHash,
) -> NativeEncodeResult<()> {
    let field = field.into();
    if hash.algorithm != "sha256" {
        return invalid_native_field(field, "hash algorithm must be sha256");
    }
    if hash.value.len() != 64
        || !hash.value.bytes().all(|byte| byte.is_ascii_hexdigit())
        || hash.value.bytes().any(|byte| byte.is_ascii_uppercase())
    {
        return invalid_native_field(field, "hash value must be lowercase SHA-256 hex");
    }
    Ok(())
}

#[cfg(feature = "ay")]
fn native_input_kind_name(input: &NativeInput) -> NativeEncodeResult<&'static str> {
    match input {
        NativeInput::RustMir(_) => Ok("rust-mir"),
        NativeInput::TrustIrModule(_) => Ok("trust_ir-module"),
        NativeInput::TrustMir { .. } | NativeInput::SmtLib { .. } => Err(unsupported_native(
            "typed_native_input_required",
            "direct native verification requires RustMir or TrustIrModule input",
        )),
    }
}

#[cfg(feature = "ay")]
fn native_input_hash(input: &NativeInput) -> NativeEncodeResult<trust_mc_core::EvidenceHash> {
    let mut payload = String::new();
    match input {
        NativeInput::RustMir(rust_mir) => {
            push_native_component(&mut payload, "kind", "rust_mir");
            push_native_component(&mut payload, "crate_name", &rust_mir.crate_name);
            push_native_component(&mut payload, "def_path", &rust_mir.def_path);
            push_native_component(&mut payload, "rustc_revision", &rust_mir.rustc_revision);
            push_native_hash(&mut payload, "body_hash", &rust_mir.body_hash);
            push_native_locals(&mut payload, "locals", &rust_mir.locals);
            push_native_contracts(&mut payload, "contracts", &rust_mir.contracts);
            push_native_obligations(&mut payload, "obligations", &rust_mir.obligations);
        }
        NativeInput::TrustIrModule(module) => {
            push_native_component(&mut payload, "kind", "trust_ir_module");
            push_native_component(&mut payload, "module_name", &module.module_name);
            push_native_component(&mut payload, "trust_ir_version", &module.trust_ir_version);
            push_native_hash(&mut payload, "snapshot_hash", &module.snapshot_hash);
            push_native_component(
                &mut payload,
                "functions.len",
                &module.functions.len().to_string(),
            );
            for (idx, function) in module.functions.iter().enumerate() {
                let prefix = format!("functions.{idx}");
                push_native_component(&mut payload, &format!("{prefix}.id"), &function.id);
                push_native_component(&mut payload, &format!("{prefix}.name"), &function.name);
                push_native_hash(&mut payload, &format!("{prefix}.body_hash"), &function.body_hash);
                push_native_span(&mut payload, &format!("{prefix}.span"), function.span.as_ref());
                push_native_locals(&mut payload, &format!("{prefix}.locals"), &function.locals);
                push_native_obligations(
                    &mut payload,
                    &format!("{prefix}.obligations"),
                    &function.obligations,
                );
            }
            push_native_contracts(&mut payload, "contracts", &module.contracts);
        }
        NativeInput::TrustMir { .. } | NativeInput::SmtLib { .. } => {
            return Err(unsupported_native(
                "typed_native_input_required",
                "direct native verification requires RustMir or TrustIrModule input",
            ));
        }
    }
    Ok(trust_mc_core::EvidenceHash::sha256_bytes(payload.as_bytes()))
}

#[cfg(feature = "ay")]
fn native_obligation_set_hash(
    input: &NativeInput,
) -> NativeEncodeResult<trust_mc_core::EvidenceHash> {
    let mut obligations = Vec::new();
    match input {
        NativeInput::RustMir(rust_mir) => {
            obligations.extend(rust_mir.obligations.iter());
        }
        NativeInput::TrustIrModule(module) => {
            for function in &module.functions {
                obligations.extend(function.obligations.iter());
            }
        }
        NativeInput::TrustMir { .. } | NativeInput::SmtLib { .. } => {
            return Err(unsupported_native(
                "typed_native_input_required",
                "direct native verification requires RustMir or TrustIrModule input",
            ));
        }
    }
    obligations.sort_by(|lhs, rhs| lhs.id.cmp(&rhs.id).then(lhs.kind.cmp(&rhs.kind)));
    let mut payload = String::new();
    push_native_component(&mut payload, "obligations.len", &obligations.len().to_string());
    for (idx, obligation) in obligations.into_iter().enumerate() {
        push_native_obligation(&mut payload, &format!("obligations.{idx}"), obligation);
    }
    Ok(trust_mc_core::EvidenceHash::sha256_bytes(payload.as_bytes()))
}

#[cfg(feature = "ay")]
fn native_options_and_environment_hash(
    options: &NativeVerifierOptions,
    environment: &NativeVerifierEnvironment,
) -> trust_mc_core::EvidenceHash {
    let mut payload = String::new();
    push_native_component(&mut payload, "proof_mode", proof_mode_payload_name(options.proof_mode));
    push_native_optional_u32(&mut payload, "bmc_depth", options.bmc_depth);
    push_native_optional_hash(
        &mut payload,
        "extra_options_hash",
        options.extra_options_hash.as_ref(),
    );
    push_native_component(&mut payload, "trust_mc_revision", &environment.trust_mc_revision);
    push_native_tool(&mut payload, "ay", &environment.ay);
    push_native_tool(&mut payload, "trust_compiler", &environment.trust_compiler);
    if let Some(snapshot) = &environment.trust_ir_snapshot {
        push_native_component(&mut payload, "trust_ir_snapshot", "present");
        push_native_component(&mut payload, "trust_ir_snapshot.name", &snapshot.name);
        push_native_component(&mut payload, "trust_ir_snapshot.revision", &snapshot.revision);
        push_native_hash(&mut payload, "trust_ir_snapshot.content_hash", &snapshot.content_hash);
    } else {
        push_native_component(&mut payload, "trust_ir_snapshot", "absent");
    }
    trust_mc_core::EvidenceHash::sha256_bytes(payload.as_bytes())
}

#[cfg(feature = "ay")]
fn native_resource_limits_hash(limits: &NativeResourceLimits) -> trust_mc_core::EvidenceHash {
    let mut payload = String::new();
    push_native_optional_u64(&mut payload, "timeout_ms", limits.timeout_ms);
    push_native_optional_u64(&mut payload, "memory_bytes", limits.memory_bytes);
    push_native_optional_u64(&mut payload, "fuel", limits.fuel);
    trust_mc_core::EvidenceHash::sha256_bytes(payload.as_bytes())
}

#[cfg(feature = "ay")]
fn push_native_component(payload: &mut String, key: &str, value: &str) {
    payload.push_str(&key.len().to_string());
    payload.push(':');
    payload.push_str(key);
    payload.push('=');
    payload.push_str(&value.len().to_string());
    payload.push(':');
    payload.push_str(value);
    payload.push(';');
}

#[cfg(feature = "ay")]
fn push_native_hash(payload: &mut String, key: &str, hash: &trust_mc_core::EvidenceHash) {
    push_native_component(payload, &format!("{key}.algorithm"), &hash.algorithm);
    push_native_component(payload, &format!("{key}.value"), &hash.value);
}

#[cfg(feature = "ay")]
fn push_native_optional_hash(
    payload: &mut String,
    key: &str,
    hash: Option<&trust_mc_core::EvidenceHash>,
) {
    if let Some(hash) = hash {
        push_native_component(payload, key, "present");
        push_native_hash(payload, key, hash);
    } else {
        push_native_component(payload, key, "absent");
    }
}

#[cfg(feature = "ay")]
fn push_native_optional_u32(payload: &mut String, key: &str, value: Option<u32>) {
    match value {
        Some(value) => push_native_component(payload, key, &value.to_string()),
        None => push_native_component(payload, key, "absent"),
    }
}

#[cfg(feature = "ay")]
fn push_native_optional_u64(payload: &mut String, key: &str, value: Option<u64>) {
    match value {
        Some(value) => push_native_component(payload, key, &value.to_string()),
        None => push_native_component(payload, key, "absent"),
    }
}

#[cfg(feature = "ay")]
fn push_native_tool(payload: &mut String, prefix: &str, tool: &NativeToolIdentity) {
    push_native_component(payload, &format!("{prefix}.name"), &tool.name);
    push_native_component(payload, &format!("{prefix}.revision"), &tool.revision);
    push_native_optional_hash(payload, &format!("{prefix}.binary_hash"), tool.binary_hash.as_ref());
}

#[cfg(feature = "ay")]
fn push_native_span(payload: &mut String, prefix: &str, span: Option<&NativeSourceSpan>) {
    if let Some(span) = span {
        push_native_component(payload, prefix, "present");
        push_native_component(payload, &format!("{prefix}.file"), &span.file);
        push_native_component(
            payload,
            &format!("{prefix}.line_start"),
            &span.line_start.to_string(),
        );
        push_native_component(
            payload,
            &format!("{prefix}.column_start"),
            &span.column_start.to_string(),
        );
        push_native_component(payload, &format!("{prefix}.line_end"), &span.line_end.to_string());
        push_native_component(
            payload,
            &format!("{prefix}.column_end"),
            &span.column_end.to_string(),
        );
    } else {
        push_native_component(payload, prefix, "absent");
    }
}

#[cfg(feature = "ay")]
fn push_native_type(payload: &mut String, prefix: &str, ty: &NativeTypeRef) {
    push_native_component(payload, &format!("{prefix}.stable_name"), &ty.stable_name);
    if let Some(layout) = &ty.layout {
        push_native_component(payload, &format!("{prefix}.layout"), "present");
        push_native_optional_u64(payload, &format!("{prefix}.layout.size_bits"), layout.size_bits);
        push_native_optional_u64(
            payload,
            &format!("{prefix}.layout.align_bits"),
            layout.align_bits,
        );
        if let Some(abi) = &layout.abi {
            push_native_component(payload, &format!("{prefix}.layout.abi"), abi);
        } else {
            push_native_component(payload, &format!("{prefix}.layout.abi"), "absent");
        }
    } else {
        push_native_component(payload, &format!("{prefix}.layout"), "absent");
    }
}

#[cfg(feature = "ay")]
fn push_native_locals(payload: &mut String, prefix: &str, locals: &[NativeLocal]) {
    push_native_component(payload, &format!("{prefix}.len"), &locals.len().to_string());
    for (idx, local) in locals.iter().enumerate() {
        let local_prefix = format!("{prefix}.{idx}");
        push_native_component(payload, &format!("{local_prefix}.index"), &local.index.to_string());
        if let Some(name) = &local.name {
            push_native_component(payload, &format!("{local_prefix}.name"), name);
        } else {
            push_native_component(payload, &format!("{local_prefix}.name"), "absent");
        }
        push_native_type(payload, &format!("{local_prefix}.ty"), &local.ty);
        push_native_span(payload, &format!("{local_prefix}.span"), local.span.as_ref());
    }
}

#[cfg(feature = "ay")]
fn push_native_contracts(payload: &mut String, prefix: &str, contracts: &[NativeContractRef]) {
    push_native_component(payload, &format!("{prefix}.len"), &contracts.len().to_string());
    for (idx, contract) in contracts.iter().enumerate() {
        let contract_prefix = format!("{prefix}.{idx}");
        push_native_component(payload, &format!("{contract_prefix}.id"), &contract.id);
        push_native_component(payload, &format!("{contract_prefix}.kind"), &contract.kind);
        push_native_hash(
            payload,
            &format!("{contract_prefix}.payload_hash"),
            &contract.payload_hash,
        );
        push_native_span(payload, &format!("{contract_prefix}.span"), contract.span.as_ref());
    }
}

#[cfg(feature = "ay")]
fn push_native_obligations(
    payload: &mut String,
    prefix: &str,
    obligations: &[NativeObligationRef],
) {
    push_native_component(payload, &format!("{prefix}.len"), &obligations.len().to_string());
    for (idx, obligation) in obligations.iter().enumerate() {
        push_native_obligation(payload, &format!("{prefix}.{idx}"), obligation);
    }
}

#[cfg(feature = "ay")]
fn push_native_obligation(payload: &mut String, prefix: &str, obligation: &NativeObligationRef) {
    push_native_component(payload, &format!("{prefix}.id"), &obligation.id);
    push_native_component(payload, &format!("{prefix}.kind"), &obligation.kind);
    push_native_component(
        payload,
        &format!("{prefix}.local_indices.len"),
        &obligation.local_indices.len().to_string(),
    );
    for (idx, local) in obligation.local_indices.iter().enumerate() {
        push_native_component(
            payload,
            &format!("{prefix}.local_indices.{idx}"),
            &local.to_string(),
        );
    }
    push_native_span(payload, &format!("{prefix}.span"), obligation.span.as_ref());
}

fn encode_smtlib_native(
    request: NativeEncodeRequest,
    script: String,
) -> NativeEncodeResult<EncodedNativeVc> {
    let (kind, provenance) = match request.proof_mode {
        NativeProofMode::Bmc => {
            let depth = request.bmc_depth.expect("validated BMC depth");
            (NativeVcKind::Bmc, NativeProofProvenance::bmc(depth))
        }
        NativeProofMode::FiniteAcyclicBmc => {
            let depth = request.bmc_depth.expect("validated finite acyclic BMC depth");
            (NativeVcKind::Bmc, NativeProofProvenance::finite_acyclic_bmc(depth))
        }
        NativeProofMode::Chc | NativeProofMode::PdrIc3 => {
            return Err(NativeEncodeError::Unsupported(NativeEncodeUnsupported {
                operation: NativeOperation::Encode,
                reason: String::from("smtlib_non_bmc_not_native_yet"),
                detail: String::from(
                    "the native SMT-LIB path currently supports only BMC proof modes",
                ),
            }));
        }
    };

    let payload = serde_json::to_vec(&serde_json::json!({
        "format": SMTLIB_BMC_PAYLOAD_FORMAT,
        "version": SMTLIB_BMC_PAYLOAD_VERSION,
        "kind": "bmc",
        "obligation_id": request.obligation_id,
        "function_name": request.function_name,
        "script": script,
        "provenance": {
            "proof_mode": proof_mode_payload_name(provenance.proof_mode),
            "bmc_depth": provenance.bmc_depth,
            "finite_acyclic": provenance.finite_acyclic,
            "producer": provenance.producer,
        },
    }))
    .map_err(|err| NativeEncodeError::InvalidInput {
        field: String::from("input.script"),
        detail: format!("failed to serialize native SMT-LIB payload: {err}"),
    })?;

    let envelope: serde_json::Value =
        serde_json::from_slice(&payload).expect("payload serialized from JSON value");
    let obligation_id = envelope["obligation_id"].as_str().unwrap_or_default().to_owned();
    let function_name = envelope["function_name"].as_str().unwrap_or_default().to_owned();
    let provenance = decode_payload_provenance(&envelope)
        .expect("payload serialized from native proof provenance");

    Ok(EncodedNativeVc { obligation_id, function_name, kind, payload, provenance })
}

fn encode_trust_mir_native(
    request: NativeEncodeRequest,
    input_format: String,
    bytes: Vec<u8>,
) -> NativeEncodeResult<EncodedNativeVc> {
    let (kind, provenance) = match request.proof_mode {
        NativeProofMode::Bmc => {
            let depth = request.bmc_depth.expect("validated BMC depth");
            (NativeVcKind::Bmc, NativeProofProvenance::bmc(depth))
        }
        NativeProofMode::FiniteAcyclicBmc => {
            let depth = request.bmc_depth.expect("validated finite acyclic BMC depth");
            (NativeVcKind::Bmc, NativeProofProvenance::finite_acyclic_bmc(depth))
        }
        NativeProofMode::Chc | NativeProofMode::PdrIc3 => {
            return Err(unsupported_native(
                "trust_mir_non_bmc_not_native_yet",
                "the native Trust MIR subset currently emits only BMC artifacts",
            ));
        }
    };

    let trust_mir = parse_supported_trust_mir(&input_format, &bytes)?;
    let payload = serde_json::to_vec(&serde_json::json!({
        "format": TRUST_MIR_BMC_PAYLOAD_FORMAT,
        "version": TRUST_MIR_BMC_PAYLOAD_VERSION,
        "kind": "bmc",
        "obligation_id": request.obligation_id,
        "function_name": request.function_name,
        "trust_mir": trust_mir.to_json(),
        "lowering": {
            "subset": TRUST_MIR_SUBSET,
            "unsupported_semantics": [
                "non-empty Trust contracts/spec predicates",
                "assignments and rvalues",
                "assert, call, switch, drop, and unwind terminators",
                "references, raw pointers, tuples, arrays, ADTs, floats, and symbolic values",
            ],
        },
        "provenance": {
            "proof_mode": proof_mode_payload_name(provenance.proof_mode),
            "bmc_depth": provenance.bmc_depth,
            "finite_acyclic": provenance.finite_acyclic,
            "producer": provenance.producer,
        },
    }))
    .map_err(|err| NativeEncodeError::InvalidInput {
        field: String::from("input.bytes"),
        detail: format!("failed to serialize native Trust MIR payload: {err}"),
    })?;

    let envelope: serde_json::Value =
        serde_json::from_slice(&payload).expect("payload serialized from JSON value");
    let obligation_id = envelope["obligation_id"].as_str().unwrap_or_default().to_owned();
    let function_name = envelope["function_name"].as_str().unwrap_or_default().to_owned();
    let provenance = decode_payload_provenance(&envelope)
        .expect("payload serialized from native proof provenance");

    Ok(EncodedNativeVc { obligation_id, function_name, kind, payload, provenance })
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SupportedTrustMir {
    input_format: String,
    name: String,
    def_path: String,
    body: SupportedTrustMirBody,
}

impl SupportedTrustMir {
    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "input_format": self.input_format,
            "name": self.name,
            "def_path": self.def_path,
            "body": self.body.to_json(),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SupportedTrustMirBody {
    locals: Vec<SupportedTrustMirLocal>,
    blocks: Vec<SupportedTrustMirBlock>,
    arg_count: usize,
    return_ty: SupportedTrustMirTy,
}

impl SupportedTrustMirBody {
    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "locals": self.locals.iter().map(SupportedTrustMirLocal::to_json).collect::<Vec<_>>(),
            "blocks": self.blocks.iter().map(SupportedTrustMirBlock::to_json).collect::<Vec<_>>(),
            "arg_count": self.arg_count,
            "return_ty": self.return_ty.to_json(),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SupportedTrustMirLocal {
    index: usize,
    ty: SupportedTrustMirTy,
    name: Option<String>,
}

impl SupportedTrustMirLocal {
    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "index": self.index,
            "ty": self.ty.to_json(),
            "name": self.name,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SupportedTrustMirTy {
    Bool,
    Int { width: u32, signed: bool },
    Unit,
    Never,
}

impl SupportedTrustMirTy {
    fn to_json(&self) -> serde_json::Value {
        match self {
            Self::Bool => serde_json::json!("Bool"),
            Self::Int { width, signed } => {
                serde_json::json!({ "Int": { "width": width, "signed": signed } })
            }
            Self::Unit => serde_json::json!("Unit"),
            Self::Never => serde_json::json!("Never"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SupportedTrustMirBlock {
    id: usize,
    stmts: Vec<SupportedTrustMirStatement>,
    terminator: SupportedTrustMirTerminator,
}

impl SupportedTrustMirBlock {
    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "id": self.id,
            "stmts": self.stmts.iter().map(SupportedTrustMirStatement::to_json).collect::<Vec<_>>(),
            "terminator": self.terminator.to_json(),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SupportedTrustMirStatement {
    StorageLive(usize),
    StorageDead(usize),
    Nop,
}

impl SupportedTrustMirStatement {
    fn to_json(&self) -> serde_json::Value {
        match self {
            Self::StorageLive(local) => serde_json::json!({ "StorageLive": local }),
            Self::StorageDead(local) => serde_json::json!({ "StorageDead": local }),
            Self::Nop => serde_json::json!("Nop"),
        }
    }

    fn local(&self) -> Option<usize> {
        match self {
            Self::StorageLive(local) | Self::StorageDead(local) => Some(*local),
            Self::Nop => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SupportedTrustMirTerminator {
    Return,
    Goto(usize),
    Unreachable,
}

impl SupportedTrustMirTerminator {
    fn to_json(&self) -> serde_json::Value {
        match self {
            Self::Return => serde_json::json!("Return"),
            Self::Goto(target) => serde_json::json!({ "Goto": target }),
            Self::Unreachable => serde_json::json!("Unreachable"),
        }
    }

    fn target(&self) -> Option<usize> {
        match self {
            Self::Goto(target) => Some(*target),
            Self::Return | Self::Unreachable => None,
        }
    }
}

fn parse_supported_trust_mir(
    input_format: &str,
    bytes: &[u8],
) -> NativeEncodeResult<SupportedTrustMir> {
    let input_format = input_format.trim();
    if !matches!(input_format, "trust-mir-v0" | "trust-types.verifiable-function.v0") {
        return Err(unsupported_native(
            "trust_mir_format_unsupported",
            format!("unsupported Trust MIR format `{input_format}`"),
        ));
    }

    let value: serde_json::Value =
        serde_json::from_slice(bytes).map_err(|err| NativeEncodeError::InvalidInput {
            field: String::from("input.bytes"),
            detail: format!("Trust MIR payload must be JSON: {err}"),
        })?;
    let object = value.as_object().ok_or_else(|| NativeEncodeError::InvalidInput {
        field: String::from("input.bytes"),
        detail: String::from("Trust MIR payload must be a JSON object"),
    })?;

    reject_non_empty_top_level_contracts(object)?;

    let name = required_string(object, "name")?;
    let def_path = required_string(object, "def_path")?;
    let body = parse_body(required_object(object, "body")?)?;

    Ok(SupportedTrustMir { input_format: input_format.to_owned(), name, def_path, body })
}

fn reject_non_empty_top_level_contracts(
    object: &serde_json::Map<String, serde_json::Value>,
) -> NativeEncodeResult<()> {
    for field in ["contracts", "preconditions", "postconditions"] {
        if let Some(value) = object.get(field)
            && value.as_array().is_some_and(|items| !items.is_empty())
        {
            return Err(unsupported_native(
                "trust_mir_contracts_not_lowered_yet",
                format!("non-empty `{field}` requires first-class Trust contract lowering"),
            ));
        }
    }

    if let Some(spec) = object.get("spec").and_then(serde_json::Value::as_object) {
        for field in ["requires", "ensures", "invariants"] {
            if spec
                .get(field)
                .and_then(serde_json::Value::as_array)
                .is_some_and(|items| !items.is_empty())
            {
                return Err(unsupported_native(
                    "trust_mir_contracts_not_lowered_yet",
                    format!(
                        "non-empty `spec.{field}` requires first-class Trust contract lowering"
                    ),
                ));
            }
        }
    }

    Ok(())
}

fn parse_body(
    object: &serde_json::Map<String, serde_json::Value>,
) -> NativeEncodeResult<SupportedTrustMirBody> {
    let locals = required_array(object, "locals")?
        .iter()
        .map(parse_local)
        .collect::<NativeEncodeResult<Vec<_>>>()?;
    let blocks = required_array(object, "blocks")?
        .iter()
        .map(parse_block)
        .collect::<NativeEncodeResult<Vec<_>>>()?;
    let arg_count = required_usize(object, "arg_count")?;
    if arg_count > locals.len().saturating_sub(1) {
        return Err(NativeEncodeError::InvalidInput {
            field: String::from("body.arg_count"),
            detail: format!(
                "arg_count {arg_count} exceeds non-return local count {}",
                locals.len().saturating_sub(1)
            ),
        });
    }
    for (expected, local) in locals.iter().enumerate() {
        if local.index != expected {
            return Err(NativeEncodeError::InvalidInput {
                field: String::from("body.locals"),
                detail: format!("local indices must be contiguous from 0; found _{}", local.index),
            });
        }
    }
    if blocks.is_empty() {
        return Err(NativeEncodeError::InvalidInput {
            field: String::from("body.blocks"),
            detail: String::from("must contain at least one block"),
        });
    }
    for (expected, block) in blocks.iter().enumerate() {
        if block.id != expected {
            return Err(NativeEncodeError::InvalidInput {
                field: String::from("body.blocks"),
                detail: format!("block ids must be contiguous from 0; found bb{}", block.id),
            });
        }
        if let Some(target) = block.terminator.target()
            && target >= blocks.len()
        {
            return Err(NativeEncodeError::InvalidInput {
                field: String::from("body.blocks.terminator"),
                detail: format!("bb{} targets missing bb{target}", block.id),
            });
        }
        for stmt in &block.stmts {
            if let Some(local) = stmt.local()
                && local >= locals.len()
            {
                return Err(NativeEncodeError::InvalidInput {
                    field: String::from("body.blocks.stmts"),
                    detail: format!("bb{} references missing local _{local}", block.id),
                });
            }
        }
    }

    Ok(SupportedTrustMirBody {
        locals,
        blocks,
        arg_count,
        return_ty: parse_ty(required_value(object, "return_ty")?)?,
    })
}

fn parse_local(value: &serde_json::Value) -> NativeEncodeResult<SupportedTrustMirLocal> {
    let object = value.as_object().ok_or_else(|| NativeEncodeError::InvalidInput {
        field: String::from("body.locals"),
        detail: String::from("local declaration must be an object"),
    })?;
    let name = match object.get("name") {
        None | Some(serde_json::Value::Null) => None,
        Some(value) => Some(
            value
                .as_str()
                .ok_or_else(|| NativeEncodeError::InvalidInput {
                    field: String::from("body.locals.name"),
                    detail: String::from("local name must be a string or null"),
                })?
                .to_owned(),
        ),
    };
    Ok(SupportedTrustMirLocal {
        index: required_usize(object, "index")?,
        ty: parse_ty(required_value(object, "ty")?)?,
        name,
    })
}

fn parse_block(value: &serde_json::Value) -> NativeEncodeResult<SupportedTrustMirBlock> {
    let object = value.as_object().ok_or_else(|| NativeEncodeError::InvalidInput {
        field: String::from("body.blocks"),
        detail: String::from("block must be an object"),
    })?;
    let stmts = required_array(object, "stmts")?
        .iter()
        .map(parse_statement)
        .collect::<NativeEncodeResult<Vec<_>>>()?;
    Ok(SupportedTrustMirBlock {
        id: required_usize(object, "id")?,
        stmts,
        terminator: parse_terminator(required_value(object, "terminator")?)?,
    })
}

fn parse_ty(value: &serde_json::Value) -> NativeEncodeResult<SupportedTrustMirTy> {
    if let Some(name) = value.as_str() {
        return match name {
            "Bool" => Ok(SupportedTrustMirTy::Bool),
            "Unit" => Ok(SupportedTrustMirTy::Unit),
            "Never" => Ok(SupportedTrustMirTy::Never),
            other => Err(unsupported_native(
                "trust_mir_type_unsupported",
                format!("unsupported scalar/string type `{other}`"),
            )),
        };
    }

    let object = value.as_object().ok_or_else(|| NativeEncodeError::InvalidInput {
        field: String::from("type"),
        detail: String::from("type must be a string or single-key object"),
    })?;
    if object.len() != 1 {
        return Err(NativeEncodeError::InvalidInput {
            field: String::from("type"),
            detail: String::from("type object must contain exactly one variant"),
        });
    }
    let (variant, payload) = object.iter().next().expect("checked object length");
    match variant.as_str() {
        "Int" => {
            let payload = payload.as_object().ok_or_else(|| NativeEncodeError::InvalidInput {
                field: String::from("type.Int"),
                detail: String::from("Int type payload must be an object"),
            })?;
            let width = required_u32(payload, "width")?;
            if !matches!(width, 8 | 16 | 32 | 64 | 128) {
                return Err(unsupported_native(
                    "trust_mir_type_unsupported",
                    format!("unsupported integer width {width}"),
                ));
            }
            Ok(SupportedTrustMirTy::Int { width, signed: required_bool(payload, "signed")? })
        }
        other => Err(unsupported_native(
            "trust_mir_type_unsupported",
            format!("type `{other}` is outside the native Trust MIR subset"),
        )),
    }
}

fn parse_statement(value: &serde_json::Value) -> NativeEncodeResult<SupportedTrustMirStatement> {
    if let Some(name) = value.as_str() {
        return match name {
            "Nop" => Ok(SupportedTrustMirStatement::Nop),
            other => Err(unsupported_native(
                "trust_mir_statement_unsupported",
                format!("statement `{other}` is outside the native Trust MIR subset"),
            )),
        };
    }

    let object = value.as_object().ok_or_else(|| NativeEncodeError::InvalidInput {
        field: String::from("statement"),
        detail: String::from("statement must be a string or single-key object"),
    })?;
    if object.len() != 1 {
        return Err(NativeEncodeError::InvalidInput {
            field: String::from("statement"),
            detail: String::from("statement object must contain exactly one variant"),
        });
    }
    let (variant, payload) = object.iter().next().expect("checked object length");
    match variant.as_str() {
        "StorageLive" => Ok(SupportedTrustMirStatement::StorageLive(value_to_usize(
            payload,
            "statement.StorageLive",
        )?)),
        "StorageDead" => Ok(SupportedTrustMirStatement::StorageDead(value_to_usize(
            payload,
            "statement.StorageDead",
        )?)),
        other => Err(unsupported_native(
            "trust_mir_statement_unsupported",
            format!("statement `{other}` is outside the native Trust MIR subset"),
        )),
    }
}

fn parse_terminator(value: &serde_json::Value) -> NativeEncodeResult<SupportedTrustMirTerminator> {
    if let Some(name) = value.as_str() {
        return match name {
            "Return" => Ok(SupportedTrustMirTerminator::Return),
            "Unreachable" => Ok(SupportedTrustMirTerminator::Unreachable),
            other => Err(unsupported_native(
                "trust_mir_terminator_unsupported",
                format!("terminator `{other}` is outside the native Trust MIR subset"),
            )),
        };
    }

    let object = value.as_object().ok_or_else(|| NativeEncodeError::InvalidInput {
        field: String::from("terminator"),
        detail: String::from("terminator must be a string or single-key object"),
    })?;
    if object.len() != 1 {
        return Err(NativeEncodeError::InvalidInput {
            field: String::from("terminator"),
            detail: String::from("terminator object must contain exactly one variant"),
        });
    }
    let (variant, payload) = object.iter().next().expect("checked object length");
    match variant.as_str() {
        "Goto" => {
            Ok(SupportedTrustMirTerminator::Goto(value_to_usize(payload, "terminator.Goto")?))
        }
        other => Err(unsupported_native(
            "trust_mir_terminator_unsupported",
            format!("terminator `{other}` is outside the native Trust MIR subset"),
        )),
    }
}

fn required_value<'a>(
    object: &'a serde_json::Map<String, serde_json::Value>,
    field: &str,
) -> NativeEncodeResult<&'a serde_json::Value> {
    object.get(field).ok_or_else(|| NativeEncodeError::InvalidInput {
        field: field.to_owned(),
        detail: String::from("missing required field"),
    })
}

fn required_object<'a>(
    object: &'a serde_json::Map<String, serde_json::Value>,
    field: &str,
) -> NativeEncodeResult<&'a serde_json::Map<String, serde_json::Value>> {
    required_value(object, field)?.as_object().ok_or_else(|| NativeEncodeError::InvalidInput {
        field: field.to_owned(),
        detail: String::from("must be an object"),
    })
}

fn required_array<'a>(
    object: &'a serde_json::Map<String, serde_json::Value>,
    field: &str,
) -> NativeEncodeResult<&'a Vec<serde_json::Value>> {
    required_value(object, field)?.as_array().ok_or_else(|| NativeEncodeError::InvalidInput {
        field: field.to_owned(),
        detail: String::from("must be an array"),
    })
}

fn required_string(
    object: &serde_json::Map<String, serde_json::Value>,
    field: &str,
) -> NativeEncodeResult<String> {
    required_value(object, field)?.as_str().map(str::to_owned).ok_or_else(|| {
        NativeEncodeError::InvalidInput {
            field: field.to_owned(),
            detail: String::from("must be a string"),
        }
    })
}

fn required_usize(
    object: &serde_json::Map<String, serde_json::Value>,
    field: &str,
) -> NativeEncodeResult<usize> {
    value_to_usize(required_value(object, field)?, field)
}

fn required_u32(
    object: &serde_json::Map<String, serde_json::Value>,
    field: &str,
) -> NativeEncodeResult<u32> {
    let value = required_value(object, field)?;
    u32::try_from(value.as_u64().ok_or_else(|| NativeEncodeError::InvalidInput {
        field: field.to_owned(),
        detail: String::from("must be a non-negative integer"),
    })?)
    .map_err(|_| NativeEncodeError::InvalidInput {
        field: field.to_owned(),
        detail: String::from("must fit in u32"),
    })
}

fn required_bool(
    object: &serde_json::Map<String, serde_json::Value>,
    field: &str,
) -> NativeEncodeResult<bool> {
    required_value(object, field)?.as_bool().ok_or_else(|| NativeEncodeError::InvalidInput {
        field: field.to_owned(),
        detail: String::from("must be a boolean"),
    })
}

fn value_to_usize(value: &serde_json::Value, field: &str) -> NativeEncodeResult<usize> {
    usize::try_from(value.as_u64().ok_or_else(|| NativeEncodeError::InvalidInput {
        field: field.to_owned(),
        detail: String::from("must be a non-negative integer"),
    })?)
    .map_err(|_| NativeEncodeError::InvalidInput {
        field: field.to_owned(),
        detail: String::from("must fit in usize"),
    })
}

fn unsupported_native(reason: impl Into<String>, detail: impl Into<String>) -> NativeEncodeError {
    NativeEncodeError::Unsupported(NativeEncodeUnsupported {
        operation: NativeOperation::Encode,
        reason: reason.into(),
        detail: detail.into(),
    })
}

fn proof_mode_payload_name(mode: NativeProofMode) -> &'static str {
    match mode {
        NativeProofMode::Bmc => "bmc",
        NativeProofMode::FiniteAcyclicBmc => "finite_acyclic_bmc",
        NativeProofMode::Chc => "chc",
        NativeProofMode::PdrIc3 => "pdr_ic3",
    }
}

fn decode_payload_provenance(value: &serde_json::Value) -> Option<NativeProofProvenance> {
    let provenance = value.get("provenance")?;
    let proof_mode = match provenance.get("proof_mode")?.as_str()? {
        "bmc" => NativeProofMode::Bmc,
        "finite_acyclic_bmc" => NativeProofMode::FiniteAcyclicBmc,
        "chc" => NativeProofMode::Chc,
        "pdr_ic3" => NativeProofMode::PdrIc3,
        _ => return None,
    };
    let bmc_depth = match provenance.get("bmc_depth")? {
        serde_json::Value::Null => None,
        value => Some(u32::try_from(value.as_u64()?).ok()?),
    };
    Some(NativeProofProvenance {
        proof_mode,
        bmc_depth,
        finite_acyclic: provenance.get("finite_acyclic")?.as_bool()?,
        producer: provenance.get("producer")?.as_str()?.to_owned(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_request(mode: NativeProofMode) -> NativeEncodeRequest {
        NativeEncodeRequest::new(
            "obligation-1",
            "crate::harness",
            NativeInput::TrustMir {
                format: String::from("trust-mir-v0"),
                bytes: minimal_trust_mir_bytes(),
            },
            mode,
        )
    }

    fn minimal_trust_mir_bytes() -> Vec<u8> {
        serde_json::to_vec(&serde_json::json!({
            "name": "harness",
            "def_path": "crate::harness",
            "span": {
                "file": "src/lib.rs",
                "line_start": 1,
                "col_start": 1,
                "line_end": 1,
                "col_end": 1,
            },
            "body": {
                "locals": [
                    { "index": 0, "ty": "Unit", "name": null },
                    { "index": 1, "ty": { "Int": { "width": 32, "signed": true } }, "name": "x" },
                ],
                "blocks": [
                    {
                        "id": 0,
                        "stmts": [
                            { "StorageLive": 1 },
                            { "StorageDead": 1 }
                        ],
                        "terminator": "Return"
                    }
                ],
                "arg_count": 1,
                "return_ty": "Unit"
            },
            "contracts": [],
            "preconditions": [],
            "postconditions": [],
            "spec": {
                "requires": [],
                "ensures": [],
                "invariants": []
            }
        }))
        .expect("fixture should serialize")
    }

    #[cfg(feature = "ay")]
    fn hash(bytes: &[u8]) -> trust_mc_core::EvidenceHash {
        trust_mc_core::EvidenceHash::sha256_bytes(bytes)
    }

    #[cfg(feature = "ay")]
    fn sample_span() -> NativeSourceSpan {
        NativeSourceSpan {
            file: String::from("src/lib.rs"),
            line_start: 10,
            column_start: 5,
            line_end: 10,
            column_end: 18,
        }
    }

    #[cfg(feature = "ay")]
    fn sample_local(index: u32, name: &str) -> NativeLocal {
        NativeLocal {
            index,
            name: Some(name.to_string()),
            ty: NativeTypeRef {
                stable_name: String::from("i32"),
                layout: Some(NativeTypeLayout {
                    size_bits: Some(32),
                    align_bits: Some(32),
                    abi: Some(String::from("scalar")),
                }),
            },
            span: Some(sample_span()),
        }
    }

    #[cfg(feature = "ay")]
    fn sample_obligation(id: &str) -> NativeObligationRef {
        NativeObligationRef {
            id: id.to_string(),
            kind: String::from("assertion"),
            span: Some(sample_span()),
            local_indices: vec![0, 1],
        }
    }

    #[cfg(feature = "ay")]
    fn sample_rust_mir_input() -> NativeRustMirInput {
        NativeRustMirInput {
            crate_name: String::from("demo"),
            def_path: String::from("demo::checked_add"),
            rustc_revision: String::from("rustc-2026-04-29"),
            body_hash: hash(b"rust mir body"),
            locals: vec![sample_local(0, "_0"), sample_local(1, "x")],
            contracts: vec![NativeContractRef {
                id: String::from("requires-1"),
                kind: String::from("requires"),
                payload_hash: hash(b"typed requires payload"),
                span: Some(sample_span()),
            }],
            obligations: vec![sample_obligation("obligation-1")],
        }
    }

    #[cfg(feature = "ay")]
    fn sample_trust_ir_module_input() -> NativeTrustIrModuleInput {
        NativeTrustIrModuleInput {
            module_name: String::from("demo_trust_ir"),
            trust_ir_version: String::from("trust_ir-v4"),
            snapshot_hash: hash(b"trust_ir snapshot"),
            functions: vec![NativeTrustIrFunctionInput {
                id: String::from("fn-1"),
                name: String::from("checked_add"),
                body_hash: hash(b"trust_ir function body"),
                span: Some(sample_span()),
                locals: vec![sample_local(0, "_0"), sample_local(1, "x")],
                obligations: vec![sample_obligation("obligation-1")],
            }],
            contracts: Vec::new(),
        }
    }

    #[cfg(feature = "ay")]
    fn sample_environment() -> NativeVerifierEnvironment {
        NativeVerifierEnvironment {
            trust_mc_revision: String::from("trust_mc-commit-a"),
            ay: NativeToolIdentity {
                name: String::from("ay"),
                revision: String::from("ay-commit-a"),
                binary_hash: Some(hash(b"ay binary")),
            },
            trust_compiler: NativeToolIdentity {
                name: String::from("trustc"),
                revision: String::from("trustc-commit-a"),
                binary_hash: Some(hash(b"trustc binary")),
            },
            trust_ir_snapshot: Some(NativeSnapshotIdentity {
                name: String::from("trust_ir"),
                revision: String::from("trust_ir-snapshot-a"),
                content_hash: hash(b"trust_ir snapshot"),
            }),
        }
    }

    #[cfg(feature = "ay")]
    fn sample_verify_request(
        input: NativeInput,
        proof_mode: NativeProofMode,
    ) -> NativeVerifyRequest {
        NativeVerifyRequest {
            input,
            options: NativeVerifierOptions {
                proof_mode,
                bmc_depth: matches!(
                    proof_mode,
                    NativeProofMode::Bmc | NativeProofMode::FiniteAcyclicBmc
                )
                .then_some(3),
                extra_options_hash: Some(hash(b"native option set")),
                resource_limits: NativeResourceLimits {
                    timeout_ms: Some(1_000),
                    memory_bytes: Some(256 * 1024 * 1024),
                    fuel: Some(64),
                },
            },
            environment: sample_environment(),
            artifact_dir: Some(String::from("trust_mc://test-run")),
        }
    }

    #[test]
    fn finite_acyclic_bmc_provenance_is_explicit() {
        let provenance = NativeProofProvenance::finite_acyclic_bmc(7);

        assert_eq!(provenance.proof_mode, NativeProofMode::FiniteAcyclicBmc);
        assert_eq!(provenance.bmc_depth, Some(7));
        assert!(provenance.finite_acyclic);
        assert!(provenance.proof_mode.is_finite_acyclic_bmc());
        assert!(!provenance.proof_mode.is_bounded());
    }

    #[cfg(feature = "ay")]
    #[test]
    fn prepare_native_verification_trust_ir_builds_content_addressed_manifest() {
        let request = sample_verify_request(
            NativeInput::TrustIrModule(sample_trust_ir_module_input()),
            NativeProofMode::Chc,
        );

        let prepared = prepare_native_verification(request).expect("typed trust_ir should prepare");

        assert_eq!(prepared.cache_key, prepared.manifest.cache_key);
        assert_eq!(
            prepared.manifest.input.kind,
            trust_mc_core::FullVerificationArtifactKind::CompilerInput
        );
        assert_eq!(
            prepared.manifest.obligation_set.kind,
            trust_mc_core::FullVerificationArtifactKind::ObligationSet
        );
        assert_eq!(
            prepared.manifest.options.kind,
            trust_mc_core::FullVerificationArtifactKind::VerificationOptions
        );
        assert_eq!(
            prepared.manifest.resource_limits.kind,
            trust_mc_core::FullVerificationArtifactKind::ResourceLimits
        );
        assert!(prepared.manifest.smt_rendering.is_none());
        assert!(prepared.manifest.validate().is_ok());
    }

    #[cfg(feature = "ay")]
    #[test]
    fn prepare_native_verification_cache_key_changes_with_identity_and_mode() {
        let base = sample_verify_request(
            NativeInput::RustMir(sample_rust_mir_input()),
            NativeProofMode::Bmc,
        );
        let base_key = prepare_native_verification(base.clone())
            .expect("base request should prepare")
            .cache_key;

        let mut pdr_request = base.clone();
        pdr_request.options.proof_mode = NativeProofMode::PdrIc3;
        pdr_request.options.bmc_depth = None;
        let pdr_key =
            prepare_native_verification(pdr_request).expect("PDR request should prepare").cache_key;

        let mut solver_request = base.clone();
        solver_request.environment.ay.binary_hash = Some(hash(b"different ay binary"));
        let solver_key = prepare_native_verification(solver_request)
            .expect("solver identity request should prepare")
            .cache_key;

        let mut snapshot_request = base;
        snapshot_request.environment.trust_ir_snapshot = Some(NativeSnapshotIdentity {
            name: String::from("trust_ir"),
            revision: String::from("trust_ir-snapshot-b"),
            content_hash: hash(b"different trust_ir snapshot"),
        });
        let snapshot_key = prepare_native_verification(snapshot_request)
            .expect("snapshot identity request should prepare")
            .cache_key;

        assert_ne!(base_key, pdr_key);
        assert_ne!(base_key, solver_key);
        assert_ne!(base_key, snapshot_key);
    }

    #[cfg(feature = "ay")]
    #[test]
    fn prepare_native_verification_rejects_text_inputs() {
        let request = sample_verify_request(
            NativeInput::SmtLib { script: String::from("(check-sat)\n") },
            NativeProofMode::Bmc,
        );

        let err = prepare_native_verification(request)
            .expect_err("direct verifier preparation must not accept text inputs");
        assert!(
            matches!(err, NativeEncodeError::Unsupported(unsupported) if unsupported.reason == "typed_native_input_required")
        );
    }

    #[test]
    fn encode_native_trust_mir_minimal_subset_returns_native_payload() {
        let request = sample_request(NativeProofMode::Bmc).with_bmc_depth(3);
        let encoded = encode_native(request).expect("minimal Trust MIR should encode natively");

        assert_eq!(encoded.kind, NativeVcKind::Bmc);
        assert_eq!(encoded.provenance.proof_mode, NativeProofMode::Bmc);
        assert_eq!(encoded.provenance.bmc_depth, Some(3));

        let payload: serde_json::Value =
            serde_json::from_slice(&encoded.payload).expect("payload should be JSON");
        assert_eq!(payload["format"], TRUST_MIR_BMC_PAYLOAD_FORMAT);
        assert_eq!(payload["version"], TRUST_MIR_BMC_PAYLOAD_VERSION);
        assert_eq!(payload["trust_mir"]["input_format"], "trust-mir-v0");
        assert_eq!(payload["trust_mir"]["body"]["blocks"][0]["terminator"], "Return");
        assert_eq!(payload["lowering"]["subset"], TRUST_MIR_SUBSET);
        assert_eq!(payload["provenance"]["bmc_depth"], 3);
    }

    #[test]
    fn encode_native_trust_mir_fails_closed_on_contracts() {
        let bytes = serde_json::to_vec(&serde_json::json!({
            "name": "harness",
            "def_path": "crate::harness",
            "body": {
                "locals": [{ "index": 0, "ty": "Unit", "name": null }],
                "blocks": [{ "id": 0, "stmts": [], "terminator": "Return" }],
                "arg_count": 0,
                "return_ty": "Unit"
            },
            "contracts": [{ "kind": "Requires", "body": "x > 0" }]
        }))
        .expect("fixture should serialize");
        let request = NativeEncodeRequest::new(
            "obligation-1",
            "crate::harness",
            NativeInput::TrustMir { format: String::from("trust-mir-v0"), bytes },
            NativeProofMode::Bmc,
        )
        .with_bmc_depth(1);

        let err = encode_native(request).expect_err("contracts are not lowered in this subset");
        assert!(
            matches!(err, NativeEncodeError::Unsupported(unsupported) if unsupported.reason == "trust_mir_contracts_not_lowered_yet")
        );
    }

    #[test]
    fn encode_native_trust_mir_fails_closed_on_unsupported_terminator() {
        let bytes = serde_json::to_vec(&serde_json::json!({
            "name": "harness",
            "def_path": "crate::harness",
            "body": {
                "locals": [{ "index": 0, "ty": "Unit", "name": null }],
                "blocks": [{
                    "id": 0,
                    "stmts": [],
                    "terminator": {
                        "Assert": {
                            "cond": { "Constant": { "Bool": true } },
                            "expected": true,
                            "target": 0
                        }
                    }
                }],
                "arg_count": 0,
                "return_ty": "Unit"
            },
            "contracts": []
        }))
        .expect("fixture should serialize");
        let request = NativeEncodeRequest::new(
            "obligation-1",
            "crate::harness",
            NativeInput::TrustMir { format: String::from("trust-mir-v0"), bytes },
            NativeProofMode::Bmc,
        )
        .with_bmc_depth(1);

        let err = encode_native(request).expect_err("Assert is not in the minimal subset");
        assert!(
            matches!(err, NativeEncodeError::Unsupported(unsupported) if unsupported.reason == "trust_mir_terminator_unsupported")
        );
    }

    #[test]
    fn encode_native_smtlib_bmc_returns_native_payload() {
        let request = NativeEncodeRequest::new(
            "obligation-1",
            "crate::harness",
            NativeInput::SmtLib {
                script: String::from("(set-logic QF_LIA)\n(assert false)\n(check-sat)\n"),
            },
            NativeProofMode::Bmc,
        )
        .with_bmc_depth(4);

        let encoded = encode_native(request).expect("SMT-LIB BMC should encode natively");
        assert_eq!(encoded.kind, NativeVcKind::Bmc);
        assert_eq!(encoded.provenance.proof_mode, NativeProofMode::Bmc);
        assert_eq!(encoded.provenance.bmc_depth, Some(4));

        let payload: serde_json::Value =
            serde_json::from_slice(&encoded.payload).expect("payload should be JSON");
        assert_eq!(payload["format"], SMTLIB_BMC_PAYLOAD_FORMAT);
        assert_eq!(payload["version"], SMTLIB_BMC_PAYLOAD_VERSION);
        assert_eq!(payload["kind"], "bmc");
        assert_eq!(payload["provenance"]["proof_mode"], "bmc");
        assert_eq!(payload["provenance"]["bmc_depth"], 4);
        assert_eq!(
            payload["script"].as_str().expect("script string"),
            "(set-logic QF_LIA)\n(assert false)\n(check-sat)\n"
        );
    }

    #[test]
    fn encode_native_smtlib_chc_remains_unsupported() {
        let request = NativeEncodeRequest::new(
            "obligation-1",
            "crate::harness",
            NativeInput::SmtLib { script: String::from("(set-logic HORN)\n") },
            NativeProofMode::Chc,
        );
        let err = encode_native(request).expect_err("CHC SMT-LIB is not this BMC path");

        assert!(
            matches!(err, NativeEncodeError::Unsupported(unsupported) if unsupported.reason == "smtlib_non_bmc_not_native_yet")
        );
    }

    #[test]
    fn encode_native_rejects_bmc_without_depth() {
        let err = encode_native(sample_request(NativeProofMode::Bmc))
            .expect_err("BMC without depth must be rejected");

        assert!(
            matches!(err, NativeEncodeError::InvalidInput { field, .. } if field == "bmc_depth")
        );
    }
}
