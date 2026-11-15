// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exhaustive admission of the options the native translator actually executes.

use trust_ir::{
    FuncId, NativeRequestId, NativeVerificationRequest, ProofDigest, ProofId, ProofLineageId,
    TrustMcArithmeticModel, TrustMcChcEngine, TrustMcInvariantSource, TrustMcMemoryModel,
    TrustMcNativeRequest, TrustMcPdrGeneralization, TrustMcSlicingMode, TrustMcVerificationMode,
};
use trust_mc_core::{
    ChcPdrEngine, ChcPdrSolveOptions, NativeMcExecutionConfig, NativeMcRequestExecutionBinding,
};

/// A well-formed native request whose selected option has no implementation.
/// No substitute VC or counterexample is constructed for this request.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("native request {request_id}: unsupported {field}={requested}: {reason}")]
pub struct NativeMcRequestOptionsRefusal {
    pub request_id: NativeRequestId,
    pub function: FuncId,
    pub obligations: Vec<ProofId>,
    pub lineage_roots: Vec<ProofLineageId>,
    pub native_obligation_id: String,
    pub field: &'static str,
    pub requested: String,
    pub reason: String,
}

fn refuse(
    request: &TrustMcNativeRequest,
    field: &'static str,
    value: impl std::fmt::Debug,
    reason: &str,
) -> NativeMcRequestOptionsRefusal {
    NativeMcRequestOptionsRefusal {
        request_id: request.id,
        function: request.function,
        obligations: request.obligations.clone(),
        lineage_roots: request.lineage_roots.clone(),
        native_obligation_id: super::native_bundle::native_obligation_id(
            request.id,
            &request.obligations,
        ),
        field,
        requested: format!("{value:?}"),
        reason: reason.into(),
    }
}

fn common(request: &TrustMcNativeRequest) -> Result<(), NativeMcRequestOptionsRefusal> {
    // Every request field is accounted for; adding a field must update this boundary.
    let trust_ir::TrustMcRequestOptions { memory_model, arithmetic_model, bmc: _, chc: _, slicing } =
        &request.options;
    match *memory_model {
        TrustMcMemoryModel::TrustIrPlaces => {}
        value @ (TrustMcMemoryModel::FlatArrays | TrustMcMemoryModel::StackedBorrows) => {
            return Err(refuse(
                request,
                "memory_model",
                value,
                "the native translator implements TrustIR places only",
            ));
        }
    }
    match *arithmetic_model {
        TrustMcArithmeticModel::FixedWidthBitvectors => {}
        value @ (TrustMcArithmeticModel::MathematicalIntegers
        | TrustMcArithmeticModel::RustChecked) => {
            return Err(refuse(
                request,
                "arithmetic_model",
                value,
                "the native translator implements bitvectors; instruction semantics and all safety checks remain intact",
            ));
        }
    }
    match *slicing {
        TrustMcSlicingMode::None => {}
        value @ (TrustMcSlicingMode::ObligationBackwardSlice
        | TrustMcSlicingMode::ConstraintIndependence) => {
            return Err(refuse(
                request,
                "slicing",
                value,
                "the native translator retains the whole function",
            ));
        }
    }
    Ok(())
}

/// The enforced translation profile, separate from engine/resource options.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NativeMcTranslationConfig {
    TrustIrPlacesFixedWidthBitvectors,
}

/// A checked CHC/PDR request profile. Private fields prevent manufacturing a
/// supported profile by setting a serialized status or digest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectiveNativeMcRequestConfig {
    binding: NativeMcRequestExecutionBinding,
}

impl EffectiveNativeMcRequestConfig {
    pub fn from_request(
        request: &TrustMcNativeRequest,
    ) -> Result<Self, NativeMcRequestOptionsRefusal> {
        common(request)?;
        match request.mode {
            TrustMcVerificationMode::Chc | TrustMcVerificationMode::Pdr => {}
            TrustMcVerificationMode::BoundedModelCheck => {
                return Err(refuse(
                    request,
                    "mode",
                    request.mode,
                    "use the acyclic BMC translator",
                ));
            }
        }
        let trust_ir::TrustMcChcOptions { engine, invariant_source, pdr, emit_horn_clauses } =
            &request.options.chc;
        let trust_ir::TrustMcPdrOptions { enabled, max_frames, generalization } = pdr;
        match *engine {
            TrustMcChcEngine::NativePdr => {}
            value @ (TrustMcChcEngine::Spacer | TrustMcChcEngine::Z3Fixedpoint) => {
                return Err(refuse(
                    request,
                    "chc.engine",
                    value,
                    "native proof execution uses the strict AY PDR engine",
                ));
            }
        }
        match *invariant_source {
            TrustMcInvariantSource::None => {}
            value @ (TrustMcInvariantSource::TrustIrProofObligations
            | TrustMcInvariantSource::TrustWp
            | TrustMcInvariantSource::TrustVc
            | TrustMcInvariantSource::UserSupplied) => {
                return Err(refuse(
                    request,
                    "chc.invariant_source",
                    value,
                    "no external invariant source is imported; internal clause-derived candidates are independently validated",
                ));
            }
        }
        if !*enabled {
            return Err(refuse(
                request,
                "chc.pdr.enabled",
                false,
                "the selected native PDR engine must be enabled",
            ));
        }
        match *generalization {
            TrustMcPdrGeneralization::Cubes => {}
            value @ (TrustMcPdrGeneralization::None | TrustMcPdrGeneralization::Interpolants) => {
                return Err(refuse(
                    request,
                    "chc.pdr.generalization",
                    value,
                    "the supported cube-blocking production profile retains independently checked heuristic candidates, including interpolation",
                ));
            }
        }
        if !*emit_horn_clauses {
            return Err(refuse(
                request,
                "chc.emit_horn_clauses",
                false,
                "CHC/PDR execution retains its Horn clauses",
            ));
        }
        if *max_frames == Some(0) {
            return Err(refuse(
                request,
                "chc.pdr.max_frames",
                Some(0u32),
                "the frame limit must be positive",
            ));
        }
        let execution = NativeMcExecutionConfig { max_frames: *max_frames };
        let request_digest = super::native_bundle::proof_digest_metadata(
            NativeVerificationRequest::TrustMc(request.clone()).stable_digest(),
        );
        Ok(Self {
            binding: NativeMcRequestExecutionBinding {
                request_digest,
                effective_config_digest: execution.digest(),
                execution,
            },
        })
    }

    pub fn translation_config(&self) -> NativeMcTranslationConfig {
        NativeMcTranslationConfig::TrustIrPlacesFixedWidthBitvectors
    }
    pub fn request_digest(&self) -> &trust_mc_core::NativeArtifactDigest {
        &self.binding.request_digest
    }
    pub fn effective_config_digest(&self) -> &trust_mc_core::NativeArtifactDigest {
        &self.binding.effective_config_digest
    }
    pub fn binding(&self) -> &NativeMcRequestExecutionBinding {
        &self.binding
    }

    /// The canonical request selects execution. The caller retains timeout and
    /// certificate controls; neither can disable the native full-safety gate.
    pub fn solve_options(&self, ceiling: &ChcPdrSolveOptions) -> ChcPdrSolveOptions {
        let mut options = ceiling.clone();
        options.engine = ChcPdrEngine::Pdr;
        options.native_request = Some(self.binding.clone());
        options
    }
}

/// BMC bounds are operative only when loops are modeled. The current acyclic
/// translator needs no unwinding and retains the request's exact bounds as data.
pub(crate) fn validate_bmc_options(
    request: &TrustMcNativeRequest,
) -> Result<ProofDigest, NativeMcRequestOptionsRefusal> {
    common(request)?;
    let trust_ir::TrustMcBmcOptions { unwind_limit, unwinding_assertions: _ } =
        &request.options.bmc;
    if *unwind_limit == 0 {
        return Err(refuse(request, "bmc.unwind_limit", 0u32, "the bound must be positive"));
    }
    Ok(NativeVerificationRequest::TrustMc(request.clone()).stable_digest())
}

pub(crate) fn unsupported_chc_mode(
    request: &TrustMcNativeRequest,
) -> NativeMcRequestOptionsRefusal {
    refuse(request, "mode", request.mode, "the CHC/PDR entry does not execute BMC requests")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{TranslateOptions, trust_mc_configured_chc_pdr_obligations_from_native_bundle};
    use std::sync::Arc;
    use std::time::Duration;

    fn selected(bundle: &trust_ir::NativeVerificationBundle) -> TrustMcNativeRequest {
        bundle
            .requests
            .iter()
            .find_map(|row| match row {
                NativeVerificationRequest::TrustMc(request) => Some(request.clone()),
                _ => None,
            })
            .unwrap()
    }

    #[test]
    fn effective_options_bind_original_request_and_preserve_caller_ceilings() {
        let bundle = crate::tests::native_trust_mc_bundle(TrustMcVerificationMode::Chc);
        let request = selected(&bundle);
        let first = EffectiveNativeMcRequestConfig::from_request(&request).unwrap();
        let mut another = request.clone();
        another.id = NativeRequestId::new(100);
        // Inactive BMC fields remain in original identity, not executed CHC settings.
        another.options.bmc.unwind_limit = 33;
        let equivalent = EffectiveNativeMcRequestConfig::from_request(&another).unwrap();
        assert_ne!(first.request_digest(), equivalent.request_digest());
        assert_eq!(first.effective_config_digest(), equivalent.effective_config_digest());
        another.options.chc.pdr.max_frames = Some(7);
        let capped = EffectiveNativeMcRequestConfig::from_request(&another).unwrap();
        assert_ne!(first.effective_config_digest(), capped.effective_config_digest());
        let caller = ChcPdrSolveOptions::default()
            .with_engine(ChcPdrEngine::AdaptivePortfolio)
            .with_timeout(Duration::from_millis(87))
            .with_proof_certificate(true);
        let actual = capped.solve_options(&caller);
        assert_eq!(actual.engine, ChcPdrEngine::Pdr);
        assert_eq!(actual.timeout, caller.timeout);
        assert!(actual.produce_proof_certificate);
        assert_eq!(actual.native_request.as_ref().unwrap().execution.max_frames, Some(7));
        assert!(actual.native_request.unwrap().is_consistent());
    }

    #[test]
    fn unsupported_options_are_named_without_a_substitute_question() {
        let original =
            selected(&crate::tests::native_trust_mc_bundle(TrustMcVerificationMode::Chc));
        let mutations: &[(&str, fn(&mut trust_ir::TrustMcRequestOptions))] = &[
            ("memory_model", |o| o.memory_model = TrustMcMemoryModel::FlatArrays),
            ("memory_model", |o| o.memory_model = TrustMcMemoryModel::StackedBorrows),
            ("arithmetic_model", |o| {
                o.arithmetic_model = TrustMcArithmeticModel::MathematicalIntegers
            }),
            ("arithmetic_model", |o| o.arithmetic_model = TrustMcArithmeticModel::RustChecked),
            ("slicing", |o| o.slicing = TrustMcSlicingMode::ObligationBackwardSlice),
            ("slicing", |o| o.slicing = TrustMcSlicingMode::ConstraintIndependence),
            ("chc.engine", |o| o.chc.engine = TrustMcChcEngine::Spacer),
            ("chc.engine", |o| o.chc.engine = TrustMcChcEngine::Z3Fixedpoint),
            ("chc.invariant_source", |o| {
                o.chc.invariant_source = TrustMcInvariantSource::TrustIrProofObligations
            }),
            ("chc.invariant_source", |o| o.chc.invariant_source = TrustMcInvariantSource::TrustWp),
            ("chc.invariant_source", |o| o.chc.invariant_source = TrustMcInvariantSource::TrustVc),
            ("chc.invariant_source", |o| {
                o.chc.invariant_source = TrustMcInvariantSource::UserSupplied
            }),
            ("chc.pdr.enabled", |o| o.chc.pdr.enabled = false),
            ("chc.pdr.generalization", |o| {
                o.chc.pdr.generalization = TrustMcPdrGeneralization::None
            }),
            ("chc.pdr.generalization", |o| {
                o.chc.pdr.generalization = TrustMcPdrGeneralization::Interpolants
            }),
            ("chc.emit_horn_clauses", |o| o.chc.emit_horn_clauses = false),
            ("chc.pdr.max_frames", |o| o.chc.pdr.max_frames = Some(0)),
        ];
        for (field, mutate) in mutations {
            let mut request = original.clone();
            mutate(&mut request.options);
            let refusal = EffectiveNativeMcRequestConfig::from_request(&request).unwrap_err();
            assert_eq!(refusal.field, *field);
            assert_eq!(refusal.request_id, request.id);
            assert_eq!(refusal.obligations, request.obligations);
            assert!(refusal.to_string().contains(field));
        }
    }

    #[test]
    fn mixed_options_keep_supported_siblings_and_share_only_translation_equivalents() {
        let mut bundle = crate::tests::native_trust_mc_bundle(TrustMcVerificationMode::Chc);
        let original = selected(&bundle);
        let mut unsupported = original.clone();
        unsupported.id = NativeRequestId::new(11);
        unsupported.options.chc.pdr.generalization = TrustMcPdrGeneralization::Interpolants;
        let mut capped = original.clone();
        capped.id = NativeRequestId::new(12);
        capped.options.chc.pdr.max_frames = Some(2);
        bundle.requests.extend([
            NativeVerificationRequest::TrustMc(unsupported),
            NativeVerificationRequest::TrustMc(capped),
        ]);
        bundle.validate().unwrap();
        let batch = trust_mc_configured_chc_pdr_obligations_from_native_bundle(
            &bundle,
            &TranslateOptions::default(),
        )
        .unwrap();
        assert_eq!(batch.obligations.len(), 2);
        assert_eq!(batch.refused_requests.len(), 1);
        assert_eq!(batch.refused_requests[0].request_id, NativeRequestId::new(11));
        assert_eq!(batch.refused_requests[0].field, "chc.pdr.generalization");
        assert_eq!(batch.work.functions_translated, 1);
        assert!(Arc::ptr_eq(
            &batch.obligations[0].obligation.vc,
            &batch.obligations[1].obligation.vc
        ));
        assert_ne!(
            batch.obligations[0].request_config.effective_config_digest(),
            batch.obligations[1].request_config.effective_config_digest()
        );
    }

    #[test]
    fn acyclic_bmc_retains_bounds_without_claiming_loop_unwinding() {
        let original =
            crate::tests::native_trust_mc_bundle(TrustMcVerificationMode::BoundedModelCheck);
        let first =
            crate::trust_mc_bmc_vcs_from_native_bundle(&original, &TranslateOptions::default())
                .unwrap();
        let mut changed = original;
        for row in &mut changed.requests {
            if let NativeVerificationRequest::TrustMc(request) = row {
                request.options.bmc.unwind_limit = 19;
                request.options.bmc.unwinding_assertions = false;
            }
        }
        let second =
            crate::trust_mc_bmc_vcs_from_native_bundle(&changed, &TranslateOptions::default())
                .unwrap();
        assert_ne!(first[0].request_digest, second[0].request_digest);
        assert_eq!(first[0].vc, second[0].vc, "acyclic bodies have no unwinding edge");
    }
}
