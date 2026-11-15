// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact execution identity for the supported native TrustIR request profile.
//! This is transport data, never authority to skip fresh translation or replay.

use serde::{Deserialize, Serialize};

use crate::{EvidenceHash, NativeArtifactDigest};

/// The native PDR cube-blocking production profile. Candidate interpolation
/// and internal clause-derived hints remain independently validated heuristics;
/// this does not advertise a pure-cube-only or imported-invariant algorithm.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NativeMcExecutionConfig {
    pub max_frames: Option<u32>,
}

impl NativeMcExecutionConfig {
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let max_frames =
            self.max_frames.map_or_else(|| "null".to_owned(), |limit| limit.to_string());
        // Only a canonical optional unsigned scalar varies; fixed JSON bytes
        // avoid adding a serialization runtime to the core dependency graph.
        format!(
            "{{\"schema\":\"trust_mc.native-request-execution/v1\",\"memory\":\"TrustIrPlaces\",\"arithmetic\":\"FixedWidthBitvectors\",\"safety\":\"all-checks\",\"engine\":\"NativePdr\",\"imported_invariant_source\":\"None\",\"generalization\":\"CubeBlockingProduction\",\"internal_candidates\":\"independently-checked-clause-derived\",\"slicing\":\"None\",\"max_frames\":{max_frames}}}"
        ).into_bytes()
    }

    pub fn digest(&self) -> NativeArtifactDigest {
        let hash = EvidenceHash::sha256_bytes(&self.canonical_bytes());
        NativeArtifactDigest::new(hash.algorithm, hash.value)
    }
}

/// The original canonical request and the effective configuration both bind
/// evidence. Distinct requests may share equivalent engine work, never seals.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NativeMcRequestExecutionBinding {
    pub request_digest: NativeArtifactDigest,
    pub effective_config_digest: NativeArtifactDigest,
    pub execution: NativeMcExecutionConfig,
}

impl NativeMcRequestExecutionBinding {
    pub fn is_consistent(&self) -> bool {
        let canonical = |digest: &NativeArtifactDigest| {
            digest.algorithm == "sha256"
                && digest.value.len() == 64
                && digest
                    .value
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        };
        canonical(&self.request_digest)
            && canonical(&self.effective_config_digest)
            && self.effective_config_digest == self.execution.digest()
            && self.execution.max_frames != Some(0)
    }
}
