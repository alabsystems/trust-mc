// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

/// Proof cross-check provenance for CHC proofs (#2574, #4055).
///
/// BMC cross-check was removed as part of Z3 elimination (#4223).
/// ay-chc's internal portfolio validation replaces external cross-checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ProofCrosscheck {
    /// No external cross-check was run (standard path).
    NotRun,
}

impl ProofCrosscheck {
    pub(crate) fn label(&self) -> Option<&'static str> {
        match self {
            Self::NotRun => None,
        }
    }
}
