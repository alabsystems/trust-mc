// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Driver-side CHC auto-invariant seed extraction — CLI adapter.
//!
//! The implementation lives in the library lane (`crate::chc_auto_hints`) so
//! the native typed-CHC runner (which the COMPILER drives) shares it; this
//! module keeps the CLI's `--ay-chc-auto-invariants` mode mapping and
//! re-exports the pieces the CLI lane (tests, proof-core) consumes.
//!
//! Part of #2875 (BV-aware detection); native unification + W3 scaled
//! accumulators live in the library module.

use crate::args::AYChcAutoInvariantsMode;
use ay::chc::{ChcProblem, LemmaHint};

#[allow(unused_imports)]
pub(super) use crate::chc_auto_hints::{
    AutoInvariantStats, MAX_CANDIDATES_PER_PREDICATE, candidate_from_comparison,
    canonical_state_expr, collect_comparisons, detect_incremented_indices,
    int_body_var_to_state_map,
};
use crate::chc_auto_hints::{HintSource, generate_lemma_hint_candidates};

pub(crate) fn generate_auto_invariant_hints(
    problem: &ChcProblem,
    mode: AYChcAutoInvariantsMode,
) -> (Vec<LemmaHint>, AutoInvariantStats) {
    let source = match mode {
        AYChcAutoInvariantsMode::Off => return (Vec::new(), AutoInvariantStats::default()),
        AYChcAutoInvariantsMode::Range => HintSource::Range,
        AYChcAutoInvariantsMode::Houdini => HintSource::Houdini,
    };
    generate_lemma_hint_candidates(problem, source)
}
