// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CHC loop invariant lemma hint injection.
//!
//! After transition rules are generated, this module scans the emitted CHC
//! rules for accumulator patterns in loop bodies and emits auxiliary error
//! rules that make nonlinear terms visible to Z3 PDR's CEGAR loop.
//!
//! This guides PDR's invariant search for harnesses with polynomial/
//! bilinear invariants that PDR cannot synthesize in LIA alone.
//!
//! The emitted rules are *hints*, not trusted axioms. PDR must still
//! verify any learned invariant inductively. If the hint is wrong (the
//! invariant doesn't actually hold), PDR may return FAIL instead of
//! UNKNOWN — the hint should only be emitted when the invariant is
//! mathematically correct.
//!
//! ## MIR Checked Arithmetic Handling
//!
//! MIR uses checked arithmetic for `sum += i`, producing:
//! ```text
//! _tmp = CheckedAdd(sum, i) → _tmp_fld0__out = sum + i; _tmp_fld1__out = overflow
//! sum = _tmp.0             → sum__out = _tmp_fld0
//! ```
//!
//! The detection submodule (`lemma_hint_detect`) resolves this indirection
//! by building a reverse-alias map and resolving through temporaries.
//!
//! ## Sub-modules
//!
//! - `lemma_hint_patterns`: invariant pattern detection (forward/countdown accumulators)
//! - `lemma_hint_pdr`: PDR bridge for `LOOP_INVARIANT_REGISTRY`
//!
//! Part of #3258: CHC lemma injection for last 2 UNKNOWN harnesses.
//! Part of designs/2026-03-05-unknown-14-recovery-roadmap.md Phase 3 Strategy A.

use std::collections::HashMap;
use std::sync::Arc;

use ay_bindings::Expr;
use tracing::debug;

use crate::codegen_ay::chc::ChcCtx;
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};

use super::lemma_hint_detect;
use super::lemma_hint_pdr::PdrHintContext;

/// Modification type for a state variable in a loop body.
#[derive(Debug)]
pub(super) enum LoopModification {
    /// Variable is incremented: out = in + source
    IncrementBy(IncrSource),
    /// Variable is decremented: out = in - source
    DecrementBy(IncrSource),
}

/// Source of an increment/decrement.
#[derive(Debug)]
pub(super) enum IncrSource {
    /// Incremented/decremented by an integer constant (e.g., i += 1)
    Constant(i64),
    /// Incremented by another state variable (e.g., sum += i).
    /// Part of #2267: Arc<str> (O(1) clone) instead of String (O(n) clone).
    Variable(Arc<str>),
}

impl IncrSource {
    /// Clone the source value. Used by detect module for alias resolution.
    /// Part of #2267: Variable case is O(1) Arc refcount bump.
    pub(super) fn clone_source(&self) -> IncrSource {
        match self {
            IncrSource::Constant(v) => IncrSource::Constant(*v),
            IncrSource::Variable(name) => IncrSource::Variable(Arc::clone(name)),
        }
    }
}

impl LoopModification {
    /// Priority for selecting among multiple detected modifications of the same
    /// variable. Higher = preferred. Downstream consumers (forward accumulator,
    /// countdown) match on specific patterns; this ordering ensures the most
    /// useful pattern wins when multiple rules produce different modifications.
    /// Part of #3343: replaces non-deterministic first-wins `or_insert`.
    pub(super) fn priority(&self) -> u8 {
        match self {
            LoopModification::IncrementBy(IncrSource::Constant(1)) => 5,
            LoopModification::DecrementBy(IncrSource::Constant(1)) => 4,
            LoopModification::IncrementBy(IncrSource::Variable(_)) => 3,
            LoopModification::DecrementBy(IncrSource::Variable(_)) => 2,
            LoopModification::IncrementBy(IncrSource::Constant(_)) => 1,
            LoopModification::DecrementBy(IncrSource::Constant(_)) => 1,
        }
    }
}

/// Detected invariant hint to emit as an auxiliary error rule.
pub(super) struct InvariantHint {
    /// The loop header block index.
    pub header_bb: usize,
    /// The negated invariant expression (added as `negated → error`).
    pub negated_invariant: Expr,
    /// Description for debug logging.
    pub description: &'static str,
}

/// Emit CHC lemma hint rules for detected loop invariant patterns.
///
/// Called after `generate_transition_rules()` in `translate_inner()`.
/// Only active when int-lift is enabled and loop headers are present.
///
/// Detection strategy:
/// 1. Scan ALL rule constraints for state variable accumulation patterns
/// 2. Cross-reference detected patterns with loop header live variables
/// 3. Emit auxiliary `bb_h(vars) ∧ ¬invariant → error` rules
/// 4. Register detected invariants in LOOP_INVARIANT_REGISTRY for PDR hints
///
/// Step 3 makes nonlinear terms (i*i, i*n, n*n) visible to PDR.
/// Step 4 bridges to the driver-side LoopInvariantHint → LemmaHint pipeline
/// so the ay-chc-native PDR engine receives proper lemma hints.
pub(in crate::codegen_ay::chc) fn emit_loop_invariant_lemmas(ctx: &mut ChcCtx<'_, '_>) {
    if !ctx.int_lift || ctx.loop_headers.is_empty() {
        return;
    }

    // Pass 1: Scan all rules for state variable modification patterns.
    // Handles MIR checked-arithmetic indirection through temporaries.
    let result = lemma_hint_detect::detect_all_modifications(&ctx.vc.rules);

    if result.modifications.is_empty() {
        return;
    }

    debug!(
        modifications = ?result.modifications.keys().collect::<Vec<_>>(),
        comparison_vars = result.comparison_targets.len(),
        "lemma hint: detected modifications"
    );

    // Build reverse map: state var name → MIR local index.
    // Used to construct ExtractedLoopInvariant with captured_vars (local indices).
    // Part of #2267: Arc<str> keys (O(1) clone) instead of String (O(n) .to_string()).
    let name_to_local: HashMap<Arc<str>, usize> = ctx
        .state_var_mgr
        .local_to_state_idx
        .iter()
        .filter_map(|(&local_idx, &state_idx)| {
            ctx.state_var_mgr
                .state_vars
                .get(state_idx)
                .map(|(name, _)| (Arc::clone(name), local_idx))
        })
        .collect();

    // Pass 2: For each loop header, check which live state vars have
    // accumulator patterns and emit invariant hints + PDR registry entries.
    let headers: Vec<usize> = ctx.loop_headers.iter().copied().collect();
    let mut hint_count = 0;
    let mut extracted_invariants = Vec::new();
    for header_bb in &headers {
        let header_bb = *header_bb;
        // Collect names of Int-typed state vars live at this header.
        // Part of #2267: Arc<str> clones (O(1)) instead of .to_string() (O(n)).
        let live_int_var_names: Vec<Arc<str>> = ctx.state_var_mgr.live_state_indices[header_bb]
            .iter()
            .filter_map(|&idx| {
                let entry = &ctx.state_var_mgr.state_vars[idx];
                if entry.1.is_int() { Some(Arc::clone(&entry.0)) } else { None }
            })
            .collect();
        let live_int_var_name_refs: Vec<&str> = live_int_var_names.iter().map(|s| &**s).collect();

        if live_int_var_names.len() < 2 {
            continue;
        }

        // Part of #3258: Build per-BB mapping from state var name to relation argument position.
        // Per-BB dead-local elimination and tuple flattening mean MIR local indices
        // differ from CHC relation argument positions. This mapping gives the correct
        // position for each state variable in this BB's relation declaration.
        // Part of #2267: Arc<str> keys (O(1) clone) instead of String (O(n) .to_string()).
        let name_to_rel_arg_pos: HashMap<Arc<str>, usize> = ctx.state_var_mgr.live_state_indices
            [header_bb]
            .iter()
            .enumerate()
            .map(|(pos, &state_idx)| {
                let name = Arc::clone(&ctx.state_var_mgr.state_vars[state_idx].0);
                (name, pos)
            })
            .collect();

        // Filter modifications to only Int-typed vars live at this header.
        // Part of #2267: Arc<str> keys — deref to &str for HashMap<&str, _> key type.
        let relevant: HashMap<&str, &LoopModification> = result
            .modifications
            .iter()
            .filter(|(name, _)| {
                let name: &str = name;
                live_int_var_name_refs.contains(&name)
            })
            .map(|(name, mods)| {
                let name: &str = name;
                (name, mods)
            })
            .collect();

        let hints = super::lemma_hint_patterns::detect_invariant_patterns(
            header_bb,
            &relevant,
            &live_int_var_name_refs,
            &result.comparison_targets,
        );

        // Part of #3258: Collect PDR lemma hints BEFORE emit_lemma_rule.
        // collect_pdr_hints reads from ctx only via name_to_local and
        // name_to_rel_arg_pos (owned), while emit_lemma_rule mutably borrows ctx.
        // Ordering avoids borrow conflict.
        let mut pdr_ctx = PdrHintContext {
            comparison_targets: &result.comparison_targets,
            name_to_local: &name_to_local,
            name_to_rel_arg_pos: &name_to_rel_arg_pos,
            out: &mut extracted_invariants,
        };
        super::lemma_hint_pdr::collect_pdr_hints(
            header_bb,
            &relevant,
            &live_int_var_name_refs,
            &mut pdr_ctx,
        );

        // Emit auxiliary error rules (mutably borrows ctx).
        for hint in &hints {
            emit_lemma_rule(ctx, hint);
            hint_count += 1;
        }
    }

    if hint_count > 0 {
        debug!(hint_count, "emitted loop invariant lemma hints");
    }

    // Part of #3258: Register auto-detected invariants for the PDR pipeline.
    if !extracted_invariants.is_empty() {
        debug!(
            fn_name = %ctx.fn_name,
            count = extracted_invariants.len(),
            "registering auto-detected loop invariants for PDR pipeline"
        );
        // Part of #2267: pass Arc<str> clone (O(1)) instead of .to_string() (O(n)).
        crate::kani_middle::transform::loop_contracts::register_loop_invariants(
            Arc::clone(&ctx.fn_name),
            extracted_invariants,
        );
    }
}

/// Emit an auxiliary error rule for a lemma hint.
///
/// The rule has the form: `bb_h(state_vars) ∧ ¬invariant → error`
///
/// This makes nonlinear terms visible to PDR's CEGAR loop.
/// If the invariant holds, the rule doesn't affect the result.
/// If the invariant doesn't hold, PDR may learn it as a lemma.
fn emit_lemma_rule(ctx: &mut ChcCtx<'_, '_>, hint: &InvariantHint) {
    let Some(header_rel) = ctx.block_relations.get(&hint.header_bb).map(|s| &**s) else {
        return;
    };

    let header_args = ctx.project_state_args(hint.header_bb);
    let header_app = RelationApp::new(header_rel, header_args);
    let error_app = RelationApp::new("error", Vec::new());

    let body = RuleBody::new(Some(header_app), vec![hint.negated_invariant.clone()]);
    ctx.vc.add_rule(Rule::new(body, error_app));

    debug!(
        header_bb = hint.header_bb,
        description = hint.description,
        "emitted loop invariant lemma hint rule"
    );
}
