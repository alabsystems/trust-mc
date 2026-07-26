// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC transition rule generation from CFG edges.
//!
//! Contains:
//! - `generate_transition_rules`: main CFG edge -> Horn rule dispatch
//! - `emit_untranslatable_assert_fallback`: conservative assert fallback
//! - `emit_goto_rule`: unconditional transition rule emission
//! - `emit_guarded_goto_rule`: conditional transition rule emission
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//! Decomposed into submodules — Part of #2408.

pub(in crate::codegen_ay::chc) mod lemma_hint;
mod lemma_hint_detect;
mod lemma_hint_patterns;
mod lemma_hint_pdr;
pub(in crate::codegen_ay::chc) mod lemma_linearize;
pub(in crate::codegen_ay::chc) mod template_check;
pub(in crate::codegen_ay::chc) mod transition_drop;
mod transition_gen;
mod transition_gen_terminators;
mod unreachable_error;

// Re-export dispatch_block_terminator for fragment_gen (Part of #112).
pub(in crate::codegen_ay::chc) use transition_gen::dispatch_block_terminator;

use std::collections::HashSet;
use std::sync::Arc;

use ay_bindings::{Expr, ExprValue};
use num_bigint::BigInt;
use tracing::{debug, warn};

use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;
use crate::codegen_ay::types::int_sort;

use super::{ChcCtx, chc_fresh_name, declare_pending_var};
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};

pub(in crate::codegen_ay::chc) struct TransitionContext<'a> {
    pub from_app: &'a RelationApp,
    pub output_args: &'a [Expr],
    pub shared_constraints: &'a Arc<[Expr]>,
    pub modified_locals: &'a HashSet<usize>,
    pub bb_idx: usize,
}

fn append_constructor_guards(extra_constraints: &mut Vec<Expr>) {
    if extra_constraints.is_empty() {
        return;
    }
    let guards = super::collect_constructor_guards(extra_constraints);
    extra_constraints.extend(guards);
}

/// Extension trait for CFG transition rule generation on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CodegenRules<'tcx, 'body> {
    fn generate_transition_rules(&mut self);
    fn emit_untranslatable_assert_fallback(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        shared_constraints: &Arc<[Expr]>,
        bb_idx: usize,
    );
    fn emit_switchint_fallback_rules(
        &mut self,
        branches: &[(u128, usize)],
        otherwise: usize,
        tctx: &TransitionContext<'_>,
        reason: &'static str,
    );
    fn emit_goto_rule(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        stmt_constraints: &[Expr],
    );
    fn emit_guarded_goto_rule(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        stmt_constraints: &[Expr],
        guard: Expr,
    );
    /// Like `emit_goto_rule`, but appends extra constraints to the base slice
    /// without copying the base into a new Vec at the call site.
    /// Part of #2267: allocation debt reduction.
    fn emit_goto_rule_extra(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        stmt_constraints: &[Expr],
        extra: impl IntoIterator<Item = Expr>,
    );

    // --- Arc-shared constraint variants (Part of #2507) ---

    /// Emit a goto rule using shared constraints. The `Arc<[Expr]>` base is
    /// not copied — only the Arc refcount is bumped.
    fn emit_goto_rule_shared(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        shared_constraints: &Arc<[Expr]>,
    );

    /// Emit a guarded goto rule using shared constraints.
    fn emit_guarded_goto_rule_shared(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        shared_constraints: &Arc<[Expr]>,
        guard: Expr,
    );

    /// Emit a goto rule with shared base + extra constraints.
    fn emit_goto_rule_shared_extra(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        shared_constraints: &Arc<[Expr]>,
        extra: impl IntoIterator<Item = Expr>,
    );
}

impl<'tcx, 'body> CodegenRules<'tcx, 'body> for ChcCtx<'tcx, 'body> {
    fn generate_transition_rules(&mut self) {
        // FC-29: locate `#[kani::loop_modifies]` clauses and build loop
        // assigns enforcement frames. Must run in BOTH step modes (loop
        // harnesses auto-select Large), before any block is encoded.
        crate::codegen_ay::chc::loop_modifies_frame::prescan_loop_modifies_frames(self);
        // Wall-2: nested-legacy loop sentinel → fail-closed demotion (see
        // `prescan_loop_rule_nested_legacy_demotion`).
        crate::codegen_ay::chc::loop_modifies_frame::prescan_loop_rule_nested_legacy_demotion(self);
        // Part of #112: dispatch to fragment-based rule generation in Large mode.
        if self.step_mode == crate::args::ChcStepMode::Large {
            super::fragment_gen::generate_fragment_rules(self);
        } else {
            transition_gen::generate_transition_rules(self);
        }
    }

    /// Fail-closed fallback for untranslatable MIR Assert conditions.
    ///
    /// Uses non-deterministic choice: emits BOTH (1) a conservative error rule
    /// (`from_rel -> error()`) and (2) an unguarded goto to the successor block.
    /// The solver explores both paths — if any path reaches error(), it reports
    /// CTREX. This is sound over-approximation: it adds behaviors (both passing
    /// and failing are possible), which can only produce spurious CTREX, never
    /// false proofs.
    ///
    /// Fix for P1:1437: W4:3652 dropped the error rule claiming "sound
    /// over-approximation", but this was actually under-approximation (removing
    /// behaviors), which produced 5 false proofs in conflict_analysis harnesses.
    ///
    /// Accepts `Arc<[Expr]>` shared constraints to avoid copying the constraint
    /// vector for the two rules emitted. Part of #2507.
    fn emit_untranslatable_assert_fallback(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        shared_constraints: &Arc<[Expr]>,
        bb_idx: usize,
    ) {
        self.diagnostics.assert_untranslatable.inc();
        debug!(bb_idx, "untranslatable Assert: non-deterministic choice (error ∨ successor)");
        // (1) Error rule: from_rel(state) ∧ constraints → error()
        self.emit_untranslatable_assert_rule_shared(
            from_app,
            shared_constraints,
            bb_idx,
            "untranslatable MIR Assert condition",
        );
        // (2) Successor edge: from_rel(state) ∧ constraints → target_rel(output)
        self.emit_goto_rule_shared(from_app, target, output_args, shared_constraints);
    }

    /// Fail-closed fallback for untranslatable `SwitchInt`.
    ///
    /// Emits a conservative error rule and selector-guarded successor edges.
    /// The fresh selector preserves branch mutual exclusivity while remaining
    /// agnostic to the actual discriminant semantics.
    ///
    /// Uses Arc-shared constraints to avoid K+2 copies of the constraint vector
    /// (1 error rule + K branch rules + 1 otherwise rule). Part of #2507.
    fn emit_switchint_fallback_rules(
        &mut self,
        branches: &[(u128, usize)],
        otherwise: usize,
        tctx: &TransitionContext<'_>,
        reason: &'static str,
    ) {
        warn!(
            bb_idx = tctx.bb_idx,
            reason,
            explicit_branches = branches.len(),
            "cannot encode SwitchInt guards; emitting fail-closed selector fallback"
        );
        self.emit_untranslatable_assert_rule_shared(
            tctx.from_app,
            tctx.shared_constraints,
            tctx.bb_idx,
            reason,
        );

        // Part of #3447: Record that SwitchInt discriminant is unresolvable —
        // the selector is unconstrained (nondeterministic branch choice).
        // Part of #3814: upgrade to reason-coded recording for bootstrap diagnosis.
        self.record_sound_fallback_reason("switchint_discriminant_unresolvable");
        let selector = declare_pending_var(chc_fresh_name("__switch_choice"), int_sort());
        for (choice_idx, (_, target)) in branches.iter().enumerate() {
            let guard = selector.clone().eq(Expr::int_const(BigInt::from(choice_idx)));
            self.emit_guarded_goto_rule_shared(
                tctx.from_app,
                *target,
                tctx.output_args,
                tctx.shared_constraints,
                guard,
            );
        }

        let otherwise_guard = selector.eq(Expr::int_const(BigInt::from(branches.len())));
        self.emit_guarded_goto_rule_shared(
            tctx.from_app,
            otherwise,
            tctx.output_args,
            tctx.shared_constraints,
            otherwise_guard,
        );
    }

    /// Emits a simple transition rule: from_rel(state) ^ stmt_constraints -> to_rel(output_state).
    fn emit_goto_rule(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        stmt_constraints: &[Expr],
    ) {
        self.emit_goto_rule_extra(from_app, target, output_args, stmt_constraints, []);
    }

    /// Like `emit_goto_rule`, but appends extra constraints without caller-side Vec allocation.
    /// Part of #2267: allocation debt reduction.
    fn emit_goto_rule_extra(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        stmt_constraints: &[Expr],
        extra: impl IntoIterator<Item = Expr>,
    ) {
        let from_app = self.refresh_block_relation_app(from_app);
        // Part of #3541: Collect extra to filter superseded store chains.
        // When call handlers emit `build_memory_store` after mid-block drain,
        // extra may contain store chain constraints (`mem_*__out = store(...)`)
        // that supersede constraints already in stmt_constraints. Without
        // filtering, both target the same __out variable → UNSAT.
        let extra_vec: Vec<Expr> = extra.into_iter().collect();
        let filtered_stmts =
            super::heap_store_chains::filter_superseded_store_chains(stmt_constraints, &extra_vec);
        let effective_stmts: &[Expr] = filtered_stmts.as_deref().unwrap_or(stmt_constraints);
        let mut extra_with_guards = extra_vec;
        append_constructor_guards(&mut extra_with_guards);

        let Some(to_rel) = self.block_relations.get(&target).map(|s| &**s) else {
            // Part of #112, #3595: Unreachable or error-only targets may have no
            // declared relation when excluded from BFS chains. Emit error rule.
            if !self.try_emit_unreachable_error(
                &from_app,
                target,
                effective_stmts,
                extra_with_guards,
            ) {
                warn!(?target, "target block not found in relation map");
            }
            return;
        };
        // Part of #2214: Project output_args to target block's live set.
        let projected = self.project_full_output_to_block(target, output_args);
        let to_app = RelationApp::new(to_rel, projected);
        let body =
            RuleBody::from_base_and_extra(Some(from_app), effective_stmts, extra_with_guards);
        self.vc.add_rule(Rule::new(body, to_app));
        debug!(?target, "emitted transition rule");
    }

    /// Emits a guarded transition rule: from_rel(state) ^ stmt_constraints ^ guard -> to_rel(output_state).
    ///
    /// This is used for conditional branches like SwitchInt where each edge
    /// has an associated guard condition.
    fn emit_guarded_goto_rule(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        stmt_constraints: &[Expr],
        guard: Expr,
    ) {
        let from_app = self.refresh_block_relation_app(from_app);
        match guard.value() {
            ExprValue::BoolConst(true) => {
                self.emit_goto_rule(&from_app, target, output_args, stmt_constraints);
                return;
            }
            ExprValue::BoolConst(false) => {
                debug!(?target, "skipping guarded transition rule (guard=false)");
                return;
            }
            _ => {} // external enum: ExprValue
        }
        let mut extra = vec![guard];
        append_constructor_guards(&mut extra);
        let Some(to_rel) = self.block_relations.get(&target).map(|s| &**s) else {
            // Part of #112, #3595: emit error rule for unreachable/error-only targets.
            if !self.try_emit_unreachable_error(&from_app, target, stmt_constraints, extra) {
                warn!(?target, "target block not found in relation map");
            }
            return;
        };

        // Part of #2214: Project output_args to target block's live set.
        let projected = self.project_full_output_to_block(target, output_args);
        let to_app = RelationApp::new(to_rel, projected);

        // Use from_base_and_extra to avoid stmt_constraints.to_vec() + push
        let body = RuleBody::from_base_and_extra(Some(from_app), stmt_constraints, extra);
        let rule = Rule::new(body, to_app);

        self.vc.add_rule(rule);
        debug!(?target, "emitted guarded transition rule");
    }

    // --- Arc-shared constraint variants (Part of #2507) ---

    /// Emit a goto rule sharing the constraint Arc — no base-slice copy.
    fn emit_goto_rule_shared(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        shared_constraints: &Arc<[Expr]>,
    ) {
        self.emit_goto_rule_shared_extra(from_app, target, output_args, shared_constraints, []);
    }

    /// Emit a guarded goto rule sharing the constraint Arc.
    fn emit_guarded_goto_rule_shared(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        shared_constraints: &Arc<[Expr]>,
        guard: Expr,
    ) {
        let from_app = self.refresh_block_relation_app(from_app);
        match guard.value() {
            ExprValue::BoolConst(true) => {
                self.emit_goto_rule_shared(&from_app, target, output_args, shared_constraints);
                return;
            }
            ExprValue::BoolConst(false) => {
                debug!(?target, "skipping guarded transition rule (guard=false)");
                return;
            }
            _ => {} // external enum: ExprValue
        }
        let mut extra = vec![guard];
        append_constructor_guards(&mut extra);
        let Some(to_rel) = self.block_relations.get(&target).map(|s| &**s) else {
            // Part of #112, #3436: emit error rule for unreachable/error-only targets.
            if !self.try_emit_unreachable_error_shared(&from_app, target, shared_constraints, extra)
            {
                warn!(?target, "target block not found in relation map");
            }
            return;
        };
        let projected = self.project_full_output_to_block(target, output_args);
        let to_app = RelationApp::new(to_rel, projected);
        let body =
            RuleBody::from_shared_base(Some(from_app), Arc::clone(shared_constraints), extra);
        self.vc.add_rule(Rule::new(body, to_app));
        debug!(?target, "emitted shared guarded transition rule");
    }

    /// Emit a goto rule with shared base + extra constraints.
    fn emit_goto_rule_shared_extra(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        output_args: &[Expr],
        shared_constraints: &Arc<[Expr]>,
        extra: impl IntoIterator<Item = Expr>,
    ) {
        let from_app = self.refresh_block_relation_app(from_app);
        let mut extra_with_guards: Vec<Expr> = extra.into_iter().collect();
        append_constructor_guards(&mut extra_with_guards);
        let Some(to_rel) = self.block_relations.get(&target).map(|s| &**s) else {
            // Part of #112, #3436: emit error rule for unreachable/error-only targets.
            if !self.try_emit_unreachable_error_shared(
                &from_app,
                target,
                shared_constraints,
                extra_with_guards,
            ) {
                warn!(?target, "target block not found in relation map");
            }
            return;
        };
        let projected = self.project_full_output_to_block(target, output_args);
        let to_app = RelationApp::new(to_rel, projected);
        let body = RuleBody::from_shared_base(
            Some(from_app),
            Arc::clone(shared_constraints),
            extra_with_guards,
        );
        self.vc.add_rule(Rule::new(body, to_app));
        debug!(?target, "emitted shared transition rule");
    }
}
