// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unreachable-target error rule helpers for `ChcCtx`.
//!
//! Part of #112: SwitchInt dispatch in `generate_perblock_fallback` can
//! target Unreachable blocks (panic paths) that have no declared relation
//! because they're excluded from BFS chains. Instead of silently dropping
//! the transition, emit an error rule: reaching Unreachable is a bug.
//!
//! Extracted from `codegen_rules/mod.rs` — Part of #3927.

use std::sync::Arc;

use ay_bindings::Expr;
use rustc_public::mir::TerminatorKind;
use tracing::debug;

use super::super::ChcCtx;
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Check if target block is Unreachable or error-only and emit an error rule if so.
    ///
    /// Returns `true` if the target was handled, `false` if the target is a
    /// normal return-reachable block.
    ///
    /// Part of #3436, #3595: Matches the shared variant's logic — both
    /// `Unreachable` terminators and error-only blocks (excluded from
    /// relation declaration by dead block elimination) are routed to `error()`.
    pub(in crate::codegen_ay::chc::rules::codegen_rules) fn try_emit_unreachable_error(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        stmt_constraints: &[Expr],
        extra: impl IntoIterator<Item = Expr>,
    ) -> bool {
        let from_app = self.refresh_block_relation_app(from_app);
        let is_unreachable = target < self.body.blocks.len()
            && matches!(self.body.blocks[target].terminator.kind, TerminatorKind::Unreachable);
        let is_error_only =
            target < self.body.blocks.len() && !self.block_relations.contains_key(&target);
        if is_unreachable || is_error_only {
            let error_app = RelationApp::new("error", Vec::new());
            let body = RuleBody::from_base_and_extra(Some(from_app), stmt_constraints, extra);
            self.vc.add_rule(Rule::new(body, error_app));
            debug!(
                ?target,
                is_unreachable,
                is_error_only,
                "emitted error rule for missing-relation target (#3436, #3595)"
            );
            return true;
        }
        false
    }

    /// Arc-shared variant of `try_emit_unreachable_error`.
    pub(in crate::codegen_ay::chc::rules::codegen_rules) fn try_emit_unreachable_error_shared(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        shared_constraints: &Arc<[Expr]>,
        extra: impl IntoIterator<Item = Expr>,
    ) -> bool {
        let from_app = self.refresh_block_relation_app(from_app);
        // Part of #3436: Emit error rule for targets that either have an
        // Unreachable terminator OR are error-only blocks (excluded from
        // relation declaration by dead block elimination). Error-only blocks
        // are on panic/formatting paths that cannot reach Return — their
        // transitions are soundly modeled as error() since reaching them
        // implies an assertion failure or panic that already triggered an
        // error rule at the branching block.
        let is_unreachable = target < self.body.blocks.len()
            && matches!(self.body.blocks[target].terminator.kind, TerminatorKind::Unreachable);
        let is_error_only =
            target < self.body.blocks.len() && !self.block_relations.contains_key(&target);
        if is_unreachable || is_error_only {
            let error_app = RelationApp::new("error", Vec::new());
            let body =
                RuleBody::from_shared_base(Some(from_app), Arc::clone(shared_constraints), extra);
            self.vc.add_rule(Rule::new(body, error_app));
            debug!(
                ?target,
                is_unreachable,
                is_error_only,
                "emitted error rule for missing-relation target (#3436)"
            );
            return true;
        }
        false
    }
}
