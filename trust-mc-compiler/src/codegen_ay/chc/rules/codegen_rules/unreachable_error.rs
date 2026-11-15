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

/// How many blocks `error_only_region_panics` may walk before it gives up (and the edge keeps
/// the unattributed `error` head).
const MAX_PANIC_REGION_BLOCKS: usize = 32;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The head an edge into the error-only region at `target` derives.
    ///
    /// Reaching an error-only block is an error, but not always a PANIC: the region may end in
    /// an `Unreachable` terminator (UB) or an undefined call. The bare `error` head says none of
    /// that, so the driver reports it as the anonymous `chc.0` check, which can never stand as
    /// the expected panic of a `should_panic` harness. When every path through the region is
    /// provably a panic — see [`Self::error_only_region_panics`] — register it as a `Panic`
    /// property instead, so `panic!()` / `assert!()` on an always-panicking path keeps its
    /// meaning (Kani reports it as a panic).
    fn error_only_region_head(&mut self, target: usize, is_unreachable: bool) -> RelationApp {
        if is_unreachable {
            // An `Unreachable` target used to take the AGGREGATE `error` head and
            // register NO property, so its check reached the driver as the
            // anonymous `chc.0` and could never be named, credited or refuted as
            // "unreachable code reached". Give it the per-BLOCK obligation
            // instead: the same `error_p{id}` every edge into the block derives.
            return self.unreachable_obligation_head(target);
        }
        if self.error_only_region_panics(target) {
            return self.register_error_head(
                trust_mc_core::violation::PropertyKind::Panic,
                target,
                Some("panic reached".to_string()),
            );
        }
        RelationApp::new("error", Vec::new())
    }

    /// The per-BLOCK `Unreachable` obligation head for `target`.
    ///
    /// One property per target BLOCK, never one per edge: a block can be reached
    /// by several edges, and "control never reaches this `Unreachable`" is a fact
    /// about the block. Every edge into it therefore derives the SAME
    /// `error_p{id}`, so the solver refutes the obligation when ANY edge is
    /// feasible and proves it only when none is. Registering per edge would both
    /// multiply the property table and let a single dead edge look like a
    /// discharge of the whole block (the hazard 852fecece measured).
    ///
    /// Falls back to the aggregate `error` head only when the property budget is
    /// spent (`MAX_CHC_PROPERTIES`), which is sound — the check still makes
    /// `error` reachable — and unnamed.
    fn unreachable_obligation_head(&mut self, target: usize) -> RelationApp {
        if let Some(existing) = self.vc.properties.iter().find(|p| {
            p.kind == trust_mc_core::violation::PropertyKind::Unreachable && p.bb == target
        }) {
            return RelationApp::new(existing.relation.clone(), Vec::new());
        }
        self.register_error_head(
            trust_mc_core::violation::PropertyKind::Unreachable,
            target,
            Some("unreachable code reached".to_string()),
        )
    }

    /// Record the obligation of an `Unreachable` target whose incoming edge the
    /// encoder just proved infeasible (its guard folded to `false`).
    ///
    /// The fold proves THAT EDGE is dead. It is not a proof about the BLOCK —
    /// another edge may still reach it — so the obligation must EXIST and be
    /// decided by a solver, never credited here. Registering the property and
    /// emitting no rule (what this replaces) left it RULELESS, which the driver
    /// cannot tell from a check the encoder DROPPED: it fails closed with
    /// `[AY:UNKNOWN_REASON:LostErrorRules]`, and 22 Kani-corpus units Kani proves
    /// paid for it.
    ///
    /// The canonical `false => error_p{id}` obligation fixes that without paying
    /// anything at solve time:
    ///   * it survives `eliminate_trivially_false_rules` (literal `false` body,
    ///     no body relation — the shape that pass deliberately RETAINS) and
    ///     `prune_orphan_block_rules` (no body relation to orphan), so the
    ///     property is never ruleless and the bridge is never pruned;
    ///   * it adds no variable and no theory, so none of the cost that got the
    ///     in-band marker reverted in 0b89f4734 arises — measured on AY
    ///     `45cc58c69`, the sliced `error_p{id} => false` obligation comes back
    ///     `unsat` with a SAFE certificate from preprocessing alone;
    ///   * if another edge into the same block IS feasible, that edge's rule
    ///     derives the same `error_p{id}` and the solver refutes it.
    pub(in crate::codegen_ay::chc::rules::codegen_rules) fn emit_infeasible_edge_unreachable_obligation(
        &mut self,
        target: usize,
    ) {
        let head = self.unreachable_obligation_head(target);
        // Budget spent: the head is the aggregate `error`, and a false-bodied
        // AGGREGATE rule is the driver's certified-discharge shape
        // (`smt_error_query_has_false_error_obligation`) — a proof reported
        // WITHOUT a solver, which one infeasible EDGE does not license. Leave the
        // absence and the fail-closed answer that follows from it.
        if !head.name.as_str().starts_with("error_p") {
            return;
        }
        // One obligation per block: the next dead edge into the same target adds
        // nothing.
        if self
            .vc
            .rules
            .iter()
            .any(|rule| rule.head.name == head.name && rule.body.relation.is_none())
        {
            return;
        }
        debug!(?target, "emitted per-block unreachable obligation for an infeasible edge");
        self.vc.add_rule(Rule::new(RuleBody::new(None, vec![Expr::bool_const(false)]), head));
    }

    /// Whether every path from `target` ends in a recognized panic (`kani::panic` hook,
    /// `PanicStub` model, or the same `PanicError` stub used by direct call dispatch)
    /// without first doing anything that can
    /// fail another way or stop the path. Allowed on the way: assignments that touch no memory
    /// through a pointer, bookkeeping statements, `Goto` / `SwitchInt`, an `Assert` (its failure
    /// is itself a panic), and a `kani::any_raw` call (it neither fails nor blocks). Anything
    /// else — a deref, another call (a `kani::assume` could make the panic unreachable), an
    /// `Unreachable`, a `Return`, a cycle, or a walk through more than
    /// [`MAX_PANIC_REGION_BLOCKS`] distinct blocks — answers
    /// `false`, and the edge keeps the unattributed head.
    fn error_only_region_panics(&self, target: usize) -> bool {
        use rustc_public::mir::{ProjectionElem, StatementKind};
        let blocks = &self.body.blocks;
        // A seen but unfinished node is a back-edge: that path may loop
        // without reaching a panic. Finished nodes may be shared by multiple
        // acyclic branches and must not be mistaken for a cycle.
        let mut stack = vec![(target, false)];
        let mut seen = std::collections::HashSet::new();
        let mut finished = std::collections::HashSet::new();
        while let Some((bb, exiting)) = stack.pop() {
            if exiting {
                finished.insert(bb);
                continue;
            }
            if finished.contains(&bb) {
                continue;
            }
            if !seen.insert(bb) {
                return false;
            }
            if seen.len() > MAX_PANIC_REGION_BLOCKS || bb >= blocks.len() {
                return false;
            }
            stack.push((bb, true));
            let block = &blocks[bb];
            let touches_memory = block.statements.iter().any(|stmt| match &stmt.kind {
                StatementKind::Assign(place, rvalue) => {
                    place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
                        || format!("{rvalue:?}").contains("Deref")
                }
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::FakeRead(..)
                | StatementKind::PlaceMention(_)
                | StatementKind::AscribeUserType { .. }
                | StatementKind::Coverage(_)
                | StatementKind::ConstEvalCounter
                | StatementKind::Nop => false,
                _ => true,
            });
            if touches_memory {
                return false;
            }
            match &block.terminator.kind {
                TerminatorKind::Goto { target } => stack.push((*target, false)),
                TerminatorKind::SwitchInt { targets, .. } => {
                    for next in targets.all_targets() {
                        stack.push((next, false));
                    }
                }
                // Holding continues to `target`; failing is a panic (`assertion` class).
                TerminatorKind::Assert { target, .. } => stack.push((*target, false)),
                TerminatorKind::Call { func, target: Some(next), .. }
                    if matches!(
                        self.detect_kani_hook(func),
                        Some(crate::kani_middle::kani_functions::KaniHook::AnyRaw)
                    ) =>
                {
                    stack.push((*next, false));
                }
                TerminatorKind::Call { func, target: None, .. } => {
                    let is_panic = matches!(
                        self.detect_kani_hook(func),
                        Some(crate::kani_middle::kani_functions::KaniHook::Panic)
                    ) || matches!(
                        self.detect_kani_model(func),
                        Some(crate::kani_middle::kani_functions::KaniModel::PanicStub)
                    ) || self.detect_stub(func)
                        == Some(crate::codegen_ay::stubs::StubKind::PanicError);
                    if !is_panic {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }

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
            let error_app = self.error_only_region_head(target, is_unreachable);
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
            let error_app = self.error_only_region_head(target, is_unreachable);
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

#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod panic_region_tests {
    use std::sync::atomic::{AtomicBool, Ordering};

    use super::ChcCtx;
    use crate::callee_body::CalleeBody;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::{METADATA_COUNTER_MUTEX, find_instance_by_suffix};

    const SOURCE: &str = r#"
        #![feature(panic_internals)]
        #![allow(dead_code, internal_features)]

        unsafe extern "C" {
            fn unknown_exit() -> !;
        }

        pub fn region_raw_panic() -> ! {
            core::panicking::panic("raw panic region");
        }

        pub fn region_unknown_divergence() -> ! {
            unsafe { unknown_exit() }
        }

        pub unsafe fn region_store_then_panic(destination: *mut u8) -> ! {
            unsafe { *destination = 1; }
            core::panicking::panic("after pointer store");
        }

        pub fn region_mixed(choose_panic: bool) -> ! {
            if choose_panic {
                core::panicking::panic("one branch panics");
            } else {
                unsafe { unknown_exit() }
            }
        }

        pub fn region_reconverging_panic(choose_left: bool) -> ! {
            let message = if choose_left { "left branch" } else { "right branch" };
            core::panicking::panic(message)
        }

        pub fn region_nonpanicking_cycle() -> ! {
            loop {}
        }

        pub fn region_cycle_or_panic(choose_panic: bool) -> ! {
            loop {
                if choose_panic {
                    core::panicking::panic("an exit does not prove termination");
                }
            }
        }
    "#;

    fn assert_panic_region(name: &'static str, expected: bool) {
        let _guard =
            METADATA_COUNTER_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        let ran = AtomicBool::new(false);
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.callee_body().expect("real compiled region body");
            assert!(!body.blocks.is_empty(), "{name}: missing entry block");
            if name == "region_reconverging_panic" {
                let mut incoming = vec![0usize; body.blocks.len()];
                let mut fork = false;
                for block in &body.blocks {
                    fork |=
                        matches!(block.terminator.kind, super::TerminatorKind::SwitchInt { .. });
                    for target in ChcCtx::block_successors(&block.terminator.kind) {
                        incoming[target] += 1;
                    }
                }
                assert!(
                    fork && incoming.iter().any(|count| *count >= 2),
                    "{name}: the compiled positive control must retain its diamond"
                );
            }
            let classifier =
                ChcCtx::new_with_instance(ctx.tcx, &body, instance, name, ChcConfig::default());
            if matches!(
                name,
                "region_raw_panic"
                    | "region_store_then_panic"
                    | "region_mixed"
                    | "region_reconverging_panic"
                    | "region_cycle_or_panic"
            ) {
                assert!(
                    body.blocks.iter().any(|block| {
                        matches!(&block.terminator.kind,
                        super::TerminatorKind::Call { func, .. }
                            if classifier.detect_stub(func)
                                == Some(crate::codegen_ay::stubs::StubKind::PanicError))
                    }),
                    "{name}: fixture must contain a real raw PanicError call"
                );
            }
            assert_eq!(
                classifier.error_only_region_panics(0),
                expected,
                "{name}: classify all paths from the actual MIR entry, body={body:?}",
            );
            ran.store(true, Ordering::SeqCst);
        });
        assert!(ran.load(Ordering::SeqCst), "{name}: compiler callback did not run");
    }

    #[test]
    fn raw_panic_region_is_recognized() {
        assert_panic_region("region_raw_panic", true);
    }

    #[test]
    fn unknown_diverging_region_is_not_certified_panic() {
        assert_panic_region("region_unknown_divergence", false);
    }

    #[test]
    fn pointer_store_before_panic_is_not_certified_panic() {
        assert_panic_region("region_store_then_panic", false);
    }

    #[test]
    fn mixed_panic_and_unknown_region_is_not_certified_panic() {
        assert_panic_region("region_mixed", false);
    }

    #[test]
    fn reconverging_panic_region_is_recognized() {
        assert_panic_region("region_reconverging_panic", true);
    }

    #[test]
    fn nonpanicking_cycle_is_not_certified_panic() {
        assert_panic_region("region_nonpanicking_cycle", false);
    }

    #[test]
    fn cycle_with_panic_exit_is_not_certified_panic() {
        assert_panic_region("region_cycle_or_panic", false);
    }
}
