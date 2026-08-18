// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Assertion/assume rule emission for CHC codegen.
//!
//! Extracted from codegen_expr.rs per #2129 decomposition.
//! Handles: translate_assert_condition, emit_assert_error_rule_shared,
//! emit_kani_{assert,assume}_rule, to_bool_expr.
//! Detection helpers (detect_kani_*) are in codegen_expr_detect.rs.
//!
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::{Expr, ExprValue, Sort, SortInner};
use rustc_public::mir::Operand;
use std::collections::HashSet;
use std::sync::Arc;
use std::sync::atomic::Ordering;
use tracing::{debug, warn};
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};
use trust_mc_core::violation::PropertyKind;

use super::codegen_ctx::diagnostics::{CellCounter, GLOBAL_COUNTERS};
use super::codegen_expr_assert_simplify::simplify_bool_expr;
use super::{ChcCtx, chc_debug_enabled};
use crate::codegen_ay::chc::{chc_fresh_name, declare_pending_var};

/// Kani-parity description for a MIR `Assert` terminator message.
///
/// Ported from Kani's `codegen_cprover_gotoc/codegen/statement.rs` assert
/// handling: messages with runtime operand values get Kani's fixed static
/// text; every other kind uses rustc's `AssertMessage::description()` string
/// ("attempt to divide by zero", "attempt to add with overflow", …). `None`
/// only when rustc has no static description (keeps the generic kind text).
fn kani_assert_message_description(msg: &rustc_public::mir::AssertMessage) -> Option<String> {
    use rustc_public::mir::AssertMessage;
    match msg {
        AssertMessage::BoundsCheck { .. } => Some(
            "index out of bounds: the length is less than or equal to the given index".to_owned(),
        ),
        AssertMessage::InvalidEnumConstruction(_) => Some(
            "invalid enum construction: value is not a valid discriminant for this enum".to_owned(),
        ),
        AssertMessage::MisalignedPointerDereference { .. } => Some(
            "misaligned pointer dereference: address must be a multiple of its type's alignment"
                .to_owned(),
        ),
        _ => msg.description().ok().map(str::to_owned),
    }
}

/// Kani-parity (kind, message) pair for a MIR `Assert` terminator message.
///
/// Shared by the block-level assert emitter (`emit_assert_error_rule_shared`)
/// and the inline walker's assert-guard side-channel so inline MIR asserts
/// carry the same per-property kind/description as host-level ones.
/// Pointer-UB asserts are memory-safety failures, NOT panics (see
/// `emit_assert_error_rule_shared`); everything else keeps the assertion kind.
pub(in crate::codegen_ay::chc) fn mir_assert_kind_and_message(
    msg: &rustc_public::mir::AssertMessage,
) -> (PropertyKind, Option<String>) {
    let kind = match msg {
        rustc_public::mir::AssertMessage::NullPointerDereference => PropertyKind::NullPointer,
        rustc_public::mir::AssertMessage::MisalignedPointerDereference { .. } => {
            PropertyKind::MemorySafety
        }
        _ => PropertyKind::Assertion,
    };
    (kind, kani_assert_message_description(msg))
}

/// Get the current number of dropped assume transitions.
/// Delegates to GLOBAL_COUNTERS (Part of #2906).
pub(in crate::codegen_ay) fn get_chc_assume_dropped_transition_count() -> usize {
    GLOBAL_COUNTERS.assume_dropped_transition.load(Ordering::Relaxed)
}

/// Get the current number of untranslatable assertion conservative error rules.
/// Delegates to GLOBAL_COUNTERS (Part of #2906).
pub(in crate::codegen_ay) fn get_chc_assert_untranslatable_count() -> usize {
    GLOBAL_COUNTERS.assert_untranslatable.load(Ordering::Relaxed)
}

/// Parameter bundle for `kani::assume` transition emission.
pub(in crate::codegen_ay::chc) struct KaniAssumeContext<'a> {
    pub from_app: &'a RelationApp,
    pub args: &'a [Operand],
    pub target: usize,
    pub output_args: &'a [Expr],
    pub extra_constraints: &'a [Expr],
    pub stmt_constraints: &'a [Expr],
    pub modified_locals: &'a HashSet<usize>,
    pub bb_idx: usize,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate an assertion condition operand into a Bool expression.
    ///
    /// Mirrors MIR semantics where non-bool conditions are treated as "!= 0".
    pub(in crate::codegen_ay::chc) fn translate_assert_condition(
        &mut self,
        cond: &Operand,
        modified_locals: &HashSet<usize>,
        bb_idx: usize,
    ) -> Option<Expr> {
        // Translate the condition operand using OUTPUT vars for modified locals (#656)
        let cond_expr =
            if let Some(expr) = self.translate_operand_with_modified(cond, modified_locals) {
                expr
            } else {
                // Use debug! not warn! - constants are common and not yet supported
                debug!(?bb_idx, ?cond, "cannot translate assertion condition");
                return None;
            };

        // Convert condition to bool if needed (non-bool means != 0)
        if cond_expr.sort().is_bool() {
            return Some(simplify_bool_expr(cond_expr));
        }
        if let Some(width) = cond_expr.sort().bitvec_width() {
            let zero = Expr::bitvec_const(0, width);
            return Some(simplify_bool_expr(cond_expr.eq(zero).not()));
        }
        if cond_expr.sort().is_int() {
            let zero = Expr::int_const(0);
            return Some(simplify_bool_expr(cond_expr.eq(zero).not()));
        }

        warn!(
            ?bb_idx,
            sort = ?cond_expr.sort(),
            "unsupported sort for assertion condition"
        );
        None
    }

    /// Emits an error rule for assertion violation using Arc-shared constraints.
    ///
    /// An assertion `assert!(cond == expected)` generates an error rule:
    /// `from_rel(state) ∧ shared_constraints ∧ (cond != expected) → error()`
    ///
    /// Reuses the block-level `Arc<[Expr]>` base when assertion handling emits
    /// both error and successor rules from the same constraints. Part of #2507.
    pub(in crate::codegen_ay::chc) fn emit_assert_error_rule_shared(
        &mut self,
        from_app: &RelationApp,
        bool_cond: Expr,
        expected: bool,
        shared_constraints: &Arc<[Expr]>,
        bb_idx: usize,
        msg: Option<&rustc_public::mir::AssertMessage>,
    ) {
        if chc_debug_enabled() {
            debug!("emit_assert_error_rule_shared bb{} expected={}", bb_idx, expected);
            debug!("  from_app.rel={}", from_app.name);
            debug!("  shared_constraints.len={}", shared_constraints.len());
            for (i, c) in shared_constraints.iter().enumerate() {
                debug!("  shared_constraint[{}]={:?}", i, c);
            }
            debug!("  bool_cond={:?}", bool_cond);
        }

        let expected_expr = Expr::bool_const(expected);
        let violation = self.fn_ptr_assert_violation_obligation(simplify_bool_expr(
            bool_cond.eq(expected_expr).not(),
        ));
        // BSEM-18: per-property error head for this assertion check.
        //
        // Pointer-UB MIR asserts (`Assert(NullPointerDereference)` /
        // `Assert(MisalignedPointerDereference)`) are memory-safety failures,
        // NOT panics: under `#[kani::should_panic]` they must count as "failures
        // other than panics" (FAILED), matching Kani. Every other AssertMessage
        // (bounds, overflow, division-by-zero, resume-after-*) — and callers with
        // no message (kani::assert/check) — keep the assertion (panic) kind.
        let kind = match msg {
            Some(rustc_public::mir::AssertMessage::NullPointerDereference) => {
                PropertyKind::NullPointer
            }
            Some(rustc_public::mir::AssertMessage::MisalignedPointerDereference { .. }) => {
                PropertyKind::MemorySafety
            }
            _ => PropertyKind::Assertion,
        };
        // `--prove-safety-only`: check UB, not user panics. Kani classifies the
        // MIR asserts that land in the `Assertion` arm above — DivisionByZero,
        // RemainderByZero, Overflow, OverflowNeg, BoundsCheck, ResumedAfter* —
        // as `PropertyClass::Assertion` (kani-compiler codegen/statement.rs), and
        // `codegen_assert_assume` turns any Assertion-class check into a bare
        // `assume` under the flag (codegen/assert.rs). Only NullPointerDereference
        // and MisalignedPointerDereference are SafetyCheck and survive — which is
        // exactly the split the `kind` match above already computes.
        //
        // We honoured the flag only in the Kani-HOOK emitters (kani::assert/check,
        // Panic, Abort), never here, so `attempt to divide by zero` and overflow
        // checks from the MIR `Assert` terminator were still reported and the
        // harness FAILED where Kani reports SUCCESS.
        //
        // Skipping ONLY the error rule reproduces Kani's semantics exactly,
        // because the assume half already exists: the block-level caller emits a
        // separate guarded goto (`emit_guarded_goto_rule_shared`) carrying the
        // same condition, so the successor stays constrained by the assertion
        // instead of the check simply vanishing. That constraint is load-bearing
        // — it is what makes a subsequent `ptr.add(offset)` provably in bounds in
        // the harness this fixes.
        if self.prove_safety_only && matches!(kind, PropertyKind::Assertion) {
            debug!(
                ?bb_idx,
                "prove_safety_only: suppressing Assertion-class MIR assert (assume half retained)"
            );
            return;
        }
        // Kani-parity descriptions: the property Description line must carry
        // rustc's AssertKind text ("attempt to divide by zero", …) exactly as
        // Kani reports it, so expected-output matching sees the same line.
        let message = msg.and_then(kani_assert_message_description);
        let error_app = self.register_error_head(kind, bb_idx, message);
        let body = RuleBody::from_shared_base(
            Some(from_app.clone()),
            Arc::clone(shared_constraints),
            [violation],
        );
        self.vc.add_rule(Rule::new(body, error_app));
        debug!(?bb_idx, "emitted shared assertion error rule");
    }

    fn fn_ptr_assert_violation_obligation(&mut self, violation: Expr) -> Expr {
        if self.fn_ptr_ids.is_empty() || !expr_is_const_false(&violation) {
            return violation;
        }

        let marker = declare_pending_var(chc_fresh_name("__fn_ptr_assert_obligation"), Sort::int());
        marker.clone().int_add(Expr::int_const(1)).eq(marker)
    }

    /// Emits an error rule for kani::assert(cond).
    ///
    /// `kani::assert(cond)` generates: `from_rel(state) ∧ !cond → error()`
    ///
    /// Uses OUTPUT variables for locals modified in the current block (#656).
    pub(in crate::codegen_ay::chc) fn emit_kani_assert_error_rule(
        &mut self,
        from_app: &RelationApp,
        args: &[Operand],
        stmt_constraints: &[Expr],
        modified_locals: &HashSet<usize>,
        bb_idx: usize,
    ) {
        // kani::assert takes (cond: bool, message: &str)
        if args.is_empty() {
            self.emit_untranslatable_assert_rule(
                from_app,
                stmt_constraints,
                bb_idx,
                "kani::assert called with no args",
            );
            return;
        }

        // Debug: trace assertion condition (#1888)
        debug!("emit_kani_assert_error_rule: args[0]={:?}", args[0]);

        // Translate the condition using OUTPUT vars for modified locals (#656)
        let cond_expr =
            if let Some(expr) = self.translate_operand_with_modified(&args[0], modified_locals) {
                expr
            } else {
                self.emit_untranslatable_assert_rule(
                    from_app,
                    stmt_constraints,
                    bb_idx,
                    "cannot translate kani::assert condition operand",
                );
                debug!("emit_kani_assert_error_rule: translate_operand FAILED");
                return;
            };

        // Debug: trace cond_expr (#1888)
        debug!("emit_kani_assert_error_rule: cond_expr={}", cond_expr);

        // Convert to bool if needed
        let bool_cond = if let Some(e) = self.to_bool_expr(cond_expr, bb_idx) {
            e
        } else {
            self.emit_untranslatable_assert_rule(
                from_app,
                stmt_constraints,
                bb_idx,
                "kani::assert condition has unsupported sort",
            );
            debug!("emit_kani_assert_error_rule: to_bool_expr FAILED");
            return;
        };

        // Debug: trace bool_cond (#1888)
        debug!("emit_kani_assert_error_rule: bool_cond={}", bool_cond);

        // Violation occurs when cond is false
        let violation = simplify_bool_expr(bool_cond.not());

        // Build error rule: from_rel(state) ∧ stmt_constraints ∧ !cond → error()
        // BSEM-18: per-property error head for this kani::assert check.
        // Kani parity: `kani::assert(cond, "msg")` reports the user's message
        // string as the property Description; surface it when args[1] is a
        // const `&str` (the overwhelmingly common shape).
        let message = args.get(1).and_then(|arg| {
            let (bytes, _) = self.try_extract_const_str_bytes(arg)?;
            String::from_utf8(bytes).ok()
        });
        let error_app = self.register_error_head(PropertyKind::Assertion, bb_idx, message);
        let body =
            RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, [violation]);
        self.vc.add_rule(Rule::new(body, error_app));
        debug!(?bb_idx, "emitted kani::assert error rule");
    }

    /// Emits a conservative error rule when `kani::assert` condition translation fails.
    ///
    /// This prevents false PROOF results by making `error()` reachable whenever
    /// assertion semantics cannot be encoded.
    pub(in crate::codegen_ay::chc) fn emit_untranslatable_assert_rule(
        &mut self,
        from_app: &RelationApp,
        stmt_constraints: &[Expr],
        bb_idx: usize,
        reason: &'static str,
    ) {
        let from_app = self.refresh_block_relation_app(from_app);
        let count = self.diagnostics.assert_untranslatable.inc_get();
        warn!(
            ?bb_idx,
            reason = reason,
            count,
            "cannot encode assertion condition; emitting conservative error rule"
        );
        // BSEM-18: per-property head (fail-closed untranslatable assertion).
        let error_app =
            self.register_error_head(PropertyKind::Assertion, bb_idx, Some(reason.to_string()));
        // Part of #2267: allocation debt reduction — avoid stmt_constraints.to_vec().
        let body = RuleBody::from_base_and_extra(Some(from_app), stmt_constraints, []);
        self.vc.add_rule(Rule::new(body, error_app));
    }

    /// Shared-constraint variant of [`Self::emit_untranslatable_assert_rule`].
    ///
    /// Uses `RuleBody::from_shared_base` to avoid cloning the statement
    /// constraints when the caller already has an Arc-shared base. Part of #2507.
    pub(in crate::codegen_ay::chc) fn emit_untranslatable_assert_rule_shared(
        &mut self,
        from_app: &RelationApp,
        shared_constraints: &Arc<[Expr]>,
        bb_idx: usize,
        reason: &'static str,
    ) {
        let from_app = self.refresh_block_relation_app(from_app);
        let count = self.diagnostics.assert_untranslatable.inc_get();
        warn!(
            ?bb_idx,
            reason = reason,
            count,
            "cannot encode assertion condition; emitting conservative error rule"
        );
        // BSEM-18: per-property head (fail-closed untranslatable assertion).
        let error_app =
            self.register_error_head(PropertyKind::Assertion, bb_idx, Some(reason.to_string()));
        let body = RuleBody::from_shared_base(Some(from_app), Arc::clone(shared_constraints), []);
        self.vc.add_rule(Rule::new(body, error_app));
    }

    /// Emits a guarded transition rule for kani::assume(cond).
    ///
    /// `kani::assume(cond)` generates: `from_rel(state) ∧ cond → target_rel(state)`
    ///
    /// Uses OUTPUT variables for locals modified in the current block (#656).
    pub(in crate::codegen_ay::chc) fn emit_kani_assume_rule(
        &mut self,
        acx: &KaniAssumeContext<'_>,
    ) {
        let from_app = acx.from_app;
        let args = acx.args;
        let target = acx.target;
        let output_args = acx.output_args;
        let extra_constraints = acx.extra_constraints;
        let stmt_constraints = acx.stmt_constraints;
        let modified_locals = acx.modified_locals;
        let bb_idx = acx.bb_idx;
        // Debug: trace assume rule emission (#1889)
        debug!("emit_kani_assume_rule bb{} -> bb{}, args.len={}", bb_idx, target, args.len());
        // kani::assume takes (cond: bool)
        if args.is_empty() {
            self.emit_conservative_assume_fallback(
                from_app,
                target,
                stmt_constraints,
                bb_idx,
                "kani::assume called with no args",
            );
            return;
        }

        // Translate the condition using OUTPUT vars for modified locals (#656)
        let cond_expr =
            if let Some(expr) = self.translate_operand_with_modified(&args[0], modified_locals) {
                expr
            } else {
                self.emit_conservative_assume_fallback(
                    from_app,
                    target,
                    stmt_constraints,
                    bb_idx,
                    "cannot translate kani::assume condition",
                );
                return;
            };

        // Convert to bool if needed — clone sort for debug log before moving cond_expr
        let cond_sort = cond_expr.sort().clone();
        let bool_cond = if let Some(e) = self.to_bool_expr(cond_expr, bb_idx) {
            e
        } else {
            self.emit_conservative_assume_fallback(
                from_app,
                target,
                stmt_constraints,
                bb_idx,
                "cannot coerce kani::assume condition to bool",
            );
            debug!("emit_kani_assume_rule: to_bool_expr failed, sort={:?}", cond_sort);
            return;
        };
        debug!("emit_kani_assume_rule: bool_cond={:?}", bool_cond);
        debug!("emit_kani_assume_rule: stmt_constraints.len={}", stmt_constraints.len());
        for (i, c) in stmt_constraints.iter().enumerate() {
            debug!("  constraint[{}]={:?}", i, c);
        }

        // Get target relation
        let to_rel = if let Some(name) = self.block_relations.get(&target) {
            name.clone()
        } else {
            // Part of #3099: emit conservative error rule instead of silently
            // dropping the transition. The previous behavior (return with no
            // rule emitted) left the target block unreachable, making downstream
            // assertions vacuously true — genuinely unsound. The conservative
            // error rule emits from(state) -> error(), which is fail-closed:
            // if the path is reachable the solver reports FAILURE (safe), and
            // if unreachable the rule is vacuous (no effect).
            self.emit_conservative_assume_fallback(
                from_app,
                target,
                stmt_constraints,
                bb_idx,
                "kani::assume target block relation missing",
            );
            return;
        };

        // Part of #2214: Project output_args to target block's live set.
        let projected = self.project_full_output_to_block(target, output_args);
        let to_app = RelationApp::new(&to_rel, projected);

        // Build guarded transition: from_rel(state) ∧ stmt_constraints ∧ cond → target_rel(output_state)
        let body = RuleBody::from_base_and_extra(
            Some(from_app.clone()),
            stmt_constraints,
            std::iter::once(bool_cond).chain(extra_constraints.iter().cloned()),
        );
        self.vc.add_rule(Rule::new(body, to_app));
        debug!(?bb_idx, ?target, "emitted kani::assume guarded transition rule");
    }

    fn emit_conservative_assume_fallback(
        &mut self,
        from_app: &RelationApp,
        target: usize,
        stmt_constraints: &[Expr],
        bb_idx: usize,
        reason: &'static str,
    ) {
        let dropped = self.diagnostics.assume_dropped_transition.inc_get();
        warn!(
            ?bb_idx,
            ?target,
            reason,
            dropped_assume_semantics = dropped,
            "kani::assume guard dropped; emitting conservative error rule"
        );
        // BSEM-18: per-property head (fail-closed dropped-assume fallback).
        let error_app =
            self.register_error_head(PropertyKind::Assumption, bb_idx, Some(reason.to_string()));
        let body = RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, []);
        self.vc.add_rule(Rule::new(body, error_app));
    }

    /// Helper to convert an expression to boolean.
    pub(in crate::codegen_ay::chc) fn to_bool_expr(
        &self,
        expr: Expr,
        bb_idx: usize,
    ) -> Option<Expr> {
        if expr.sort().is_bool() {
            Some(simplify_bool_expr(expr))
        } else if let Some(width) = expr.sort().bitvec_width() {
            // For bitvectors, non-zero is true
            let zero = Expr::bitvec_const(0, width);
            Some(simplify_bool_expr(expr.eq(zero).not()))
        } else if expr.sort().is_int() {
            // For integers, non-zero is true
            let zero = Expr::int_const(0);
            Some(simplify_bool_expr(expr.eq(zero).not()))
        } else if expr.sort().is_datatype() {
            // Phase 3a (#2584): Handle Datatype sorts for assume/assert guards.
            // Enum-typed guards (e.g., assume(opt.is_some())) may arrive as DT exprs.
            self.dt_to_bool_expr(expr, bb_idx)
        } else {
            warn!(?bb_idx, sort = ?expr.sort(), "unsupported sort for condition");
            // Not counted here: all callers already increment their own counters
            // (assert_untranslatable, assume_dropped_transition, heap_check_untranslatable)
            // when to_bool_expr returns None. Adding a counter here would double-count.
            None
        }
    }

    /// Convert a Datatype expression to Bool.
    ///
    /// Handles three patterns:
    /// 1. **Option-like struct** with a Bool `is_some` field: extract it directly.
    /// 2. **Multi-constructor enum** (2+ ctors): if one ctor has fields and one
    ///    does not (option-like), test with `is_constructor` on the payload variant.
    /// 3. **Single-constructor struct**: extract field 0 and recursively convert.
    ///
    /// Part of #2584 (AssumeDroppedTransition).
    fn dt_to_bool_expr(&self, expr: Expr, bb_idx: usize) -> Option<Expr> {
        let SortInner::Datatype(dt) = expr.sort().inner() else {
            return None;
        };
        // Clone the DT metadata we need before consuming expr via move.
        let dt_name = dt.name.clone();
        let constructors = dt.constructors.clone();

        // Strategy 1: Look for a Bool-sorted field named "is_some" in any ctor.
        // This is the struct encoding of Option<T> where is_some is a Bool flag.
        for ctor in &constructors {
            if ctor.fields.iter().any(|f| f.name == "is_some" && f.sort.is_bool()) {
                debug!(
                    ?bb_idx,
                    dt_name = dt_name.as_str(),
                    "dt_to_bool_expr: using Bool is_some field"
                );
                return Some(expr.field_select(dt_name, "is_some", Sort::bool()));
            }
        }

        // Strategy 2: Multi-constructor enum — option-like pattern (one ctor with
        // fields, one without). Use `is_constructor` on the payload variant.
        if constructors.len() == 2 {
            let payload_ctors: Vec<_> =
                constructors.iter().filter(|c| !c.fields.is_empty()).collect();
            if payload_ctors.len() == 1 {
                let payload_ctor_name = payload_ctors[0].name.clone();
                debug!(
                    ?bb_idx,
                    dt_name = dt_name.as_str(),
                    payload_ctor = payload_ctor_name.as_str(),
                    "dt_to_bool_expr: option-like enum, testing payload constructor"
                );
                return Some(expr.is_constructor(dt_name, payload_ctor_name));
            }
        }

        // Strategy 3: Single-constructor struct — extract field 0 and recurse.
        if constructors.len() == 1 {
            let ctor = &constructors[0];
            if let Some(field) = ctor.fields.first() {
                let field_sort = field.sort.clone();
                let field_name = field.name.clone();
                debug!(
                    ?bb_idx,
                    dt_name = dt_name.as_str(),
                    field = field_name.as_str(),
                    field_sort = %field_sort,
                    "dt_to_bool_expr: single-ctor struct, extracting field 0"
                );
                let field_expr = expr.field_select(dt_name, field_name, field_sort);
                return self.to_bool_expr(field_expr, bb_idx);
            }
        }

        // No applicable strategy — fall through to None.
        warn!(
            ?bb_idx,
            dt_name = dt_name.as_str(),
            num_constructors = constructors.len(),
            "dt_to_bool_expr: no applicable conversion strategy"
        );
        None
    }
}

fn expr_is_const_false(expr: &Expr) -> bool {
    matches!(expr.value(), ExprValue::BoolConst(false))
        || trust_mc_core::chc_const_prop::eval::try_eval_to_const(expr)
            .is_some_and(|folded| matches!(folded.value(), ExprValue::BoolConst(false)))
}
