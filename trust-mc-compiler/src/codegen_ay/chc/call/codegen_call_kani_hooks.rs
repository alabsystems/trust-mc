// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Per-group Kani hook handlers: assertion, safety-check, and utility hooks.
//!
//! Each handler corresponds to a logical group of `KaniHook` variants:
//! - Assert/Check: emit error rule for condition violation
//! - Safety checks: combined assert+assume or assert-only
//! - Panic/Unsupported: unconditional error for unsupported checks, optional panic suppression
//! - No-op transitions: Cover, InitContracts, etc.
//!
//! Pointer-query hooks (`IsAllocated`, `PointerObject`, `PointerOffset`) live
//! in `codegen_call_kani_hooks_pointer`. Nondet/quantifier/validity-bound hooks
//! (`AnyRaw`, `Forall`/`Exists`, discriminant/char bounds) live in
//! `codegen_call_kani_hooks_model`.

use ay_bindings::Expr;
use tracing::debug;

use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_expr_assert::KaniAssumeContext;
use super::codegen_rules::CodegenRules;
use super::{ChcCtx, RelationApp, Rule, RuleBody};
use trust_mc_core::violation::PropertyKind;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle `KaniHook::Assert | KaniHook::Check`: emit error rule for `!cond`.
    ///
    /// Part of #4217: When `prove_safety_only` is true, user assertions are
    /// converted to assumptions — the assertion condition guards the successor
    /// transition (like `kani::assume`) and no error rule is emitted. This
    /// preserves the constraint from the assertion while not treating violation
    /// as an error.
    pub(in crate::codegen_ay::chc) fn hook_assert_check(&mut self, dcx: &DispatchCallContext<'_>) {
        let bb_idx = dcx.bb_idx;
        let from_app = dcx.from_app;
        let stmt_constraints = dcx.stmt_constraints;
        let modified_locals = dcx.modified_locals;

        if let Some(target) = dcx.target {
            if let Some(bool_cond) = dcx
                .args
                .first()
                .and_then(|cond| self.translate_assert_condition(cond, modified_locals, bb_idx))
            {
                let new_output_args =
                    self.build_output_args(modified_locals, &[dcx.destination.local]);
                self.emit_guarded_goto_rule(
                    from_app,
                    *target,
                    &new_output_args,
                    stmt_constraints,
                    bool_cond,
                );
            } else {
                // Part of #3099: reclassified from record_fallback() (DEMOTED)
                // to record_sound_fallback() (SOUND_APPROXIMATION).
                // Assert condition translation failed — the success transition
                // proceeds without the assertion guard. However, emit_kani_assert_error_rule
                // (called unconditionally below unless prove_safety_only) emits a
                // conservative `from → error()` rule that prevents false PROOF: if this
                // block is reachable, the solver reports FAILURE. The conservative error
                // rule is strictly more conservative than the correct assertion encoding.
                emit_sound_fallback_goto(
                    self,
                    from_app,
                    *target,
                    modified_locals,
                    &[dcx.destination.local],
                    stmt_constraints,
                );
            }
        } else {
            self.record_diverging_call_drop(dcx.func, Some(bb_idx), "kani_hook::Assert", None);
        }
        // Part of #4217: Skip user assertion error rule in prove_safety_only mode.
        // The assertion condition is already a guard on the successor transition
        // (emitted above), acting as an assumption. We do not emit an error rule
        // because user assertions are not safety checks.
        if !self.prove_safety_only {
            self.emit_kani_assert_error_rule(
                from_app,
                dcx.args,
                stmt_constraints,
                modified_locals,
                bb_idx,
            );
        }
    }

    /// Handle `KaniHook::Assume`: emit guarded transition with condition.
    pub(in crate::codegen_ay::chc) fn hook_assume(&mut self, dcx: &DispatchCallContext<'_>) {
        let bb_idx = dcx.bb_idx;
        debug!(
            "KaniHook::Assume matched in bb{}, target={:?}, args.len={}",
            bb_idx,
            dcx.target,
            dcx.args.len()
        );
        if let Some(target) = dcx.target {
            let dest_local = dcx.destination.local;
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            let dest_constraints = self
                .canonical_zst_call_dest_constraint(dest_local, "kani_hook::Assume::zst_dest")
                .into_iter()
                .collect::<Vec<_>>();
            let assume_cx = KaniAssumeContext {
                from_app: dcx.from_app,
                args: dcx.args,
                target: *target,
                output_args: &new_output_args,
                extra_constraints: &dest_constraints,
                stmt_constraints: dcx.stmt_constraints,
                modified_locals: dcx.modified_locals,
                bb_idx,
            };
            self.emit_kani_assume_rule(&assume_cx);
        } else {
            self.record_diverging_call_drop(dcx.func, Some(bb_idx), "kani_hook::Assume", None);
        }
    }

    /// Handle `KaniHook::SafetyCheck`: assert(cond) + assume(cond).
    ///
    /// Part of #9271: When the condition is untranslatable, emit a conservative
    /// `from -> error()` rule and still keep the successor reachable. This is
    /// fail-closed: "cannot check safety" must not become PROOF.
    /// Extract the human-readable message a `kani::safety_check(cond, msg)`
    /// carries in `args[1]`, when it is a const `&str` (the shape every
    /// in-tree emitter uses). Mirrors `emit_kani_assert_error_rule`.
    fn safety_check_message(
        &mut self,
        args: &[rustc_public::mir::Operand],
    ) -> Option<String> {
        let (bytes, _) = self.try_extract_const_str_bytes(args.get(1)?)?;
        String::from_utf8(bytes).ok()
    }

    pub(in crate::codegen_ay::chc) fn hook_safety_check(&mut self, dcx: &DispatchCallContext<'_>) {
        let bb_idx = dcx.bb_idx;
        let from_app = dcx.from_app;
        let stmt_constraints = dcx.stmt_constraints;
        let modified_locals = dcx.modified_locals;

        // Pre-translate the condition to decide error rule strategy.
        let cond_bool = dcx
            .args
            .first()
            .and_then(|cond| self.translate_assert_condition(cond, modified_locals, bb_idx));

        if let Some(ref bool_cond) = cond_bool {
            // Condition translatable — emit proper error rule: from ∧ !cond → error()
            let violation = bool_cond.clone().not();
            // BSEM-18: per-property head for this safety check.
            // `kani::safety_check(cond, "msg")` carries its message in
            // args[1], exactly like `kani::assert`. Dropping it made every
            // loop-contract obligation (invariant base case, inductive step,
            // decreases ranking) surface as a bare "CHC verification: memory
            // safety" with no Description — indistinguishable from a real
            // memory-safety failure, and from each other. Surface it.
            let message = self.safety_check_message(dcx.args);
            let error_app =
                self.register_error_head(PropertyKind::MemorySafety, bb_idx, message);
            let body = RuleBody::from_base_and_extra(
                Some(from_app.clone()),
                stmt_constraints,
                [violation],
            );
            self.vc.add_rule(Rule::new(body, error_app));
            debug!(?bb_idx, "emitted safety check error rule");
        } else {
            self.emit_untranslatable_assert_rule(
                from_app,
                stmt_constraints,
                bb_idx,
                "untranslatable kani::safety_check condition",
            );
        }

        if let Some(target) = dcx.target {
            let new_output_args = self.build_output_args(modified_locals, &[dcx.destination.local]);
            if let Some(bool_cond) = cond_bool {
                // Condition translatable — emit guarded transition: from ∧ cond → target
                self.emit_guarded_goto_rule(
                    from_app,
                    *target,
                    &new_output_args,
                    stmt_constraints,
                    bool_cond,
                );
            } else {
                // Condition untranslatable — emit unconditional transition.
                self.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
            }
        } else {
            self.record_diverging_call_drop(dcx.func, Some(bb_idx), "kani_hook::SafetyCheck", None);
        }
    }

    /// Handle `KaniHook::SafetyCheckNoAssume`: assert only (no assume).
    ///
    /// Part of #9271: Same fail-closed strategy as `hook_safety_check` when the
    /// condition is untranslatable. Because this is no-assume, the successor
    /// transition remains unguarded even when the condition translates.
    pub(in crate::codegen_ay::chc) fn hook_safety_check_no_assume(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) {
        let bb_idx = dcx.bb_idx;
        let from_app = dcx.from_app;
        let stmt_constraints = dcx.stmt_constraints;
        let modified_locals = dcx.modified_locals;

        // Pre-translate the condition to decide error rule strategy.
        let cond_bool = dcx
            .args
            .first()
            .and_then(|cond| self.translate_assert_condition(cond, modified_locals, bb_idx));

        if let Some(ref bool_cond) = cond_bool {
            // Condition translatable — emit proper error rule: from ∧ !cond → error()
            let violation = bool_cond.clone().not();
            // BSEM-18: per-property head for this safety check.
            // `kani::safety_check(cond, "msg")` carries its message in
            // args[1], exactly like `kani::assert`. Dropping it made every
            // loop-contract obligation (invariant base case, inductive step,
            // decreases ranking) surface as a bare "CHC verification: memory
            // safety" with no Description — indistinguishable from a real
            // memory-safety failure, and from each other. Surface it.
            let message = self.safety_check_message(dcx.args);
            let error_app =
                self.register_error_head(PropertyKind::MemorySafety, bb_idx, message);
            let body = RuleBody::from_base_and_extra(
                Some(from_app.clone()),
                stmt_constraints,
                [violation],
            );
            self.vc.add_rule(Rule::new(body, error_app));
            debug!(?bb_idx, "emitted safety check (no assume) error rule");
        } else {
            self.emit_untranslatable_assert_rule(
                from_app,
                stmt_constraints,
                bb_idx,
                "untranslatable kani::safety_check_no_assume condition",
            );
        }

        if let Some(target) = dcx.target {
            let new_output_args = self.build_output_args(modified_locals, &[dcx.destination.local]);
            self.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
        } else {
            self.record_diverging_call_drop(
                dcx.func,
                Some(bb_idx),
                "kani_hook::SafetyCheckNoAssume",
                None,
            );
        }
    }

    /// Handle `KaniHook::Panic`: unconditional error unless user panics are suppressed.
    ///
    /// Part of #4217: Skip error rule in `prove_safety_only` mode. Aborts from
    /// user assertions (assert, explicit abort) are not safety checks — they
    /// should be suppressed when only proving safety properties. The goto
    /// transition to the successor block is still emitted so control flow
    /// continues (matching the "assertion becomes assumption" semantics).
    pub(in crate::codegen_ay::chc) fn hook_panic(&mut self, dcx: &DispatchCallContext<'_>) {
        let from_app = dcx.from_app;
        let stmt_constraints = dcx.stmt_constraints;

        if !self.prove_safety_only {
            self.emit_unconditional_error_rule(
                from_app,
                stmt_constraints,
                PropertyKind::Panic,
                dcx.bb_idx,
            );
        }

        if let Some(target) = dcx.target {
            let new_output_args =
                self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
            self.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
        }
    }

    /// Handle `KaniHook::UnsupportedCheck`: conservative unconditional error.
    ///
    /// Unsupported checks represent compiler-inserted "cannot check safety"
    /// conditions, not user assertions. They remain fail-closed even when
    /// `prove_safety_only` suppresses user panics.
    ///
    /// P3-uninit: the hook's message operand (`kani::unsupported(message)`)
    /// is plumbed into the per-property metadata so the reported check
    /// description matches Kani's text (e.g. "Kani currently doesn't support
    /// checking memory initialization for pointers to `E1...`").
    pub(in crate::codegen_ay::chc) fn hook_unsupported_check(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) {
        let from_app = dcx.from_app;
        let stmt_constraints = dcx.stmt_constraints;
        let message = dcx.args.iter().find_map(const_str_from_operand);
        self.emit_unconditional_error_rule_with_message(
            from_app,
            stmt_constraints,
            PropertyKind::UndefinedBehavior,
            dcx.bb_idx,
            message,
        );

        if let Some(target) = dcx.target {
            let new_output_args =
                self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
            self.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
        }
    }

    fn emit_unconditional_error_rule(
        &mut self,
        from_app: &RelationApp,
        stmt_constraints: &[Expr],
        kind: PropertyKind,
        bb_idx: usize,
    ) {
        self.emit_unconditional_error_rule_with_message(
            from_app,
            stmt_constraints,
            kind,
            bb_idx,
            None,
        );
    }

    fn emit_unconditional_error_rule_with_message(
        &mut self,
        from_app: &RelationApp,
        stmt_constraints: &[Expr],
        kind: PropertyKind,
        bb_idx: usize,
        message: Option<String>,
    ) {
        // BSEM-18: per-property head for this unconditional panic/unsupported check.
        let error_app = self.register_error_head(kind, bb_idx, message);
        let body = RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, []);
        self.vc.add_rule(Rule::new(body, error_app));
    }

    /// Handle `KaniHook::Cover`: emit cover property declaration and transition.
    ///
    /// Part of #1162: In CHC mode, cover properties cannot be encoded as
    /// assertion violations (CHC UNSAT = property holds). Instead, we record
    /// the cover condition as a `(declare-const ay_cover_N Bool)` +
    /// `(assert (= ay_cover_N condition))` pair. The driver's secondary SAT
    /// check evaluates each cover predicate independently.
    pub(in crate::codegen_ay::chc) fn hook_cover(&mut self, dcx: &DispatchCallContext<'_>) {
        let bb_idx = dcx.bb_idx;

        // Translate the cover condition and register it as a cover assertion.
        if let Some(cond) = dcx
            .args
            .first()
            .and_then(|arg| self.translate_assert_condition(arg, dcx.modified_locals, bb_idx))
        {
            let cover_id = self.vc.cover_assertions.len();
            let name = format!("ay_cover_{cover_id}");
            debug!(?bb_idx, cover_name = %name, "CHC: emitting cover property declaration");
            self.vc.add_cover_assertion(name, cond);
        } else {
            debug!(?bb_idx, "CHC: cover condition untranslatable, skipping cover property");
        }

        // Cover is still a pass-through for control flow — emit goto to target.
        if let Some(target) = dcx.target {
            let new_output_args =
                self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
            self.emit_goto_rule(dcx.from_app, *target, &new_output_args, dcx.stmt_constraints);
        } else {
            self.record_diverging_call_drop(dcx.func, Some(dcx.bb_idx), "kani_hook::Cover", None);
        }
    }

    /// Handle no-op hooks: `InitContracts`, `ValueView`, `UntrackedDeref`.
    pub(in crate::codegen_ay::chc) fn hook_noop_transition(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        label: &'static str,
    ) {
        if let Some(target) = dcx.target {
            let new_output_args =
                self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
            self.emit_goto_rule(dcx.from_app, *target, &new_output_args, dcx.stmt_constraints);
        } else {
            self.record_diverging_call_drop(dcx.func, Some(dcx.bb_idx), label, None);
        }
    }

    pub(in crate::codegen_ay::chc) fn canonical_zst_call_dest_constraint(
        &mut self,
        dest_local: usize,
        site: &'static str,
    ) -> Option<Expr> {
        let dest_ty = self.body.locals()[dest_local].ty;
        if !super::codegen_call_kani_model_dst::is_zst_ty(dest_ty) {
            return None;
        }
        let dest_vec_idx = self.try_state_idx_for_local(dest_local)?;
        let (out_name, out_sort) =
            self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()?;
        let canonical = super::codegen_call_kani_model_zst::canonical_zst_expr(dest_ty)?;
        let dest_var = Expr::var(&*out_name, out_sort.clone());
        self.make_coerced_eq_constraint(&dest_var, canonical, &out_sort, dest_local, site)
    }
}

/// Extract a `&str` constant operand's contents (P3-uninit).
///
/// Follows the fat-pointer allocation's provenance to the string bytes,
/// mirroring the BMC-side `try_extract_str_constant` (operand_ref.rs). Used
/// to plumb `kani::unsupported(message)` into the property description.
fn const_str_from_operand(operand: &rustc_public::mir::Operand) -> Option<String> {
    use rustc_public::mir::alloc::GlobalAlloc;
    use rustc_public::mir::{ConstOperand, Operand};
    use rustc_public::ty::{ConstantKind, RigidTy, TyConstKind, TyKind};

    let ConstOperand { const_: mir_const, .. } = match operand {
        Operand::Constant(c) => c,
        _ => return None, // external enum: Operand
    };

    let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _)) = mir_const.ty().kind() else {
        return None; // external enum: TyKind
    };
    if !matches!(pointee_ty.kind(), TyKind::RigidTy(RigidTy::Str)) {
        return None;
    }

    let alloc = match mir_const.kind() {
        ConstantKind::Allocated(alloc) => alloc.clone(),
        ConstantKind::Ty(ty_const) => match ty_const.kind() {
            TyConstKind::Value(_, alloc) => alloc.clone(),
            _ => return None, // external enum: TyConstKind
        },
        _ => return None, // external enum: ConstantKind
    };

    // Fat pointer layout: [data_ptr (with provenance), len].
    let (_, prov) = alloc.provenance.ptrs.first()?;
    let target_alloc = match GlobalAlloc::from(prov.0) {
        GlobalAlloc::Memory(target) => target,
        _ => return None, // external enum: GlobalAlloc
    };

    let ptr_bytes = crate::codegen_ay::types::POINTER_WIDTH as usize / 8;
    let len_bytes = alloc.bytes.get(ptr_bytes..ptr_bytes * 2)?;
    let mut len_value: usize = 0;
    for (i, byte) in len_bytes.iter().take(ptr_bytes).enumerate() {
        len_value |= (*(byte.as_ref()?) as usize) << (i * 8);
    }

    let str_bytes: Vec<u8> = target_alloc.bytes.iter().take(len_value).filter_map(|b| *b).collect();
    if str_bytes.len() != len_value {
        return None;
    }
    String::from_utf8(str_bytes).ok()
}
