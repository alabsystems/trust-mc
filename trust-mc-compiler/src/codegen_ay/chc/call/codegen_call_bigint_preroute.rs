// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BigInt pre-route call handlers for CHC encoding.
//!
//! These handle real `num_bigint` library calls that bypass the normal
//! BigInt stub method table because they use path-based detection:
//! - `Sign::mul` — fieldless enum multiplication
//! - `BigInt::from_biguint` — signed construction from sign + magnitude
//! - `BigUint::set_zero` — receiver mutation to zero
//!
//! Part of #3687: close num_bigint internal helper gaps that caused
//! uninterpreted CHC predicates in the factorial proof path.

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::error;

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_rules::CodegenRules;
use super::stubs_option_helpers::OptionHelpers;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // === Path-based detectors ===

    pub(in crate::codegen_ay::chc) fn is_bigint_sign_mul_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func).as_deref().is_some_and(|path| {
            path.contains("num_bigint::Sign")
                && path.contains("ops::Mul")
                && path.ends_with("::mul")
        })
    }

    /// Part of #3687: detect `BigInt::from_biguint(Sign, BigUint) -> BigInt`.
    pub(in crate::codegen_ay::chc) fn is_bigint_from_biguint_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func)
            .as_deref()
            .is_some_and(|path| path.contains("BigInt") && path.ends_with("::from_biguint"))
    }

    /// Part of #3687: detect `BigUint::set_zero(&mut self)` or `BigInt::set_zero(&mut self)`.
    pub(in crate::codegen_ay::chc) fn is_bigint_set_zero_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func).as_deref().is_some_and(|path| {
            (path.contains("BigUint") || path.contains("BigInt")) && path.ends_with("::set_zero")
        })
    }

    // === Handlers ===

    /// Handle `num_bigint::Sign * Sign` directly as a fieldless-enum BV operation.
    pub(in crate::codegen_ay::chc) fn codegen_call_bigint_sign_mul(
        &mut self,
        cx: &ChcCallContext<'_>,
    ) {
        let dest_local: usize = cx.destination.local;
        let Some(lhs) = cx
            .args
            .first()
            .and_then(|arg| self.translate_operand_with_modified(arg, cx.modified_locals))
        else {
            self.emit_bigint_fail_closed(cx, "CHC: Sign::mul lhs translation failed");
            return;
        };
        let Some(rhs) = cx
            .args
            .get(1)
            .and_then(|arg| self.translate_operand_with_modified(arg, cx.modified_locals))
        else {
            self.emit_bigint_fail_closed(cx, "CHC: Sign::mul rhs translation failed");
            return;
        };
        let (Some(lhs_width), Some(rhs_width)) =
            (lhs.sort().bitvec_width(), rhs.sort().bitvec_width())
        else {
            self.emit_bigint_fail_closed(cx, "CHC: Sign::mul expects bitvec enum operands");
            return;
        };

        let width = lhs_width.max(rhs_width);
        let lhs = coerce_bitvec_width_safe(lhs, width, SignExtension::ZeroExtend);
        let rhs = coerce_bitvec_width_safe(rhs, width, SignExtension::ZeroExtend);
        // `num_bigint::Sign` is encoded with sequential fieldless-enum discriminants:
        // Minus=0, NoSign=1, Plus=2.
        let minus = Expr::bitvec_const(0u64, width);
        let no_sign = Expr::bitvec_const(1u64, width);
        let plus = Expr::bitvec_const(2u64, width);
        let result = Expr::ite(
            lhs.clone().eq(no_sign.clone()).or(rhs.clone().eq(no_sign.clone())),
            no_sign,
            Expr::ite(lhs.eq(rhs), plus, minus),
        );

        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            self.emit_bigint_fail_closed(cx, "CHC: Sign::mul destination has no output slot");
            return;
        };
        let out_sort = dest_var.sort();
        let Some(eq) = self.make_coerced_eq_constraint(
            &dest_var,
            result,
            out_sort,
            dest_local,
            "codegen_call_bigint_sign_mul",
        ) else {
            self.emit_bigint_fail_closed(cx, "CHC: Sign::mul destination sort mismatch");
            return;
        };

        let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            [eq],
        );
    }

    /// Part of #3687: Handle `BigInt::from_biguint(Sign, BigUint) -> BigInt`.
    ///
    /// In the SMT Int model:
    /// - Sign is a fieldless enum BV (Minus=0, NoSign=1, Plus=2)
    /// - BigUint data is Int (non-negative magnitude)
    /// - Result: if Minus → -data, if NoSign → 0, if Plus → data
    pub(in crate::codegen_ay::chc) fn codegen_call_bigint_from_biguint(
        &mut self,
        cx: &ChcCallContext<'_>,
    ) {
        let dest_local: usize = cx.destination.local;
        // args[0] = Sign (BV enum), args[1] = BigUint (Int)
        let Some(sign_expr) = cx
            .args
            .first()
            .and_then(|arg| self.translate_operand_with_modified(arg, cx.modified_locals))
        else {
            self.emit_bigint_fail_closed(cx, "CHC: from_biguint sign translation failed");
            return;
        };
        let data_expr = cx
            .args
            .get(1)
            .and_then(|arg| self.get_bigint_arg(arg, cx.modified_locals))
            .unwrap_or_else(|| Expr::int_const(0));

        // Sign::Minus=0 → negate, Sign::NoSign=1 → zero, Sign::Plus=2 → identity
        let result = if let Some(width) = sign_expr.sort().bitvec_width() {
            let minus = Expr::bitvec_const(0u64, width);
            let no_sign = Expr::bitvec_const(1u64, width);
            Expr::ite(
                sign_expr.clone().eq(minus),
                data_expr.clone().int_neg(),
                Expr::ite(sign_expr.eq(no_sign), Expr::int_const(0), data_expr),
            )
        } else if sign_expr.sort().is_int() {
            Expr::ite(
                sign_expr.clone().eq(Expr::int_const(0)),
                data_expr.clone().int_neg(),
                Expr::ite(sign_expr.eq(Expr::int_const(1)), Expr::int_const(0), data_expr),
            )
        } else {
            self.record_sound_fallback_reason("bigint_abs_sign_unresolved");
            data_expr
        };

        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            self.emit_bigint_fail_closed(cx, "CHC: from_biguint destination has no output slot");
            return;
        };
        let out_sort = dest_var.sort();
        let Some(eq) = self.make_coerced_eq_constraint(
            &dest_var,
            result,
            out_sort,
            dest_local,
            "codegen_call_bigint_from_biguint",
        ) else {
            self.emit_bigint_fail_closed(cx, "CHC: from_biguint destination sort mismatch");
            return;
        };

        let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            [eq],
        );
    }

    /// Part of #3687: Handle `BigUint::set_zero(&mut self)` / `BigInt::set_zero(&mut self)`.
    ///
    /// Writes `int_const(0)` to the receiver local (args[0] reference target).
    pub(in crate::codegen_ay::chc) fn codegen_call_bigint_set_zero(
        &mut self,
        cx: &ChcCallContext<'_>,
    ) {
        if let Some(Operand::Copy(place) | Operand::Move(place)) = cx.args.first() {
            let ref_local: usize = place.local;
            let target_local = self
                .ref_resolution
                .bigint_ref_targets
                .get(&ref_local)
                .copied()
                .unwrap_or(ref_local);
            if let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(target_local).cloned()
            {
                let dest_var = Expr::var(&*out_name, out_sort.clone());
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    Expr::int_const(0),
                    &out_sort,
                    target_local,
                    "codegen_call_bigint_set_zero",
                );
                let new_output_args = self.build_output_args(cx.modified_locals, &[target_local]);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    eq,
                );
                return;
            }
        }
        // Fallback: receiver not resolvable, emit plain goto (value stays identity).
        // Part of #3745: Reclassified SOUND_APPROXIMATION → DEMOTED.
        // Identity semantics (old value preserved) is under-approximation, not
        // sound over-approximation.
        self.record_fallback();
        let new_output_args = self.build_output_args(cx.modified_locals, &[]);
        self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
    }

    // === Shared helpers ===

    pub(in crate::codegen_ay::chc) fn emit_bigint_fail_closed(
        &mut self,
        cx: &ChcCallContext<'_>,
        message: &'static str,
    ) {
        let count = self.diagnostics.bigint_unsound_skip.inc_get();
        error!("{message} (hit #{count})");
        // Sound over-approximation: leave destination unconstrained rather than
        // killing the transition with `false` (which is vacuously true in CHC).
        let new_output_args = self.build_output_args(cx.modified_locals, &[cx.destination.local]);
        self.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            [],
        );
        self.record_sound_fallback_reason("bigint_fail_closed");
    }

    pub(in crate::codegen_ay::chc) fn try_emit_bigint_partial_cmp_flattened_destination(
        &mut self,
        ordering_int: Expr,
        cx: &ChcCallContext<'_>,
        biguint_guard: Option<Expr>,
    ) -> bool {
        let dest_local = cx.destination.local;
        if cx.stub != StubKind::BigIntPartialCmp
            || !self.flatten.flattened_tuple_locals.contains(&dest_local)
            || self.flattened_field_count(dest_local) < 2
        {
            return false;
        }

        let Some(vec_idx) = self.try_state_idx_for_local(dest_local) else {
            return false;
        };
        let mut constraints = Vec::new();

        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
        {
            let is_some_var = Expr::var(&*out_name, out_sort.clone());
            let is_some_val = if out_sort.is_bool() {
                Expr::bool_const(true)
            } else {
                Expr::bitvec_const(1u64, out_sort.bitvec_width().unwrap_or(1))
            };
            self.encode.flattened_field_env.insert((dest_local, 0), is_some_val.clone());
            constraints.push(is_some_var.eq(is_some_val));
        }

        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(vec_idx + 1).cloned()
        {
            let payload_var = Expr::var(&*out_name, out_sort.clone());
            let payload_value = match out_sort.bitvec_width() {
                Some(width) => self.convert_ordering_int_to_bv(ordering_int, width),
                None if out_sort.is_int() => ordering_int,
                None => {
                    return false;
                }
            };
            self.encode.flattened_field_env.insert((dest_local, 1), payload_value.clone());
            constraints.push(payload_var.eq(payload_value));
        }

        if constraints.is_empty() {
            return false;
        }

        let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            biguint_guard.into_iter().chain(constraints),
        );
        true
    }
}
