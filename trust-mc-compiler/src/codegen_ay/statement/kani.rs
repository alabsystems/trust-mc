// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Kani verification intrinsic handlers.
//!
//! This module contains codegen for Kani-specific verification primitives:
//! - `kani::any_raw` / `kani::any` - creates fresh symbolic variables
//! - `kani::assume` - adds path constraints
//! - `kani::assert` - records verification violations
//! - `kani::cover` - reachability checks
//! - `kani::float::float_to_int_in_range` - see `kani_float.rs` (#1369, #3840)
//!
//! Part of #718 - statement module refactoring.

use std::sync::Arc;

use crate::kani_middle::abi::LayoutOf;
use ay_bindings::{Expr, Sort, SortInner};
use rustc_public::CrateDef;
use rustc_public::mir::{Operand, Place};
use rustc_public::ty::{AdtKind, GenericArgKind, RigidTy, Ty, TyKind};
use tracing::{debug, warn};

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen kani::any_raw - creates a fresh symbolic variable.
    pub(super) fn codegen_kani_any_raw(&mut self, destination: &Place) {
        let base_name = self.ssa_base_name(destination);
        // Bump SSA version even though we use a dedicated any var name.
        let _ssa_name = self.ssa_name_from_base(&base_name, true);
        let ty = destination.ty(self.body.locals()).into_option();
        if let Some(ty) = ty {
            // #408: ZST types need no SMT variable - they're phantom values.
            // ZST types are phantom values — no SMT variable needed.
            if Self::is_zst_type(ty) {
                debug!("codegen_kani_any_raw: ZST type {:?}, returning phantom (no SMT var)", ty);
                // ZST has exactly one value - no symbolic variable needed.
                // Don't add to env - assignments to ZST places are also skipped.
                return;
            }

            if let TyKind::RigidTy(RigidTy::Array(elem_ty, len)) = ty.kind()
                && let (Some(len), Some(elem_sort)) =
                    (len.eval_target_usize().into_option(), Self::infer_sort_from_ty(elem_ty))
            {
                let base_array_name = self.ctx.fresh_name("ay_any_array");
                let array_sort = Sort::array(ptr_sort(), elem_sort);
                let mut array_expr = self.ctx.declare_var(&base_array_name, array_sort);
                for idx in 0..len {
                    // Use helper to add discriminant constraints for nested enum elements (#448)
                    let elem_expr = self.create_constrained_symbolic(elem_ty, "ay_any");
                    let idx_expr = Expr::bitvec_const(idx as i128, POINTER_WIDTH);
                    array_expr = array_expr.store(idx_expr, elem_expr);
                }
                self.env_update(base_name, array_expr);
                return;
            }
            // Handle tuple types with flattening optimization (#398).
            // Instead of creating a single ADT variable, create N field variables.
            if let TyKind::RigidTy(RigidTy::Tuple(tys)) = ty.kind()
                && !tys.is_empty()
            {
                let mut field_exprs = Vec::with_capacity(tys.len());
                for field_ty in &tys {
                    // Use helper to add discriminant constraints for nested enum fields (#448)
                    let field_expr = self.create_constrained_symbolic(*field_ty, "ay_any");
                    field_exprs.push(field_expr);
                }
                // Store flattened tuple fields for later Field projection lookup
                self.flattened_tuples.insert(Arc::from(base_name), field_exprs);
                // Don't store anything in current_env - Field projection will use flattened_tuples
                return;
            }
            // Handle enum types: add discriminant validity constraints (#442).
            // Unit enums (all variants have no fields) are encoded as bitvectors,
            // and we must constrain the symbolic value to valid discriminant range.
            if let TyKind::RigidTy(RigidTy::Adt(def, _args)) = ty.kind()
                && def.kind() == AdtKind::Enum
            {
                let variants = def.variants();
                let num_variants = variants.len();
                // Check if this is a unit enum (all variants have no fields)
                let is_unit_enum = variants.iter().all(|v| v.fields().is_empty());

                if is_unit_enum && num_variants > 0 {
                    // For unit enums, the value IS the discriminant.
                    // Bug fix (#1393): Use 32 bits to match sort_inference.rs.
                    let bits = if num_variants <= 65536 { 32 } else { 64 };
                    let dest_name = self.ctx.fresh_name("ay_any");
                    let sort = Sort::bitvec(bits);
                    let expr = self.ctx.declare_var(&dest_name, sort);
                    self.ctx.record_kani_any_var(expr.clone());

                    // Add discriminant validity constraint: value < num_variants
                    // This prevents invalid discriminant values from causing spurious failures.
                    let upper_bound = Expr::bitvec_const(num_variants as i128, bits);
                    let validity_constraint = expr.clone().bvult(upper_bound);
                    self.ctx.assert(validity_constraint);
                    debug!(
                        "codegen_kani_any_raw: enum {} with {} variants, added discriminant constraint",
                        def.name(),
                        num_variants
                    );

                    self.env_update(base_name, expr);
                    return;
                }
            }
        }

        let dest_name = self.ctx.fresh_name("ay_any");
        let sort = self.infer_sort_from_place(destination).unwrap_or_else(|| Sort::bitvec(32));
        let expr = self.ctx.declare_var(&dest_name, sort);
        self.ctx.record_kani_any_var(expr.clone());
        if let Some(ty) = ty {
            self.assert_scalar_validity_for_ty(ty, expr.clone());
        }
        self.env_update(base_name, expr);
    }

    /// Creates a symbolic variable for a type, adding discriminant constraints
    /// if the type is a unit enum (#448). This prevents invalid discriminant values
    /// in nested contexts like arrays and tuples.
    #[must_use]
    pub(super) fn create_constrained_symbolic(
        &mut self,
        ty: rustc_public::ty::Ty,
        name_prefix: &str,
    ) -> Expr {
        // Check if type is a unit enum that needs discriminant constraints
        if let TyKind::RigidTy(RigidTy::Adt(def, _args)) = ty.kind()
            && def.kind() == AdtKind::Enum
        {
            let variants = def.variants();
            let num_variants = variants.len();
            let is_unit_enum = variants.iter().all(|v| v.fields().is_empty());

            if is_unit_enum && num_variants > 0 {
                // For unit enums, the value IS the discriminant.
                // Bug fix (#1393): Use 32 bits to match sort_inference.rs.
                let bits = if num_variants <= 65536 { 32 } else { 64 };
                let name = self.ctx.fresh_name(name_prefix);
                let sort = Sort::bitvec(bits);
                let expr = self.ctx.declare_var(&name, sort);
                self.ctx.record_kani_any_var(expr.clone());

                // Add discriminant validity constraint: value < num_variants
                let upper_bound = Expr::bitvec_const(num_variants as i128, bits);
                let validity_constraint = expr.clone().bvult(upper_bound);
                self.ctx.assert(validity_constraint);
                debug!(
                    "create_constrained_symbolic: nested enum {} with {} variants, added discriminant constraint",
                    def.name(),
                    num_variants
                );

                return expr;
            }
        }

        // Default: create unconstrained symbolic variable
        let sort = Self::infer_sort_from_ty(ty).unwrap_or_else(|| Sort::bitvec(32));
        let name = self.ctx.fresh_name(name_prefix);
        let expr = self.ctx.declare_var(&name, sort);
        self.ctx.record_kani_any_var(expr.clone());
        self.assert_scalar_validity_for_ty(ty, expr.clone());
        expr
    }

    pub(super) fn codegen_kani_write_any_slim(&mut self, args: &[Operand]) -> bool {
        let Some(pointer_arg) = args.first() else {
            return false;
        };
        let Some(pointer_expr) = self.codegen_operand(pointer_arg) else {
            return false;
        };
        let Some(pointee_ty) = Self::operand_pointee_ty(pointer_arg, self.body.locals()) else {
            return false;
        };
        if LayoutOf::new(pointee_ty).size_of() == Some(0) {
            return true;
        }

        let fresh = self.create_constrained_symbolic(pointee_ty, "ay_write_any");
        let pointer = self.resolve_concrete_expr(&self.coerce_to_ptr_width(pointer_expr));
        self.ctx.store_memory_bytes(pointer.clone(), fresh.clone());
        self.update_addressed_local_after_write_any(&pointer, fresh);
        true
    }

    fn operand_pointee_ty(
        operand: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> Option<Ty> {
        let ty = operand.ty(locals).into_option()?;
        match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
            | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Some(pointee),
            _ => None,
        }
    }

    fn update_addressed_local_after_write_any(&mut self, pointer: &Expr, fresh: Expr) {
        let Some((base, _addr)) = self
            .addr_symbols
            .iter()
            .find(|(_base, addr)| *addr == pointer)
            .map(|(base, addr)| (std::sync::Arc::<str>::clone(base), addr.clone()))
        else {
            return;
        };

        let ssa_name = self.ssa_name_from_base(&base, true);
        let ssa_var = self.ctx.declare_var(&ssa_name, fresh.sort().clone());
        self.assert_ssa_def(ssa_var.clone(), fresh.clone(), &base);
        self.env_update(std::sync::Arc::clone(&base), ssa_var);
        self.heap_pointees.insert(base, fresh);
    }

    fn assert_scalar_validity_for_ty(&mut self, ty: Ty, expr: Expr) {
        self.assert_char_validity_for_ty(ty, expr.clone());
        self.assert_nonzero_validity_for_ty(ty, expr);
    }

    fn assert_char_validity_for_ty(&mut self, ty: rustc_public::ty::Ty, expr: Expr) {
        if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Char)) {
            return;
        }
        if let Some(validity) = Self::char_validity_constraint(expr) {
            self.ctx.assert(validity);
        }
    }

    fn assert_nonzero_validity_for_ty(&mut self, ty: Ty, expr: Expr) {
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            return;
        };
        if def.trimmed_name() != "NonZero" {
            return;
        }
        let Some(GenericArgKind::Type(_inner)) = args.0.first() else {
            return;
        };
        let Some(validity) = Self::nonzero_validity_constraint(expr) else {
            return;
        };
        self.ctx.assert(validity);
    }

    fn nonzero_validity_constraint(expr: Expr) -> Option<Expr> {
        if let Some(width) = expr.sort().bitvec_width() {
            return Some(expr.eq(Expr::bitvec_const(0u64, width)).not());
        }
        if expr.sort().is_int() {
            return Some(expr.eq(Expr::int_const(0)).not());
        }
        None
    }

    fn char_validity_constraint(expr: Expr) -> Option<Expr> {
        if let Some(width) = expr.sort().bitvec_width() {
            let low_range = expr.clone().bvule(Expr::bitvec_const(0xD7FFu64, width));
            let high_lower = expr.clone().bvuge(Expr::bitvec_const(0xE000u64, width));
            let high_upper = expr.bvule(Expr::bitvec_const(0x10FFFFu64, width));
            return Some(low_range.or(high_lower.and(high_upper)));
        }
        if expr.sort().is_int() {
            let non_negative = expr.clone().int_ge(Expr::int_const(0));
            let low_range = expr.clone().int_le(Expr::int_const(0xD7FFi64));
            let high_lower = expr.clone().int_ge(Expr::int_const(0xE000i64));
            let high_upper = expr.int_le(Expr::int_const(0x10FFFFi64));
            return Some(non_negative.and(low_range.or(high_lower.and(high_upper))));
        }
        None
    }

    /// Coerce an expression to bool. BitVec and Int values are converted via `!= 0`.
    /// Returns `None` for sorts that cannot be coerced (e.g. arrays, datatypes).
    fn coerce_to_bool(expr: Expr) -> Option<Expr> {
        match expr.sort().inner() {
            SortInner::Bool => Some(expr),
            SortInner::BitVec(bv) => {
                let zero = Expr::bitvec_const(0, bv.width);
                Some(expr.eq(zero).not()) // bv != 0
            }
            SortInner::Int => {
                let zero = Expr::int_const(0);
                Some(expr.eq(zero).not()) // int != 0
            }
            other => {
                warn!(?other, "codegen_kani: un-coercible sort, condition dropped");
                None
            }
        }
    }

    /// Codegen kani::assume - asserts the condition as a path assumption.
    pub(super) fn codegen_kani_assume(&mut self, args: &[Operand]) {
        if args.is_empty() {
            return;
        }
        // assume(cond) -> assert(cond) in SMT (constrains the path)
        // Part of #3211: Track dropped assume conditions via demotion counter.
        // Dropping an assume is sound over-approximation (more states explored),
        // but should be visible to the demotion pipeline.
        if let Some(cond_expr) = self.codegen_operand(&args[0]) {
            if let Some(bool_cond) = Self::coerce_to_bool(cond_expr) {
                self.assert_guarded(bool_cond);
            } else {
                warn!("codegen_kani_assume: coerce_to_bool returned None, assume dropped");
                self.ctx.unsupported_with_fallback(
                    "kani_assume_condition_drop",
                    "coerce_to_bool returned None",
                );
            }
        } else {
            warn!("codegen_kani_assume: codegen_operand returned None, assume dropped");
            self.ctx.unsupported_with_fallback(
                "kani_assume_condition_drop",
                "codegen_operand returned None",
            );
        }
    }

    /// Codegen the assume half of Kani's assert-assume lowering.
    ///
    /// CBMC/Kani semantics: `kani::assert(cond)` lowers to `assert(cond)`
    /// followed by `assume(cond)` — code after a failed assert is
    /// path-constrained (reported UNREACHABLE, not SUCCESS). Unlike
    /// `codegen_kani_assume`, the constraint is NOT asserted globally: a
    /// global assert would retroactively mask the assert's own violation
    /// (and any earlier failure). Instead it is folded into the ordered
    /// assumption context, which only constrains checks recorded after it.
    ///
    /// If the condition cannot be translated, the assume is silently dropped:
    /// the paired `codegen_kani_assert` already recorded a fail-closed
    /// unconditional violation plus a demotion counter for that case, and
    /// dropping an assume is a sound over-approximation.
    pub(super) fn codegen_kani_assume_ordered(&mut self, args: &[Operand]) {
        if args.is_empty() {
            return;
        }
        let Some(cond_expr) = self.codegen_operand(&args[0]) else {
            debug!("codegen_kani_assume_ordered: untranslatable condition, assume dropped");
            return;
        };
        let Some(bool_cond) = Self::coerce_to_bool(cond_expr) else {
            debug!("codegen_kani_assume_ordered: un-coercible sort, assume dropped");
            return;
        };
        let constraint = match &self.current_path_condition {
            None => bool_cond,
            Some(pc) => pc.clone().implies(bool_cond),
        };
        self.ctx.add_ordered_assumption(constraint);
    }

    /// Codegen kani::assert - for verification, we negate to find counterexamples.
    pub(super) fn codegen_kani_assert(&mut self, args: &[Operand]) {
        if args.is_empty() {
            // Conservative: record unconditional violation when kani::assert
            // is called with no arguments. Mirrors CHC emit_untranslatable_assert_rule
            // behavior — prevents false PROOF from silently dropped assertion.
            self.record_violation_guarded(Expr::bool_const(true), "kani_assert_no_args");
            return;
        }
        // assert(cond) -> for counterexample search, we assert(not(cond))
        // If satisfiable, we found a counterexample
        // The assertion is guarded by the current path condition.
        // Part of #3211: fail-closed behavior for untranslatable assertions.
        // When condition can't be translated, record an unconditional violation
        // (conservative: any path reaching here is a failure) plus demotion counter.
        if let Some(cond_expr) = self.codegen_operand(&args[0]) {
            if let Some(bool_cond) = Self::coerce_to_bool(cond_expr) {
                // The kani::assert intrinsic carries the assertion message as a
                // &str in args[1] (e.g. "assertion failed: foo() == None", built
                // by the assert! macro). Capture it so the driver reports the full
                // expression text instead of a generic "assertion failed".
                let message = args.get(1).and_then(|op| self.try_extract_str_constant(op));
                self.record_violation_guarded_with_message(bool_cond.not(), "kani_assert", message);
            } else {
                warn!("codegen_kani_assert: coerce_to_bool returned None for {:?}", &args[0]);
                self.record_violation_guarded(Expr::bool_const(true), "untranslatable_kani_assert");
                self.ctx.unsupported_with_fallback(
                    "kani_assert_condition_drop",
                    "coerce_to_bool returned None",
                );
            }
        } else {
            warn!("codegen_kani_assert: codegen_operand returned None for {:?}", &args[0]);
            self.record_violation_guarded(Expr::bool_const(true), "untranslatable_kani_assert");
            self.ctx.unsupported_with_fallback(
                "kani_assert_condition_drop",
                "codegen_operand returned None",
            );
        }
    }

    /// Codegen kani::cover - checks if a condition is reachable.
    ///
    /// Cover properties don't affect verification success/failure. They report
    /// whether the specified condition can be reached during execution.
    ///
    /// Unlike assert (which fails if condition can be false), cover reports
    /// SATISFIED if the condition can be true at this program point.
    ///
    /// args[0]: condition to check (bool)
    /// args[1]: message (&str) - optional description
    pub(super) fn codegen_kani_cover(&mut self, args: &[Operand]) {
        if args.is_empty() {
            return;
        }

        // Get the condition to cover, coercing to bool if needed
        let cond_expr = match self.codegen_operand(&args[0]).and_then(Self::coerce_to_bool) {
            Some(expr) => expr,
            _ => return, // non-enum: Option<Expr>
        };

        // Guard the cover condition by the current path condition
        // Cover is satisfied if: path_condition ∧ cover_condition is SAT
        let guarded_cond = match &self.current_path_condition {
            Some(pc) => pc.clone().and(cond_expr),
            None => cond_expr,
        };

        // #1164: Pass source location for property location tracking
        let location = self.current_source_location();

        // #1311: Extract optional message from args[1] if present
        let message = args.get(1).and_then(|msg_op| self.try_extract_str_constant(msg_op));

        let cover_id =
            self.ctx.record_cover_property_with_location(guarded_cond, location, message);
        debug!("codegen_kani_cover: recorded cover property ay_cover_{}", cover_id);
    }

    /// Part of #1906: Codegen kani::value_view - convert machine to mathematical values.
    fn emit_value_view_fallback(
        &mut self,
        base_name: &str,
        fallback_sort: Sort,
        location: impl Into<String>,
    ) {
        let name = self.ctx.fresh_name("ay_value_view_fallback");
        let expr = self.ctx.declare_var(&name, fallback_sort);
        self.env_update(base_name.to_owned(), expr);
        self.ctx.unsupported_with_fallback("value_view", location);
    }

    /// Part of #1906: Codegen kani::value_view - convert machine to mathematical values.
    pub(super) fn codegen_kani_value_view(&mut self, args: &[Operand], destination: &Place) {
        let base_name = self.ssa_base_name(destination);
        let _ssa_name = self.ssa_name_from_base(&base_name, true);

        if args.is_empty() {
            debug!("codegen_kani_value_view: no arguments provided");
            let fallback_sort =
                self.infer_sort_from_place(destination).unwrap_or_else(|| Sort::bitvec(32));
            self.emit_value_view_fallback(
                &base_name,
                fallback_sort,
                format!("{destination:?}: no arguments"),
            );
            return;
        }

        let arg = &args[0];
        let arg_ty = if let Some(ty) = arg.ty(self.body.locals()).into_option() {
            ty
        } else {
            debug!("codegen_kani_value_view: could not determine argument type");
            let fallback_sort =
                self.infer_sort_from_place(destination).unwrap_or_else(|| Sort::bitvec(32));
            self.emit_value_view_fallback(
                &base_name,
                fallback_sort,
                format!("{destination:?}: could not determine argument type"),
            );
            return;
        };

        let (view_sort, is_signed) = if let Some(result) = Self::view_sort_from_ty(arg_ty) {
            result
        } else {
            debug!(?arg_ty, "codegen_kani_value_view: unsupported type, using fallback");
            let fallback_sort =
                Self::infer_sort_from_ty(arg_ty).unwrap_or_else(|| Sort::bitvec(32));
            let name = self.ctx.fresh_name("ay_value_view_unsupported");
            let expr = self.ctx.declare_var(&name, fallback_sort);
            self.env_update(base_name, expr);
            return;
        };

        let arg_expr = if let Some(expr) = self.codegen_operand(arg) {
            expr
        } else {
            debug!("codegen_kani_value_view: could not codegen argument");
            self.emit_value_view_fallback(
                &base_name,
                view_sort,
                format!("{destination:?}: could not codegen operand"),
            );
            return;
        };

        let arg_sort = arg_expr.sort().clone();
        let viewed_expr = match arg_sort.inner() {
            ay_bindings::SortInner::BitVec(_) => {
                if is_signed {
                    debug!(?arg_ty, "codegen_kani_value_view: bv2int_signed");
                    arg_expr.bv2int_signed()
                } else {
                    debug!(?arg_ty, "codegen_kani_value_view: bv2int");
                    arg_expr.bv2int()
                }
            }
            ay_bindings::SortInner::Bool => {
                debug!(?arg_ty, "codegen_kani_value_view: bool passthrough");
                arg_expr
            }
            ay_bindings::SortInner::Int => {
                debug!(?arg_ty, "codegen_kani_value_view: int passthrough");
                arg_expr
            }
            _ => {
                // external enum: SortInner (ay_bindings crate)
                debug!(?arg_ty, "codegen_kani_value_view: unknown sort passthrough");
                arg_expr
            }
        };

        // Add Unicode scalar value constraint for char type.
        // Rust `char` is [0, 0xD7FF] ∪ [0xE000, 0x10FFFF] — surrogates excluded.
        // Consistent with CHC path (char_nondet_bounds at codegen_call_kani_hooks.rs).
        if matches!(arg_ty.kind(), TyKind::RigidTy(RigidTy::Char)) {
            let lower_bound = viewed_expr.clone().int_ge(Expr::int_const(0));
            // Exclude surrogates: (val <= 0xD7FF) || (val >= 0xE000 && val <= 0x10FFFF)
            let low_range = viewed_expr.clone().int_le(Expr::int_const(0xD7FF));
            let high_lower = viewed_expr.clone().int_ge(Expr::int_const(0xE000));
            let high_upper = viewed_expr.clone().int_le(Expr::int_const(0x10FFFF));
            let scalar_range = low_range.or(high_lower.and(high_upper));
            self.ctx.assert(lower_bound);
            self.ctx.assert(scalar_range);
            debug!(
                "codegen_kani_value_view: added char Unicode scalar constraint (surrogates excluded)"
            );
        }

        self.env_update(base_name, viewed_expr);
    }
}
