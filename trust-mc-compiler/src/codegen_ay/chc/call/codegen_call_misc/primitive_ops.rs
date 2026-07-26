// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Clone and raw_eq handlers.
//! Part of #2408 S1: codegen_call_misc decomposition.
//! Slice stub handling moved to codegen_call_slice.rs (Part of #408).

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use std::collections::HashSet;
use tracing::{debug, warn};

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort};

use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_call_kani_model_dst::is_zst_ty;
use super::super::codegen_call_kani_model_zst::canonical_zst_expr;
use super::super::codegen_expr_signedness::arg_signedness_or_fallback;
use super::super::codegen_rules::CodegenRules;
use super::super::codegen_types::CodegenTypes;
use super::super::{ChcCtx, RelationApp};
use super::CallMisc;
use crate::codegen_ay::shared::SignednessFallbackKind;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle Clone::clone for primitives — identity (Copy semantics) (Part of #2196).
    ///
    /// `clone(&self) -> Self` for Copy types is an identity operation: the result
    /// equals the dereferenced argument. Resolves `&self` through ref_targets,
    /// then constrains `dest = value` with sort coercion.
    pub(in crate::codegen_ay::chc) fn codegen_call_primitive_clone_impl(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: BasicBlockIdx,
        from_app: &RelationApp,
        stmt_constraints: &[Expr],
        modified_locals: &HashSet<usize>,
    ) {
        let dest_local: usize = destination.local;
        debug!("PrimitiveClone dest={} args={}", dest_local, args.len());

        // Resolve &self to the referent value
        let value = args.first().and_then(|arg| {
            self.resolve_ref_operand(arg, modified_locals)
                .or_else(|| self.translate_operand_with_modified(arg, modified_locals))
        });

        // Part of #3182: check for flattened destination first.
        if let Some(value_expr) = value {
            if let Some(fc) =
                self.build_flattened_destination_constraints(dest_local, value_expr.clone())
            {
                let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(from_app, target, &new_output_args, stmt_constraints, fc);
                return;
            } else if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    value_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_primitive_clone",
                );
                if eq.is_some() {
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    self.emit_goto_rule_extra(
                        from_app,
                        target,
                        &new_output_args,
                        stmt_constraints,
                        eq,
                    );
                    return;
                }
            }
        }
        // Part of #4113: ZST clone — canonical deterministic value.
        // For zero-sized types like `[(); 10]`, clone has exactly one valid
        // result. Constrain the destination to the canonical ZST expression
        // instead of leaving it unconstrained (which breaks array equality).
        let dest_ty = self.body.locals()[dest_local].ty;
        if is_zst_ty(dest_ty) {
            if let Some(canonical) = canonical_zst_expr(dest_ty) {
                if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                    let eq = self.make_coerced_eq_constraint(
                        &dest_var,
                        canonical,
                        dest_var.sort(),
                        dest_local,
                        "codegen_call_primitive_clone_zst",
                    );
                    if eq.is_some() {
                        debug!(
                            fn_name = %self.fn_name,
                            "CHC: primitive clone on ZST; constraining to canonical value"
                        );
                        let new_output_args =
                            self.build_output_args(modified_locals, &[dest_local]);
                        self.emit_goto_rule_extra(
                            from_app,
                            target,
                            &new_output_args,
                            stmt_constraints,
                            eq,
                        );
                        return;
                    }
                }
            }
        }
        // Fallback: could not resolve, leave unconstrained.
        warn!(
            fn_name = %self.fn_name,
            "CHC: primitive clone unresolved; emitting unconstrained transition with fallback metadata"
        );
        emit_sound_fallback_goto(
            self,
            from_app,
            target,
            modified_locals,
            &[dest_local],
            stmt_constraints,
        );
    }

    /// Handle `std::intrinsics::raw_eq` calls (Part of #1739).
    ///
    /// `raw_eq<T>(a: &T, b: &T) -> bool` compares two values by byte
    /// representation. In CHC we model this as SMT equality on the translated
    /// expressions, which is sound for fixed-layout types (arrays, scalars).
    ///
    /// For array types `[T; N]`, compares element-wise through type-indexed
    /// memory arrays: `∀i ∈ 0..N: select(mem_T, addr_a + i*sz) = select(mem_T, addr_b + i*sz)`.
    pub(in crate::codegen_ay::chc) fn codegen_call_raw_eq_impl(
        &mut self,
        func: &Operand,
        ecx: &super::super::chc_call_context::CallEmitContext<'_>,
    ) {
        let dest_local: usize = ecx.destination.local;

        // Part of #1739: Check if this is raw_eq on an array type.
        // For arrays, use element-wise memory comparison instead of scalar equality.
        if let Some(eq_expr) = self.try_raw_eq_array(func, ecx.args, ecx.modified_locals) {
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                let result = match dest_var.sort().bitvec_width() {
                    Some(bits) => {
                        Expr::ite(eq_expr, Expr::bitvec_const(1, bits), Expr::bitvec_const(0, bits))
                    }
                    None => eq_expr,
                };
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    result,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_raw_eq_array",
                );
                if eq.is_some() {
                    let new_output_args =
                        self.build_output_args(ecx.modified_locals, &[dest_local]);
                    self.emit_goto_rule_extra(
                        ecx.from_app,
                        ecx.target,
                        &new_output_args,
                        ecx.stmt_constraints,
                        eq,
                    );
                    return;
                }
            }
        }

        // Scalar path: resolve to *referent* values (not pointers).
        // Chain: ref_targets → const_ref_values → direct translation
        // → bare local. Part of #2173: const_ref_values now covers promoted
        // constant array references that ref_targets cannot track.
        let lhs =
            ecx.args.first().and_then(|arg| self.resolve_raw_eq_referent(arg, ecx.modified_locals));
        let rhs =
            ecx.args.get(1).and_then(|arg| self.resolve_raw_eq_referent(arg, ecx.modified_locals));

        if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
            // AY .eq() requires same sort. Guard against sort mismatches
            // (e.g., one operand resolves to Array, the other to BV).
            let eq_expr = if *lhs.sort() == *rhs.sort() {
                lhs.eq(rhs)
            } else if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
                // Same sort family, different widths — coerce to max.
                let lhs_w =
                    lhs.sort().bitvec_width().expect("bitvec operand sort must report width");
                let rhs_w =
                    rhs.sort().bitvec_width().expect("bitvec operand sort must report width");
                let target_width = lhs_w.max(rhs_w);
                // Part of #2976: derive signedness from operand type for BV widening.
                let signed = ecx
                    .args
                    .first()
                    .map(|arg| {
                        arg_signedness_or_fallback(
                            arg,
                            self.body.locals(),
                            "raw_eq_scalar",
                            SignednessFallbackKind::Comparison,
                        )
                    })
                    .unwrap_or(false);
                let lhs = coerce_bitvec_width_safe(
                    lhs,
                    target_width,
                    SignExtension::for_signedness(signed),
                );
                let rhs = coerce_bitvec_width_safe(
                    rhs,
                    target_width,
                    SignExtension::for_signedness(signed),
                );
                lhs.eq(rhs)
            } else if let Some(rhs_coerced) = Self::reinterpret_fixed_layout_expr(&rhs, lhs.sort())
            {
                // Part of #3951: BV→Array coercion for raw_eq operands.
                lhs.eq(rhs_coerced)
            } else if let Some(lhs_coerced) = Self::reinterpret_fixed_layout_expr(&lhs, rhs.sort())
            {
                // Part of #3951: symmetric case.
                lhs_coerced.eq(rhs)
            } else {
                // Incompatible sorts (e.g., Array vs BV) — fall through
                // to unconstrained. Cannot build a valid equality.
                warn!(
                    fn_name = %self.fn_name,
                    lhs_sort = ?lhs.sort(),
                    rhs_sort = ?rhs.sort(),
                    "CHC: raw_eq sort mismatch; emitting unconstrained transition with fallback metadata"
                );
                emit_sound_fallback_goto(
                    self,
                    ecx.from_app,
                    ecx.target,
                    ecx.modified_locals,
                    &[dest_local],
                    ecx.stmt_constraints,
                );
                return;
            };

            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                // raw_eq returns bool; coerce to destination width when needed.
                let result = match dest_var.sort().bitvec_width() {
                    Some(bits) => {
                        Expr::ite(eq_expr, Expr::bitvec_const(1, bits), Expr::bitvec_const(0, bits))
                    }
                    None => eq_expr,
                };
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    result,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_raw_eq",
                );
                if eq.is_some() {
                    let new_output_args =
                        self.build_output_args(ecx.modified_locals, &[dest_local]);
                    self.emit_goto_rule_extra(
                        ecx.from_app,
                        ecx.target,
                        &new_output_args,
                        ecx.stmt_constraints,
                        eq,
                    );
                } else {
                    warn!(
                        fn_name = %self.fn_name,
                        "CHC: raw_eq coercion failed; emitting unconstrained transition with fallback metadata"
                    );
                    emit_sound_fallback_goto(
                        self,
                        ecx.from_app,
                        ecx.target,
                        ecx.modified_locals,
                        &[dest_local],
                        ecx.stmt_constraints,
                    );
                }
                return;
            }
        }
        // Fallback: couldn't resolve operands, leave unconstrained.
        // Part of #2773: was invisible to demotion pipeline.
        warn!(
            fn_name = %self.fn_name,
            "CHC: raw_eq couldn't resolve operands; destination left unconstrained"
        );
        emit_sound_fallback_goto(
            self,
            ecx.from_app,
            ecx.target,
            ecx.modified_locals,
            &[dest_local],
            ecx.stmt_constraints,
        );
    }

    /// Try array comparison for `raw_eq::<[T; N]>`.
    ///
    /// Part of #1739: For array types, first tries to resolve both operands
    /// as local array expressions (through ref_targets / const_ref_values) for
    /// direct SMT array equality. Falls back to element-wise comparison through
    /// the type-indexed memory array when local resolution fails.
    ///
    /// Returns `None` if the type argument is not an array or operands
    /// cannot be resolved.
    fn try_raw_eq_array(
        &mut self,
        func: &Operand,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Extract the generic type argument T from raw_eq::<T>.
        let func_ty = func.ty(self.body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::FnDef(_, fn_args)) = func_ty.kind() else {
            return None;
        };
        let type_arg = fn_args.0.iter().find_map(|arg| match arg {
            GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })?;

        // Only handle fixed-size arrays [T; N].
        let TyKind::RigidTy(RigidTy::Array(elem_ty, const_len)) = type_arg.kind() else {
            return None;
        };
        let array_len = const_len.eval_target_usize().ok()? as usize;
        if array_len == 0 {
            // Empty arrays are trivially equal.
            return Some(Expr::bool_const(true));
        }
        // Limit to reasonable array sizes to avoid formula blowup.
        // 256 covers common fixed-size arrays (e.g., [u8; 65] in array_64 test).
        if array_len > 256 {
            debug!(array_len, "CHC: raw_eq array too large for element-wise comparison");
            return None;
        }

        // Tier 1: Try resolving both operands as local array expressions.
        // This handles cases where one or both arrays exist only as tracked
        // locals (e.g., literal [0,0,0,0] from assert!(arr == [0,0,0,0]))
        // that are not mirrored into the type-indexed memory.
        //
        // IMPORTANT (Part of #2979): Use element-wise comparison at indices
        // 0..N, NOT full SMT array equality. SMT arrays are infinite —
        // `lhs.eq(rhs)` compares ALL indices including those beyond the
        // Rust array length. Background values of distinct SMT arrays
        // are unconstrained and may differ, causing spurious inequality
        // even when the Rust-visible elements are identical.
        let lhs_local =
            args.first().and_then(|arg| self.resolve_raw_eq_referent(arg, modified_locals));
        let rhs_local =
            args.get(1).and_then(|arg| self.resolve_raw_eq_referent(arg, modified_locals));

        if let (Some(lhs), Some(rhs)) = (lhs_local, rhs_local) {
            if lhs.sort().is_array() && rhs.sort().is_array() && *lhs.sort() == *rhs.sort() {
                if let Some(idx_sort) = lhs.sort().array_sort().map(|s| s.index_sort.clone()) {
                    let mut result = Expr::bool_const(true);
                    for i in 0..array_len {
                        let idx = if let Some(width) = idx_sort.bitvec_width() {
                            Expr::bitvec_const(i as u64, width)
                        } else if idx_sort.is_int() {
                            Expr::int_const(i as u64)
                        } else {
                            // Unsupported index sort — fall through to Tier 2.
                            debug!(
                                fn_name = %self.fn_name,
                                array_len,
                                idx_sort = ?idx_sort,
                                "CHC: raw_eq Tier 1 unsupported index sort, falling through"
                            );
                            return None;
                        };
                        let lhs_elem = lhs.clone().select(idx.clone());
                        let rhs_elem = rhs.clone().select(idx);
                        result = result.and(lhs_elem.eq(rhs_elem));
                    }
                    debug!(
                        fn_name = %self.fn_name,
                        array_len,
                        "CHC: raw_eq array comparison via element-wise local array equality"
                    );
                    return Some(result);
                }
            }
        }

        // Tier 2: Element-wise comparison through type-indexed memory.
        // Get the element sort and byte width.
        let elem_sort = Self::translate_ty(elem_ty)?;
        let elem_byte_width = self.get_type_size(elem_ty)? as u64;

        // Part of #3661: resolve generic params for consistent type keys.
        let type_key = self.type_key_for_body_ty(elem_ty);

        // Get the current memory array expression for this type.
        let (arr_name, _, declared_elem_sort, _) =
            self.heap_state.get_or_create_type_array(&type_key, elem_sort, &self.fn_name);
        // Part of #3184: Mark this type array as read (raw_eq comparison loads values).
        // Part of #3436: Per-block tracking for error-path-aware pruning.
        self.heap_state.mark_type_array_read(&arr_name, self.current_encode_bb);
        let arr_sort = Sort::array(ptr_sort(), declared_elem_sort);
        let mem_arr = if let Some(accumulated) = self.heap_state.get_store_chain(&type_key) {
            accumulated.clone()
        } else {
            Expr::var(&*arr_name, arr_sort)
        };

        // Resolve both operand addresses. raw_eq args are references (&T),
        // so translate_operand_with_modified gives us the BV64 pointer values.
        let addr_a = args
            .first()
            .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals))?;
        let addr_b = args
            .get(1)
            .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals))?;

        // Coerce addresses to pointer width if needed.
        let addr_a = coerce_bitvec_width_safe(addr_a, POINTER_WIDTH, SignExtension::ZeroExtend);
        let addr_b = coerce_bitvec_width_safe(addr_b, POINTER_WIDTH, SignExtension::ZeroExtend);

        // Build conjunction: ∀i ∈ 0..N: select(mem, addr_a + i*sz) = select(mem, addr_b + i*sz)
        let mut result = Expr::bool_const(true);
        for i in 0..array_len {
            let offset = Expr::bitvec_const((i as u64) * elem_byte_width, POINTER_WIDTH);
            let elem_a = mem_arr.clone().select(addr_a.clone().bvadd(offset.clone()));
            let elem_b = mem_arr.clone().select(addr_b.clone().bvadd(offset));
            result = result.and(elem_a.eq(elem_b));
        }

        debug!(
            fn_name = %self.fn_name,
            array_len,
            elem_type = %type_key,
            "CHC: raw_eq array comparison via element-wise memory reads"
        );
        Some(result)
    }
}
