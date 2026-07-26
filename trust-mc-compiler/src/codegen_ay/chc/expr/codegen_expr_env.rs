// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Loop-invariant extraction and expression translation in local environments.
//!
//! Extracted from codegen_expr.rs per #2246 decomposition.
//! Migrated from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::{Expr, Sort, SortInner};
use rustc_public::mir::{
    BinOp, Operand, Place, ProjectionElem, RETURN_LOCAL, Rvalue, StatementKind, TerminatorKind,
    UnOp,
};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{HashMap, HashSet};
use tracing::{debug, trace, warn};

use crate::codegen_ay::shared::IntoOption;
use crate::codegen_ay::types::{
    POINTER_WIDTH, int_ty_to_bitvec_width, ty_to_bv_width, uint_ty_to_bitvec_width,
};

use super::codegen_expr_constant::ExprConstant;
use super::codegen_expr_signedness::{ExprSignedness, ty_signedness};
use super::codegen_types::CodegenTypes;
use super::{ChcCtx, UnknownProjectionPolicy, collect_field_projections, names};
use crate::codegen_ay::shared::signedness_fallback_for_binop;

fn operand_is_raw_pointer_like(operand: &Operand, locals: &[rustc_public::mir::LocalDecl]) -> bool {
    fn ty_is_raw_pointer_like(ty: rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(..)) => true,
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty_is_raw_pointer_like(inner),
            _ => false,
        }
    }

    operand.ty(locals).ok().is_some_and(ty_is_raw_pointer_like)
}

/// Extension trait for loop-invariant extraction and environment-based
/// expression translation on `ChcCtx`.
pub(in crate::codegen_ay) trait ExprEnv {
    #[must_use]
    fn extract_loop_invariant_formula(&mut self, captured_vars: &[usize]) -> Option<Expr>;
}

impl<'tcx, 'body> ExprEnv for ChcCtx<'tcx, 'body> {
    /// Extract a loop invariant formula from a closure body, if possible.
    ///
    /// This evaluates straight-line closure bodies and returns the expression
    /// assigned to the return local. Captured variables are mapped to harness
    /// locals using the captured_vars list.
    fn extract_loop_invariant_formula(&mut self, captured_vars: &[usize]) -> Option<Expr> {
        if self.body.blocks.len() != 1 {
            return None;
        }
        let block = &self.body.blocks[0];
        if !matches!(block.terminator.kind, TerminatorKind::Return) {
            return None;
        }

        let closure_env_local = if self.body.arg_locals().is_empty() { None } else { Some(1) };
        let mut env: HashMap<usize, Expr> = HashMap::new();

        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(place, rvalue) => {
                    if !place.projection.is_empty() {
                        return None;
                    }
                    let expr = self.translate_rvalue_with_env(
                        rvalue,
                        &env,
                        captured_vars,
                        closure_env_local,
                        Some(place.local),
                    )?;
                    env.insert(place.local, expr);
                }
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop
                | StatementKind::FakeRead(..)
                | StatementKind::PlaceMention(..)
                | StatementKind::AscribeUserType { .. }
                | StatementKind::Coverage(..)
                | StatementKind::ConstEvalCounter
                | StatementKind::Retag(..) => {}
                _ => return None, // external enum: StatementKind
            }
        }

        let expr = env.get(&RETURN_LOCAL)?.clone();
        if expr.sort().is_bool() { Some(expr) } else { None }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn translate_rvalue_with_env(
        &mut self,
        rvalue: &Rvalue,
        env: &HashMap<usize, Expr>,
        captured_vars: &[usize],
        closure_env_local: Option<usize>,
        dest_local: Option<usize>,
    ) -> Option<Expr> {
        match rvalue {
            Rvalue::Use(operand) => {
                self.translate_operand_with_env(operand, env, captured_vars, closure_env_local)
            }
            Rvalue::BinaryOp(op, lhs_op, rhs_op) | Rvalue::CheckedBinaryOp(op, lhs_op, rhs_op) => {
                let lhs =
                    self.translate_operand_with_env(lhs_op, env, captured_vars, closure_env_local)?;
                let rhs =
                    self.translate_operand_with_env(rhs_op, env, captured_vars, closure_env_local)?;
                let raw_pointer_ordering = operand_is_raw_pointer_like(lhs_op, self.body.locals())
                    && operand_is_raw_pointer_like(rhs_op, self.body.locals());
                // For shift operations, only the value operand's (LHS) signedness matters.
                // The shift amount is often a different type in MIR (e.g., u32 << i32),
                // causing a mixed-signedness conflict that triggers a spurious fallback.
                // For non-shift ops, check both operands (#1889).
                let inferred_signed = if raw_pointer_ordering {
                    Some(false)
                } else if matches!(
                    op,
                    BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked
                ) {
                    self.operand_signedness(lhs_op)
                } else {
                    self.is_signed_integer_op(lhs_op, rhs_op)
                };
                // Part of #3099: when operand signedness is unknown for div/rem,
                // try the destination local's MIR type before recording a fallback.
                // In Rust MIR, arithmetic ops preserve the operand integer type
                // in the destination.
                // Part of #3253: skip destination fallback for all comparison ops.
                // Their destination is `bool`, and ty_signedness_shallow(bool)
                // returns Some(false) (unsigned), NOT None. For ordered
                // comparisons this is a soundness bug (bvult vs bvslt); for
                // Eq/Ne it causes wrong width coercion (zero-extend vs
                // sign-extend) on mixed-width operands.
                let is_comparison = matches!(
                    op,
                    BinOp::Lt
                        | BinOp::Le
                        | BinOp::Ge
                        | BinOp::Gt
                        | BinOp::Cmp
                        | BinOp::Eq
                        | BinOp::Ne
                );
                let inferred_signed = if inferred_signed.is_none() && !is_comparison {
                    let dest_signed = dest_local.and_then(|idx| {
                        let local_ty = self.body.locals().get(idx)?.ty;
                        ty_signedness(local_ty)
                    });
                    if dest_signed.is_some() {
                        debug!(
                            ?op,
                            ?dest_signed,
                            "CHC: signedness resolved from destination type in env context (Part of #3099)"
                        );
                        dest_signed
                    } else if matches!(op, BinOp::Div | BinOp::Rem) {
                        // Part of #2749: genuinely unknown signedness on div/rem is high-risk.
                        warn!(
                            ?op,
                            "CHC: div/rem with unknown signedness in env context — recording fallback (Part of #2749)"
                        );
                        self.record_fallback();
                        None
                    } else {
                        None
                    }
                } else {
                    inferred_signed
                };
                let is_signed = inferred_signed.unwrap_or_else(|| {
                    signedness_fallback_for_binop(*op, "translate_rvalue_with_env")
                });
                // Part of #3043: derive BV width from LHS operand's MIR type.
                // Part of #3243: bail instead of defaulting to 32 on type resolution failure.
                let lhs_ty = lhs_op.ty(self.body.locals()).ok()?;
                let int_bv_width = match ty_to_bv_width(lhs_ty) {
                    Some(width) => width,
                    None if matches!(
                        op,
                        BinOp::Lt
                            | BinOp::Le
                            | BinOp::Ge
                            | BinOp::Gt
                            | BinOp::Cmp
                            | BinOp::Eq
                            | BinOp::Ne
                    ) =>
                    {
                        // Part of #4030: env-based translation can also see
                        // wide raw-pointer comparisons lowered to MIR BinOps.
                        // Keep the comparison path alive with pointer width
                        // instead of bailing on an unsized pointee type.
                        POINTER_WIDTH
                    }
                    None => return None,
                };

                // Part of #3140: IEEE 754 float comparison override.
                let is_float = matches!(lhs_ty.kind(), TyKind::RigidTy(RigidTy::Float(_)));
                if is_float
                    && is_comparison
                    && matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
                    && lhs.sort().is_bitvec()
                {
                    use crate::codegen_ay::float_compare::{
                        bv_float_ge, bv_float_gt, bv_float_le, bv_float_lt,
                    };
                    let width = int_bv_width;
                    return Some(match op {
                        BinOp::Lt => bv_float_lt(&lhs, &rhs, width),
                        BinOp::Le => bv_float_le(&lhs, &rhs, width),
                        BinOp::Gt => bv_float_gt(&lhs, &rhs, width),
                        BinOp::Ge => bv_float_ge(&lhs, &rhs, width),
                        // INVARIANT: guard at line 213 restricts to Lt|Le|Gt|Ge only.
                        _ => unreachable!(),
                    });
                }

                // Float Add/Sub/Mul/Div/Rem in CHC route through
                // `ChcCtx::float_binop_chc_term` (inside translate_binop):
                // constant-fold when both operands are concrete bit patterns,
                // congruent unconstrained-table select when symbolic (sound
                // for proofs; see float_binop_table.rs). PDR does not reason
                // about FP theory in CHC bodies, so the BMC
                // `bv_to_ieee_fp → fp_op → fp_to_ieee_bv` round-trip is not
                // used here. Raw BV integer arithmetic on float bits would
                // let the solver build false counterexamples.
                match rvalue {
                    Rvalue::BinaryOp(_, _, _) => {
                        self.translate_binop(*op, lhs, rhs, is_signed, int_bv_width, is_float)
                    }
                    Rvalue::CheckedBinaryOp(_, _, _) => {
                        self.translate_checked_binop(*op, lhs, rhs, is_signed, int_bv_width)
                    }
                    _ => None, // external enum: Rvalue
                }
            }
            Rvalue::UnaryOp(UnOp::PtrMetadata, operand) => {
                // PtrMetadata in closure/expr context: use same logic as statement path.
                self.translate_ptr_metadata(operand, &HashSet::new())
            }
            Rvalue::UnaryOp(op, operand) => {
                // Part of #3043: derive BV width from operand's MIR type.
                // Part of #3243: bail instead of defaulting to 32 on type resolution failure.
                let int_bv_width = ty_to_bv_width(operand.ty(self.body.locals()).ok()?)?;
                // Part of #3055: derive signedness for bv2int conversion.
                // Part of #3247: Neg is only defined on signed types; default signed for Neg.
                let default_signed = matches!(op, UnOp::Neg);
                let is_signed = self.operand_signedness(operand).unwrap_or(default_signed);
                let expr = self.translate_operand_with_env(
                    operand,
                    env,
                    captured_vars,
                    closure_env_local,
                )?;
                self.translate_unop(*op, expr, int_bv_width, is_signed)
            }
            Rvalue::Cast(_kind, operand, target_ty) => self.translate_cast_with_env(
                operand,
                *target_ty,
                env,
                captured_vars,
                closure_env_local,
            ),
            Rvalue::Len(place) => {
                // Part of #1888: Rvalue::Len returns usize.
                // For fixed-size arrays [T; N], use the compile-time constant length.
                let ty = place.ty(self.body.locals()).into_option();

                if let Some(ty) = &ty
                    && let TyKind::RigidTy(RigidTy::Array(_, const_len)) = ty.kind()
                    && let Some(len) = const_len.eval_target_usize().into_option()
                {
                    debug!(?place, len, "CHC: Rvalue::Len on array - compile-time length");
                    return Some(Expr::bitvec_const(len as u128, POINTER_WIDTH));
                }

                // Part of #3099: Try to recover array length from Unsize origin.
                // Works on MIR body analysis — no env dependency.
                if let Some(len) = self.try_resolve_len_from_unsize(place) {
                    debug!(
                        ?place,
                        len, "CHC: Rvalue::Len in env — recovered length from array unsize"
                    );
                    return Some(Expr::bitvec_const(len as u128, POINTER_WIDTH));
                }

                // Part of #3495: Try to recover length from Subslice ref chain.
                if let Some(len) = self.try_resolve_len_from_subslice_ref(place) {
                    debug!(
                        ?place,
                        len, "CHC: Rvalue::Len in env — recovered length from subslice ref"
                    );
                    return Some(Expr::bitvec_const(len as u128, POINTER_WIDTH));
                }

                // Part of #3084: Try to resolve Vec/Slice length from Datatype in env.
                // Resolve the place via the env to get a Datatype expression, then
                // extract `fld_len` if the Datatype has it (Vec/Slice pattern).
                if let Some(expr) =
                    self.translate_place_with_env(place, env, captured_vars, closure_env_local)
                {
                    let sort = expr.sort();
                    if let SortInner::Datatype(dt) = sort.inner() {
                        if let Some(ctor) = dt.constructors.first() {
                            if ctor.fields.iter().any(|f| &*f.name == "fld_len") {
                                let dt_name = dt.name.clone();
                                debug!(
                                    ?place,
                                    %dt_name,
                                    "CHC: Rvalue::Len in env — extracted fld_len from Datatype"
                                );
                                return Some(expr.field_select(
                                    &*dt_name,
                                    "fld_len",
                                    crate::codegen_ay::types::ptr_sort(),
                                ));
                            }
                        }
                    }
                }

                // Part of #3369: Reclassified SOUND_APPROXIMATION → DEMOTED.
                // Returning None triggers caller fallback (identity).
                warn!(?place, "CHC: Rvalue::Len on non-array in env context — recording fallback");
                self.record_fallback();
                None
            }
            other => {
                // Part of #3369: Reclassified SOUND_APPROXIMATION → DEMOTED.
                self.record_fallback();
                warn!(?other, "CHC: translate_rvalue_with_env - unsupported rvalue kind");
                None
            }
        }
    }

    fn translate_operand_with_env(
        &mut self,
        operand: &Operand,
        env: &HashMap<usize, Expr>,
        captured_vars: &[usize],
        closure_env_local: Option<usize>,
    ) -> Option<Expr> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.translate_place_with_env(place, env, captured_vars, closure_env_local)
            }
            Operand::Constant(const_op) => self.translate_constant(const_op),
        }
    }

    fn translate_place_with_env(
        &mut self,
        place: &Place,
        env: &HashMap<usize, Expr>,
        captured_vars: &[usize],
        closure_env_local: Option<usize>,
    ) -> Option<Expr> {
        if let Some(env_local) = closure_env_local
            && place.local == env_local
            && !place.projection.is_empty()
            && let ProjectionElem::Field(field_idx, _) = place.projection[0]
        {
            let captured_local = *captured_vars.get(field_idx)?;
            let place_ty = place.ty(self.body.locals()).into_option()?;
            let sort = Self::translate_ty(place_ty)?;
            let mut expr = Expr::var(
                crate::codegen_ay::names::state_var_name(&self.fn_name, captured_local),
                sort,
            );

            let mut remaining = place.projection[1..].to_vec();
            if matches!(remaining.first(), Some(ProjectionElem::Deref)) {
                remaining.remove(0);
            }
            if remaining.is_empty() {
                return Some(expr);
            }
            let field_projections = collect_field_projections(
                &remaining,
                UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
            );
            if field_projections.is_empty() {
                return None;
            }
            expr = Self::apply_field_selections(expr, &field_projections)?;
            return Some(expr);
        }

        if place.projection.is_empty() {
            return env.get(&place.local).cloned();
        }

        let base = env.get(&place.local)?.clone();
        let field_projections = collect_field_projections(
            &place.projection,
            UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
        );
        if field_projections.is_empty() {
            return None;
        }
        Self::apply_field_selections(base, &field_projections)
    }

    pub(in crate::codegen_ay::chc) fn translate_cast_with_env(
        &mut self,
        operand: &Operand,
        target_ty: rustc_public::ty::Ty,
        env: &HashMap<usize, Expr>,
        captured_vars: &[usize],
        closure_env_local: Option<usize>,
    ) -> Option<Expr> {
        let expr =
            self.translate_operand_with_env(operand, env, captured_vars, closure_env_local)?;
        let src_sort = expr.sort().clone();

        let target_width = match target_ty.kind() {
            TyKind::RigidTy(RigidTy::Int(int_ty)) => Some(int_ty_to_bitvec_width(int_ty)),
            TyKind::RigidTy(RigidTy::Uint(uint_ty)) => Some(uint_ty_to_bitvec_width(uint_ty)),
            TyKind::RigidTy(RigidTy::Bool) => None, // Handled separately via bool-specific path
            TyKind::RigidTy(RigidTy::Char) => Some(32),
            TyKind::RigidTy(RigidTy::RawPtr(_, _) | RigidTy::Ref(_, _, _)) => {
                Self::translate_ty(target_ty).and_then(|sort| sort.bitvec_width())
            }
            other => {
                trace!(?other, "CHC: translate_cast_with_env - no bit width for cast target type");
                None
            }
        };

        let src_signed = self.operand_signedness_for_cast(operand).unwrap_or_else(|| {
            warn!(?operand, "translate_cast_with_env: cannot determine signedness");
            false
        });

        match (src_sort.inner(), target_width) {
            (SortInner::Bool, Some(width)) => {
                let bv1 = Expr::ite(expr, Expr::bitvec_const(1, 1), Expr::bitvec_const(0, 1));
                if width == 1 { Some(bv1) } else { Some(bv1.zero_extend(width - 1)) }
            }
            (SortInner::BitVec(src_bv), None)
                if matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::Bool)) =>
            {
                Some(expr.ne(Expr::bitvec_const(0, src_bv.width)))
            }
            (SortInner::BitVec(src_bv), Some(dst_width)) => {
                if src_bv.width == dst_width {
                    Some(expr)
                } else if src_bv.width < dst_width {
                    let extra_bits = dst_width - src_bv.width;
                    if src_signed {
                        Some(expr.sign_extend(extra_bits))
                    } else {
                        Some(expr.zero_extend(extra_bits))
                    }
                } else {
                    Some(expr.extract(dst_width - 1, 0))
                }
            }
            (SortInner::Int, Some(width)) => Some(expr.int2bv(width)),
            (SortInner::BitVec(_), None) => Some(expr),
            // Unsupported sort/width combinations — explicit arms for exhaustiveness.
            (SortInner::Bool, None)
            | (SortInner::Int, None)
            | (SortInner::Real, _)
            | (SortInner::Array(_), _)
            | (SortInner::Datatype(_), _)
            | (SortInner::String, _)
            | (SortInner::FloatingPoint(_, _), _)
            | (SortInner::Uninterpreted(_), _)
            | (SortInner::RegLan, _) => {
                debug!(
                    ?src_sort,
                    ?target_ty,
                    "CHC: apply_cast_with_env - unsupported sort/width combination"
                );
                None
            }
            (_, _) => {
                debug!(
                    ?src_sort,
                    ?target_ty,
                    "CHC: apply_cast_with_env - unsupported sort/width combination"
                );
                None
            }
        }
    }

    /// Generates a tuple sort name from field sorts.
    /// Accepts any field name type (the name component is ignored; only sorts matter).
    pub(in crate::codegen_ay::chc) fn tuple_sort_name<N>(fields: &[(N, Sort)]) -> String {
        let mut name = String::from("Tuple");
        for (_, sort) in fields {
            name.push('_');
            name.push_str(&names::sort_short_name(sort));
        }
        name
    }
}
