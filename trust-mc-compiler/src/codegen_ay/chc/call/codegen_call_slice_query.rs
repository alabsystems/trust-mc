// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC slice query stubs: `SliceIsEmpty` and `SliceFirst`.
//!
//! Extracted from `codegen_call_slice.rs` for file-size compliance (Part of #4130).
//! Both methods use the same 5-strategy length resolution chain.

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;
use super::canonical_zst_expr_for_sort;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto_prebuilt};
use super::codegen_call_misc::CallMisc;
use super::codegen_rules::CodegenRules;
use super::stubs_option_helpers::{OptionHelpers, option_value_sort};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle `SliceIsEmpty` — returns `len == 0`. Part of #3713.
    ///
    /// Length resolution order (mirrors statement backend):
    /// 1. Static `[T; N]` length from operand type
    /// 2. `subslice_len` for known subslices
    /// 3. `translate_ptr_metadata` for `&[T]` / fat-pointer slice receivers
    /// 4. direct `fld_len` read from a resolved slice datatype local
    /// 5. `resolve_slice_arg_length` (sidecar, slice_to_vec_local, iter tracking)
    /// 6. Sound fallback: unconstrained bool
    pub(in crate::codegen_ay::chc) fn codegen_call_slice_is_empty_impl(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        new_output_args: &[Expr],
    ) {
        let args = cx.args;
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);

        // Try to resolve length from the receiver operand.
        let len_expr = args.first().and_then(|receiver| {
            let local = match receiver {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                _ => None,
            };

            // Strategy 1: Static array length from type.
            let receiver_ty = receiver.ty(self.body.locals()).ok();
            let pointee_ty = receiver_ty.and_then(|ty| match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => Some(inner),
                _ => None,
            });
            if let Some(pointee) = pointee_ty {
                if let TyKind::RigidTy(RigidTy::Array(_, const_len)) = pointee.kind() {
                    if let Ok(n) = const_len.eval_target_usize() {
                        return Some(Expr::bitvec_const(n as u128, POINTER_WIDTH));
                    }
                }
            }

            // Strategy 2: subslice_len metadata.
            if let Some(l) = local {
                if let Some(len) = self.ref_resolution.subslice_len.get(&l).cloned() {
                    return Some(len);
                }
            }

            // Strategy 3: use the wide-pointer metadata path for `&[T]`.
            if let Some(len) = self.translate_ptr_metadata(receiver, cx.modified_locals) {
                return Some(len);
            }

            // Strategy 4: read `fld_len` from the resolved slice referent.
            // For `&[T]` parameters, translate_operand_with_modified returns the
            // pointer-typed receiver; resolve_ref_or_const_referent bridges to
            // the pointee slice datatype when CHC has already seeded it.
            if let Some(expr) = self.resolve_ref_or_const_referent(receiver, cx.modified_locals) {
                let expr_for_sort = expr.clone();
                let expr_sort = expr_for_sort.sort();
                if let Some(dt_name) = expr_sort.datatype_name()
                    && let Some(len_sort) = Self::get_dt_field_sort(&expr_for_sort, "fld_len")
                {
                    return Some(expr.field_select(dt_name, "fld_len", len_sort));
                }
            }

            // Strategy 5: resolve_slice_arg_length (sidecar + ref_targets + vec mappings).
            self.resolve_slice_arg_length(args, 0, cx.modified_locals)
        });

        if let Some(len) = len_expr {
            let is_empty = len.eq(zero);
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    is_empty,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_slice::SliceIsEmpty",
                );
                if eq.is_some() {
                    self.emit_goto_rule_extra(
                        cx.from_app,
                        cx.target,
                        new_output_args,
                        cx.stmt_constraints,
                        eq,
                    );
                    return;
                }
            }
        }

        // Fallback: unconstrained (sound over-approximation).
        debug!(fn_name = %self.fn_name, "CHC slice is_empty: length unresolved; fallback");
        emit_sound_fallback_goto_prebuilt(
            self,
            cx.from_app,
            cx.target,
            new_output_args,
            cx.stmt_constraints,
        );
    }

    /// Handle `SliceFirst` — returns `Option<&T>`: `Some(&self[0])` if non-empty, `None` otherwise.
    /// Part of #3768.
    ///
    /// Uses the same 5-strategy length resolution chain as `SliceIsEmpty`.
    /// For the first element, attempts array select at index 0.
    /// Falls back to unconstrained Option (sound over-approximation) when
    /// element access cannot be resolved.
    pub(in crate::codegen_ay::chc) fn codegen_call_slice_first_impl(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        new_output_args: &[Expr],
    ) {
        let args = cx.args;
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);

        // Resolve the destination output variable and its Option sort.
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            debug!(fn_name = %self.fn_name, "CHC slice first: destination unresolved; fallback");
            emit_sound_fallback_goto_prebuilt(
                self,
                cx.from_app,
                cx.target,
                new_output_args,
                cx.stmt_constraints,
            );
            return;
        };
        let dest_sort = dest_var.sort().clone();

        // Resolve length using the same 5-strategy chain as SliceIsEmpty.
        let len_expr = args.first().and_then(|receiver| {
            let local = match receiver {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                _ => None,
            };
            let receiver_ty = receiver.ty(self.body.locals()).ok();
            let pointee_ty = receiver_ty.and_then(|ty| match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => Some(inner),
                _ => None,
            });
            if let Some(pointee) = pointee_ty {
                if let TyKind::RigidTy(RigidTy::Array(_, const_len)) = pointee.kind() {
                    if let Ok(n) = const_len.eval_target_usize() {
                        return Some(Expr::bitvec_const(n as u128, POINTER_WIDTH));
                    }
                }
            }
            if let Some(l) = local {
                if let Some(len) = self.ref_resolution.subslice_len.get(&l).cloned() {
                    return Some(len);
                }
            }
            if let Some(len) = self.translate_ptr_metadata(receiver, cx.modified_locals) {
                return Some(len);
            }
            if let Some(expr) = self.resolve_ref_or_const_referent(receiver, cx.modified_locals) {
                let expr_sort = expr.sort().clone();
                if let Some(dt_name) = expr_sort.datatype_name()
                    && let Some(len_sort) = Self::get_dt_field_sort(&expr, "fld_len")
                {
                    return Some(expr.field_select(dt_name, "fld_len", len_sort));
                }
            }
            self.resolve_slice_arg_length(args, 0, cx.modified_locals)
        });

        let Some(len) = len_expr else {
            debug!(fn_name = %self.fn_name, "CHC slice first: length unresolved; fallback");
            emit_sound_fallback_goto_prebuilt(
                self,
                cx.from_app,
                cx.target,
                new_output_args,
                cx.stmt_constraints,
            );
            return;
        };

        // Part of #4113: detect ZST element type from receiver. For ZST arrays
        // like `[(); N]`, `slice::first()` returns `Option<&()>`. At Reg level,
        // `&()` is value-semantic (Bool(true)), not a BV64 address. Use canonical
        // ZST value `Bool(true)` as payload so it matches promoted constants.
        let zst_elem_ty = args.first().and_then(|receiver| {
            let receiver_ty = receiver.ty(self.body.locals()).ok()?;
            let pointee = match receiver_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
                _ => return None,
            };
            match pointee.kind() {
                TyKind::RigidTy(RigidTy::Array(elem_ty, _))
                | TyKind::RigidTy(RigidTy::Slice(elem_ty)) => {
                    super::codegen_call_kani_model_dst::is_zst_ty(elem_ty).then_some(elem_ty)
                }
                _ => None,
            }
        });

        let zst_payload_sort = if zst_elem_ty.is_some() {
            if self.is_flattened_enum_like_local(dest_local) {
                self.try_state_idx_for_local(dest_local).and_then(|vec_idx| {
                    self.state_var_mgr
                        .output_state_vars
                        .get(vec_idx + 1)
                        .map(|(_, sort)| sort.clone())
                })
            } else {
                option_value_sort(&dest_sort)
            }
        } else {
            None
        };

        // Build the None expression for this Option sort.
        let none_expr = self.make_none_expr_for_option(&dest_sort);

        // `slice::first()` returns `Option<&T>`, so the payload is the address
        // of the first element, not its value. For array-backed receivers at Reg
        // level the plain operand translation collapses `&arr` to the referent
        // value; recover the reference identity through promoted-const metadata
        // or `ref_targets`, then build `Some(addr)` when the slice is non-empty.
        //
        // Part of #4113/#4290: `Option<&T>` is modeled value-semantically when
        // `T` is ZST, so the canonical payload for `Some(&())` is `Bool(true)`.
        // Flattened destinations can still coerce that Bool into a BV slot when
        // older lowering paths expect packed storage.
        let first_ref = if let Some(elem_ty) = zst_elem_ty {
            zst_payload_sort
                .as_ref()
                .and_then(|sort| canonical_zst_expr_for_sort(elem_ty, sort))
                .or_else(|| Some(Expr::bool_const(true)))
        } else {
            args.first().and_then(|receiver| match receiver {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    if let Some(promoted_obj_id) =
                        self.ref_resolution.const_ref_promoted_obj_ids.get(&place.local).copied()
                    {
                        return Some(self.heap_state.promoted_const_address_for(promoted_obj_id));
                    }
                    if let Some(ref_target) =
                        self.ref_resolution.ref_targets.get(&place.local).cloned()
                    {
                        let target_place = rustc_public::mir::Place {
                            local: ref_target.local,
                            projection: ref_target.projections,
                        };
                        return self.translate_ref_to_address(&target_place, cx.modified_locals);
                    }
                    if let Some(receiver_expr) =
                        self.translate_operand_with_modified(receiver, cx.modified_locals)
                    {
                        if receiver_expr.sort().is_bitvec() {
                            return Some(receiver_expr);
                        }
                        if let Some(dt_name) = receiver_expr.clone().sort().datatype_name()
                            && let Some(ptr_field_sort) =
                                Self::get_dt_field_sort(&receiver_expr, "fld_ptr")
                        {
                            return Some(receiver_expr.field_select(
                                dt_name,
                                "fld_ptr",
                                ptr_field_sort,
                            ));
                        }
                    }
                    None
                }
                _ => None,
            })
        };

        let is_nonempty = len.clone().ne(zero);

        // Part of #3768/#4024: treat enum-like flattened destinations the same way
        // as tuple-flattened locals. Some compiletest paths preserve the flattened
        // discriminant/value slots while dropping the tuple-local marker.
        if self.is_flattened_enum_like_local(dest_local) {
            let is_some_val = is_nonempty;
            let payload_val = if let Some(first_ref) = first_ref {
                Some(first_ref)
            } else if let ExprValue::BitVecConst { value: len_const, .. } = len.value() {
                if *len_const == 0u8.into() {
                    // Statically empty: is_some=false, value is don't-care.
                    None
                } else {
                    debug!(
                        fn_name = %self.fn_name,
                        "CHC slice first (flat): non-empty but first-ref unresolved; fallback"
                    );
                    emit_sound_fallback_goto_prebuilt(
                        self,
                        cx.from_app,
                        cx.target,
                        new_output_args,
                        cx.stmt_constraints,
                    );
                    return;
                }
            } else {
                debug!(
                    fn_name = %self.fn_name,
                    "CHC slice first (flat): symbolic length, first-ref unresolved; fallback"
                );
                emit_sound_fallback_goto_prebuilt(
                    self,
                    cx.from_app,
                    cx.target,
                    new_output_args,
                    cx.stmt_constraints,
                );
                return;
            };
            let mut field_values: Vec<Option<Expr>> = vec![Some(is_some_val)];
            field_values.push(payload_val);
            while field_values.len() < self.flattened_field_count(dest_local) {
                field_values.push(None);
            }
            let mut extra_constraints = Vec::new();
            if !self.constrain_flattened_fields_for_call(
                dest_local,
                &field_values,
                &mut extra_constraints,
            ) {
                self.record_sound_fallback_reason("flattened_fields_unconstrained");
            }
            let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                &new_output_args,
                cx.stmt_constraints,
                extra_constraints,
            );
            return;
        }

        // Non-flattened Option Datatype path.
        let result_expr = if let Some(none) = none_expr {
            if let Some(first_ref) = first_ref {
                if let Some(some) = self.make_some_expr_for_option(first_ref, &dest_sort) {
                    // Part of #4290: collapse `ite(true, Some, None)` / `ite(false, ..)`
                    // when the slice length is a compile-time constant. Emitting the
                    // raw ITE here would produce `ite(is-Some(Some x), ..)` tautologies
                    // downstream that PDR fails to simplify during projection,
                    // leading to false CTREX on probe_zst_first and friends.
                    if let ExprValue::BitVecConst { value: len_const, .. } = len.value() {
                        if *len_const == 0u8.into() { none } else { some }
                    } else {
                        Expr::ite(is_nonempty, some, none)
                    }
                } else {
                    debug!(
                        fn_name = %self.fn_name,
                        "CHC slice first: Option<&T> Some(payload) construction failed; fallback"
                    );
                    emit_sound_fallback_goto_prebuilt(
                        self,
                        cx.from_app,
                        cx.target,
                        new_output_args,
                        cx.stmt_constraints,
                    );
                    return;
                }
            } else {
                // For statically-empty slices, `None` is exact even when we cannot
                // materialize a first-element address. For non-empty slices this
                // would be unsound, so fall back instead of fabricating `None`.
                if let ExprValue::BitVecConst { value: len_const, .. } = len.value() {
                    if *len_const == 0u8.into() {
                        none
                    } else {
                        debug!(
                            fn_name = %self.fn_name,
                            "CHC slice first: first-element address unresolved for non-empty slice; fallback"
                        );
                        emit_sound_fallback_goto_prebuilt(
                            self,
                            cx.from_app,
                            cx.target,
                            new_output_args,
                            cx.stmt_constraints,
                        );
                        return;
                    }
                } else {
                    debug!(
                        fn_name = %self.fn_name,
                        "CHC slice first: symbolic length with unresolved first-element address; fallback"
                    );
                    emit_sound_fallback_goto_prebuilt(
                        self,
                        cx.from_app,
                        cx.target,
                        new_output_args,
                        cx.stmt_constraints,
                    );
                    return;
                }
            }
        } else {
            // Can't construct Option at all — sound fallback.
            debug!(fn_name = %self.fn_name, "CHC slice first: Option construction failed; fallback");
            emit_sound_fallback_goto_prebuilt(
                self,
                cx.from_app,
                cx.target,
                new_output_args,
                cx.stmt_constraints,
            );
            return;
        };

        let eq = self.make_coerced_eq_constraint(
            &dest_var,
            result_expr,
            dest_var.sort(),
            dest_local,
            "codegen_call_slice::SliceFirst",
        );
        if eq.is_some() {
            self.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                new_output_args,
                cx.stmt_constraints,
                eq,
            );
            return;
        }

        // Coercion failed — sound fallback.
        debug!(fn_name = %self.fn_name, "CHC slice first: coercion failed; fallback");
        emit_sound_fallback_goto_prebuilt(
            self,
            cx.from_app,
            cx.target,
            new_output_args,
            cx.stmt_constraints,
        );
    }
}
