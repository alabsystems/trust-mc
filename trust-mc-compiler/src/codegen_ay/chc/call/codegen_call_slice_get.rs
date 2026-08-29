// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC slice get and range-full identity stubs.
//!
//! Extracted from `codegen_call_slice.rs` for file-size compliance (Part of #4130).
//! - `SliceGet`: checked element access returning `Option<&T>`.
//! - `codegen_call_slice_range_full_identity`: `Index::index(slice, RangeFull)` as identity.

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::args::ChcTrackLevel;
use crate::codegen_ay::provenance::Loc;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto_prebuilt};
use super::codegen_call_misc::CallMisc;
use super::codegen_rules::CodegenRules;
use super::stubs_option_helpers::OptionHelpers;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle `SliceGet` — returns `Option<&T>`: `Some(&self[idx])` if `idx < len`, `None` otherwise.
    /// Part of #4174.
    ///
    /// Generalizes `SliceFirst` to an arbitrary index. The index is taken from `args[1]`.
    /// When the index is a constant 0 this degenerates to `SliceFirst` behavior.
    pub(in crate::codegen_ay::chc) fn codegen_call_slice_get_impl(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        new_output_args: &[Expr],
    ) {
        let args = cx.args;

        // Need at least 2 args: (slice_or_self, index).
        if args.len() < 2 {
            debug!(fn_name = %self.fn_name, "CHC slice get: insufficient args; fallback");
            emit_sound_fallback_goto_prebuilt(
                self,
                cx.from_app,
                cx.target,
                new_output_args,
                cx.stmt_constraints,
            );
            return;
        }

        // Resolve the index operand to a BV expression.
        let idx_expr = self
            .translate_operand_with_modified(&args[1], cx.modified_locals)
            .and_then(|expr| self.coerce_to_pointer_width(expr));

        let Some(idx_expr) = idx_expr else {
            debug!(fn_name = %self.fn_name, "CHC slice get: index unresolved; fallback");
            emit_sound_fallback_goto_prebuilt(
                self,
                cx.from_app,
                cx.target,
                new_output_args,
                cx.stmt_constraints,
            );
            return;
        };

        // Resolve destination output variable and its Option sort.
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            debug!(fn_name = %self.fn_name, "CHC slice get: destination unresolved; fallback");
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

        // Resolve length using the same 5-strategy chain as SliceFirst/SliceIsEmpty.
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
                return Some(len.into_expr());
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
            debug!(fn_name = %self.fn_name, "CHC slice get: length unresolved; fallback");
            emit_sound_fallback_goto_prebuilt(
                self,
                cx.from_app,
                cx.target,
                new_output_args,
                cx.stmt_constraints,
            );
            return;
        };

        // Detect ZST element type from receiver (same as SliceFirst).
        let is_zst_elem = args
            .first()
            .and_then(|receiver| {
                let receiver_ty = receiver.ty(self.body.locals()).ok()?;
                let pointee = match receiver_ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                    | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
                    _ => return None,
                };
                match pointee.kind() {
                    TyKind::RigidTy(RigidTy::Array(elem_ty, _))
                    | TyKind::RigidTy(RigidTy::Slice(elem_ty)) => {
                        Some(super::codegen_call_kani_model_dst::is_zst_ty(elem_ty))
                    }
                    _ => None,
                }
            })
            .unwrap_or(false);

        // Build None expression for this Option sort.
        let none_expr = self.make_none_expr_for_option(&dest_sort);

        // Build the element reference. For ZST, use canonical BV64(1).
        // Otherwise, resolve from receiver backing + index offset.
        let is_inbounds = idx_expr.clone().bvult(len);

        let elem_ref = if is_zst_elem {
            Some(Expr::bitvec_const(1u64, POINTER_WIDTH))
        } else {
            args.first().and_then(|receiver| match receiver {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    // For promoted const arrays, compute base + idx * elem_size.
                    if let Some(promoted_obj_id) =
                        self.ref_resolution.const_ref_promoted_obj_ids.get(&place.local).copied()
                    {
                        let base = self.heap_state.promoted_const_address_for(promoted_obj_id);
                        // For index 0, just return the base address.
                        if let ExprValue::BitVecConst { value, .. } = idx_expr.value() {
                            if *value == 0u8.into() {
                                return Some(base);
                            }
                        }
                        // For non-zero index, compute base + idx * elem_size.
                        // Fall through to other resolution paths if elem_size unknown.
                        return None;
                    }
                    // For ref_targets, translate_ref_to_address gives the base.
                    if let Some(ref_target) =
                        self.ref_resolution.ref_targets.get(&place.local).cloned()
                    {
                        let target_place =
                            Place { local: ref_target.local, projection: ref_target.projections };
                        if let ExprValue::BitVecConst { value, .. } = idx_expr.value() {
                            if *value == 0u8.into() {
                                // This closure's other lanes hand back pointer
                                // VALUES (a bv receiver, an `fld_ptr` select),
                                // so `elem_ref` is not uniformly an address and
                                // must not be typed as one; the address lane
                                // drops its tag here rather than laundering the
                                // others into `Loc`.
                                return self
                                    .translate_ref_to_address(&target_place, cx.modified_locals)
                                    .map(Loc::into_expr);
                            }
                        }
                        return None;
                    }
                    // For BV64 pointer values, just use the pointer directly for index 0.
                    if let Some(receiver_expr) =
                        self.translate_operand_with_modified(receiver, cx.modified_locals)
                    {
                        if receiver_expr.sort().is_bitvec() {
                            if let ExprValue::BitVecConst { value, .. } = idx_expr.value() {
                                if *value == 0u8.into() {
                                    return Some(receiver_expr);
                                }
                            }
                            return None;
                        }
                        if let Some(dt_name) = receiver_expr.clone().sort().datatype_name()
                            && let Some(ptr_field_sort) =
                                Self::get_dt_field_sort(&receiver_expr, "fld_ptr")
                        {
                            let base =
                                receiver_expr.field_select(dt_name, "fld_ptr", ptr_field_sort);
                            if let ExprValue::BitVecConst { value, .. } = idx_expr.value() {
                                if *value == 0u8.into() {
                                    return Some(base);
                                }
                            }
                            return None;
                        }
                    }
                    None
                }
                _ => None,
            })
        };

        // Flattened enum-like path (same structure as SliceFirst).
        if self.is_flattened_enum_like_local(dest_local) {
            let is_some_val = is_inbounds;
            let payload_val = if let Some(elem_ref) = elem_ref {
                Some(elem_ref)
            } else {
                debug!(
                    fn_name = %self.fn_name,
                    "CHC slice get (flat): elem_ref unresolved; fallback"
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
            if let Some(elem_ref) = elem_ref {
                if let Some(some) = self.make_some_expr_for_option(elem_ref, &dest_sort) {
                    Expr::ite(is_inbounds, some, none)
                } else {
                    debug!(
                        fn_name = %self.fn_name,
                        "CHC slice get: Option<&T> Some(payload) construction failed; fallback"
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
                    "CHC slice get: elem_ref unresolved; fallback"
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
            debug!(fn_name = %self.fn_name, "CHC slice get: Option construction failed; fallback");
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
            "codegen_call_slice::SliceGet",
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
        debug!(fn_name = %self.fn_name, "CHC slice get: coercion failed; fallback");
        emit_sound_fallback_goto_prebuilt(
            self,
            cx.from_app,
            cx.target,
            new_output_args,
            cx.stmt_constraints,
        );
    }

    /// Handle `Index::index(slice, RangeFull)` as identity. Part of #3495.
    pub(super) fn codegen_call_slice_range_full_identity(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        slice_arg: &Operand,
    ) {
        let modified_locals = cx.modified_locals;
        debug!(fn_name = %self.fn_name, "CHC slice index: RangeFull identity propagation");

        // RangeFull preserves the source length, but may not create authority
        // from a path-insensitive backing-table entry.  Derive the length from
        // the conflict-sticky MIR provenance walk before resolving backing
        // storage: that walk retains unanimous joins (4 vs 4) and rejects
        // conflicting joins (4 vs 8).  Clear any stale destination metadata
        // first so a failed derivation cannot inherit a fact from another CFG
        // producer visited earlier.
        self.clear_path_insensitive_ref_metadata(dest_local);
        let exact_source_len = Self::operand_local(slice_arg)
            .and_then(|local| self.try_resolve_slice_len_for_local(local))
            .map(|len| Expr::bitvec_const(len as u128, POINTER_WIDTH));
        let slice_backing = self.resolve_slice_backing(slice_arg, modified_locals);
        let slice_value = self.resolve_ref_or_const_referent(slice_arg, modified_locals);
        if let Some(backing) = slice_backing.as_ref() {
            self.ref_resolution.const_ref_values.insert(dest_local, backing.data.as_expr().clone());
            if *backing.offset.as_expr() != Expr::bitvec_const(0u64, POINTER_WIDTH) {
                self.ref_resolution
                    .subslice_offset
                    .insert(dest_local, backing.offset.as_expr().clone());
            } else {
                self.ref_resolution.subslice_offset.remove(&dest_local);
            }
            self.ref_resolution.subslice_len.insert(dest_local, backing.len.as_expr().clone());
        } else if let Some(len) = exact_source_len {
            self.ref_resolution.subslice_len.insert(dest_local, len);
        }
        // Compute pointer-level value BEFORE the Mem-level bridge so it can be
        // stored into typed memory (which expects BV64 pointer sort, not Array sort).
        let source_expr = self.translate_operand_with_modified(slice_arg, modified_locals);

        // Part of #3528/#3495: Mem-level bridge — mirror result into typed memory
        // so subsequent SubSlice references through load_from_memory read correct data.
        // Store the BV64 pointer value (source_expr), not the Array-sorted slice data (sv),
        // to match the element sort of type-indexed memory arrays like mem_ref_slice_i32.
        let mut mem_constraints: Vec<Expr> = Vec::new();
        if self.track_level >= ChcTrackLevel::Mem {
            let store_val = source_expr.as_ref().or(slice_value.as_ref());
            if let Some(val) = store_val {
                let local_place = Place { local: dest_local, projection: vec![] };
                if let Some(addr_expr) =
                    self.translate_ref_to_address(&local_place, modified_locals)
                {
                    let local_ty = self.body.locals()[dest_local].ty;
                    if let Some(sc) = self.build_memory_store(addr_expr, val.clone(), local_ty) {
                        mem_constraints.push(sc);
                    }
                    mem_constraints.append(&mut self.heap_state.pending_updates);
                    mem_constraints
                        .append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
                }
            }
        }

        // Part of #2970, #3528: build_output_args AFTER mem bridge flush.
        let out = self.build_output_args(modified_locals, &[dest_local]);

        // Part of #3528: Filter superseded store chain constraints.
        let filtered_stmts = super::heap_store_chains::filter_superseded_store_chains(
            cx.stmt_constraints,
            &mem_constraints,
        );
        let effective_stmts: &[Expr] = filtered_stmts.as_deref().unwrap_or(cx.stmt_constraints);

        // Try pointer-level equality first, then array-value fallback.
        for (expr, site) in source_expr
            .into_iter()
            .map(|e| (e, "RangeFull_identity"))
            .chain(slice_value.into_iter().map(|e| (e, "RangeFull_identity_value")))
        {
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    expr,
                    dest_var.sort(),
                    dest_local,
                    site,
                );
                if eq.is_some() {
                    let extra: Vec<Expr> =
                        eq.into_iter().chain(mem_constraints.iter().cloned()).collect();
                    self.emit_goto_rule_extra(cx.from_app, cx.target, &out, effective_stmts, extra);
                    return;
                }
            }
        }
        self.emit_goto_rule(cx.from_app, cx.target, &out, effective_stmts);
    }
}
