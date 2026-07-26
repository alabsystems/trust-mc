// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Flattened tuple/enum/struct local assignment helpers for CHC block encoding.
//!
//! Extracted from codegen_stmt.rs per #2226.
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.
//!
//! Constraint emission utilities (`constrain_flattened_fields`, `constrain_flattened_pair`,
//! etc.) extracted to `codegen_stmt_flatten_constrain.rs` (Part of #3199, D3).
//!
//! Copy/move patterns (4, 5), generic rvalue fallback, `collect_leaf_exprs`,
//! and `propagate_collection_len_cap_from_flattened_aggregate` extracted to
//! `codegen_stmt_flatten_copy.rs` per #4130.
//!
//! Flattened locals (Option, Result, checked-op tuples, String, closures, etc.)
//! decompose a single MIR local into N consecutive scalar state vars
//! (fld0..fldN-1). These helpers handle the repeated pattern of constraining
//! fields and tracking constraint replacement indices.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{AggregateKind, BinOp, Operand, Place, Rvalue};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::rustc_public_bridge::IndexedVal;

use super::ChcCtx;
use super::codegen_expr_signedness::ExprSignedness;
// Re-export collect_leaf_exprs so existing callers via
// `codegen_stmt_flatten::collect_leaf_exprs` continue to resolve.
pub(in crate::codegen_ay::chc) use super::codegen_stmt_flatten_copy::collect_leaf_exprs;
use super::stmt_accumulator::StmtAccumulator;
use crate::codegen_ay::chc::codegen_ctx::types::CollectionProjectionKind;
use crate::codegen_ay::shared::signedness_fallback_for_arithmetic;
use crate::codegen_ay::types::ty_to_bv_width;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate an aggregate operand for a flattened destination field.
    ///
    /// Most flattened aggregate operands can use the normal operand translator.
    /// Ref-typed operands are special at Reg level: `_tmp = &arr` deliberately
    /// stores value semantics (the referent array) so direct deref consumers can
    /// stay concrete, but tuple locals inside `assert_eq!` and similar macros
    /// need the reference value itself. When the destination field expects a
    /// pointer-sort slot and the normal translation produced a non-pointer value,
    /// recover the reference address via promoted-const metadata or `ref_targets`.
    fn translate_flattened_aggregate_operand(
        &mut self,
        operand: &Operand,
        dest_local: usize,
        field_idx: usize,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        let translated = self.translate_operand_with_modified(operand, modified_locals);
        let expected_sort = self
            .try_state_idx_for_local(dest_local)
            .and_then(|vec_idx| self.state_var_mgr.output_state_vars.get(vec_idx + field_idx))
            .map(|(_, sort)| sort.clone());
        let operand_ty = operand.ty(self.body.locals()).ok()?;
        let is_ref_like = matches!(
            operand_ty.kind(),
            TyKind::RigidTy(RigidTy::Ref(_, _, _) | RigidTy::RawPtr(_, _))
        );

        if !is_ref_like || !expected_sort.as_ref().is_some_and(Sort::is_bitvec) {
            return translated;
        }
        if translated.as_ref().is_some_and(|expr| expr.sort().is_bitvec()) {
            return translated;
        }

        let place = match operand {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => place,
            _ => return translated,
        };

        if let Some(promoted_obj_id) =
            self.ref_resolution.const_ref_promoted_obj_ids.get(&place.local).copied()
        {
            return Some(self.heap_state.promoted_const_address_for(promoted_obj_id));
        }

        if let Some(ref_target) = self.ref_resolution.ref_targets.get(&place.local).cloned() {
            let target_place =
                Place { local: ref_target.local, projection: ref_target.projections };
            if let Some(addr) = self.translate_ref_to_address(&target_place, modified_locals) {
                return Some(addr);
            }
        }

        translated
    }

    /// Try to encode an assignment to a flattened tuple/enum/struct local.
    ///
    /// Handles rvalue patterns targeting flattened locals:
    /// 1. `CheckedBinaryOp` → (result_value, overflow_bool)
    /// 2. `Aggregate(_, ops)` with N matching operands → N field values
    ///    2b. `Aggregate(_, ops)` with recursive decomposition → leaf values
    /// 3. `Aggregate(Adt(_, variant), ops)` → (discriminant_bool, payload) for Option/Result
    /// 4. `Use(Copy/Move(src))` where src is also flattened (no projection) → copy all fields
    /// 5. `Use(Copy/Move(src))` where src has field projections → translate + decompose
    ///
    /// Returns `true` if handled (caller should `continue`).
    /// Part of #3517: accepts `StmtAccumulator` instead of raw triple.
    pub(in crate::codegen_ay::chc) fn try_encode_flattened_local_assign(
        &mut self,
        local_idx: usize,
        rhs: &'body Rvalue,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let field_count = self.flattened_field_count(local_idx);
        debug!(
            fn_name = %self.fn_name, local_idx, field_count,
            rhs_discr = ?std::mem::discriminant(rhs),
            "flatten_assign_entry",
        );
        if let Rvalue::Aggregate(kind, operands) = rhs {
            let kind_name = match kind {
                AggregateKind::Array(_) => "Array",
                AggregateKind::Tuple => "Tuple",
                AggregateKind::Adt(_, _, _, _, _) => "Adt",
                AggregateKind::Closure(_, _) => "Closure",
                AggregateKind::Coroutine(_, _) => "Coroutine",
                _ => "Other",
            };
            debug!(
                fn_name = %self.fn_name, local_idx, field_count,
                operands_len = operands.len(), kind_name,
                "flatten_assign: aggregate",
            );
        }

        // Pattern 1: CheckedBinaryOp → (result, overflow) — always 2-field
        if let Rvalue::CheckedBinaryOp(op, lhs_op, rhs_op) = rhs {
            let lhs_val = self.translate_operand_with_modified(lhs_op, acc.modified);
            let rhs_val = self.translate_operand_with_modified(rhs_op, acc.modified);
            if let (Some(l), Some(r)) = (lhs_val, rhs_val) {
                // For shift operations, only the value operand's (LHS) signedness
                // matters; the shift amount may have a different type in MIR.
                let is_signed = if matches!(
                    op,
                    BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked
                ) {
                    self.operand_signedness(lhs_op)
                } else {
                    self.is_signed_integer_op(lhs_op, rhs_op)
                }
                .unwrap_or_else(|| signedness_fallback_for_arithmetic("checked_binop"));
                // Part of #3043: derive BV width from LHS operand's MIR type.
                // Part of #3243: bail instead of defaulting to 32 on type resolution failure.
                let Some(int_bv_width) =
                    lhs_op.ty(self.body.locals()).ok().and_then(ty_to_bv_width)
                else {
                    return false;
                };
                if let Some((result, overflow)) =
                    self.translate_checked_binop_flat(*op, l, r, is_signed, int_bv_width)
                {
                    self.constrain_flattened_pair(local_idx, result, Some(overflow), acc);
                    debug!(
                        local_idx,
                        "CHC: assigned flattened CheckedBinaryOp to 2 scalar state vars"
                    );
                    return true;
                }
            }
        }

        // BV-flattened multi-constructor enum Aggregate delegated to
        // codegen_stmt_flatten_copy.rs (Part of #4130).
        if self.try_encode_bv_flattened_enum(local_idx, rhs, acc, field_count) {
            return true;
        }

        // Pattern 2: Aggregate with operands matching the flattened field count.
        // This runs before the Adt-specific pattern 3 because structs like
        // Range { start, end } and String { ptr, len, cap } are
        // `AggregateKind::Adt` with N operands but should use the symmetric
        // N-field constraint, not discriminant+payload.
        // Only falls through to pattern 3 when operands can't be translated.
        if let Rvalue::Aggregate(_, operands) = rhs {
            let has_discr = self.flatten.flattened_enum_discr.contains_key(&local_idx);
            debug!(
                fn_name = %self.fn_name, local_idx,
                ops = operands.len(), field_count, has_discr,
                p2 = operands.len() == field_count && !has_discr,
                p2b = operands.len() < field_count && !has_discr,
                "flatten_assign: P2 check",
            );
        }
        if let Rvalue::Aggregate(kind, operands) = rhs
            && operands.len() == field_count
            && !self.flatten.flattened_enum_discr.contains_key(&local_idx)
        {
            let translated: Vec<Option<Expr>> = operands
                .iter()
                .enumerate()
                .map(|(field_idx, op)| {
                    self.translate_flattened_aggregate_operand(
                        op,
                        local_idx,
                        field_idx,
                        acc.modified,
                    )
                })
                .collect();
            if translated.iter().all(std::option::Option::is_some) {
                self.constrain_flattened_fields(local_idx, &translated, acc);
                // Part of #3348: Propagate presence/len/cap aliases from collection
                // operands in ADT Aggregate construction. Without this, struct locals
                // that embed BTreeMap/HashMap fields (e.g., `Array { stores: BTreeMap }`)
                // lose the presence alias, causing get() to read a disconnected
                // presence array from the insert() path.
                if matches!(kind, AggregateKind::Adt(_, _, _, _, _)) {
                    self.propagate_collection_presence_from_aggregate(local_idx, operands);
                    self.propagate_collection_len_cap_from_flattened_aggregate(
                        local_idx,
                        operands,
                        acc.constraints,
                    );
                }
                // Part of #4101: Propagate ref_targets through flattened aggregate
                // construction. When a single-field transparent wrapper (Container<T>,
                // NonNull<T>, Unique<T>) is flattened to a single BV64 pointer,
                // the aggregate operand's ref_target must be carried to the wrapper
                // local so that later deref of `wrapper.0` resolves through ref_targets.
                if field_count == 1 {
                    if let Some(Operand::Copy(place) | Operand::Move(place)) = operands.first()
                        && place.projection.is_empty()
                    {
                        let src_local: usize = place.local;
                        if let Some(ref_target) =
                            self.ref_resolution.ref_targets.get(&src_local).cloned()
                        {
                            debug!(
                                local_idx,
                                src_local,
                                "flatten_assign: propagated ref_target from aggregate operand (#4101)"
                            );
                            self.ref_resolution.ref_targets.insert(local_idx, ref_target);
                            self.ref_resolution.call_forwarded_raw_ptrs.insert(local_idx);
                        }
                    }
                }
                debug!(
                    local_idx,
                    field_count,
                    kind = ?std::mem::discriminant(kind),
                    "CHC: assigned flattened Aggregate to {n} scalar state vars",
                    n = field_count
                );
                return true;
            }
        }

        // Pattern 2b: Recursively flattened struct Aggregate (Part of #2970).
        // When the Aggregate has fewer operands than leaf state vars (because
        // some operands are themselves nested Datatypes that get recursively
        // flattened), decompose operand expressions into leaf scalar values.
        // Example: `Outer { inner: Point { x: 5, y: 6 }, value: 100 }`
        //   - inner operand → Point_mk(5, 6) → decompose to [5, 6]
        //   - value operand → 100 → [100]
        //   - leaf_values = [5, 6, 100] → matches 3 leaf state vars.
        //
        // Part of #3348: When an operand is a flattened local (e.g., Vec<bool>
        // in `Bits(vec_local)`), translate_operand returns None because flattened
        // locals have no single expression. Fall back to reading leaf state vars
        // directly from the source flattened local.
        if let Rvalue::Aggregate(kind, operands) = rhs
            && operands.len() < field_count
            && !self.flatten.flattened_enum_discr.contains_key(&local_idx)
        {
            let mut leaf_values: Vec<Option<Expr>> = Vec::with_capacity(field_count);
            let mut all_resolved = true;

            for op in operands {
                let translate_result = self.translate_operand_with_modified(op, acc.modified);
                if let Some(expr) = translate_result {
                    collect_leaf_exprs(&expr, &mut leaf_values);
                } else if let Operand::Copy(place) | Operand::Move(place) = op
                    && place.projection.is_empty()
                    && self.flatten.flattened_tuple_locals.contains(&place.local)
                {
                    // Part of #3348: operand is a flattened local — read its leaf
                    // state vars directly instead of failing the whole aggregate.
                    let src_n = self.flattened_field_count(place.local);
                    for i in 0..src_n {
                        let fexpr = self.flattened_local_field_expr(place.local, i, acc.modified);
                        leaf_values.push(fexpr);
                    }
                } else {
                    all_resolved = false;
                    break;
                }
            }

            if all_resolved && leaf_values.len() == field_count {
                // Part of #3984: Array IntoIter leaf reordering.
                // MIR IntoIter has fields [data: Array, alive: IndexRange(start, end)]
                // producing leaf order [Array, BV64, BV64]. Our sort is
                // IntoIter { PolymorphicIter { fld_alive: IndexRange, fld_data: Array } }
                // producing leaf order [BV64, BV64, Array]. Rotate the Array from
                // position 0 to the end to match the flattened sort layout.
                if self.collections.projection_locals.get(&local_idx)
                    == Some(&CollectionProjectionKind::ArrayIntoIter)
                    && leaf_values.len() == 3
                    && leaf_values[0].as_ref().is_some_and(|e| e.sort().is_array())
                    && leaf_values[1].as_ref().is_some_and(|e| e.sort().is_bitvec())
                    && leaf_values[2].as_ref().is_some_and(|e| e.sort().is_bitvec())
                {
                    leaf_values.rotate_left(1);
                    debug!(
                        local_idx,
                        "CHC: reordered ArrayIntoIter leaves [Array,BV,BV] -> [BV,BV,Array]"
                    );
                }

                self.constrain_flattened_fields(local_idx, &leaf_values, acc);
                // Part of #3348: Propagate presence/len/cap aliases for recursive
                // flattened ADT Aggregates (same rationale as Pattern 2).
                if matches!(kind, AggregateKind::Adt(_, _, _, _, _)) {
                    self.propagate_collection_presence_from_aggregate(local_idx, operands);
                    self.propagate_collection_len_cap_from_flattened_aggregate(
                        local_idx,
                        operands,
                        acc.constraints,
                    );
                }
                debug!(
                    local_idx,
                    field_count,
                    operands = operands.len(),
                    kind = ?std::mem::discriminant(kind),
                    "CHC: assigned recursively flattened Aggregate to {n} leaf state vars",
                    n = field_count
                );
                return true;
            }
        }

        // Pattern 3: Adt aggregate (Option/Result) assignment to flattened locals.
        //
        // Most flattened enum locals use a Bool discriminant in fld0. Some legacy
        // layouts still carry the full ADT value in fld0 and payload in fld1. Pick
        // the fld0 encoding mode from the declared state-variable sort.
        //
        // For 3-field heterogeneous Result<T,E>: fld0=is_ok, fld1=ok_val, fld2=err_val.
        // Ok variant constrains fld0=true + fld1=payload, Err constrains fld0=false + fld2=payload.
        if let Rvalue::Aggregate(AggregateKind::Adt(_, variant_idx, _, _, _), operands) = rhs {
            // Part of #3768: graceful fallback instead of panic
            let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
                return false;
            };
            let fld0_sort =
                self.state_var_mgr.output_state_vars.get(vec_idx).map(|(_, sort)| sort.clone());
            let fld0_is_bool = fld0_sort.as_ref().is_some_and(Sort::is_bool);

            let payload = if let Some(operand) = operands.first() {
                let payload_slot_sort = if field_count == 3
                    && fld0_is_bool
                    && self.flatten.flattened_enum_discr.contains_key(&local_idx)
                {
                    let true_discr = self.flatten.flattened_enum_discr[&local_idx].0;
                    let is_true_variant = (variant_idx.to_index() as u64) == true_discr;
                    let target_slot_offset = if is_true_variant { 1 } else { 2 };
                    self.state_var_mgr
                        .output_state_vars
                        .get(vec_idx + target_slot_offset)
                        .map(|(_, sort)| sort.clone())
                } else {
                    self.state_var_mgr
                        .output_state_vars
                        .get(vec_idx + 1)
                        .map(|(_, sort)| sort.clone())
                };
                payload_slot_sort
                    .as_ref()
                    .and_then(|sort| self.canonical_ref_to_zst_payload_expr(operand, sort))
                    .or_else(|| self.translate_operand_with_modified(operand, acc.modified))
            } else {
                None
            };

            // Determine discriminant expression
            let discr_expr = if fld0_is_bool {
                let (true_discr, _) = self.infer_flattened_discr(local_idx);
                Some(Expr::bool_const((variant_idx.to_index() as u64) == true_discr))
            } else {
                None
            };

            // 3-field heterogeneous Result: (is_ok, ok_val, err_val)
            // Guard: only use this path when the payload fits in a single slot.
            // Option<struct> locals (e.g., Option<Point>) also have field_count==3
            // but need leaf decomposition (disc, x, y), not Ok/Err partitioning.
            // Part of #435: check payload sort against fld1 slot sort.
            // Part of #4068: check the variant-appropriate slot. For the true
            // variant, the payload targets fld1 (vec_idx+1). For the false variant,
            // the payload targets fld2 (vec_idx+2). Previously always checked fld1,
            // causing ControlFlow Break(BV128) to fail the guard when fld1 is BV64
            // (Continue's slot), even though fld2 (Break's slot) may accept it.
            if field_count == 3
                && fld0_is_bool
                && self.flatten.flattened_enum_discr.contains_key(&local_idx)
            {
                let true_discr = self.flatten.flattened_enum_discr[&local_idx].0;
                let is_true_variant = (variant_idx.to_index() as u64) == true_discr;
                let target_slot_offset = if is_true_variant { 1 } else { 2 };
                let payload_fits_slot = payload.as_ref().map_or(true, |p| {
                    self.state_var_mgr
                        .output_state_vars
                        .get(vec_idx + target_slot_offset)
                        .is_some_and(|(_, slot_sort)| *p.sort() == *slot_sort)
                });
                if payload_fits_slot {
                    let values = if is_true_variant {
                        // Ok variant: fld0=true, fld1=ok_payload, fld2=unconstrained
                        vec![discr_expr, payload, None]
                    } else {
                        // Err variant: fld0=false, fld1=unconstrained, fld2=err_payload
                        vec![discr_expr, None, payload]
                    };
                    self.constrain_flattened_fields(local_idx, &values, acc);
                    debug!(
                        local_idx,
                        variant = variant_idx.to_index(),
                        is_true_variant,
                        "CHC: assigned flattened 3-field Result to (is_ok, ok_val, err_val)"
                    );
                    return true;
                }
            }

            // Part of #3207: General N-field flattened enum with Bool discriminant.
            // Decomposes payload DatatypeConstructor expressions into leaf scalar
            // values, enabling correct constraint emission for Option<struct> locals
            // (e.g., Option<MyType { val: u8 }> flattened to [Bool, BitVec8]).
            if fld0_is_bool && self.flatten.flattened_enum_discr.contains_key(&local_idx) {
                let mut values: Vec<Option<Expr>> = vec![discr_expr];
                if let Some(ref payload_expr) = payload {
                    let mut leaves = Vec::new();
                    collect_leaf_exprs(payload_expr, &mut leaves);
                    values.extend(leaves);
                }
                while values.len() < field_count {
                    values.push(None);
                }
                if values.len() == field_count {
                    self.constrain_flattened_fields(local_idx, &values, acc);
                    debug!(
                        local_idx,
                        variant = variant_idx.to_index(),
                        field_count,
                        "CHC: assigned flattened enum via leaf decomposition ({n} fields)",
                        n = field_count
                    );
                    return true;
                }
            }

            // Legacy non-Bool-discriminant path: fld0 carries the full ADT value.
            let fld0_expr = if let Some(full_adt_value) =
                self.translate_rvalue_with_modified(rhs, acc.modified, Some(local_idx))
            {
                full_adt_value
            } else {
                // Part of #3038: emit self-loop for all flattened fields instead
                // of leaving them unconstrained.
                acc.modified.insert(local_idx);
                let emitted = self.emit_flattened_self_loop_constraints(local_idx, acc);
                if emitted == 0 {
                    // No flattened fields found — emit BoolConst(true) placeholder
                    // to maintain constraint-or-unchanged invariant.
                    acc.replace_constraint(local_idx, Expr::bool_const(true));
                }
                self.record_sound_fallback_reason("flatten_pair_resolution_failed");
                return true;
            };

            self.constrain_flattened_pair(local_idx, fld0_expr, payload, acc);
            debug!(
                local_idx,
                variant = variant_idx.to_index(),
                fld0_is_bool,
                "CHC: assigned flattened ADT aggregate (legacy non-Bool discr)"
            );
            return true;
        }

        // Patterns 4, 5, and generic rvalue fallback delegated to
        // codegen_stmt_flatten_copy.rs (Part of #4130).
        if self.try_encode_flattened_copy_or_rvalue(local_idx, rhs, acc, field_count) {
            return true;
        }

        // No flattened pattern matched — mark as modified and emit self-loop
        // constraints for all flattened fields to preserve previous values.
        // Part of #3038: constraint-or-unchanged invariant.
        warn!(
            fn_name = %self.fn_name,
            local_idx,
            field_count,
            rhs_discr = ?std::mem::discriminant(rhs),
            "flatten_self_loop_fallback: no pattern matched"
        );
        acc.modified.insert(local_idx);
        let emitted = self.emit_flattened_self_loop_constraints(local_idx, acc);
        if emitted == 0 {
            // No flattened fields found — emit BoolConst(true) placeholder
            // to maintain constraint-or-unchanged invariant.
            acc.replace_constraint(local_idx, Expr::bool_const(true));
        }
        self.record_sound_fallback_reason("flatten_self_loop_fallback");
        // Return true: we handled the assignment (with self-loop fallback).
        // Previously returned false which caused the caller to retry via the
        // non-flattened path, but that path can't handle flattened locals
        // (it would emit a single self-loop for vec_idx only, missing fields).
        true
    }
}
