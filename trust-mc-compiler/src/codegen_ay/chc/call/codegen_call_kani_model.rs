// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Kani model function handling (any, offset, simd_bitmask). Extracted per #2408.

use ay_bindings::{Expr, ExprValue};
use rustc_public::CrateDef;
use rustc_public::mir::{Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{BTreeMap, HashMap, HashSet};
use tracing::debug;
use trust_mc_core::violation::PropertyKind;

use crate::args::ChcTrackLevel;
use crate::codegen_ay::provenance::Loc;
use crate::codegen_ay::shared::IntoOption;
use crate::codegen_ay::types::{
    POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ty_to_bv_width,
};

use super::super::stub_codegen::stubs_option_helpers::OptionHelpers;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_closure::{
    resolve_closure_body_for_operand, resolve_closure_body_via_unique_aggregate_def,
};
use super::codegen_call_coerce::{
    CallCoerce, emit_sound_fallback_goto, emit_sound_fallback_goto_extra,
};
use super::codegen_call_result_mem::build_call_result_memory_bridge_constraints;
use super::codegen_call_slice_helpers::ResolvedSliceBacking;
use super::codegen_expr_signedness::{ExprSignedness, ty_signedness};
use super::codegen_rules::CodegenRules;
use super::codegen_types::CodegenTypes;
use super::inline_body::translate_closure_inline_result;
use super::pointer_step::step_split_pointer;
use super::ptr_offset_common;
use super::{
    ChcCtx, KaniModel, RelationApp, Rule, RuleBody, UnknownProjectionPolicy, chc_debug_enabled,
    chc_fresh_name, codegen_decl_flatten, collect_field_projections, declare_pending_var,
};

pub(in crate::codegen_ay::chc) fn simd_bitmask_lane_bit(mask_width: u32, lane_idx: usize) -> Expr {
    let one = Expr::bitvec_const(1u64, mask_width);
    let shift = Expr::bitvec_const(lane_idx as u64, mask_width);
    one.bvshl(shift)
}

/// A `KaniModel::Offset` safety obligation with its Kani-parity classification
/// (marker: offset_isize_overflow_precise).
///
/// Splits the offset-model UB into the two INDEPENDENT obligation families the
/// Rust/Kani `offset` model checks:
///   (1) isize-overflow — `count` fits `isize` ("Offset value overflows
///       isize") and `count * size_of::<T>()` fits `isize` ("Offset in bytes
///       overflows isize"). PRECISE, pure arithmetic, provenance-INDEPENDENT.
///   (2) in-bounds — wrap / same-object / allocation-size / provenance-valid.
///       Provenance-DEPENDENT; keeps the existing fail-closed net (the
///       `OffsetProvenanceUnresolved` demotion) untouched.
/// Carrying the exact Kani message lets the driver report the precise UB
/// verbatim instead of the generic "CHC verification: memory safety" line.
struct ModelOffsetCheck {
    cond: Expr,
    kind: PropertyKind,
    message: Option<String>,
}

impl ModelOffsetCheck {
    /// Obligation (1): a precise isize-overflow assertion, reported with its
    /// exact Kani description (`PropertyKind::PointerOverflow`).
    fn overflow(cond: Expr, message: &str) -> Self {
        Self { cond, kind: PropertyKind::PointerOverflow, message: Some(message.to_string()) }
    }

    /// Obligation (2): a provenance-dependent in-bounds assertion, reported as
    /// the existing generic "CHC verification: memory safety" line.
    fn memory(cond: Expr) -> Self {
        Self { cond, kind: PropertyKind::MemorySafety, message: None }
    }
}

const WRITE_ANY_SLICE_MAX_CONCRETE_ELEMS: usize = 64;

fn concrete_len_from_expr(expr: &Expr) -> Option<usize> {
    match expr.value() {
        ExprValue::BitVecConst { value, .. } | ExprValue::IntConst(value) => {
            usize::try_from(value).ok()
        }
        _ => None,
    }
}

fn write_any_slim_projected_validity_bounds(
    ty: rustc_public::ty::Ty,
    expr: &Expr,
    int_lift: bool,
) -> Vec<Expr> {
    let mut constraints = Vec::new();

    if int_lift
        && expr.sort().is_int()
        && let Some(width) = ty_to_bv_width(ty)
    {
        let is_signed = ty_signedness(ty).unwrap_or(false);
        if is_signed {
            constraints.push(
                expr.clone()
                    .int_ge(Expr::int_const(-(num_bigint::BigInt::from(1u128) << (width - 1)))),
            );
            constraints.push(
                expr.clone()
                    .int_lt(Expr::int_const(num_bigint::BigInt::from(1u128) << (width - 1))),
            );
        } else {
            constraints.push(expr.clone().int_ge(Expr::int_const(0)));
            constraints.push(
                expr.clone().int_lt(Expr::int_const(num_bigint::BigInt::from(1u128) << width)),
            );
        }
    }

    if ty.kind().is_char()
        && let Some(char_bound) = write_any_slim_projected_char_bound(expr)
    {
        constraints.push(char_bound);
    }

    if write_any_slim_projected_ty_is_nonzero(ty)
        && let Some(nonzero_bound) = write_any_slim_projected_nonzero_bound(expr)
    {
        constraints.push(nonzero_bound);
    }

    constraints
}

fn write_any_slim_projected_ty_is_nonzero(ty: rustc_public::ty::Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if {
        let name = def.trimmed_name();
        name == "NonZero" || name.starts_with("NonZero")
    })
}

fn write_any_slim_projected_char_bound(expr: &Expr) -> Option<Expr> {
    let sort = expr.sort();
    if let Some(bv_width) = sort.bitvec_width() {
        let low_range = expr.clone().bvule(Expr::bitvec_const(0xD7FFu64, bv_width));
        let high_lower = expr.clone().bvuge(Expr::bitvec_const(0xE000u64, bv_width));
        let high_upper = expr.clone().bvule(Expr::bitvec_const(0x10FFFFu64, bv_width));
        Some(low_range.or(high_lower.and(high_upper)))
    } else if sort.is_int() {
        let low_range = expr.clone().int_le(Expr::int_const(0xD7FFi64));
        let high_lower = expr.clone().int_ge(Expr::int_const(0xE000i64));
        let high_upper = expr.clone().int_le(Expr::int_const(0x10FFFFi64));
        Some(low_range.or(high_lower.and(high_upper)))
    } else {
        None
    }
}

fn write_any_slim_projected_nonzero_bound(expr: &Expr) -> Option<Expr> {
    let sort = expr.sort();
    if let Some(width) = sort.bitvec_width() {
        Some(expr.clone().ne(Expr::bitvec_const(0u64, width)))
    } else if sort.is_int() {
        Some(expr.clone().ne(Expr::int_const(0)))
    } else {
        None
    }
}

/// Extension trait for Kani model function handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallKaniModel {
    fn codegen_call_kani_model(&mut self, dcx: &DispatchCallContext<'_>, kani_model: KaniModel);

    fn try_emit_write_any_slim(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    fn try_emit_write_any_slim_collection_havoc(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    fn try_emit_write_any_slim_heap_alloc_havoc(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    fn try_emit_write_any_slice(&mut self, dcx: &DispatchCallContext<'_>) -> bool;

    fn write_any_slice_effective_offset(
        &self,
        pointer_arg: &Operand,
        backing: &ResolvedSliceBacking,
    ) -> Expr;

    fn constrain_write_any_slim_projected_target(
        &mut self,
        target_place: &Place,
        target_ty: rustc_public::ty::Ty,
        target_vec_idx: usize,
        out_name: &str,
        out_sort: &ay_bindings::Sort,
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
    ) -> Option<Expr>;

    fn constrain_write_any_slim_projected_flattened(
        &mut self,
        target_place: &Place,
        target_ty: rustc_public::ty::Ty,
        target_vec_idx: usize,
        field_projs: &[super::FieldProjection],
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
    ) -> Option<Expr>;

    fn resolve_write_any_slim_target_place(&self, pointer_arg: &Operand) -> Option<Place>;

    fn resolve_write_any_slim_target_local(&self, pointer_arg: &Operand) -> Option<usize>;

    fn resolve_local_from_state_expr(&self, expr: &Expr) -> Option<usize>;

    fn find_ref_source_local(&self, local: usize) -> Option<usize>;

    fn find_untracked_deref_value_source(&self, local: usize) -> Option<usize>;

    /// Extract LANES count from simd_bitmask model function generic args.
    ///
    /// The model signature is `simd_bitmask<T, U, E, const LANES: usize>`.
    /// LANES is the 4th generic arg (index 3).
    fn extract_simd_bitmask_lanes(&self, func: &Operand) -> Option<usize>;
}

impl<'tcx, 'body> CallKaniModel for ChcCtx<'tcx, 'body> {
    /// Handle kani::any() and other Kani models.
    fn codegen_call_kani_model(&mut self, dcx: &DispatchCallContext<'_>, kani_model: KaniModel) {
        let bb_idx = dcx.bb_idx;
        let func = dcx.func;
        let args = dcx.args;
        let destination = dcx.destination;
        let target = dcx.target;
        let from_app = dcx.from_app;
        let stmt_constraints = dcx.stmt_constraints;
        let modified_locals = dcx.modified_locals;
        match kani_model {
            KaniModel::Any => {
                // kani::any() returns a nondet value.
                let dest_local: usize = destination.local;
                debug!(
                    "kani::any() detected, dest_local={} (bb{}->bb{:?})",
                    dest_local, bb_idx, target
                );
                if let Some(target) = target {
                    // ZST types have exactly one inhabitant, but the destination
                    // local still needs that canonical value written into it.
                    // An identity goto leaves zero-sized arrays carrying an
                    // unconstrained input array, which then breaks fixed-array
                    // equality even though the Rust value space is singleton.
                    let dest_ty = self.body.locals()[dest_local].ty;
                    if super::codegen_call_kani_model_dst::is_zst_ty(dest_ty) {
                        debug!("kani::any() on ZST type, emitting canonical deterministic value");
                        let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
                            self.record_sound_fallback_reason("state_idx_missing_kani_any_zst");
                            emit_sound_fallback_goto(
                                self,
                                from_app,
                                *target,
                                modified_locals,
                                &[dest_local],
                                stmt_constraints,
                            );
                            return;
                        };
                        let Some((out_name, out_sort)) =
                            self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
                        else {
                            self.record_sound_fallback_reason("output_slot_missing_kani_any_zst");
                            emit_sound_fallback_goto(
                                self,
                                from_app,
                                *target,
                                modified_locals,
                                &[dest_local],
                                stmt_constraints,
                            );
                            return;
                        };
                        let Some(canonical_zst) =
                            super::codegen_call_kani_model_zst::canonical_zst_expr(dest_ty)
                        else {
                            self.record_sound_fallback_reason(
                                "canonical_zst_expr_missing_kani_any",
                            );
                            emit_sound_fallback_goto(
                                self,
                                from_app,
                                *target,
                                modified_locals,
                                &[dest_local],
                                stmt_constraints,
                            );
                            return;
                        };
                        let dest_var = Expr::var(&*out_name, out_sort.clone());
                        let eq = self.make_coerced_eq_constraint(
                            &dest_var,
                            canonical_zst,
                            &out_sort,
                            dest_local,
                            "kani_model::Any::canonical_zst",
                        );
                        let new_output_args =
                            self.build_output_args(modified_locals, &[dest_local]);
                        self.emit_goto_rule_extra(
                            from_app,
                            *target,
                            &new_output_args,
                            stmt_constraints,
                            eq,
                        );
                        return;
                    }

                    let mut extra_constraints = Vec::new();

                    // Mem-level: mirror the nondet value into memory so that
                    // subsequent raw-pointer dereferences (`*ptr`) read the same
                    // value as the CHC state variable. Without this, `let x = kani::any();
                    // let p = &x; assert!(*p == x)` fails because the memory load
                    // returns an independent unconstrained value. (Part of #1739 Bug 4)
                    if self.track_level >= ChcTrackLevel::Mem {
                        let dest_vec_idx = self.state_idx_for_local(dest_local);
                        // Part of #3270: Decomposed from .and_then chain for clarity.
                        if let Some((out_name, out_sort)) =
                            self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
                        {
                            let dest_var = Expr::var(&*out_name, out_sort);
                            extra_constraints.extend(build_call_result_memory_bridge_constraints(
                                self,
                                dest_local,
                                &dest_var,
                                modified_locals,
                            ));
                        }

                        let pending_checks: Vec<_> =
                            self.heap_state.pending_checks.drain(..).collect();
                        for check in pending_checks {
                            self.emit_error_rule_for_condition(
                                from_app,
                                check,
                                stmt_constraints,
                                bb_idx,
                            );
                        }
                    }

                    // Part of #112 Direction 2: bound Int-lifted nondet outputs to BV range.
                    extra_constraints.extend(self.int_lift_nondet_bounds(dest_local));
                    extra_constraints.extend(self.unit_enum_discriminant_bounds(dest_local)); // #3041
                    extra_constraints.extend(self.char_nondet_bounds(dest_local)); // #3470
                    extra_constraints.extend(self.nonzero_nondet_bounds(dest_local));

                    // Build output args after heap side effects so modified memory arrays
                    // are routed to their `__out` vars.
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);

                    self.emit_goto_rule_extra(
                        from_app,
                        *target,
                        &new_output_args,
                        stmt_constraints,
                        extra_constraints,
                    );
                } else {
                    self.record_diverging_call_drop(func, Some(bb_idx), "kani_model::Any", None);
                }
            }
            KaniModel::Offset => {
                // rustc_intrinsics::offset(base_ptr, count) -> pointer arithmetic.
                // Use element-count semantics (scaled by pointee size) via the same
                // helper used for BinOp::Offset rvalues.
                let dest_local: usize = destination.local;
                if let Some(target) = target {
                    let dest_vec_idx = self.state_idx_for_local(dest_local);
                    let mut sound_fallback = false;
                    let (eq, safety_checks) = if let [lhs_op, rhs_op, ..] = args
                        && let Some(offset_expr) = self.translate_pointer_offset_with_modified(
                            lhs_op,
                            rhs_op,
                            modified_locals,
                        ) {
                        let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
                        let dest_var = Expr::var(
                            &*self.state_var_mgr.output_state_vars[dest_vec_idx].0,
                            out_sort.clone(),
                        );
                        (
                            self.make_coerced_eq_constraint(
                                &dest_var,
                                offset_expr,
                                &out_sort,
                                dest_local,
                                "codegen_call_kani_model::Offset",
                            ),
                            // Part of #4217: Emit safety checks when prove_safety_only
                            // is active. Pointer offset overflow and same-allocation
                            // checks are safety properties, not user assertions.
                            // Default-on under memory_safety_checks now that the
                            // checks carry a real allocation-size bound and the
                            // fully-concrete case const-folds (static discharge
                            // survives; only the obj_valid provenance select stays
                            // behind extra_pointer_checks).
                            if self.memory_safety_checks
                                || self.extra_pointer_checks
                                || self.prove_safety_only
                            {
                                self.model_offset_safety_checks(lhs_op, rhs_op, modified_locals)
                            } else {
                                Vec::new()
                            },
                        )
                    } else {
                        if chc_debug_enabled() {
                            debug!("KaniModel::Offset fallback to nondet (args={})", args.len());
                        }
                        sound_fallback = true;
                        (None, Vec::new())
                    };

                    if sound_fallback {
                        emit_sound_fallback_goto_extra(
                            self,
                            from_app,
                            *target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                            eq,
                        );
                    } else {
                        // Emit each obligation as a per-property error rule
                        // carrying its Kani-parity kind + description (the
                        // precise isize-overflow obligations report
                        // "Offset value overflows isize" /
                        // "Offset in bytes overflows isize"; the in-bounds
                        // obligations keep the generic memory-safety line).
                        for check in &safety_checks {
                            self.emit_error_rule_for_condition_with_kind(
                                from_app,
                                check.cond.clone(),
                                stmt_constraints,
                                bb_idx,
                                check.kind,
                                check.message.clone(),
                            );
                        }
                        let new_output_args =
                            self.build_output_args(modified_locals, &[dest_local]);
                        self.emit_goto_rule_extra(
                            from_app,
                            *target,
                            &new_output_args,
                            stmt_constraints,
                            safety_checks.into_iter().map(|c| c.cond).chain(eq),
                        );
                        // Part of #3798/#4156: Propagate ref_targets/subslice_offset through
                        // KaniModel::Offset so downstream derefs and copy intrinsics can resolve
                        // the destination pointer back to the original array local. The model's
                        // count is signed (`isize`), so `ptr.sub(1)` reaches this path as `-1`.
                        self.propagate_signed_ptr_offset_result_metadata(
                            dest_local,
                            args,
                            modified_locals,
                        );
                    }
                } else {
                    self.record_diverging_call_drop(func, Some(bb_idx), "kani_model::Offset", None);
                }
            }
            KaniModel::SimdBitmask => {
                // Part of #2285: Encode simd_bitmask semantics — extract lane MSBs
                // into a bitmask integer.
                //
                // The model function signature is:
                //   simd_bitmask<T, U, E, const LANES: usize>(input: T) -> U
                // where T is the SIMD struct, U is the mask integer (u8/u16/etc.),
                // E is the element type, and LANES is the lane count.
                //
                // The SIMD argument (args[0]) is represented in CHC as an array
                // from BV64 indices to BV_elem values. We extract each lane,
                // check if it's nonzero (mask TRUE = all-ones = nonzero), and
                // build the bitmask by OR-ing shifted bits.
                let dest_local: usize = destination.local;
                if let Some(target) = target {
                    let dest_vec_idx = self.state_idx_for_local(dest_local);
                    let mut sound_fallback = false;
                    let lanes = self.extract_simd_bitmask_lanes(func);
                    // The SIMD argument is a flattened single-field struct (e.g., i32x4([i32; 4])).
                    // translate_operand returns None for bare reads of flattened locals.
                    // Instead, directly read the base state variable (fld0 = the inner array).
                    let simd_arr = args.first().and_then(|op| {
                        // Try normal translation first (for non-flattened SIMD types).
                        if let Some(expr) =
                            self.translate_operand_with_modified(op, modified_locals)
                        {
                            return Some(expr);
                        }
                        // Fallback: extract the local index and directly access fld0.
                        let arg_local = match op {
                            Operand::Copy(p) | Operand::Move(p) => p.local,
                            _ => return None, // external enum: Operand
                        };
                        let vec_idx = self.state_idx_for_local(arg_local);
                        let vars = if modified_locals.contains(&arg_local) {
                            &self.state_var_mgr.output_state_vars
                        } else {
                            &self.state_var_mgr.state_vars
                        };
                        vars.get(vec_idx).map(|(name, sort)| Expr::var(&**name, sort.clone()))
                    });

                    let eq = if let (Some(lanes), Some(arr_expr)) = (lanes, simd_arr) {
                        let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
                        let dest_var = Expr::var(
                            &*self.state_var_mgr.output_state_vars[dest_vec_idx].0,
                            out_sort.clone(),
                        );
                        let mask_width = out_sort.bitvec_width();
                        let elem_width = arr_expr
                            .sort()
                            .array_sort()
                            .and_then(|a| a.element_sort.bitvec_width());

                        if let (Some(mask_width), Some(elem_width)) = (mask_width, elem_width) {
                            let zero_elem = Expr::bitvec_const(0u64, elem_width);
                            let mut mask_expr = Expr::bitvec_const(0u64, mask_width);
                            for i in 0..lanes.min(mask_width as usize) {
                                let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
                                let lane_val = arr_expr.clone().select(idx);
                                let lane_set = lane_val.ne(zero_elem.clone());
                                let bit = Expr::ite(
                                    lane_set,
                                    simd_bitmask_lane_bit(mask_width, i),
                                    Expr::bitvec_const(0u64, mask_width),
                                );
                                mask_expr = mask_expr.bvor(bit);
                            }

                            self.make_coerced_eq_constraint(
                                &dest_var,
                                mask_expr,
                                &out_sort,
                                dest_local,
                                "codegen_call_kani_model::SimdBitmask",
                            )
                        } else {
                            if chc_debug_enabled() {
                                debug!(
                                    "SimdBitmask fallback to nondet (non-bitvec sort: mask_width={}, elem_width={})",
                                    mask_width.is_some(),
                                    elem_width.is_some()
                                );
                            }
                            sound_fallback = true;
                            None
                        }
                    } else {
                        if chc_debug_enabled() {
                            debug!(
                                "SimdBitmask fallback to nondet (lanes={:?}, arr={})",
                                lanes,
                                !args.is_empty()
                            );
                        }
                        sound_fallback = true;
                        None
                    };

                    if sound_fallback {
                        emit_sound_fallback_goto_extra(
                            self,
                            from_app,
                            *target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                            eq,
                        );
                    } else {
                        let new_output_args =
                            self.build_output_args(modified_locals, &[dest_local]);
                        self.emit_goto_rule_extra(
                            from_app,
                            *target,
                            &new_output_args,
                            stmt_constraints,
                            eq,
                        );
                    }
                } else {
                    self.record_diverging_call_drop(
                        func,
                        Some(bb_idx),
                        "kani_model::SimdBitmask",
                        None,
                    );
                }
            }
            KaniModel::PtrOffsetFrom | KaniModel::PtrOffsetFromUnsigned => {
                // rustc_intrinsics::ptr_offset_from*(lhs, rhs) -> (lhs - rhs) / sizeof(T).
                // Part of #2912: model pointer-distance intrinsics instead of leaving
                // destination unconstrained, which creates spurious CTREX in VecIntoIter paths.
                let is_unsigned = matches!(kani_model, KaniModel::PtrOffsetFromUnsigned);
                if let Some(target) = target {
                    ptr_offset_common::codegen_ptr_offset_from_call(
                        self,
                        dcx,
                        *target,
                        is_unsigned,
                        if is_unsigned {
                            "codegen_call_kani_model::PtrOffsetFromUnsigned"
                        } else {
                            "codegen_call_kani_model::PtrOffsetFrom"
                        },
                    );
                } else {
                    let label = if is_unsigned {
                        "kani_model::PtrOffsetFromUnsigned"
                    } else {
                        "kani_model::PtrOffsetFrom"
                    };
                    self.record_diverging_call_drop(func, Some(bb_idx), label, None);
                }
            }
            // Part of #3210: SizeOfSliceObject — compute exact size for slice-tail DSTs.
            KaniModel::SizeOfSliceObject => {
                super::codegen_call_kani_model_dst::dispatch_size_of_slice_object(self, dcx);
            }
            // Part of #3210: SizeOfVal/AlignOfVal — resolve pointee layout at compile time.
            KaniModel::SizeOfVal => {
                super::codegen_call_kani_model_dst::dispatch_size_of_val(self, dcx);
            }
            KaniModel::AlignOfVal => {
                super::codegen_call_kani_model_dst::dispatch_align_of_val(self, dcx);
            }
            // MEMUB-24/25/27: Is*PtrInitialized — real verdicts from the
            // scalar shadow-memory state (falls back to `true` when the
            // shape is untranslatable or `-Z uninit-checks` is off).
            KaniModel::IsPtrInitialized
            | KaniModel::IsStrPtrInitialized
            | KaniModel::IsSliceChunkPtrInitialized
            | KaniModel::IsSlicePtrInitialized => {
                self.codegen_mem_init_model(dcx, kani_model);
            }
            // Part of #3210 Phase 2: Dyn object size/align — vtable ITE lookup.
            KaniModel::AlignOfDynObject => {
                super::codegen_call_kani_model_dyn::dispatch_align_of_dyn_object(self, dcx);
            }
            KaniModel::SizeOfDynObject => {
                super::codegen_call_kani_model_dyn::dispatch_size_of_dyn_object(self, dcx);
            }
            // MEMUB-24/25/27: shadow-memory writes are guarded updates of the
            // scalar shadow state vars (plain goto when `-Z uninit-checks` is
            // off, preserving the #4066 no-op behavior).
            KaniModel::SetPtrInitialized
            | KaniModel::SetSliceChunkPtrInitialized
            | KaniModel::SetSlicePtrInitialized
            | KaniModel::SetStrPtrInitialized
            | KaniModel::CopyInitState
            | KaniModel::CopyInitStateSingle
            | KaniModel::InitializeMemoryInitializationState
            | KaniModel::LoadArgument
            | KaniModel::StoreArgument => {
                self.codegen_mem_init_model(dcx, kani_model);
            }
            // Part of #4217: PanicStub represents a panic from user `assert!()`
            // failures (Kani transforms `core::panicking::panic` into PanicStub).
            // Emit an unconditional error rule — unless prove_safety_only is
            // active, in which case user assertion panics are suppressed.
            KaniModel::PanicStub => {
                if !self.prove_safety_only {
                    let error_app = RelationApp::new("error", Vec::new());
                    let body =
                        RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, []);
                    self.vc.add_rule(Rule::new(body, error_app));
                }
                if let Some(target) = target {
                    emit_sound_fallback_goto(
                        self,
                        from_app,
                        *target,
                        modified_locals,
                        &[destination.local],
                        stmt_constraints,
                    );
                } else {
                    self.record_diverging_call_drop(
                        func,
                        Some(bb_idx),
                        "kani_model::PanicStub",
                        None,
                    );
                }
            }
            KaniModel::RunContract | KaniModel::RunLoopContract => {
                let is_loop_contract = matches!(kani_model, KaniModel::RunLoopContract);
                let Some(target) = target else {
                    let reason = if is_loop_contract {
                        "kani_run_loop_contract_diverging"
                    } else {
                        "kani_run_contract_diverging"
                    };
                    self.record_sound_fallback_reason(reason);
                    self.record_diverging_call_drop(
                        func,
                        Some(bb_idx),
                        if is_loop_contract {
                            "kani_model::run_loop_contract"
                        } else {
                            "kani_model::run_contract"
                        },
                        None,
                    );
                    return;
                };
                if let Some(closure_arg) = args.first()
                    && let Some(closure_body) =
                        resolve_closure_body_for_operand(self.tcx, closure_arg, self.body.locals())
                            // Wall-2 strategy (b): when the operand's declared
                            // type is opaque, recover the closure from its
                            // unique `Aggregate(Closure)` defining assign
                            // (fail-closed walk). The demotion below stays the
                            // fallback for anything still unresolved.
                            .or_else(|| {
                                resolve_closure_body_via_unique_aggregate_def(
                                    self.tcx,
                                    closure_arg,
                                    self.body,
                                )
                            })
                {
                    let captures = self.extract_closure_env_captures(closure_arg, modified_locals);
                    if let Some(inline_result) = translate_closure_inline_result(
                        self,
                        &closure_body,
                        &[],
                        &captures,
                        bb_idx,
                        0,
                    ) {
                        let super::inline_body::InlineReturn {
                            value,
                            vtable,
                            alias_updates,
                            deferred_checks,
                            ..
                        } = inline_result;
                        let pre_resolved_args = BTreeMap::new();
                        let caller_vtable_ids = HashMap::new();
                        debug!(
                            bb_idx,
                            is_loop_contract,
                            "kani contract model lowered as direct closure inline"
                        );
                        self.emit_translated_inline_call_result(
                            dcx,
                            *target,
                            value,
                            vtable,
                            alias_updates,
                            deferred_checks,
                            &pre_resolved_args,
                            &caller_vtable_ids,
                            None,
                            if is_loop_contract {
                                "kani_run_loop_contract_inline"
                            } else {
                                "kani_run_contract_inline"
                            },
                            if is_loop_contract {
                                "kani_run_loop_contract_alias_update"
                            } else {
                                "kani_run_contract_alias_update"
                            },
                        );
                        return;
                    }
                }

                self.record_sound_fallback_reason(if is_loop_contract {
                    "kani_run_loop_contract_closure_unresolved"
                } else {
                    "kani_run_contract_closure_unresolved"
                });
                emit_sound_fallback_goto(
                    self,
                    from_app,
                    *target,
                    modified_locals,
                    &[destination.local],
                    stmt_constraints,
                );
            }
            KaniModel::WriteAnySlim => {
                if self.try_emit_write_any_slim(dcx) {
                    return;
                }
                if let Some(target) = target {
                    emit_sound_fallback_goto(
                        self,
                        from_app,
                        *target,
                        modified_locals,
                        &[destination.local],
                        stmt_constraints,
                    );
                } else {
                    self.record_sound_fallback_reason("kani_write_any_slim_unresolved");
                    self.record_diverging_call_drop(
                        func,
                        Some(bb_idx),
                        "kani_model::write_any_slim",
                        None,
                    );
                }
            }
            KaniModel::WriteAnySlice => {
                if self.try_emit_write_any_slice(dcx) {
                    return;
                }
                if let Some(target) = target {
                    emit_sound_fallback_goto(
                        self,
                        from_app,
                        *target,
                        modified_locals,
                        &[destination.local],
                        stmt_constraints,
                    );
                } else {
                    self.record_sound_fallback_reason("kani_write_any_slice_unresolved");
                    self.record_diverging_call_drop(
                        func,
                        Some(bb_idx),
                        "kani_model::write_any_slice",
                        None,
                    );
                }
            }
            // Upstream Kani does not implement arbitrary `str` writes. Fail
            // closed instead of silently treating it like a normal nondet call.
            KaniModel::WriteAnyStr => {
                let error_app = RelationApp::new("error", Vec::new());
                let body =
                    RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, []);
                self.vc.add_rule(Rule::new(body, error_app));
                self.record_sound_fallback_reason("kani_write_any_str_unsupported");

                if let Some(target) = target {
                    let new_output_args =
                        self.build_output_args(modified_locals, &[destination.local]);
                    self.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
                } else {
                    self.record_diverging_call_drop(
                        func,
                        Some(bb_idx),
                        "kani_model::write_any_str_unsupported",
                        None,
                    );
                }
            }
        }
    }

    fn try_emit_write_any_slim(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };
        let Some(pointer_arg) = dcx.args.first() else { return false };
        let Some(target_place) = self.resolve_write_any_slim_target_place(pointer_arg) else {
            // The pointer does not resolve to a state-var-backed place. Try the
            // checked collection-store lane (IndexMut-returned &mut T into a Vec
            // backing array) before failing closed.
            if self.try_emit_write_any_slim_collection_havoc(dcx) {
                return true;
            }
            // REPLACE-lane heap shape: the pointer identity chain lands on a
            // whole heap allocation (Box pointee) whose readers use the Mem
            // lane. Havoc through the same Mem store path readers select from.
            if self.try_emit_write_any_slim_heap_alloc_havoc(dcx) {
                return true;
            }
            self.record_sound_fallback_reason("kani_write_any_slim_target_unresolved");
            return false;
        };

        // Static-mut target (Part of #428 modeling): `&mut STATIC` resolves to
        // a `[Deref]`-projected static-ref local whose pointee is a dedicated
        // static state variable. Havoc = fresh unconstrained OUTPUT var for
        // that state slot (same mechanism the Reg-level static store uses),
        // plus type-validity bounds on the fresh value.
        {
            use rustc_public::mir::ProjectionElem;
            if target_place.projection.len() == 1
                && matches!(target_place.projection[0], ProjectionElem::Deref)
            {
                let Some(&static_vec_idx) =
                    self.ref_resolution.static_ref_to_state_idx.get(&target_place.local)
                else {
                    self.record_sound_fallback_reason(
                        "kani_write_any_slim_deref_target_not_static",
                    );
                    return false;
                };
                let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(static_vec_idx).cloned()
                else {
                    self.record_sound_fallback_reason("kani_write_any_slim_static_output_missing");
                    return false;
                };
                let out_var = Expr::var(&*out_name, out_sort);
                let mut extra_constraints = Vec::new();
                if let Some(pointee_ty) = pointer_arg
                    .ty(self.body.locals())
                    .into_option()
                    .and_then(ChcCtx::deref_pointee_ty)
                {
                    extra_constraints.extend(write_any_slim_projected_validity_bounds(
                        pointee_ty,
                        &out_var,
                        self.int_lift,
                    ));
                }
                self.mark_state_var_modified(static_vec_idx);
                let new_output_args =
                    self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
                self.emit_goto_rule_extra(
                    dcx.from_app,
                    *target,
                    &new_output_args,
                    dcx.stmt_constraints,
                    extra_constraints,
                );
                debug!(
                    bb_idx = dcx.bb_idx,
                    static_vec_idx, "kani::write_any_slim lowered as static state-var havoc"
                );
                return true;
            }
        }

        let target_local = target_place.local;
        let Some(target_vec_idx) = self.try_state_idx_for_local(target_local) else {
            self.record_sound_fallback_reason("kani_write_any_slim_state_idx_missing");
            return false;
        };
        let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(target_vec_idx).cloned()
        else {
            self.record_sound_fallback_reason("kani_write_any_slim_output_slot_missing");
            return false;
        };

        let mut extra_constraints = Vec::new();
        let fresh_value = if target_place.projection.is_empty() {
            let out_var = Expr::var(&*out_name, out_sort.clone());
            let fresh_value =
                declare_pending_var(chc_fresh_name("__kani_write_any_slim"), out_sort.clone());
            if let Some(eq) = self.make_coerced_eq_constraint(
                &out_var,
                fresh_value.clone(),
                &out_sort,
                target_local,
                "kani_model::WriteAnySlim",
            ) {
                extra_constraints.push(eq);
            }
            extra_constraints.extend(self.int_lift_nondet_bounds(target_local));
            extra_constraints.extend(self.char_nondet_bounds(target_local));
            extra_constraints.extend(self.nonzero_nondet_bounds(target_local));
            fresh_value
        } else {
            let Some(target_ty) = target_place.ty(self.body.locals()).ok() else {
                self.record_sound_fallback_reason("kani_write_any_slim_projected_ty_missing");
                return false;
            };
            let Some(fresh_value) = self.constrain_write_any_slim_projected_target(
                &target_place,
                target_ty,
                target_vec_idx,
                &out_name,
                &out_sort,
                dcx.modified_locals,
                &mut extra_constraints,
            ) else {
                return false;
            };
            fresh_value
        };

        if self.track_level >= ChcTrackLevel::Mem {
            if let Some(addr_expr) =
                self.translate_ref_to_address(&target_place, dcx.modified_locals)
            {
                let target_ty = target_place
                    .ty(self.body.locals())
                    .unwrap_or(self.body.locals()[target_local].ty);
                let prev_suppress = self.suppress_heap_store_checks;
                self.suppress_heap_store_checks = true;
                if let Some(store_constraint) =
                    self.build_memory_store(addr_expr, fresh_value, target_ty)
                {
                    extra_constraints.push(store_constraint);
                }
                self.suppress_heap_store_checks = prev_suppress;
                extra_constraints.append(&mut self.heap_state.pending_updates);
                extra_constraints
                    .append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
                let pending_checks: Vec<_> = self.heap_state.pending_checks.drain(..).collect();
                for check in pending_checks {
                    self.emit_error_rule_for_condition(
                        dcx.from_app,
                        check,
                        dcx.stmt_constraints,
                        dcx.bb_idx,
                    );
                }
            }
        }

        let extra_dests = [target_local, dcx.destination.local];
        let new_output_args = self.build_output_args(dcx.modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            extra_constraints,
        );
        debug!(
            bb_idx = dcx.bb_idx,
            target_local,
            projected = !target_place.projection.is_empty(),
            "kani::write_any_slim lowered as place havoc"
        );
        true
    }

    /// Checked havoc store for `write_any_slim` pointers that do not resolve to
    /// a state-var-backed place but do carry collection-store metadata
    /// (`collection_mut_refs`, seeded by IndexMut tracking).
    ///
    /// Emits a FRESH nondet (constrained only by type-validity bounds) into the
    /// Vec backing array through the same handler ordinary `*p = v` deref
    /// stores use, so readers observe the havoc through the identical lane.
    /// Returns `false` (caller stays fail-closed) when the identity chain does
    /// not reach a `collection_mut_refs` local or the store is not emitted.
    fn try_emit_write_any_slim_collection_havoc(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        use super::stmt_accumulator::StmtAccumulator;

        let Some(target) = dcx.target else { return false };
        let Some(pointer_arg) = dcx.args.first() else { return false };

        // Walk the pointer-value identity chain to a collection_mut_refs local.
        let mut current = match pointer_arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return false,
        };
        let mut cmr = None;
        let mut visited = HashSet::new();
        for _ in 0..8 {
            if !visited.insert(current) {
                return false;
            }
            if let Some(found) = self
                .ref_resolution
                .collection_mut_refs
                .get(&current)
                .or_else(|| self.ref_resolution.collection_index_refs.get(&current))
            {
                cmr = Some(found.clone());
                break;
            }
            let Some(next) = self
                .find_ref_source_local(current)
                .or_else(|| self.find_untracked_deref_value_source(current))
            else {
                return false;
            };
            current = next;
        }
        let Some(cmr) = cmr else { return false };

        // Fresh nondet of the pointee type, constrained ONLY by type-validity.
        let Some(pointee_ty) =
            pointer_arg.ty(self.body.locals()).into_option().and_then(ChcCtx::deref_pointee_ty)
        else {
            return false;
        };
        let Some(pointee_sort) = Self::translate_ty(pointee_ty) else {
            return false;
        };
        let fresh = declare_pending_var(chc_fresh_name("__kani_write_any_slim_cmr"), pointee_sort);
        let mut extra_constraints =
            write_any_slim_projected_validity_bounds(pointee_ty, &fresh, self.int_lift);

        // Commit through the checked deref-store collection lane.
        let mut modified = dcx.modified_locals.clone();
        let mut last_constraint_for_local: HashMap<usize, usize> = HashMap::new();
        let handled = {
            let mut acc = StmtAccumulator::new(
                &mut modified,
                &mut extra_constraints,
                &mut last_constraint_for_local,
            );
            self.handle_collection_mut_ref_store(fresh, &cmr, &mut acc)
        };
        if !handled {
            return false;
        }

        // Call-terminator handlers bypass encode_block_statements: flush heap
        // side effects and emit pending checks as error rules (checked lane).
        extra_constraints.append(&mut self.heap_state.pending_updates);
        extra_constraints.append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
        let pending_checks: Vec<_> = self.heap_state.pending_checks.drain(..).collect();
        for check in pending_checks {
            self.emit_error_rule_for_condition(
                dcx.from_app,
                check,
                dcx.stmt_constraints,
                dcx.bb_idx,
            );
        }

        let new_output_args = self.build_output_args(&modified, &[dcx.destination.local]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            extra_constraints,
        );
        debug!(
            bb_idx = dcx.bb_idx,
            collection_local = cmr.collection_local,
            "kani::write_any_slim lowered as checked collection havoc store"
        );
        true
    }

    /// Reader-consistent havoc for `write_any_slim` pointers whose identity
    /// chain lands on a WHOLE heap allocation (contract-modifies REPLACE lane,
    /// Box pointee shape: `#[kani::modifies(ptr.as_ref())]` with
    /// `ptr: &mut Box<T>`).
    ///
    /// Heap cells have no state-variable backing — every reader resolves the
    /// deref base through `known_alloc_ids` and selects from the type-indexed /
    /// region Mem arrays (`#4179`). Emitting the fresh nondet through
    /// `build_memory_store` at the allocation base address therefore writes
    /// exactly the lane readers observe. This is NOT the stale-state-var trap
    /// (Shape A): that trap is stack locals whose readers use state variables,
    /// excluded here by the `local_idx_for_obj_id` gate.
    ///
    /// Fail-closed gates (all must hold, else the caller records
    /// `kani_write_any_slim_target_unresolved`):
    /// - Mem track level (readers use the Mem lane only at Mem).
    /// - Every identity-chain hop is definite; a hop carries a
    ///   `known_alloc_ids` entry.
    /// - The object is NOT a stack local's address object
    ///   (`local_idx_for_obj_id` — those readers use state variables).
    /// - The allocation size is concretely known and EQUALS the pointee size
    ///   (whole-object, offset-0 havoc only; excludes interior-field targets,
    ///   statics, and symbolic-size allocations).
    fn try_emit_write_any_slim_heap_alloc_havoc(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        if self.track_level < ChcTrackLevel::Mem {
            return false;
        }
        let Some(target) = dcx.target else { return false };
        let Some(pointer_arg) = dcx.args.first() else { return false };

        let mut current = match pointer_arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return false,
        };
        // Walk the pointer VALUE-identity chain, collecting `known_alloc_ids`
        // entries at every hop. Entries naming STACK address objects are
        // pointer-STORAGE provenance (the cell the reference value sits in —
        // closure envs, spilled temps), not the pointee; skip them and keep
        // walking. Accept only a unique HEAP object across the chain.
        //
        // When the value chain dead-ends on a Box inner-pointer load
        // (`x = (((*b).0: Unique<T>).0: NonNull<T>)` from the inlined
        // `Box::as_ref`/`as_mut`), cross to the `&Box` base and resolve it in
        // REF space to the plain local holding the Box value; that local's
        // `known_alloc_ids` entry names the pointee heap cell. known-alloc
        // hits are NEVER accepted while in ref-to-Box space (they would name
        // the cell HOLDING the box — wrong object for nested boxes).
        let mut obj_id: Option<u32> = None;
        let mut visited = HashSet::new();
        for _ in 0..12 {
            if !visited.insert(current) {
                break;
            }
            if let Some(&found) = self.known_alloc_ids.get(&current) {
                debug!(
                    bb_idx = dcx.bb_idx,
                    current, found, "write_any_slim heap havoc: chain hop has alloc entry"
                );
                if self.heap_state.local_idx_for_obj_id(found).is_none() {
                    match obj_id {
                        Some(prev) if prev != found => {
                            // Ambiguous heap provenance — fail closed.
                            debug!(
                                bb_idx = dcx.bb_idx,
                                prev, found, "write_any_slim heap havoc: ambiguous heap objects"
                            );
                            return false;
                        }
                        _ => obj_id = Some(found),
                    }
                }
            }
            if let Some(next) = self
                .find_ref_source_local(current)
                .or_else(|| self.find_untracked_deref_value_source(current))
            {
                current = next;
                continue;
            }
            // Dead end in value space: try the Box inner-pointer cross.
            if obj_id.is_none() {
                let box_ref_local = self.find_box_inner_pointer_load_base(current);
                let box_holder =
                    box_ref_local.and_then(|b| self.resolve_ref_chain_to_plain_local(b));
                let found = box_holder.and_then(|l| self.known_alloc_ids.get(&l).copied());
                debug!(
                    bb_idx = dcx.bb_idx,
                    current,
                    ?box_ref_local,
                    ?box_holder,
                    ?found,
                    "write_any_slim heap havoc: Box inner-pointer cross attempt"
                );
                if let Some(found) = found
                    && self.heap_state.local_idx_for_obj_id(found).is_none()
                {
                    obj_id = Some(found);
                }
            }
            break;
        }
        let Some(obj_id) = obj_id else {
            debug!(bb_idx = dcx.bb_idx, current, "write_any_slim heap havoc: no heap provenance");
            return false;
        };
        debug!(bb_idx = dcx.bb_idx, obj_id, "write_any_slim heap havoc: chain hit heap alloc");

        // Whole-object gate: pointee size must match the concrete allocation
        // size (offset-0 havoc of the full cell). Statics and symbolic-size
        // allocations have no recorded heap size and fail closed here.
        let Some(pointee_ty) =
            pointer_arg.ty(self.body.locals()).into_option().and_then(ChcCtx::deref_pointee_ty)
        else {
            return false;
        };
        let Some(pointee_size) = self.get_type_size(pointee_ty) else {
            return false;
        };
        if u32::try_from(pointee_size).ok() != self.heap_state.heap_alloc_size(obj_id)
            || pointee_size == 0
        {
            return false;
        }
        let Some(pointee_sort) = Self::translate_ty(pointee_ty) else {
            return false;
        };

        // Fresh nondet constrained ONLY by type-validity bounds, committed
        // through the same store path ordinary `*p = v` heap stores use.
        let fresh = declare_pending_var(chc_fresh_name("__kani_write_any_slim_heap"), pointee_sort);
        let mut extra_constraints =
            write_any_slim_projected_validity_bounds(pointee_ty, &fresh, self.int_lift);
        let addr = Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32));
        // The write is legitimized by the (already verified) modifies clause;
        // suppress store-side UB checks like the resolved-place Mem mirror does.
        let prev_suppress = self.suppress_heap_store_checks;
        self.suppress_heap_store_checks = true;
        if let Some(store_constraint) = self.build_memory_store_untyped(addr, fresh, pointee_ty) {
            extra_constraints.push(store_constraint);
        }
        self.suppress_heap_store_checks = prev_suppress;

        // Call-terminator handlers bypass encode_block_statements: flush heap
        // side effects and emit any pending checks as error rules.
        extra_constraints.append(&mut self.heap_state.pending_updates);
        extra_constraints.append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
        let pending_checks: Vec<_> = self.heap_state.pending_checks.drain(..).collect();
        for check in pending_checks {
            self.emit_error_rule_for_condition(
                dcx.from_app,
                check,
                dcx.stmt_constraints,
                dcx.bb_idx,
            );
        }

        let new_output_args = self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            extra_constraints,
        );
        debug!(
            bb_idx = dcx.bb_idx,
            obj_id, "kani::write_any_slim lowered as whole-heap-object havoc store"
        );
        true
    }

    fn constrain_write_any_slim_projected_target(
        &mut self,
        target_place: &Place,
        target_ty: rustc_public::ty::Ty,
        target_vec_idx: usize,
        out_name: &str,
        out_sort: &ay_bindings::Sort,
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
    ) -> Option<Expr> {
        let target_local = target_place.local;
        let field_projs = collect_field_projections(
            &target_place.projection,
            UnknownProjectionPolicy::ReturnEmpty(&self.diagnostics),
        );
        if field_projs.is_empty() {
            self.record_sound_fallback_reason("kani_write_any_slim_projection_unsupported");
            return None;
        }

        if self.flatten.flattened_tuple_locals.contains(&target_local) {
            return self.constrain_write_any_slim_projected_flattened(
                target_place,
                target_ty,
                target_vec_idx,
                &field_projs,
                modified_locals,
                extra_constraints,
            );
        }

        let out_var = Expr::var(out_name, out_sort.clone());
        let root_in = if modified_locals.contains(&target_local) {
            self.encode
                .local_expr_env
                .get(&target_local)
                .cloned()
                .unwrap_or_else(|| Expr::var(out_name, out_sort.clone()))
        } else {
            self.state_var_mgr.state_vars.get(target_vec_idx).map_or_else(
                || Expr::var(out_name, out_sort.clone()),
                |(name, sort)| Expr::var(&**name, sort.clone()),
            )
        };

        let Some(projected) = Self::apply_field_selections(root_in.clone(), &field_projs) else {
            self.record_sound_fallback_reason("kani_write_any_slim_projected_select_failed");
            return None;
        };
        let fresh_value =
            declare_pending_var(chc_fresh_name("__kani_write_any_slim"), projected.sort().clone());
        extra_constraints.extend(write_any_slim_projected_validity_bounds(
            target_ty,
            &fresh_value,
            self.int_lift,
        ));
        let Some(updated_root) =
            Self::apply_projection_update(&root_in, &field_projs, fresh_value.clone())
        else {
            self.record_sound_fallback_reason("kani_write_any_slim_projected_update_failed");
            return None;
        };
        let Some(eq) = self.make_coerced_eq_constraint(
            &out_var,
            updated_root,
            out_sort,
            target_local,
            "kani_model::WriteAnySlim",
        ) else {
            self.record_sound_fallback_reason("kani_write_any_slim_projected_eq_failed");
            return None;
        };
        extra_constraints.push(eq);
        Some(fresh_value)
    }

    fn constrain_write_any_slim_projected_flattened(
        &mut self,
        target_place: &Place,
        target_ty: rustc_public::ty::Ty,
        target_vec_idx: usize,
        field_projs: &[super::FieldProjection],
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
    ) -> Option<Expr> {
        let target_local = target_place.local;
        let local_ty = self.body.locals().get(target_local)?.ty;
        let Some(local_sort) = Self::translate_ty(local_ty) else {
            self.record_sound_fallback_reason("kani_write_any_slim_flattened_sort_missing");
            return None;
        };
        let field_indices: Vec<usize> = field_projs.iter().map(|proj| proj.field_idx).collect();
        let Some((leaf_offset, leaf_count)) =
            codegen_decl_flatten::compute_nested_flat_span(&local_sort, &field_indices)
        else {
            self.record_sound_fallback_reason("kani_write_any_slim_flattened_slot_missing");
            return None;
        };
        if leaf_count != 1 {
            self.record_sound_fallback_reason("kani_write_any_slim_flattened_multi_leaf");
            return None;
        }

        let slot = target_vec_idx + leaf_offset;
        let Some((_, leaf_sort)) = self.state_var_mgr.output_state_vars.get(slot).cloned() else {
            self.record_sound_fallback_reason("kani_write_any_slim_flattened_output_missing");
            return None;
        };
        let fresh_value = declare_pending_var(chc_fresh_name("__kani_write_any_slim"), leaf_sort);
        extra_constraints.extend(write_any_slim_projected_validity_bounds(
            target_ty,
            &fresh_value,
            self.int_lift,
        ));
        let field_count = self.flattened_field_count(target_local);
        let mut values = Vec::with_capacity(field_count);
        for field_idx in 0..field_count {
            if field_idx == leaf_offset {
                values.push(Some(fresh_value.clone()));
            } else {
                values.push(self.flattened_local_field_expr(
                    target_local,
                    field_idx,
                    modified_locals,
                ));
            }
        }
        if !self.constrain_flattened_fields_for_call(target_local, &values, extra_constraints) {
            self.record_sound_fallback_reason("kani_write_any_slim_flattened_constraints_missing");
            return None;
        }
        Some(fresh_value)
    }

    fn try_emit_write_any_slice(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else { return false };
        let Some(pointer_arg) = dcx.args.first() else { return false };
        let Some(backing) = self.resolve_slice_backing(pointer_arg, dcx.modified_locals) else {
            self.record_sound_fallback_reason("kani_write_any_slice_backing_unresolved");
            return false;
        };
        let Some(target_local) = self
            .resolve_write_any_slim_target_local(pointer_arg)
            .or_else(|| self.resolve_local_from_state_expr(backing.data.as_expr()))
        else {
            self.record_sound_fallback_reason("kani_write_any_slice_target_unresolved");
            return false;
        };
        let Some(target_vec_idx) = self.try_state_idx_for_local(target_local) else {
            self.record_sound_fallback_reason("kani_write_any_slice_state_idx_missing");
            return false;
        };
        let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(target_vec_idx).cloned()
        else {
            self.record_sound_fallback_reason("kani_write_any_slice_output_slot_missing");
            return false;
        };
        let Some(array_sort) = out_sort.array_sort().cloned() else {
            self.record_sound_fallback_reason("kani_write_any_slice_target_not_array");
            return false;
        };
        if backing.data.as_expr().sort().array_sort().is_none() {
            self.record_sound_fallback_reason("kani_write_any_slice_backing_not_array");
            return false;
        }
        let Some(len) = concrete_len_from_expr(backing.len.as_expr()) else {
            self.record_sound_fallback_reason("kani_write_any_slice_symbolic_len");
            return false;
        };
        if len > WRITE_ANY_SLICE_MAX_CONCRETE_ELEMS {
            self.record_sound_fallback_reason("kani_write_any_slice_len_cap");
            return false;
        }

        let arr_in = if self.encode.modified_state_indices.contains(&target_vec_idx) {
            Expr::var(&*out_name, out_sort.clone())
        } else {
            let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(target_vec_idx) else {
                self.record_sound_fallback_reason("kani_write_any_slice_input_slot_missing");
                return false;
            };
            Expr::var(&**in_name, in_sort.clone())
        };
        let arr_out = Expr::var(&*out_name, out_sort.clone());
        let mut updated = arr_in;
        let mut fresh_elems = Vec::with_capacity(len);
        let write_offset = self.write_any_slice_effective_offset(pointer_arg, &backing);
        let slice_elem_ty = self.chc_slice_elem_ty(pointer_arg);
        let mut extra_constraints = Vec::new();
        for i in 0..len {
            let raw_fresh = declare_pending_var(
                chc_fresh_name("__kani_write_any_slice_elem"),
                array_sort.element_sort.clone(),
            );
            let Some(fresh) = self.coerce_value_to_sort(raw_fresh, &array_sort.element_sort, false)
            else {
                self.record_sound_fallback_reason("kani_write_any_slice_elem_coerce_failed");
                return false;
            };
            if let Some(elem_ty) = slice_elem_ty {
                extra_constraints.extend(write_any_slim_projected_validity_bounds(
                    elem_ty,
                    &fresh,
                    self.int_lift,
                ));
            }
            let logical_idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
            let source_idx = Self::slice_rebase_source_index(&write_offset, logical_idx.clone(), i);
            updated = updated.store(source_idx, fresh.clone());
            fresh_elems.push((logical_idx, fresh));
        }

        if let Some(eq) = self.make_coerced_eq_constraint(
            &arr_out,
            updated,
            &out_sort,
            target_local,
            "kani_model::WriteAnySlice",
        ) {
            extra_constraints.push(eq);
        }

        if self.track_level >= ChcTrackLevel::Mem
            && let Some(elem_ty) = self.chc_slice_elem_ty(pointer_arg)
            && let Some(elem_size) = self.get_type_size(elem_ty)
            // Address by construction; `build_memory_store` below is the
            // wave-13 keystone and still takes a bare `Expr`, so the tag is
            // dropped once here rather than per element.
            && let Some(base_addr) =
                self.slice_as_ptr_data_expr(pointer_arg, dcx.modified_locals).map(Loc::into_expr)
        {
            let prev_suppress = self.suppress_heap_store_checks;
            self.suppress_heap_store_checks = true;
            for (logical_idx, fresh) in &fresh_elems {
                let byte_offset = if elem_size <= 1 {
                    logical_idx.clone()
                } else {
                    logical_idx.clone().bvmul(Expr::bitvec_const(elem_size as u128, POINTER_WIDTH))
                };
                let addr = if len == 0 || Self::is_zero_pointer_width_bitvec(&byte_offset) {
                    base_addr.clone()
                } else {
                    base_addr.clone().bvadd(byte_offset)
                };
                if let Some(store_constraint) =
                    self.build_memory_store_untyped(addr, fresh.clone(), elem_ty)
                {
                    extra_constraints.push(store_constraint);
                }
            }
            self.suppress_heap_store_checks = prev_suppress;
            extra_constraints.append(&mut self.heap_state.pending_updates);
            extra_constraints.append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
            let pending_checks: Vec<_> = self.heap_state.pending_checks.drain(..).collect();
            for check in pending_checks {
                self.emit_error_rule_for_condition(
                    dcx.from_app,
                    check,
                    dcx.stmt_constraints,
                    dcx.bb_idx,
                );
            }
        }

        let extra_dests = [target_local, dcx.destination.local];
        let new_output_args = self.build_output_args(dcx.modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            extra_constraints,
        );
        debug!(bb_idx = dcx.bb_idx, target_local, len, "kani::write_any_slice lowered");
        true
    }

    fn write_any_slice_effective_offset(
        &self,
        pointer_arg: &Operand,
        backing: &ResolvedSliceBacking,
    ) -> Expr {
        if !Self::is_zero_pointer_width_bitvec(backing.offset.as_expr()) {
            return backing.offset.as_expr().clone();
        }

        if let Operand::Copy(place) | Operand::Move(place) = pointer_arg
            && place.projection.is_empty()
        {
            if let Some(offset) = self.ref_resolution.subslice_offset.get(&place.local)
                && !Self::is_zero_pointer_width_bitvec(offset)
            {
                return offset.clone();
            }
            let resolved = self.resolve_provenance_local(place.local);
            if resolved != place.local
                && let Some(offset) = self.ref_resolution.subslice_offset.get(&resolved)
                && !Self::is_zero_pointer_width_bitvec(offset)
            {
                return offset.clone();
            }
        }

        let mut alias_offset = None;
        for (local, data) in &self.ref_resolution.const_ref_values {
            if data != backing.data.as_expr() {
                continue;
            }
            let Some(offset) = self.ref_resolution.subslice_offset.get(local) else {
                continue;
            };
            if Self::is_zero_pointer_width_bitvec(offset) {
                continue;
            }
            if let Some(len) = self.ref_resolution.subslice_len.get(local)
                && len != backing.len.as_expr()
            {
                continue;
            }
            match &alias_offset {
                Some(existing) if existing != offset => {
                    return backing.offset.as_expr().clone();
                }
                Some(_) => {}
                None => alias_offset = Some(offset.clone()),
            }
        }

        if alias_offset.is_none() {
            // Inlined `slice_from_raw_parts_mut(ptr.add(k), len)` can seed the
            // offset on an internal return local that no longer carries the
            // resolved backing array. Use it only when the current function has
            // one unambiguous nonzero subslice offset.
            for offset in self.ref_resolution.subslice_offset.values() {
                if Self::is_zero_pointer_width_bitvec(offset) {
                    continue;
                }
                match &alias_offset {
                    Some(existing) if existing != offset => {
                        return backing.offset.as_expr().clone();
                    }
                    Some(_) => {}
                    None => alias_offset = Some(offset.clone()),
                }
            }
        }

        alias_offset.unwrap_or_else(|| backing.offset.as_expr().clone())
    }

    fn resolve_write_any_slim_target_place(&self, pointer_arg: &Operand) -> Option<Place> {
        let mut current = match pointer_arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return None,
        };
        let mut visited = HashSet::new();
        for _ in 0..8 {
            if !visited.insert(current) {
                return None;
            }
            if let Some(target) = self.ref_resolution.ref_targets.get(&current) {
                return Some(Place { local: target.local, projection: target.projections.clone() });
            }
            let Some(next) = self
                .find_ref_source_local(current)
                .or_else(|| self.find_untracked_deref_value_source(current))
            else {
                return None;
            };
            current = next;
        }
        None
    }

    fn resolve_write_any_slim_target_local(&self, pointer_arg: &Operand) -> Option<usize> {
        let target_place = self.resolve_write_any_slim_target_place(pointer_arg)?;
        target_place.projection.is_empty().then_some(target_place.local)
    }

    fn resolve_local_from_state_expr(&self, expr: &Expr) -> Option<usize> {
        let ExprValue::Var { name } = expr.value() else {
            return None;
        };
        let state_idx = self.state_var_index_by_name(name)?;
        (0..self.body.locals().len())
            .find(|&local| self.try_state_idx_for_local(local) == Some(state_idx))
    }

    /// Return the unique pointer-value-identity source for `local`.
    ///
    /// Follows statements whose RHS carries the same pointer value:
    /// - `local = Use/Cast(src)` (bit-copy of the pointer)
    /// - `local = &mut *src` / `local = &raw mut *src` (reborrow — same address)
    ///
    /// Wrong resolution here would havoc the wrong place (false-Safe factory),
    /// so if the body assigns `local` from more than one distinct source
    /// (e.g. branch-dependent), resolution fails closed with `None`.
    fn find_ref_source_local(&self, local: usize) -> Option<usize> {
        use rustc_public::mir::ProjectionElem;
        let mut found: Option<usize> = None;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let rustc_public::mir::StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if place.local != local || !place.projection.is_empty() {
                    continue;
                }
                let next = match rvalue {
                    rustc_public::mir::Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                    | rustc_public::mir::Rvalue::Cast(
                        _,
                        Operand::Copy(src) | Operand::Move(src),
                        _,
                    ) if src.projection.is_empty() => src.local,
                    // Reborrow-unwrap (FC modifies Shape A): `p = &mut *q` and
                    // `p = &raw mut *q` preserve the pointer value exactly.
                    rustc_public::mir::Rvalue::Ref(_, _, src)
                    | rustc_public::mir::Rvalue::AddressOf(_, src)
                        if src.projection.len() == 1
                            && matches!(src.projection[0], ProjectionElem::Deref) =>
                    {
                        src.local
                    }
                    _ => continue,
                };
                match found {
                    None => found = Some(next),
                    Some(prev) if prev != next => return None,
                    Some(_) => {}
                }
            }
        }
        found
    }

    /// Return the pointer-value-identity source across a
    /// `local = kani::internal::untracked_deref(arg)` call.
    ///
    /// The hook returns a bit-copy of `*arg`; when `arg`'s pointee is a plain
    /// local `t` (via `ref_targets` with no projections), the returned value
    /// is exactly the reference value held in `t`, so the identity chain
    /// continues from `t`. Any other shape fails closed with `None`.
    fn find_untracked_deref_value_source(&self, local: usize) -> Option<usize> {
        use rustc_public::mir::TerminatorKind;
        let mut found: Option<usize> = None;
        for block in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
            else {
                continue;
            };
            if destination.local != local || !destination.projection.is_empty() {
                continue;
            }
            if self.detect_kani_hook(func)
                != Some(crate::kani_middle::kani_functions::KaniHook::UntrackedDeref)
            {
                continue;
            }
            let Some(Operand::Copy(arg) | Operand::Move(arg)) = args.first() else {
                continue;
            };
            if !arg.projection.is_empty() {
                continue;
            }
            let Some(arg_target) = self.ref_resolution.ref_targets.get(&arg.local) else {
                continue;
            };
            if !arg_target.projections.is_empty() {
                continue;
            }
            let next = arg_target.local;
            match found {
                None => found = Some(next),
                Some(prev) if prev != next => return None,
                Some(_) => {}
            }
        }
        found
    }

    /// Extract LANES count from simd_bitmask model function generic args.
    ///
    /// The model signature is `simd_bitmask<T, U, E, const LANES: usize>`.
    /// LANES is the 4th generic arg (index 3).
    fn extract_simd_bitmask_lanes(&self, func: &Operand) -> Option<usize> {
        use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
        let func_ty = func.ty(self.body.locals()).ok()?;
        let (_fn_def, fn_args) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return None, // external enum: TyKind
        };
        // LANES is the 4th generic arg (index 3)
        if let Some(GenericArgKind::Const(len_const)) = fn_args.0.get(3).cloned() {
            len_const.eval_target_usize().into_option().map(|v| v as usize)
        } else {
            None
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// If `local` is defined by a Box inner-pointer load —
    /// `local = Copy/Move((((*b).0: std::ptr::Unique<T>).0: std::ptr::NonNull<T>))`
    /// (the inlined `Box::as_ref`/`as_mut` body) — return the `&Box` base
    /// local `b`. The loaded value is the Box's heap pointer, so the pointee
    /// of `local` is the heap cell owned by the Box held at `*b`.
    ///
    /// Requires a UNIQUE defining assignment of this exact shape; anything
    /// else returns `None` (fail-closed).
    fn find_box_inner_pointer_load_base(&self, local: usize) -> Option<usize> {
        use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind};
        let mut found: Option<usize> = None;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if place.local != local || !place.projection.is_empty() {
                    continue;
                }
                let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue else {
                    return None;
                };
                // Exact shape: [Deref, Field(0, Unique<T>), Field(0, NonNull<T>)]
                let [
                    ProjectionElem::Deref,
                    ProjectionElem::Field(0, unique_ty),
                    ProjectionElem::Field(0, nonnull_ty),
                ] = src.projection.as_slice()
                else {
                    return None;
                };
                let is_adt_named = |ty: &rustc_public::ty::Ty, want: &str| {
                    matches!(
                        ty.kind(),
                        TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == want
                    )
                };
                if !is_adt_named(unique_ty, "Unique") || !is_adt_named(nonnull_ty, "NonNull") {
                    return None;
                }
                match found {
                    None => found = Some(src.local),
                    Some(prev) if prev != src.local => return None,
                    Some(_) => {}
                }
            }
        }
        found
    }

    /// Resolve a reference-typed local in REF space to the plain local it
    /// points at: walk value-identity hops until `ref_targets` yields a
    /// target with NO projections. Projected targets or unresolved hops
    /// return `None` (fail-closed).
    fn resolve_ref_chain_to_plain_local(&self, start: usize) -> Option<usize> {
        let mut current = start;
        let mut visited = HashSet::new();
        for _ in 0..8 {
            if !visited.insert(current) {
                return None;
            }
            if let Some(target) = self.ref_resolution.ref_targets.get(&current) {
                debug!(current, target_local = target.local, "ref-chain: ref_targets hit");
                return target.projections.is_empty().then_some(target.local);
            }
            // A Box-typed local IS the value holder — deref-load hops jump
            // through the reference straight to the holder local.
            if let Some(decl) = self.body.locals().get(current)
                && matches!(
                    decl.ty.kind(),
                    TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "Box"
                )
            {
                debug!(current, "ref-chain: Box-typed holder local");
                return Some(current);
            }
            let next = self
                .find_ref_source_local(current)
                .or_else(|| self.find_untracked_deref_value_source(current))
                .or_else(|| self.find_deref_load_value_source(current));
            debug!(current, ?next, "ref-chain: hop");
            current = next?;
        }
        None
    }

    /// Return the pointer-value-identity source across a plain MIR deref
    /// load `local = Copy/Move((*b))` (projection exactly `[Deref]`).
    ///
    /// The loaded value is the reference stored at `b`'s pointee; when `b`'s
    /// `ref_targets` entry is a plain local `t` (no projections), the loaded
    /// value is exactly the reference value held in `t`, so the identity
    /// chain continues from `t`. This is the statement-level twin of
    /// [`CallKaniModel::find_untracked_deref_value_source`] (the
    /// `untracked_deref` hook computes the same bit-copy through a call).
    /// Any other shape — multiple conflicting defs, projected pointee —
    /// fails closed with `None`.
    fn find_deref_load_value_source(&self, local: usize) -> Option<usize> {
        use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind};
        let mut found: Option<usize> = None;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if place.local != local || !place.projection.is_empty() {
                    continue;
                }
                let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue else {
                    return None;
                };
                if !matches!(src.projection.as_slice(), [ProjectionElem::Deref]) {
                    return None;
                }
                let Some(src_target) = self.ref_resolution.ref_targets.get(&src.local) else {
                    return None;
                };
                if !src_target.projections.is_empty() {
                    return None;
                }
                let next = src_target.local;
                match found {
                    None => found = Some(next),
                    Some(prev) if prev != next => return None,
                    Some(_) => {}
                }
            }
        }
        found
    }

    fn nonzero_nondet_bounds(&self, dest_local: usize) -> Option<Expr> {
        let ty = self.body.locals()[dest_local].ty;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
            return None;
        };
        let name = def.trimmed_name();
        if name != "NonZero" && !name.starts_with("NonZero") {
            return None;
        }

        let vec_idx = self.try_state_idx_for_local(dest_local)?;
        let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx)?;
        let out_var = Expr::var(&**out_name, out_sort.clone());

        if let Some(constraint) = Self::build_nonzero_constraint(out_var.clone()) {
            debug!(dest_local, "nonzero_nondet_bounds: direct output constraint");
            return Some(constraint);
        }

        // Output state variable = the NonZero local's contents: a value.
        let out_val = crate::codegen_ay::provenance::Val::of_value(out_var);
        let field_expr = Self::datatype_field_select(&out_val, 0, None)?;
        let constraint = Self::build_nonzero_constraint(field_expr.into_expr())?;
        debug!(dest_local, "nonzero_nondet_bounds: field output constraint");
        Some(constraint)
    }

    fn build_nonzero_constraint(expr: Expr) -> Option<Expr> {
        let sort = expr.sort().clone();
        if let Some(width) = sort.bitvec_width() {
            Some(expr.ne(Expr::bitvec_const(0u64, width)))
        } else if sort.is_int() {
            Some(expr.ne(Expr::int_const(0)))
        } else {
            None
        }
    }

    fn model_offset_safety_checks(
        &mut self,
        ptr_op: &Operand,
        count_op: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Vec<ModelOffsetCheck> {
        let Some(ptr) = self.translate_operand_with_modified(ptr_op, modified_locals) else {
            return Vec::new();
        };
        let Some(count) = self.translate_operand_with_modified(count_op, modified_locals) else {
            return Vec::new();
        };

        let ptr = if ptr.sort().is_int() { ptr.int2bv(POINTER_WIDTH) } else { ptr };
        let count = if count.sort().is_int() { count.int2bv(POINTER_WIDTH) } else { count };
        if !ptr.sort().is_bitvec() || !count.sort().is_bitvec() {
            return Vec::new();
        }

        let ptr = coerce_bitvec_width_safe(ptr, POINTER_WIDTH, SignExtension::ZeroExtend);
        // Signedness has THREE cases, not two — mirrors the Rvalue-lane twin in
        // codegen_stmt_rvalue_offset.rs (#4118).
        //
        // `unwrap_or(false)` reads an UNKNOWN-signedness count as UNSIGNED, and the
        // two readings disagree on the same 64-bit pattern: `ptr.offset(-1)` is
        // 0xFFFF_FFFF_FFFF_FFFF, a small negative signed but 2^64-1 unsigned. Taking
        // the unsigned branch there FABRICATES an "Offset value overflows isize"
        // violation on correct code. Asserting the signed range instead says nothing
        // (every 64-bit value satisfies it), so neither reading is safe to assume.
        //
        // So: skip the obligation and fail closed. An unaudited reason hits the
        // catch-all `FallbackSoundness::FailClose` and stays UNACCOUNTED, so no Safe
        // verdict can rest on the range check we are declining to emit.
        //
        // Believed unreachable here — `count_op` comes from the intrinsic's call
        // args, whose type resolves via `ty_signedness_shallow` (Uint -> Some(false),
        // Int -> Some(true)) — but "believed unreachable" is exactly how the Rvalue
        // lane's vacuous check survived, so it is handled rather than assumed.
        let count_signedness = self.operand_signedness(count_op);
        if count_signedness.is_none() {
            self.record_sound_fallback_reason("offset_count_signedness_unknown");
        }
        let count_is_signed = count_signedness.unwrap_or(true);
        let count = coerce_bitvec_width_safe(
            count,
            POINTER_WIDTH,
            SignExtension::for_signedness(count_is_signed),
        );

        let pointee_size_opt = ptr_op.ty(self.body.locals()).ok().and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _))
            | TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => self.get_type_size(inner),
            _ => None,
        });
        let Some(pointee_size) = pointee_size_opt else {
            return Vec::new();
        };

        // ZST discharge (marker: offset_isize_overflow_precise). The Rust/Kani
        // `offset` model returns the pointer UNCHANGED for a zero-size pointee
        // (`if t_size == 0 { return ptr; }`) BEFORE both the `offset.to_isize()`
        // conversion ("Offset value overflows isize") and the byte-product
        // overflow check ("Offset in bytes overflows isize"). So for a ZST:
        //   - obligation (1) (isize-overflow) does not apply — the byte offset
        //     is `count * size_of::<T>() == count * 0 == 0`, trivially in isize;
        //   - obligation (2) (in-bounds) is trivially satisfied — the result
        //     address equals the base, so there is nothing to bound and nothing
        //     to demote.
        // Emit NO obligations: the offset site is fully discharged and the
        // harness can prove Safe. (Previously the count-only isize-range check
        // below was emitted even for a ZST, spuriously failing a ZST offset
        // whose `count` exceeds isize::MAX — the false positive this fixes.)
        if pointee_size == 0 {
            debug!(
                "offset_isize_overflow_precise_marker: ZST offset site discharged \
                 (no isize-overflow or in-bounds obligation)"
            );
            return Vec::new();
        }

        let isize_max = Expr::bitvec_const((1i128 << (POINTER_WIDTH - 1)) - 1, POINTER_WIDTH);
        let isize_min = Expr::bitvec_const(-(1i128 << (POINTER_WIDTH - 1)), POINTER_WIDTH);
        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);

        // Constant-count fast-path: fold the count-only checks numerically so
        // fully-concrete offsets don't leave live error rules (static discharge).
        // `count` is the intrinsic's element COUNT operand — a value, not an
        // address (the twin producer in `ptr_offset_overflow_conditions` carries
        // the same tag from its own coercion site).
        let const_count_checks = Self::const_fold_offset_count_checks(
            &crate::codegen_ay::provenance::Val::of_value(count.clone()),
            count_is_signed,
            pointee_size as u64,
        );

        let mut checks: Vec<ModelOffsetCheck> = Vec::new();

        // Obligation (1a) — "Offset value overflows isize": the `count` must fit
        // `isize` (the `offset.to_isize()` conversion, reached only for a
        // non-ZST pointee). PRECISE, pure arithmetic, provenance-INDEPENDENT.
        match const_count_checks {
            Some((true, _)) => {}
            Some((false, _)) => checks.push(ModelOffsetCheck::overflow(
                Expr::bool_const(false),
                "Offset value overflows isize",
            )),
            None => {
                let count_in_range = if count_is_signed {
                    count.clone().bvsle(isize_max).and(count.clone().bvsge(isize_min))
                } else {
                    count.clone().bvule(isize_max)
                };
                checks.push(ModelOffsetCheck::overflow(
                    count_in_range,
                    "Offset value overflows isize",
                ));
            }
        }

        let byte_offset = if pointee_size == 1 {
            count.clone()
        } else {
            let size_expr = Expr::bitvec_const(pointee_size as u128, POINTER_WIDTH);
            let offset = count.clone().bvmul(size_expr.clone());
            // Obligation (1b) — "Offset in bytes overflows isize":
            // `count * size_of::<T>()` must not overflow `isize`. PRECISE, pure
            // arithmetic, provenance-INDEPENDENT.
            match const_count_checks {
                Some((_, true)) => {}
                Some((_, false)) => checks.push(ModelOffsetCheck::overflow(
                    Expr::bool_const(false),
                    "Offset in bytes overflows isize",
                )),
                None => {
                    let div_back = offset.clone().bvsdiv(size_expr);
                    checks.push(ModelOffsetCheck::overflow(
                        div_back.eq(count.clone()),
                        "Offset in bytes overflows isize",
                    ));
                }
            }
            offset
        };

        // Definite obligation-(1) violation short-circuit (marker:
        // offset_isize_overflow_precise). When the isize-overflow obligation is
        // an UNCONDITIONAL violation (count exceeds isize, or its byte product
        // overflows isize), the offset is UB purely arithmetically — the
        // resulting pointer is already invalid, so the provenance-DEPENDENT
        // in-bounds obligation (2) below is moot. Return now, BEFORE
        // `ptr_offset_alloc_bound_check`, so we do NOT record the
        // `OffsetProvenanceUnresolved` fail-closed demotion for a base pointer
        // whose obj_id lane happens to be symbolic. That demotion is a
        // crate-global counter with no per-harness attribution; emitting it on
        // a genuinely-failing harness leaks soundness doubt onto sibling
        // harnesses (e.g. a ZST twin whose own offset site is fully
        // discharged), spuriously flipping their proofs to failures. This
        // mirrors the established `intrinsic_span_check_folded_definite`
        // discharge: it fires ONLY when a check DEFINITELY fails, so the
        // harness fails genuinely on obligation (1) — it can NEVER convert a
        // proof into a false Safe, and the in-bounds net stays intact for every
        // non-definite (symbolic / fold-clean) offset. (A symbolic count whose
        // value the solver later finds to overflow still emits obligation (2)
        // below; its `OffsetProvenanceUnresolved` demotion is attributed to
        // THIS harness by the per-fn recording in `translate()`, so it never
        // leaks onto a sibling — see `record_offset_provenance_unresolved_for_fn`.)
        if matches!(const_count_checks, Some((false, _)) | Some((_, false))) {
            return checks;
        }

        // SOUNDNESS GATE: resolve side-channel provenance only when the
        // count-only checks POSITIVELY fold clean — see the twin comment in
        // ptr_offset_overflow_conditions (offset-bytes-overflow false-Safe:
        // resolving on an overflowing count removes the load-bearing
        // OffsetProvenanceUnresolved demotion).
        let count_checks_fold_clean = matches!(const_count_checks, Some((true, true)));

        // P4-3: projected-Vec base lane (twin of ptr_offset_overflow_conditions):
        // `vec.as_ptr().add(k)` — the buffer extent is the seeded cap state
        // var, `0 <= k && k <= cap` (one-past-end inclusive).
        //
        // P3-uninit: resolved BEFORE the wrap / same-object checks — those
        // operate on the 32-bit offset LANE of the split-pointer encoding of
        // the Vec's `fld_ptr`, an unconstrained symbolic value, so the solver
        // could pick a lane value that "wraps" and produce a spurious
        // Genuine-looking CTREX (vec-read-init FP). The cap bound subsumes
        // them for this lane: the walk proves the base is the ALLOCATION
        // START (buffer offset 0), Rust allocations fit isize, and the
        // fold-clean gate has verified the concrete count and its byte
        // product — a real address at offset 0 stepping 0 <= k <= cap cannot
        // wrap and cannot change objects.
        if count_checks_fold_clean
            && let Some(vec_bound) =
                self.projected_vec_offset_bound_for_operand(ptr_op, &count, modified_locals)
        {
            checks.push(ModelOffsetCheck::memory(vec_bound));
            debug!("CHC: generated projected-Vec model-offset alloc bound (P4-3)");
            if self.extra_pointer_checks
                && !self.int_lift
                && let Some((obj_id, _)) = self.split_pointer(&ptr)
            {
                let obj_valid = self.current_obj_valid_array();
                self.mark_heap_metadata_read();
                checks.push(ModelOffsetCheck::memory(obj_valid.select(obj_id)));
            }
            return checks;
        }

        // Raw-alloc route: anchored fold lane (twin of the BinOp::Offset
        // lane in `ptr_offset_overflow_conditions`) — a base pointer at a
        // concrete byte delta from a `__rust_alloc` allocation start with a
        // concrete size folds the whole bound at emission; wrap/same-object
        // subsumed by the same argument as the P4-3 Vec lane. Note the
        // fold-clean gate guarantees an unsigned count fits isize, so the
        // signed interpretation inside the helper is exact for both
        // signednesses.
        if count_checks_fold_clean
            && let Some(bound) =
                self.anchored_alloc_offset_bound_for_operand(ptr_op, &count, pointee_size as u64)
        {
            checks.push(ModelOffsetCheck::memory(bound));
            debug!("CHC: folded anchored raw-alloc model-offset alloc bound (raw-alloc route)");
            if self.extra_pointer_checks
                && !self.int_lift
                && let Some((obj_id, _)) = self.split_pointer(&ptr)
            {
                let obj_valid = self.current_obj_valid_array();
                self.mark_heap_metadata_read();
                checks.push(ModelOffsetCheck::memory(obj_valid.select(obj_id)));
            }
            return checks;
        }

        // Part of #3921: use split-pointer step for wrap detection + same-object check.
        let step = step_split_pointer(ptr.clone(), byte_offset);
        let result_ptr = step.result;
        let wrapped_forward =
            count.clone().bvsge(zero.clone()).and(result_ptr.clone().bvult(ptr.clone()));
        let wrapped_backward = count.clone().bvslt(zero).and(result_ptr.clone().bvugt(ptr.clone()));
        checks.push(ModelOffsetCheck::memory(wrapped_forward.or(wrapped_backward).not()));

        // When split-pointer recomposition was used, enforce same-object preservation.
        if let Some(same_object_ok) = step.same_object_ok {
            checks.push(ModelOffsetCheck::memory(same_object_ok));
        }

        // Allocation-size bound — the previously-vacuous part of the "same
        // allocation" guarantee (see ptr_offset_alloc_bound_check).
        {
            let known_obj_id = count_checks_fold_clean
                .then(|| self.offset_bound_obj_id_for_operand(ptr_op))
                .flatten();
            if let Some(bound_ok) =
                self.ptr_offset_alloc_bound_check(&ptr, &result_ptr, known_obj_id)
            {
                checks.push(ModelOffsetCheck::memory(bound_ok));
            }
        }

        if self.extra_pointer_checks
            && !self.int_lift
            && let Some((obj_id, _)) = self.split_pointer(&ptr)
        {
            let obj_valid = self.current_obj_valid_array();
            self.mark_heap_metadata_read();
            checks.push(ModelOffsetCheck::memory(obj_valid.select(obj_id)));
        }

        checks
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

    const ANY_ZST_ARRAY_COMPARE_SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        fn first<T>(slice: &[T]) -> Option<&T> {
            slice.first()
        }

        mod kani {
            #[kanitool::fn_marker = "AnyModel"]
            pub fn any<T>() -> T {
                panic!("model-only marker function")
            }

            #[kanitool::fn_marker = "AssumeHook"]
            pub fn assume(_cond: bool) {}
        }

        pub fn probe_any_zero_len_array_eq() {
            let empty_array: [u8; 0] = kani::any();
            assert_eq!(empty_array.len(), 0);
            assert_eq!(first(&empty_array), None);

            let cloned = empty_array.clone();
            assert_eq!(cloned, empty_array);

            let moved = empty_array;
            assert_eq!(moved, cloned);

            for _ in empty_array {
                unreachable!("no iteration should be possible");
            }
        }

        pub fn probe_any_zst_array_eq() {
            let zst_array: [(); 10] = kani::any();
            assert_eq!(zst_array.len(), 10);
            assert_eq!(first(&zst_array), Some(&()));

            let cloned = zst_array.clone();
            assert_eq!(cloned, zst_array);

            let moved = zst_array;
            assert_eq!(moved, cloned);

            for e in zst_array {
                assert_eq!(e, ());
            }
        }
    "#;

    fn assert_kani_any_zst_array_compare_has_no_dangerous_drops(fn_name: &str) {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        crate::codegen_ay::chc::clear_chc_fallback_counts();
        let _ = crate::codegen_ay::chc::take_translation_drop_by_fn();
        let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let mut missing_const_ref_type_keys = Vec::new();
        let mut flattened_locals = Vec::new();

        with_test_ay_ctx_for_source(ANY_ZST_ARRAY_COMPARE_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let mut debug_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            debug_ctx.declare_block_relations();
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            missing_const_ref_type_keys = debug_ctx
                .ref_resolution
                .const_ref_memory_inits
                .iter()
                .filter(|(type_key, _, _, _, _)| {
                    !debug_ctx.heap_state.type_arrays.contains_key(&**type_key)
                })
                .map(|(type_key, elem_sort, value, promoted_obj_id, byte_offset)| {
                    (
                        type_key.to_string(),
                        format!("{elem_sort:?}"),
                        format!("{:?}", value.sort()),
                        *promoted_obj_id,
                        *byte_offset,
                    )
                })
                .collect();
            flattened_locals = debug_ctx
                .flatten
                .flattened_tuple_locals
                .iter()
                .copied()
                .map(|local| (local, format!("{:?}", body.locals()[local].ty)))
                .collect();
            let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

            assert!(
                !vc.rules.is_empty(),
                "{fn_name} should produce a non-empty VC after canonical ZST any() assignment"
            );
            assert_eq!(
                diagnostics.unhandled_call.get(),
                0,
                "{fn_name} should translate without unhandled calls"
            );

            let fallback_count = crate::codegen_ay::chc::get_chc_fallback_counts()
                .get(fn_name)
                .copied()
                .unwrap_or(0);
            assert_eq!(
                fallback_count, 0,
                "{fn_name} should not record CHC fallbacks while comparing canonical any()-backed arrays"
            );
        });

        let translation_drops = crate::codegen_ay::chc::take_translation_drop_by_fn();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
        let fn_reasons = translation_sites.get(fn_name).cloned().unwrap_or_default();
        let resume_abort_count = fn_reasons.get("resume_abort").copied().unwrap_or(0);
        // call_dispatch_fallback is a sound overapproximation for calls that
        // cannot be inlined (e.g. ZST array iterator methods). Exclude it
        // from the "dangerous" drop count; per-reason checks below still
        // catch the harmful fallback families.
        let dispatch_fallback_count =
            fn_reasons.get("call_dispatch_fallback").copied().unwrap_or(0);
        let benign_drops = resume_abort_count + dispatch_fallback_count;
        assert!(
            drop_count >= benign_drops,
            "{fn_name} raw translation-drop count should cover all benign site-tagged drops. \
             total={drop_count}, resume_abort={resume_abort_count}, \
             call_dispatch_fallback={dispatch_fallback_count}, site_reasons={fn_reasons:?}"
        );
        let dangerous_drops = drop_count - benign_drops;

        assert_eq!(
            dangerous_drops, 0,
            "{fn_name} should have zero dangerous translation drops. total={drop_count}, \
             resume_abort={resume_abort_count}, call_dispatch_fallback={dispatch_fallback_count}, \
             site_reasons={fn_reasons:?}, \
             missing_const_ref_type_keys={missing_const_ref_type_keys:?}, \
             flattened_locals={flattened_locals:?}"
        );
        assert_eq!(
            fn_reasons.get("assign_sort_mismatch_nonbv").copied().unwrap_or(0),
            0,
            "{fn_name} should not hit Bool->Array assignment fallback, site_reasons={fn_reasons:?}"
        );
        assert_eq!(
            fn_reasons.get("flatten_dest_sort_mismatch").copied().unwrap_or(0),
            0,
            "{fn_name} should not hit flattened destination sort mismatch, site_reasons={fn_reasons:?}"
        );
        assert_eq!(
            fn_reasons.get("call_dispatch_fallback_prebuilt").copied().unwrap_or(0),
            0,
            "{fn_name} should not hit prebuilt call fallback, site_reasons={fn_reasons:?}"
        );
    }

    #[test]
    fn test_kani_any_zero_len_array_compare_avoids_translation_drops() {
        assert_kani_any_zst_array_compare_has_no_dangerous_drops("probe_any_zero_len_array_eq");
    }

    #[test]
    fn test_kani_any_zst_array_compare_avoids_translation_drops() {
        assert_kani_any_zst_array_compare_has_no_dangerous_drops("probe_any_zst_array_eq");
    }

    /// Contract-shim shaped fixture: the `write_any_slim` pointer flows through
    /// `&dst -> untracked_deref -> reborrow (&raw mut *p)` exactly like the
    /// kani modifies REPLACE lowering (FC modifies Shape A).
    const WRITE_ANY_UNTRACKED_SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            pub mod internal {
                #[kanitool::fn_marker = "UntrackedDerefHook"]
                #[inline(never)]
                pub fn untracked_deref<T>(_: &T) -> T {
                    unreachable!()
                }

                #[kanitool::fn_marker = "WriteAnySlimModel"]
                #[inline(never)]
                pub unsafe fn write_any_slim<T>(_pointer: *mut T) {}
            }
        }

        pub fn probe_write_any_untracked(dst: &mut u32) -> u32 {
            let holder = &dst;
            let copied: &mut u32 = kani::internal::untracked_deref(holder);
            let ptr: *mut u32 = &raw mut *copied;
            unsafe { kani::internal::write_any_slim(ptr) };
            *dst
        }

        pub fn probe_write_any_opaque(ptr_source: fn() -> *mut u32) -> u32 {
            let p = ptr_source();
            unsafe { kani::internal::write_any_slim(p) };
            0
        }
    "#;

    fn write_any_site_reasons(fn_name: &str) -> std::collections::BTreeMap<String, usize> {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        crate::codegen_ay::chc::clear_chc_fallback_counts();
        let _ = crate::codegen_ay::chc::take_translation_drop_by_fn();
        let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

        with_test_ay_ctx_for_source(WRITE_ANY_UNTRACKED_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            let (vc, _, _) = chc_ctx.translate_with_diagnostics();
            assert!(!vc.rules.is_empty(), "{fn_name} should produce a non-empty VC");
        });

        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        translation_sites.get(fn_name).cloned().unwrap_or_default()
    }

    /// Shape A regression: the shim-shaped pointer chain must resolve, so the
    /// modifies havoc is emitted through the checked place-havoc path and no
    /// fail-close markers are recorded for the write_any call.
    #[test]
    fn test_write_any_slim_resolves_untracked_deref_reborrow_chain() {
        let reasons = write_any_site_reasons("probe_write_any_untracked");
        assert_eq!(
            reasons.get("kani_write_any_slim_target_unresolved").copied().unwrap_or(0),
            0,
            "untracked_deref + reborrow chain should resolve, site_reasons={reasons:?}"
        );
        assert_eq!(
            reasons.get("call_dispatch_fallback").copied().unwrap_or(0),
            0,
            "resolved write_any_slim must not fall back, site_reasons={reasons:?}"
        );
    }

    /// Fail-close retention: a pointer with no resolvable identity chain (from
    /// an opaque fn-pointer call) must keep recording the unresolved marker —
    /// the havoc must never be silently dropped without demotion.
    #[test]
    fn test_write_any_slim_opaque_pointer_stays_fail_closed() {
        let reasons = write_any_site_reasons("probe_write_any_opaque");
        assert_eq!(
            reasons.get("kani_write_any_slim_target_unresolved").copied().unwrap_or(0),
            1,
            "opaque pointer must stay fail-closed, site_reasons={reasons:?}"
        );
    }
}

// DST model helpers and is_zst_ty live in codegen_call_kani_model_dst.rs (Part of #3210, #2408).
