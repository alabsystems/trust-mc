// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC transition rule helpers: Box type detection, deallocation semantics,
//! SwitchInt guard construction, and block relation naming.
//!
//! Contains:
//! - `is_box_ty`: Box<T> type detection
//! - `detect_box_drop_call`: core::mem::drop(Box<T>) detection
//! - `emit_box_dealloc_transition`: Box deallocation with RustDealloc-shaped guards
//! - `switchint_case_guard`: SwitchInt branch guard construction
//! - `block_relation_name`: unique relation name for basic blocks
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::{Expr, ExprValue};

use crate::codegen_ay::provenance::Loc;
use num_bigint::BigInt;
use rustc_public::CrateDef;
use rustc_public::mir::{BasicBlockIdx, Operand};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;
use tracing::warn;

use super::codegen_expr_heap::{obj_size_in, obj_size_out, obj_valid_in, obj_valid_out};
use super::codegen_rules::CodegenRules;
use super::{CallCoerce, ChcCtx};
use trust_mc_core::chc::RelationApp;

/// Extension trait for rule generation helpers on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CodegenRulesHelpers<'tcx, 'body> {
    fn is_box_ty(ty: rustc_public::ty::Ty) -> bool;
    fn detect_box_drop_call(&self, func: &Operand, args: &[Operand]) -> bool;
    fn emit_box_dealloc_transition(
        &mut self,
        bb_idx: usize,
        from_app: &RelationApp,
        target: BasicBlockIdx,
        ptr_expr: Expr,
        known_alloc_id: Option<u32>,
        stmt_constraints: &[Expr],
        modified_locals: &HashSet<usize>,
    ) -> bool;
    #[must_use]
    fn switchint_case_guard(discr_expr: &Expr, case_val: u128, bb_idx: usize) -> Option<Expr>;
    #[must_use]
    fn switchint_otherwise_guard(
        discr_expr: &Expr,
        case_vals: &[u128],
        bb_idx: usize,
    ) -> Option<Expr>;
    fn block_relation_name(&self, bb: BasicBlockIdx) -> String;
}

impl<'tcx, 'body> CodegenRulesHelpers<'tcx, 'body> for ChcCtx<'tcx, 'body> {
    /// Returns true when `ty` is exactly `Box<T>`.
    fn is_box_ty(ty: rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                let name = def.name();
                name == "std::boxed::Box"
                    || name == "alloc::boxed::Box"
                    || def.trimmed_name() == "Box"
            }
            _ => false, // external enum: TyKind
        }
    }

    /// Detects `core::mem::drop` / `std::mem::drop` calls where the dropped value is Box-like.
    fn detect_box_drop_call(&self, func: &Operand, args: &[Operand]) -> bool {
        let Some(path) = self.resolve_callee_path(func) else {
            return false;
        };
        let is_mem_drop = path.contains("core::mem::drop") || path.contains("std::mem::drop");
        let Some(arg) = args.first() else {
            return false;
        };

        if is_mem_drop {
            if !arg.ty(self.body.locals()).ok().is_some_and(Self::is_box_ty) {
                return false;
            }

            // Restrict to direct local operands. MIR can represent `drop(&b)` via a
            // projected operand that still has Box type; modeling that as deallocation
            // is unsound because the referent is not consumed.
            return matches!(
                arg,
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty()
            );
        }

        if !path.contains("drop_in_place") && !path.contains("Drop>::drop") {
            return false;
        }

        let Ok(arg_ty) = arg.ty(self.body.locals()) else {
            return false;
        };
        match arg_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
            | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => Self::is_box_ty(pointee),
            _ => false,
        }
    }

    /// Emits Box deallocation semantics matching RustDealloc metadata updates.
    ///
    /// This models:
    /// - double-free guard (`obj_size[obj_id] == 0 || obj_valid[obj_id]`)
    /// - base-pointer guard (`obj_size[obj_id] == 0 || offset == 0`)
    /// - transition update (`obj_valid__out = store(obj_valid, obj_id, false)`)
    /// - obj_size passthrough (`obj_size__out = obj_size`)
    ///
    /// Returns false when the pointer cannot be split in the heap model.
    fn emit_box_dealloc_transition(
        &mut self,
        bb_idx: usize,
        from_app: &RelationApp,
        target: BasicBlockIdx,
        ptr_expr: Expr,
        known_alloc_id: Option<u32>,
        stmt_constraints: &[Expr],
        modified_locals: &HashSet<usize>,
    ) -> bool {
        // Part of #3655: Box<str> and Box<[T]> are represented as Datatype
        // expressions (e.g. Slice_bv8(fld_ptr, fld_len, fld_data)) rather than
        // flat BV64 pointers. Extract the fld_ptr field before split_pointer().
        let bv_ptr = super::dyn_coercion::extract_pointer_expr(&ptr_expr)
            .map(Loc::into_expr)
            .unwrap_or(ptr_expr);
        let Some((raw_obj_id_expr, offset_expr)) = self.split_pointer(&bv_ptr) else {
            return false;
        };
        let obj_id_expr = rust_dealloc_obj_id_expr(raw_obj_id_expr, known_alloc_id);

        let obj_valid_in = obj_valid_in();
        let obj_valid_out = obj_valid_out();
        let obj_size_in = obj_size_in();
        let obj_size_out = obj_size_out();

        // Safety check: object must still be valid (double-free/UAF guard).
        let is_valid = rust_dealloc_validity_guard(&obj_valid_in, &obj_size_in, &obj_id_expr);
        self.emit_error_rule_for_condition(from_app, is_valid, stmt_constraints, bb_idx);

        // Safety check: deallocation requires a base pointer.
        let offset_zero = rust_dealloc_base_pointer_guard(&obj_size_in, &obj_id_expr, offset_expr);
        self.emit_error_rule_for_condition(from_app, offset_zero, stmt_constraints, bb_idx);

        // Part of #3159: Prevent dealloc from aliasing with stack locals.
        // Same rationale as the check in translate_rust_dealloc: stack locals
        // are never freed, so the dealloc obj_id must differ from all of them.
        // These are TRANSITION CONSTRAINTS (not error rules) because the obj_id
        // may be symbolic — error rules would be trivially satisfiable.
        // Collect before obj_id_expr is consumed by the freed constraint.
        let mut extra_constraints = Vec::new();
        for stack_obj_id in self.heap_state.stack_local_obj_ids() {
            let stack_id_expr = Expr::bitvec_const(stack_obj_id as i128, 32);
            extra_constraints.push(obj_id_expr.clone().eq(stack_id_expr).not());
        }

        let freed = obj_valid_out.eq(obj_valid_in.store(obj_id_expr, Expr::bool_const(false)));
        let size_preserved = obj_size_out.eq(obj_size_in);
        extra_constraints.push(freed);
        extra_constraints.push(size_preserved);

        self.mark_heap_metadata_modified();
        // Fix #2310: Use the shared build_output_args which now correctly
        // propagates metadata arrays (obj_valid, obj_size) and memory arrays,
        // and properly maps MIR local indices to state-vector indices.
        let new_output_args = self.build_output_args(modified_locals, &[]);

        self.emit_goto_rule_extra(
            from_app,
            target,
            &new_output_args,
            stmt_constraints,
            extra_constraints,
        );
        true
    }

    /// Builds a SwitchInt branch guard for a given discriminant and case value.
    fn switchint_case_guard(discr_expr: &Expr, case_val: u128, bb_idx: usize) -> Option<Expr> {
        if discr_expr.sort().is_bool() {
            let guard = match case_val {
                0 => discr_expr.clone().not(),
                1 => discr_expr.clone(),
                _ => {
                    // non-enum: u128 (case_val)
                    warn!(?bb_idx, case_val, "bool SwitchInt case value outside 0/1");
                    return Some(Expr::bool_const(false));
                }
            };
            return Some(guard);
        }

        if let Some(width) = discr_expr.sort().bitvec_width() {
            // Guard: 0-width bitvec is degenerate — no value can match any case.
            // Sort::bitvec(0) panics in the AY API, so this shouldn't occur in
            // practice, but Expr::bitvec_const(val, 0) would also panic. The
            // width > 0 guard at the sign-extension check (W3:3365) only protects
            // that sub-path; this early return protects the bitvec_const call below.
            if width == 0 {
                warn!(?bb_idx, case_val, "degenerate 0-width bitvec in SwitchInt discriminant");
                return Some(Expr::bool_const(false));
            }
            if width < 128 {
                // Mask case_val to bitvec width. MIR stores signed discriminants
                // (e.g., Ordering::Less = -1) as u128::MAX, which exceeds the
                // bitvec range. Masking gives the correct bit pattern.
                // Consistent with BMC path (terminator.rs:287-288).
                let mask = (1u128 << width) - 1;
                let masked_val = case_val & mask;

                // Detect genuine overflow vs sign-extension (#3560).
                // After masking, sign-extend back to 128 bits: if the result
                // matches case_val, this was a valid signed representation
                // (e.g., -1 stored as u128::MAX → masked 0xFF → sign-extended
                // back to u128::MAX). If not, case_val genuinely overflows
                // the bitvec width (e.g., 256 in 8-bit) → branch unreachable.
                if masked_val != case_val {
                    let sign_bit = 1u128 << (width - 1);
                    let sign_extended =
                        if masked_val & sign_bit != 0 { masked_val | !mask } else { masked_val };
                    if sign_extended != case_val {
                        return Some(Expr::bool_const(false));
                    }
                }

                return Some(discr_expr.clone().eq(Expr::bitvec_const(masked_val, width)));
            }
            return Some(discr_expr.clone().eq(Expr::bitvec_const(case_val, width)));
        }

        if discr_expr.sort().is_int() {
            let value = BigInt::from(case_val);
            return Some(discr_expr.clone().eq(Expr::int_const(value)));
        }

        // Part of #4181: Array-sorted SwitchInt from coroutine state locals.
        if let Some(guard) = switchint_array_sort_guard(discr_expr, case_val, bb_idx) {
            return Some(guard);
        }

        warn!(
            ?bb_idx,
            sort = ?discr_expr.sort(),
            "unsupported SwitchInt discriminant sort"
        );
        None
    }

    /// Builds the SwitchInt otherwise guard. If the discriminant expression has
    /// a finite syntactic value set already covered by explicit cases, the
    /// otherwise branch is unreachable and can be skipped before solver time.
    fn switchint_otherwise_guard(
        discr_expr: &Expr,
        case_vals: &[u128],
        bb_idx: usize,
    ) -> Option<Expr> {
        if switchint_cases_cover_expr(discr_expr, case_vals) {
            return Some(Expr::bool_const(false));
        }

        case_vals
            .iter()
            .filter_map(|&case_val| Self::switchint_case_guard(discr_expr, case_val, bb_idx))
            .map(Expr::not)
            .reduce(Expr::and)
    }

    /// Generates a unique relation name for a basic block.
    fn block_relation_name(&self, bb: BasicBlockIdx) -> String {
        use std::fmt::Write;
        let mut name = String::with_capacity(self.fn_name.len() + 6);
        name.push_str(&self.fn_name);
        name.push_str("__bb");
        let _ = write!(name, "{bb}");
        name
    }
}

/// Only a bare dropped local owns the allocation identity represented by
/// `known_alloc_ids[local]`. A projected drop like `drop(_x.field)` must derive
/// the deallocated object from the projected pointer expression instead.
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) fn known_alloc_id_for_unprojected_drop_place(
    ctx: &ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
) -> Option<u32> {
    if place.projection.is_empty() { ctx.known_alloc_ids.get(&place.local).copied() } else { None }
}

pub(in crate::codegen_ay::chc) fn traced_alloc_id_for_unprojected_drop_place(
    ctx: &ChcCtx<'_, '_>,
    place: &rustc_public::mir::Place,
) -> Option<u32> {
    if !place.projection.is_empty() {
        return None;
    }
    let operand =
        Operand::Copy(rustc_public::mir::Place { local: place.local, projection: Vec::new() });
    ctx.trace_arg_to_alloc_id(&operand)
        .or_else(|| ctx.trace_deref_store_alloc_id(place.local))
        .filter(|obj_id| !drop_alloc_id_is_stack_obj(ctx, *obj_id))
        .or_else(|| unique_known_heap_alloc_id_for_drop(ctx))
}

fn drop_alloc_id_is_stack_obj(ctx: &ChcCtx<'_, '_>, obj_id: u32) -> bool {
    ctx.heap_state.stack_local_obj_ids().contains(&obj_id)
}

fn unique_known_heap_alloc_id_for_drop(ctx: &ChcCtx<'_, '_>) -> Option<u32> {
    let stack_obj_ids = ctx.heap_state.stack_local_obj_ids();
    let mut found = None;
    for obj_id in ctx.known_alloc_ids.values().copied() {
        if stack_obj_ids.contains(&obj_id) {
            continue;
        }
        if found.is_some_and(|seen| seen != obj_id) {
            return None;
        }
        found = Some(obj_id);
    }
    found
}

pub(in crate::codegen_ay::chc) fn rust_dealloc_base_ptr_for_known_alloc_id(obj_id: u32) -> Expr {
    Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0u64, 32))
}

/// Match RustDealloc's allocation identity recovery: when the pointer value is
/// symbolic but the dropped local still has a safe known allocation ID, use that
/// ID for metadata selects/stores instead of the raw pointer extract.
pub(in crate::codegen_ay::chc) fn rust_dealloc_obj_id_expr(
    raw_obj_id_expr: Expr,
    known_alloc_id: Option<u32>,
) -> Expr {
    known_alloc_id.map(|obj_id| Expr::bitvec_const(obj_id as i128, 32)).unwrap_or(raw_obj_id_expr)
}

pub(in crate::codegen_ay::chc) fn rust_dealloc_zero_sized_or_unregistered_guard(
    obj_size: &Expr,
    obj_id_expr: &Expr,
) -> Expr {
    obj_size.clone().select(obj_id_expr.clone()).eq(Expr::bitvec_const(0u64, 32))
}

pub(in crate::codegen_ay::chc) fn rust_dealloc_validity_guard(
    obj_valid: &Expr,
    obj_size: &Expr,
    obj_id_expr: &Expr,
) -> Expr {
    Expr::or(
        rust_dealloc_zero_sized_or_unregistered_guard(obj_size, obj_id_expr),
        obj_valid.clone().select(obj_id_expr.clone()),
    )
}

pub(in crate::codegen_ay::chc) fn rust_dealloc_base_pointer_guard(
    obj_size: &Expr,
    obj_id_expr: &Expr,
    offset_expr: Expr,
) -> Expr {
    Expr::or(
        rust_dealloc_zero_sized_or_unregistered_guard(obj_size, obj_id_expr),
        offset_expr.eq(Expr::bitvec_const(0, 32)),
    )
}

fn switchint_cases_cover_expr(discr_expr: &Expr, case_vals: &[u128]) -> bool {
    let Some(values) = finite_switchint_values(discr_expr, 0) else {
        return false;
    };
    if values.is_empty() {
        return false;
    }

    let covered: Vec<u128> = case_vals
        .iter()
        .filter_map(|&case_val| normalize_switchint_case_for_sort(discr_expr, case_val))
        .collect();

    values.into_iter().all(|value| covered.contains(&value))
}

fn finite_switchint_values(expr: &Expr, depth: usize) -> Option<Vec<u128>> {
    if depth > 8 {
        return None;
    }

    if expr.sort().is_bool() {
        return Some(vec![0, 1]);
    }

    match expr.value() {
        ExprValue::BitVecConst { value, .. } | ExprValue::IntConst(value) => {
            u128::try_from(value.clone()).ok().map(|value| vec![value])
        }
        ExprValue::Ite { then_expr, else_expr, .. } => {
            let mut values = finite_switchint_values(then_expr, depth + 1)?;
            for value in finite_switchint_values(else_expr, depth + 1)? {
                if !values.contains(&value) {
                    values.push(value);
                }
            }
            Some(values)
        }
        _ => None,
    }
}

fn normalize_switchint_case_for_sort(discr_expr: &Expr, case_val: u128) -> Option<u128> {
    if discr_expr.sort().is_bool() {
        return (case_val <= 1).then_some(case_val);
    }

    if let Some(width) = discr_expr.sort().bitvec_width() {
        if width == 0 {
            return None;
        }
        if width < 128 {
            let mask = (1u128 << width) - 1;
            let masked_val = case_val & mask;
            if masked_val != case_val {
                let sign_bit = 1u128 << (width - 1);
                let sign_extended =
                    if masked_val & sign_bit != 0 { masked_val | !mask } else { masked_val };
                if sign_extended != case_val {
                    return None;
                }
            }
            return Some(masked_val);
        }
        return Some(case_val);
    }

    discr_expr.sort().is_int().then_some(case_val)
}

/// Part of #4181: Array-sorted SwitchInt discriminants arise when coroutine
/// state or drop-flag locals get byte-array sorts (Array(BV64, BV8)) from
/// large [u8; N] fields. The discriminant value lives at index 0 of the
/// byte array. Select the first byte and compare against the case value
/// truncated to the element width.
fn switchint_array_sort_guard(discr_expr: &Expr, case_val: u128, bb_idx: usize) -> Option<Expr> {
    let array_sort = discr_expr.sort().array_sort()?;
    let elem_width = array_sort.element_sort.bitvec_width()?;
    let index_expr = if array_sort.index_sort.is_bitvec() {
        let idx_width = array_sort.index_sort.bitvec_width().unwrap_or(64);
        Expr::bitvec_const(0u64, idx_width)
    } else if array_sort.index_sort.is_int() {
        Expr::int_const(BigInt::from(0u64))
    } else {
        tracing::warn!(
            ?bb_idx,
            sort = ?discr_expr.sort(),
            "unsupported SwitchInt array index sort"
        );
        return None;
    };
    let selected = discr_expr.clone().select(index_expr);
    let mask = if elem_width < 128 { (1u128 << elem_width) - 1 } else { u128::MAX };
    let masked_val = case_val & mask;
    tracing::debug!(
        ?bb_idx,
        case_val,
        masked_val,
        elem_width,
        "SwitchInt on Array sort: selecting byte 0 for discriminant guard"
    );
    Some(selected.eq(Expr::bitvec_const(masked_val, elem_width)))
}
