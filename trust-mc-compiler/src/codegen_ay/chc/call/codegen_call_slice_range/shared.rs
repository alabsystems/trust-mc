// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared subslice pipeline helpers.
//! Part of #3981.

use std::collections::HashSet;
use std::sync::Arc;

use ay_bindings::{Expr, Sort, SortInner};
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{ConstantKind, IntTy, RigidTy, Ty, TyConstKind, TyKind, UintTy};
use tracing::debug;

use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::{PtrRepr, PtrSlot};
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

use super::super::ChcCtx;
use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_rules::CodegenRules;

pub(super) struct SubsliceMaterialization {
    /// Where the materialized subslice lives.
    ///
    /// Both producers mint an address and know it: a fresh `concat(obj_id, 0)`
    /// allocation, or the source-derived address
    /// [`ChcCtx::resolve_subslice_source_addr`] decoded out of the source
    /// pointer. Carrying that as a [`Loc`] is what lets
    /// [`ChcCtx::emit_subslice_destination`] stop re-testing the width of its
    /// own allocation before packing it into a fat pointer.
    pub fresh_addr: Loc,
    pub elem_key: String,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn resolve_range_bounds_from_local(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<(Expr, Expr)> {
        Some((
            self.resolve_range_field_from_local(
                local,
                0,
                &["start", "fld_start"],
                modified_locals,
            )?,
            self.resolve_range_field_from_local(local, 1, &["end", "fld_end"], modified_locals)?,
        ))
    }

    pub(in crate::codegen_ay::chc) fn resolve_range_field_from_local(
        &mut self,
        local: usize,
        field_idx: usize,
        field_names: &[&str],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if let Some(expr) = self.extract_range_const_field_from_mir(local, field_idx) {
            debug!(local, field_idx, "range field: resolved via MIR constants");
            return Some(expr);
        }

        if let Some(expr) = self.flattened_local_field_expr(local, field_idx, modified_locals) {
            debug!(local, field_idx, "range field: resolved via flattened state vars");
            return Some(expr);
        }

        let expr = self.try_resolve_local_expr(local, modified_locals)?;
        let dt_name = expr.sort().datatype_name()?;
        for field_name in field_names {
            if let Some(field_sort) = Self::get_dt_field_sort(&expr, field_name) {
                debug!(local, field_idx, field_name, "range field: resolved via datatype field");
                return Some(expr.clone().field_select(dt_name, *field_name, field_sort));
            }
        }
        None
    }

    /// Allocate an address for a materialized subslice.
    ///
    /// The shifted backing array itself stays in the slice side tables
    /// (`const_ref_values` + `subslice_offset`/`subslice_len`). We do not store
    /// it under `slice_<elem>` typed memory because that lane is element-addressed
    /// (`Array<BV64, Elem>`), not array-valued (`Array<BV64, Array<BV64, Elem>>`).
    /// RangeFrom still seeds per-element typed memory separately for address-based
    /// loads through the fresh pointer.
    ///
    /// When `addr_override` is `Some`, the caller-supplied address is used
    /// instead of a fresh allocation; this preserves pointer identity for
    /// subslices derived from the same source array.
    /// Part of #4030: source-derived addresses fix fat pointer comparison.
    pub(super) fn materialize_subslice_type_array(
        &mut self,
        shifted: Expr,
        _inner_arr_sort: Sort,
        elem_ty: Ty,
        addr_override: Option<Loc>,
    ) -> Option<SubsliceMaterialization> {
        let _ = shifted;
        let fresh_addr = if let Some(addr) = addr_override {
            addr
        } else {
            // Allocation: an object id paired with a zero offset is an address
            // by construction, which is one of the two canonical `Loc` producers.
            let obj_id = self.heap_state.next_alloc_id()?;
            Loc::of_address(
                Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32)),
            )
        };

        let elem_key = self.type_key_for_body_ty(elem_ty).to_string();
        Some(SubsliceMaterialization { fresh_addr, elem_key })
    }

    /// Flush store chains, constrain destination pointer + fat-pointer length,
    /// and emit the final goto rule.
    pub(super) fn emit_subslice_destination(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        fresh_addr: Loc,
        coerce_label: &'static str,
        fat_ptr_label: &'static str,
    ) {
        let mut extra_constraints = Vec::new();
        extra_constraints.append(&mut self.heap_state.pending_updates);
        extra_constraints.append(&mut self.heap_state.drain_store_chains(&self.diagnostics));

        let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);

        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            // Part of #4030: a fat-pointer destination takes `[len | ptr]`.
            //
            // This used to be a two-part width test: `dest is bv128 AND
            // fresh_addr is bv64`. The second half tested this function's own
            // input — every producer of `fresh_addr` mints a `POINTER_WIDTH`
            // address (a `concat(obj_id, 0)` allocation, or `PtrRepr`'s data
            // half, which is `POINTER_WIDTH` for all three shapes) — so it was
            // asking whether an address is an address. Typing the parameter
            // `Loc` answers that once, and the remaining question is purely
            // about the DECLARED destination sort, which is what `PtrSlot` is
            // for. The packing order is stated by `PtrRepr::into_packed`
            // instead of being restated here as a bare `concat`.
            let coerce_value = if PtrSlot::of_sort(dest_var.sort()) == Some(PtrSlot::Fat) {
                let len_expr = self
                    .ref_resolution
                    .subslice_len
                    .get(&dest_local)
                    .cloned()
                    .unwrap_or_else(|| Expr::bitvec_const(0, POINTER_WIDTH));
                PtrRepr::from_declared_roles(fresh_addr, Val::of_value(len_expr))
                    .into_packed()
                    .expect("invariant: declared roles always pack")
            } else {
                fresh_addr.into_expr()
            };
            if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                coerce_value,
                dest_var.sort(),
                dest_local,
                coerce_label,
            ) {
                extra_constraints.push(eq);
            }
        }

        if self.flatten.flattened_tuple_locals.contains(&dest_local) {
            if let Some(len_expr) = self.ref_resolution.subslice_len.get(&dest_local).cloned()
                && let Some(base_idx) = self.try_state_idx_for_local(dest_local)
            {
                if let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(base_idx + 1).cloned()
                {
                    let len_var = Expr::var(&*out_name, out_sort.clone());
                    self.push_coerced_eq_constraint(
                        &mut extra_constraints,
                        &len_var,
                        len_expr,
                        &out_sort,
                        dest_local,
                        fat_ptr_label,
                    );
                    debug!(
                        fn_name = %self.fn_name,
                        dest_local,
                        "CHC slice range: constrained fat pointer length field"
                    );
                }
            }
        }

        self.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            extra_constraints,
        );
    }

    /// Seed per-element entries into element-level memory.
    /// RangeFrom-only: the slice-level store is not read by load_from_memory.
    pub(super) fn seed_subslice_element_memory(
        &mut self,
        fresh_addr: &Loc,
        source_inner: &Expr,
        effective_start: &Expr,
        elem_ty: Ty,
        inner_arr_sort: &Sort,
        elem_key: &str,
        max_elems: usize,
    ) {
        let SortInner::Array(ref arr_info) = *inner_arr_sort.inner() else {
            return;
        };
        let elem_val_sort = arr_info.element_sort.clone();
        let elem_size = self.get_type_size(elem_ty).unwrap_or(1) as u64;

        let (e_arr_in, e_arr_out, declared_e_sort, e_is_new) = self
            .heap_state
            .get_or_create_type_array(elem_key, elem_val_sort.clone(), &self.fn_name);
        self.heap_state.mark_type_array_written(&e_arr_in, self.current_encode_bb);
        if e_is_new {
            let e_arr_sort = Sort::array(ptr_sort(), elem_val_sort);
            self.push_late_state_var_pair(Arc::clone(&e_arr_in), &e_arr_out, e_arr_sort);
        }
        let e_state_idx = self.state_var_index_by_name(&e_arr_in);

        let e_outer_sort = Sort::array(ptr_sort(), declared_e_sort);
        let mut e_arr = if let Some(acc) = self.heap_state.get_store_chain(elem_key) {
            acc.clone()
        } else {
            Expr::var(&*e_arr_in, e_outer_sort)
        };

        for i in 0..max_elems {
            let idx_bv = Expr::bitvec_const(i as i128, POINTER_WIDTH);
            let byte_off =
                idx_bv.clone().bvmul(Expr::bitvec_const(elem_size as i128, POINTER_WIDTH));
            let elem_addr = fresh_addr.as_expr().clone().bvadd(byte_off);
            let src_idx = effective_start.clone().bvadd(idx_bv);
            let elem_val = source_inner.clone().select(src_idx);
            // Part of #4212: coerce source element to match target memory array sort.
            let elem_val =
                Self::coerce_store_value(e_arr.sort(), elem_val, false, &self.diagnostics);
            e_arr = e_arr.store(elem_addr, elem_val);
        }

        self.heap_state.accumulate_store(elem_key, &*e_arr_out, e_arr);
        if let Some(idx) = e_state_idx {
            self.mark_state_var_modified(idx);
        }
    }

    fn extract_range_const_field_from_mir(
        &self,
        start_local: usize,
        field_idx: usize,
    ) -> Option<Expr> {
        let locals_to_check = self.trace_move_copy_chain(start_local);

        if let Some(expr) = self.scan_aggregate_range_field_consts(&locals_to_check, field_idx) {
            return Some(expr);
        }
        self.scan_call_range_field_consts(&locals_to_check, field_idx)
    }

    /// Trace Move/Copy assignment chains from `start_local` to collect all
    /// reachable locals (up to depth 4).
    fn trace_move_copy_chain(&self, start_local: usize) -> Vec<usize> {
        use rustc_public::mir::{Rvalue, StatementKind};

        let mut locals_to_check = vec![start_local];
        for _ in 0..4 {
            let mut new_locals = Vec::new();
            for bb_data in &self.body.blocks {
                for stmt in &bb_data.statements {
                    let StatementKind::Assign(place, rvalue) = &stmt.kind else { continue };
                    if !place.projection.is_empty() {
                        continue;
                    }
                    if !locals_to_check.contains(&place.local) {
                        continue;
                    }
                    if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue {
                        if src.projection.is_empty()
                            && !locals_to_check.contains(&src.local)
                            && !new_locals.contains(&src.local)
                        {
                            new_locals.push(src.local);
                        }
                    }
                }
            }
            if new_locals.is_empty() {
                break;
            }
            locals_to_check.extend(new_locals);
        }
        locals_to_check
    }

    /// Scan MIR Aggregate statements for range constructors with constant fields.
    fn scan_aggregate_range_field_consts(
        &self,
        locals_to_check: &[usize],
        field_idx: usize,
    ) -> Option<Expr> {
        use rustc_public::mir::{AggregateKind, Rvalue, StatementKind};

        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else { continue };
                if !place.projection.is_empty() || !locals_to_check.contains(&place.local) {
                    continue;
                }
                if let Rvalue::Aggregate(AggregateKind::Adt(def, _, _, _, _), fields) = rvalue {
                    let name = def.trimmed_name();
                    if !matches!(
                        name.as_str(),
                        "Range" | "RangeInclusive" | "RangeFrom" | "RangeTo" | "RangeToInclusive"
                    ) || fields.len() <= field_idx
                    {
                        continue;
                    }
                    let field = &fields[field_idx];
                    if let Some(expr) = Self::try_extract_const_bitvec(field)
                        .or_else(|| self.trace_operand_to_const(field))
                    {
                        debug!(%name, local = place.local, field_idx, "extract_range_consts: found Aggregate");
                        return Some(expr);
                    }
                }
            }
        }
        None
    }

    /// Scan Call terminators for range constructors with constant args.
    fn scan_call_range_field_consts(
        &self,
        locals_to_check: &[usize],
        field_idx: usize,
    ) -> Option<Expr> {
        use rustc_public::mir::TerminatorKind;

        for bb_data in &self.body.blocks {
            let TerminatorKind::Call { func, args: call_args, destination, .. } =
                &bb_data.terminator.kind
            else {
                continue;
            };
            if !destination.projection.is_empty() || !locals_to_check.contains(&destination.local) {
                continue;
            }
            let callee_name = if let Operand::Constant(f) = func {
                format!("{:?}", f.const_.ty().kind())
            } else {
                continue;
            };
            if !(callee_name.contains("Range") && callee_name.contains("new"))
                || call_args.len() <= field_idx
            {
                continue;
            }
            let field = &call_args[field_idx];
            if let Some(expr) =
                Self::try_extract_const_bitvec(field).or_else(|| self.trace_operand_to_const(field))
            {
                debug!(
                    local = destination.local,
                    field_idx, "extract_range_consts: found Call new()"
                );
                return Some(expr);
            }
        }
        None
    }

    /// Trace a Move/Copy operand back through MIR to find a constant definition.
    fn trace_operand_to_const(&self, operand: &Operand) -> Option<Expr> {
        use rustc_public::mir::{Rvalue, StatementKind};
        let local = match operand {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return None,
        };
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else { continue };
                if place.local != local || !place.projection.is_empty() {
                    continue;
                }
                if let Rvalue::Use(inner_op) = rvalue
                    && let Some(expr) = Self::try_extract_const_bitvec(inner_op)
                {
                    return Some(expr);
                }
            }
        }
        None
    }

    /// Extract a constant integer from a MIR `Operand` as a AY bitvec expression.
    fn try_extract_const_bitvec(operand: &Operand) -> Option<Expr> {
        let Operand::Constant(const_op) = operand else { return None };
        let mir_const = &const_op.const_;
        let ty = mir_const.ty();

        let width: u32 = match ty.kind() {
            TyKind::RigidTy(RigidTy::Uint(u)) => match u {
                UintTy::U8 => 8,
                UintTy::U16 => 16,
                UintTy::U32 => 32,
                UintTy::U64 => 64,
                UintTy::U128 => 128,
                UintTy::Usize => POINTER_WIDTH,
            },
            TyKind::RigidTy(RigidTy::Int(i)) => match i {
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 => 64,
                IntTy::I128 => 128,
                IntTy::Isize => POINTER_WIDTH,
            },
            _ => return None,
        };

        let extract_from_alloc = |alloc: &rustc_public::ty::Allocation| -> Option<Expr> {
            let value = alloc.read_uint().ok()?;
            Some(Expr::bitvec_const(value, width))
        };

        match mir_const.kind() {
            ConstantKind::Allocated(alloc) => extract_from_alloc(alloc),
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_, alloc) => extract_from_alloc(alloc),
                _ => None,
            },
            _ => None,
        }
    }

    /// Resolve a source-derived data address for a subslice.
    ///
    /// Traces the `slice_arg` to its provenance local, looks up the local's
    /// stack address in `local_addresses`, and computes `base + start * elem_size`.
    /// Returns `None` when the source address is not resolvable (e.g., heap or
    /// symbolic provenance), in which case the caller should fall back to a
    /// fresh allocation.
    ///
    /// Part of #4030: preserves pointer identity for fat pointer comparison.
    pub(super) fn resolve_subslice_source_addr(
        &self,
        slice_arg: &Operand,
        effective_start: &Expr,
        elem_ty: Ty,
        modified_locals: &HashSet<usize>,
    ) -> Option<Loc> {
        let local = Self::operand_local(slice_arg)?;
        let elem_size = self.get_type_size(elem_ty)? as u64;

        // Strategy 1: stack local with known address. An object id paired with a
        // zero offset is an address by construction.
        let source_local = self.resolve_provenance_local(local);
        if let Some((obj_id, _)) = self.heap_state.local_addresses.get(&source_local) {
            let base_addr = Loc::of_address(
                Expr::bitvec_const(*obj_id as i128, 32).concat(Expr::bitvec_const(0, 32)),
            );
            return Some(self.apply_subslice_byte_offset(base_addr, effective_start, elem_size));
        }

        // Strategy 2: resolve the input local's expression and take its data
        // address. `slice_arg` is a slice operand, so the term is a pointer —
        // the caller establishes that from the MIR, not from this function.
        //
        // This used to be TWO returns partitioned by width: one for a `bv64`
        // thin pointer ("the expression IS the data address"), one for a `bv128`
        // fat pointer ("lower 64 bits are the data pointer"). The only thing the
        // width decided was *where the data address sits inside the term*, which
        // is exactly what `PtrRepr` answers — and `data()` is total, so both
        // shapes now take one path and a widened thin pointer (which the width
        // test read as a fat one) is no longer a third, unhandled case.
        let input_expr = self.try_resolve_local_expr(local, modified_locals)?;
        let data_addr = PtrRepr::classify(&input_expr)?.into_data();
        Some(self.apply_subslice_byte_offset(data_addr, effective_start, elem_size))
    }

    /// Advance an address by `effective_start` elements.
    ///
    /// Address plus value: the two operands are no longer interchangeable
    /// `Expr`s, and the result is the address, not the offset.
    fn apply_subslice_byte_offset(
        &self,
        base_addr: Loc,
        effective_start: &Expr,
        elem_size: u64,
    ) -> Loc {
        if elem_size == 0 {
            return base_addr;
        }
        let byte_offset =
            effective_start.clone().bvmul(Expr::bitvec_const(elem_size as i128, POINTER_WIDTH));
        Loc::of_address(base_addr.into_expr().bvadd(byte_offset))
    }

    /// Build cache key `(provenance_root, start_const)` for subslice address dedup.
    /// Part of #4098: use `resolve_provenance_root` so Box deref temps
    /// (`_tmp = &(*_box)`) share a cache key with the original Box local.
    pub(super) fn subslice_cache_key(
        &self,
        slice_arg: &Operand,
        effective_start: &Expr,
    ) -> Option<(usize, u64)> {
        let raw_local = Self::operand_local(slice_arg)?;
        let local = self.resolve_provenance_root(raw_local);
        let start_u64 = Self::try_eval_const_bv(effective_start)?;
        Some((local, start_u64))
    }

    /// Evaluate a BV expression to constant u64, folding `BvAdd(const, const)`.
    fn try_eval_const_bv(expr: &Expr) -> Option<u64> {
        use ay_bindings::ExprValue;
        match expr.value() {
            ExprValue::BitVecConst { value, .. } => value.clone().try_into().ok(),
            ExprValue::BvAdd(a, b) => {
                let a_val = Self::try_eval_const_bv(a)?;
                let b_val = Self::try_eval_const_bv(b)?;
                Some(a_val.wrapping_add(b_val))
            }
            _ => None,
        }
    }
}
