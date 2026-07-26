// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Next-variant and range dispatch arms for iterator adapter CHC call codegen.
//!
//! Extracted from mod.rs per #4129 (500 LOC threshold).

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Operand;

use tracing::debug;

use crate::codegen_ay::stubs::StubKind;

use super::super::ChcCtx;
use super::super::stubs_option_helpers::OptionHelpers;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle MapNext/FilterNext/FilterMapNext/FlattenNext/ChainNext/ZipNext arms.
    pub(in crate::codegen_ay::chc) fn codegen_adapter_next_arm(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        dest_local: usize,
        dest_vec_idx: usize,
    ) -> (Option<Expr>, Option<Vec<Option<Expr>>>, Option<(usize, Expr)>, Vec<Expr>) {
        let mut result_expr: Option<Expr> = None;
        let mut flattened_result_fields: Option<Vec<Option<Expr>>> = None;
        let mut iter_update: Option<(usize, Expr)> = None;
        let mut adapter_extra_constraints: Vec<Expr> = Vec::new();

        if let Some((iter_expr, iter_local)) =
            self.iterator_receiver_expr_and_local(args, modified_locals)
            && let Some((advanced_iter, has_remaining)) = self.advance_iterator_expr(&iter_expr)
        {
            if let Some(iter_local) = iter_local {
                iter_update = Some((iter_local, advanced_iter));
            }
            // Part of #2874 Step 3: When dest is a flattened Option
            // (is_some: Bool, value: T), build field values directly
            // instead of constructing a Datatype that would mismatch
            // the scalar output slots.
            if self.flatten.flattened_tuple_locals.contains(&dest_local)
                && self.flatten.flattened_enum_discr.contains_key(&dest_local)
            {
                let field_count = self.flattened_field_count(dest_local);
                if field_count == 2
                    && let Some((_, payload_sort)) =
                        self.state_var_mgr.output_state_vars.get(dest_vec_idx + 1).cloned()
                {
                    let payload = self.fresh_adapter_symbol("iter_next_value", payload_sort);
                    // Part of #4112: constrain FlattenNext payload to concrete chars
                    // from MIR string array when flat_map operates on string literals.
                    if matches!(stub, StubKind::FlattenNext) {
                        if let Some(constraint) = self.try_constrain_flatten_next_payload(&payload)
                        {
                            adapter_extra_constraints.push(constraint);
                        }
                    }
                    flattened_result_fields = Some(vec![Some(has_remaining), Some(payload)]);
                }
            } else {
                // Non-flattened dest: build full Datatype Option result.
                if let Some(out_sort) =
                    self.state_var_mgr.output_state_vars.get(dest_vec_idx).map(|(_, s)| s.clone())
                {
                    let (option_result, raw_payload) =
                        self.build_adapter_next_result(stub, has_remaining, &out_sort);
                    if let Some(option_result) = option_result {
                        // Part of #4112: constrain FlattenNext payload to concrete chars
                        // from MIR string array when flat_map operates on string literals.
                        if matches!(stub, StubKind::FlattenNext) {
                            if let Some(payload) = &raw_payload {
                                if let Some(constraint) =
                                    self.try_constrain_flatten_next_payload(payload)
                                {
                                    adapter_extra_constraints.push(constraint);
                                }
                            }
                        }
                        result_expr = Some(option_result);
                    }
                }
            }
        }

        // Part of #4112: FlattenNext fallback for opaque BV64 iterators (FlatMap/FlattenCompat).
        // When advance_iterator_expr fails because the sort is BV64, model the iterator
        // as a position counter and use concrete chars from adapter_source_data.
        debug!(
            result_is_none = result_expr.is_none(),
            flat_is_none = flattened_result_fields.is_none(),
            ?stub,
            "FlattenNext fallback check (#4112)"
        );
        if result_expr.is_none()
            && flattened_result_fields.is_none()
            && matches!(stub, StubKind::FlattenNext)
        {
            if let Some((res, flat, upd, extras)) =
                self.try_concrete_flatten_next_bv64(args, modified_locals, dest_local, dest_vec_idx)
            {
                result_expr = res;
                flattened_result_fields = flat;
                iter_update = upd;
                adapter_extra_constraints.extend(extras);
            }
        }

        (result_expr, flattened_result_fields, iter_update, adapter_extra_constraints)
    }

    /// FlattenNext for opaque BV64 iterators with concrete chars from adapter_source_data.
    ///
    /// Part of #4112: flat_map(|s| s.chars()) over concrete string literals.
    fn try_concrete_flatten_next_bv64(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        dest_local: usize,
        dest_vec_idx: usize,
    ) -> Option<(Option<Expr>, Option<Vec<Option<Expr>>>, Option<(usize, Expr)>, Vec<Expr>)> {
        debug!("[4112-DIAG] try_concrete_flatten_next_bv64 entered dest_local={dest_local}");
        let (iter_expr, iter_local) =
            self.iterator_receiver_expr_and_local(args, modified_locals)?;
        debug!("[4112-DIAG] iter_local={iter_local:?} iter_sort={:?}", iter_expr.sort());

        // Only handle BV (opaque) iterator sorts
        let iter_width = iter_expr.sort().bitvec_width()?;

        // Find concrete chars stored by the constructor
        let iter_local_val = iter_local?;
        let concrete_elems = self
            .collections
            .adapter_source_data
            .get(&iter_local_val)
            .and_then(|d| d.concrete_elems.as_ref())
            .cloned();
        debug!(
            "[4112-DIAG] concrete_elems count={:?} for iter_local={iter_local_val}",
            concrete_elems.as_ref().map(|v| v.len())
        );
        let concrete_elems = concrete_elems?;

        if concrete_elems.is_empty() {
            return None;
        }
        debug!(
            "[4112-DIAG] BV64: have {} concrete elems, iter_width={}",
            concrete_elems.len(),
            iter_width
        );

        let total_count = concrete_elems.len();
        let count_bv = Expr::bitvec_const(total_count as u64, iter_width);
        let has_remaining = iter_expr.clone().bvult(count_bv);
        let one = Expr::bitvec_const(1u64, iter_width);
        let next_pos =
            Expr::ite(has_remaining.clone(), iter_expr.clone().bvadd(one), iter_expr.clone());

        let upd = Some((iter_local_val, next_pos));

        debug!(
            iter_local = iter_local_val,
            total_chars = total_count,
            "FlattenNext: BV64 concrete char dispatch (#4112)"
        );

        // Check if dest is flattened Option or Datatype Option
        if self.flatten.flattened_tuple_locals.contains(&dest_local)
            && self.flatten.flattened_enum_discr.contains_key(&dest_local)
        {
            let field_count = self.flattened_field_count(dest_local);
            if field_count == 2 {
                if let Some((_, payload_sort)) =
                    self.state_var_mgr.output_state_vars.get(dest_vec_idx + 1).cloned()
                {
                    let payload_width = payload_sort.bitvec_width().unwrap_or(32);
                    let payload = Self::build_concrete_ite_chain(
                        &iter_expr,
                        &concrete_elems,
                        iter_width,
                        payload_width,
                    );
                    debug!(
                        "[4112-DIAG] BV64 flatten-path: has_remaining_sort={:?} payload_sort={:?}",
                        has_remaining.sort(),
                        payload.sort()
                    );
                    let flat = Some(vec![Some(has_remaining), Some(payload)]);
                    return Some((None, flat, upd, vec![]));
                }
            }
        }

        // Non-flattened: build Datatype Option result
        if let Some(out_sort) =
            self.state_var_mgr.output_state_vars.get(dest_vec_idx).map(|(_, s)| s.clone())
        {
            let payload_sort = Self::adapter_option_payload_sort(&out_sort)?;
            let payload_width = payload_sort.bitvec_width().unwrap_or(32);
            let payload = Self::build_concrete_ite_chain(
                &iter_expr,
                &concrete_elems,
                iter_width,
                payload_width,
            );
            let some_value = self.make_some_expr_for_option(payload, &out_sort)?;
            let none_value = self.make_none_expr_for_option(&out_sort)?;
            let result = Expr::ite(has_remaining, some_value, none_value);
            debug!(result_sort = ?result.sort(), "BV64 non-flat path (#4112)");
            return Some((Some(result), None, upd, vec![]));
        }

        None
    }

    /// Build an ITE chain mapping position index to concrete element values.
    ///
    /// Part of #4112.
    fn build_concrete_ite_chain(
        pos: &Expr,
        elems: &[Expr],
        pos_width: u32,
        payload_width: u32,
    ) -> Expr {
        let mut result = Self::coerce_concrete_elem(
            elems.last().expect("invariant: elems non-empty checked by caller"),
            payload_width,
        );
        for (i, elem) in elems.iter().enumerate().rev() {
            let idx = Expr::bitvec_const(i as u64, pos_width);
            let coerced = Self::coerce_concrete_elem(elem, payload_width);
            result = Expr::ite(pos.clone().eq(idx), coerced, result);
        }
        result
    }

    /// Coerce a concrete element BV expression to the target payload width.
    fn coerce_concrete_elem(elem: &Expr, target_width: u32) -> Expr {
        let elem_width = elem.sort().bitvec_width().unwrap_or(32);
        if elem_width == target_width {
            elem.clone()
        } else {
            Expr::bitvec_const(0u64, target_width)
        }
    }

    /// Handle Range<T>::into_iter(self) identity arm.
    pub(in crate::codegen_ay::chc) fn codegen_range_into_iter_arm(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        dest_local: usize,
    ) -> (Option<Expr>, Option<Vec<Option<Expr>>>) {
        let mut result_expr: Option<Expr> = None;
        let mut flattened_result_fields: Option<Vec<Option<Expr>>> = None;

        // Range<T>::into_iter(self) is identity — the iterator IS the range.
        // For flattened Range locals, copy fields from source to destination.
        // Part of #3002: Without this, the destination iterator local is
        // unconstrained (free variable), making loop iteration non-deterministic.
        if let Some(receiver) = args.first()
            && let Operand::Copy(place) | Operand::Move(place) = receiver
        {
            let src_local: usize = place.local;
            if self.flatten.flattened_tuple_locals.contains(&src_local)
                && self.flatten.flattened_tuple_locals.contains(&dest_local)
            {
                // Flattened path: copy field-by-field (start, end, ...).
                let field_count = self.flattened_field_count(src_local);
                let mut fields = Vec::with_capacity(field_count);
                for i in 0..field_count {
                    fields.push(self.flattened_local_field_expr(src_local, i, modified_locals));
                }
                flattened_result_fields = Some(fields);
            } else {
                // Non-flattened (Datatype) path: direct expression copy.
                if let Some(src_expr) = self
                    .get_collection_arg(receiver, modified_locals)
                    .or_else(|| self.translate_operand_with_modified(receiver, modified_locals))
                {
                    result_expr = Some(src_expr);
                }
            }
        }

        (result_expr, flattened_result_fields)
    }

    /// Handle RangeSpecNext arm.
    pub(in crate::codegen_ay::chc) fn codegen_range_spec_next_arm(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        dest_local: usize,
        dest_vec_idx: usize,
    ) -> (
        Option<Expr>,
        Option<Vec<Option<Expr>>>,
        Option<(usize, Expr)>,
        Option<(usize, Expr, Expr)>,
        Vec<Expr>,
    ) {
        let mut result_expr: Option<Expr> = None;
        let mut flattened_result_fields: Option<Vec<Option<Expr>>> = None;
        let mut iter_update: Option<(usize, Expr)> = None;
        let mut iter_flattened_update: Option<(usize, Expr, Expr)> = None;
        let mut extra_constraints: Vec<Expr> = Vec::new();

        if let Some((iter_expr, iter_local)) =
            self.iterator_receiver_expr_and_local(args, modified_locals)
            && let Some((advanced_iter, has_remaining, current_item)) =
                self.advance_range_iterator_expr(&iter_expr, iter_local, modified_locals)
        {
            if let Some(bound) = self.range_advance_bound_constraint(
                &iter_expr,
                iter_local,
                &advanced_iter,
                &has_remaining,
                modified_locals,
            ) {
                extra_constraints.push(bound);
            }
            if let Some(iter_local) = iter_local {
                if self.flatten.flattened_tuple_locals.contains(&iter_local)
                    && let Some(iter_end) =
                        self.flattened_local_field_expr(iter_local, 1, modified_locals)
                {
                    iter_flattened_update = Some((iter_local, advanced_iter, iter_end));
                } else {
                    iter_update = Some((iter_local, advanced_iter));
                }
            }
            if self.flatten.flattened_tuple_locals.contains(&dest_local)
                && self.flatten.flattened_enum_discr.contains_key(&dest_local)
            {
                if let Some(values) = self.build_flattened_range_next_fields(
                    dest_local,
                    has_remaining,
                    current_item,
                    modified_locals,
                ) {
                    flattened_result_fields = Some(values);
                }
            } else if let Some(out_sort) =
                self.state_var_mgr.output_state_vars.get(dest_vec_idx).map(|(_, s)| s.clone())
                && let Some(option_result) =
                    self.build_range_next_result(has_remaining, current_item, &out_sort)
            {
                result_expr = Some(option_result);
            }
        }

        (
            result_expr,
            flattened_result_fields,
            iter_update,
            iter_flattened_update,
            extra_constraints,
        )
    }
}
