// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec extend-range operation: VecExtendRange + range resolution helpers.
//!
//! Extracted from `codegen_call_vec_ops_len.rs` per design:
//! designs/2026-03-17-vec-ops-len-misnamed-module-decomposition.md
//!
//! Part of #3928 decomposition.

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use std::collections::HashSet;
use tracing::debug;

use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;
use super::codegen_call_vec::ChcVecFields;
use super::codegen_ctx::types::CollectionProjectionKind;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// VecExtendRange: extend Vec from a Range/RangeInclusive iterator.
    ///
    /// Extracts the range start/end from args[1] (the iterator argument),
    /// computes range_len = end - start + 1, updates Vec len, and stores
    /// elements into the data array for small constant ranges.
    /// Part of #3607 D3.
    pub(in crate::codegen_ay::chc) fn vec_op_extend_range(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            return;
        };
        let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            return;
        };
        let old_len = self.collection_current_len(&len_var_name);
        debug!(coll_local, %len_var_name, "VecExtendRange: entry");

        // Resolve range start/end from args[1] (the Range/RangeInclusive struct).
        let (range_start, range_end) = match self.resolve_range_bounds(args, 1, modified_locals) {
            Some(pair) => pair,
            None => {
                // Cannot resolve range bounds — leave len unconstrained (sound).
                debug!(coll_local, "VecExtendRange: range bounds unresolved");
                self.mark_collection_len_modified(&len_var_name);
                return;
            }
        };

        // Widen range bounds to POINTER_WIDTH for len arithmetic.
        let start_wide = Self::widen_to_ptr_width(&range_start);
        let end_wide = Self::widen_to_ptr_width(&range_end);
        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        // Constant-fold range_len when both bounds are concrete (AY doesn't fold).
        let range_len = {
            use ay_bindings::ExprValue;
            match (range_start.value(), range_end.value()) {
                (
                    ExprValue::BitVecConst { value: sv, .. },
                    ExprValue::BitVecConst { value: ev, .. },
                ) if ev >= sv => Expr::bitvec_const(ev - sv + 1, POINTER_WIDTH),
                _ => end_wide.bvsub(start_wide).bvadd(one),
            }
        };
        debug!(?range_start, ?range_end, ?range_len, "VecExtendRange: computed range_len");

        let new_len = old_len.clone().bvadd(range_len.clone());
        // Guard: new_len >= old_len (unsigned overflow).
        acc.constraints.push(new_len.clone().bvuge(old_len.clone()));
        self.collection_len_set(&len_var_name, new_len.clone(), acc);

        // Cap growth: cap = max(cap, new_len).
        if let Some(cap_var_name) = self.collections.len_state.get_cap_var(coll_local).cloned() {
            let old_cap = self.collection_current_cap(&cap_var_name);
            let grow_needed = old_cap.clone().bvult(new_len.clone());
            let new_cap = Expr::ite(grow_needed, new_len.clone(), old_cap);
            self.collection_cap_set(&cap_var_name, new_cap.clone(), acc);
            Self::emit_cap_ge_len(new_cap, new_len, acc.constraints);
        }

        // Element storage: store data[old_len + i] = start + i for constant ranges.
        self.try_store_range_elements(
            coll_local,
            &old_len,
            &range_start,
            &range_len,
            modified_locals,
            acc,
        );
    }

    /// Resolve range start/end from a MIR operand at `arg_idx`.
    ///
    /// The operand should be a Range/RangeInclusive struct local. Tries:
    /// 1. Flattened fields: state vars at [base+0 (start), base+1 (end)]
    /// 2. Datatype: field_select on "start" / "end" fields
    fn resolve_range_bounds(
        &mut self,
        args: &[Operand],
        arg_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<(Expr, Expr)> {
        let arg = args.get(arg_idx)?;
        let arg_local = match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return None,
        };
        self.resolve_range_bounds_from_local(arg_local, modified_locals)
    }

    /// Try to store range elements into the Vec data array.
    ///
    /// For singleton constant ranges, stores:
    ///   data[old_len] = start
    /// For symbolic or multi-element ranges, skips (data left unconstrained —
    /// sound). Multi-element unrolling inside loops has proven expensive for
    /// AY's CHC invariant synthesis and length/capacity tracking is sufficient
    /// for safety-only extend loops.
    fn try_store_range_elements(
        &mut self,
        coll_local: usize,
        old_len: &Expr,
        range_start: &Expr,
        range_len: &Expr,
        _modified_locals: &HashSet<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        use ay_bindings::ExprValue;

        // Only unroll singleton constant range lengths.
        let concrete_len = match range_len.value() {
            ExprValue::BitVecConst { value, .. } => u64::try_from(value).ok().filter(|&n| n == 1),
            _ => None,
        };
        let Some(n) = concrete_len else { return };
        let Some(elem_width) = range_start.sort().bitvec_width() else {
            return;
        };

        // Path 1: Projected (flattened scalar fields) — mirrors VecPush projected path.
        if self.collections.projection_locals.get(&coll_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let data_field = self.flattened_local_field_expr(coll_local, 3, _modified_locals);
            if let Some(old_data) = data_field
                && old_data.sort().is_array()
            {
                let mut new_data = old_data;
                for i in 0..n {
                    let idx = old_len.clone().bvadd(Expr::bitvec_const(i, POINTER_WIDTH));
                    let val = range_start.clone().bvadd(Expr::bitvec_const(i, elem_width));
                    // Part of #4212: coerce range element to match data array sort.
                    let val =
                        Self::coerce_store_value(new_data.sort(), val, false, &self.diagnostics);
                    new_data = new_data.store(idx, val);
                }
                // Reconstruct all 4 fields with updated data.
                let ptr_field = self.flattened_local_field_expr(coll_local, 0, _modified_locals);
                let len_field = self.flattened_local_field_expr(coll_local, 1, _modified_locals);
                let cap_field = self.flattened_local_field_expr(coll_local, 2, _modified_locals);
                if let (Some(old_ptr), Some(old_fld_len), Some(old_fld_cap)) =
                    (ptr_field, len_field, cap_field)
                {
                    let new_fld_len = old_fld_len.bvadd(Expr::bitvec_const(n, POINTER_WIDTH));
                    let grow_needed = old_fld_cap.clone().bvult(new_fld_len.clone());
                    let new_fld_cap = Expr::ite(grow_needed, new_fld_len.clone(), old_fld_cap);
                    acc.constraints.push(new_fld_cap.clone().bvuge(new_fld_len.clone()));
                    let emitted = self.constrain_flattened_fields_for_call(
                        coll_local,
                        &[Some(old_ptr), Some(new_fld_len), Some(new_fld_cap), Some(new_data)],
                        acc.constraints,
                    );
                    if emitted {
                        acc.dests.push(coll_local);
                    }
                    debug!(
                        coll_local,
                        n, "VecExtendRange: stored {} elements via projected path", n
                    );
                }
            }
            return;
        }

        // Path 2: Datatype (Vec as single aggregate state var).
        let vec_idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&coll_local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied());
        let Some(vec_idx) = vec_idx else { return };

        let vec_input = self
            .state_var_mgr
            .state_vars
            .get(vec_idx)
            .map(|(name, sort)| Expr::var(&**name, sort.clone()));
        let Some(vec_in) = vec_input else { return };

        if let Some(fields) = ChcVecFields::extract(vec_in) {
            let ChcVecFields { vec_sort, ptr, len, cap, data } = fields;
            if !data.sort().is_array() {
                return;
            }

            let mut new_data = data;
            for i in 0..n {
                let idx = old_len.clone().bvadd(Expr::bitvec_const(i, POINTER_WIDTH));
                let val = range_start.clone().bvadd(Expr::bitvec_const(i, elem_width));
                // Part of #4212: coerce range element to match data array sort.
                let val = Self::coerce_store_value(new_data.sort(), val, false, &self.diagnostics);
                new_data = new_data.store(idx, val);
            }

            let new_len_field = len.bvadd(Expr::bitvec_const(n, POINTER_WIDTH));
            let grow_needed = cap.clone().bvult(new_len_field.clone());
            let new_cap_field = Expr::ite(grow_needed, new_len_field.clone(), cap);

            if let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
            {
                let dt_name = vec_sort.datatype_name().expect("ChcVecFields ensures datatype sort");
                acc.constraints.push(Self::build_vec_datatype_eq(
                    &dt_name,
                    vec![ptr, new_len_field, new_cap_field, new_data],
                    &out_name,
                    &out_sort,
                ));
                acc.dests.push(coll_local);
                debug!(coll_local, n, "VecExtendRange: stored {} elements via Datatype path", n);
            }
        }
    }

    /// Return a Vec's current `data` array expression for either the projected
    /// (flattened scalar field 3) or datatype (`ChcVecFields`) representation.
    /// Returns `None` if the local is not a tracked Vec, or `data` is not an
    /// array sort. Part of Fix 4 (append/extend element-value tracking).
    pub(in crate::codegen_ay::chc) fn vec_current_data_expr(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if self.collections.projection_locals.get(&local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let data = self.flattened_local_field_expr(local, 3, modified_locals)?;
            if data.sort().is_array() {
                return Some(data);
            }
            return None;
        }
        let vec_idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&local).copied())?;
        let vec_in = self
            .state_var_mgr
            .state_vars
            .get(vec_idx)
            .map(|(name, sort)| Expr::var(&**name, sort.clone()))?;
        let fields = ChcVecFields::extract(vec_in)?;
        if fields.data.sort().is_array() { Some(fields.data) } else { None }
    }

    /// Store an explicit list of source element `values` into a destination
    /// Vec's `data` array at logical indices `old_len + i`, reconstructing the
    /// len/cap fields, for BOTH the projected and datatype Vec representations.
    ///
    /// Mirrors [`try_store_range_elements`] but takes concrete element VALUES —
    /// used by `vec_op_append` / `vec_op_extend_from_slice` when the source
    /// element COUNT is a concrete constant. Adding `data'[old_len + i] ==
    /// values[i]` is a genuine fact, so this only TIGHTENS the (already-sound)
    /// over-approximation; symbolic counts keep the caller's unconstrained
    /// fallback. Returns true iff the data stores + field reconstruction were
    /// emitted. Part of Fix 4.
    pub(in crate::codegen_ay::chc) fn vec_store_appended_elements(
        &mut self,
        coll_local: usize,
        old_len: &Expr,
        values: &[Expr],
        modified_locals: &HashSet<usize>,
        acc: &mut CallAccumulator<'_>,
    ) -> bool {
        let n = values.len();
        if n == 0 {
            return false;
        }
        let n_bv = Expr::bitvec_const(n as u64, POINTER_WIDTH);

        // Path 1: Projected (flattened scalar fields) — mirrors VecPush.
        if self.collections.projection_locals.get(&coll_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let data_field = self.flattened_local_field_expr(coll_local, 3, modified_locals);
            let Some(old_data) = data_field.filter(|d| d.sort().is_array()) else {
                return false;
            };
            let mut new_data = old_data;
            for (i, val) in values.iter().enumerate() {
                let idx = old_len.clone().bvadd(Expr::bitvec_const(i as u64, POINTER_WIDTH));
                let val = Self::coerce_store_value(
                    new_data.sort(),
                    val.clone(),
                    false,
                    &self.diagnostics,
                );
                new_data = new_data.store(idx, val);
            }
            let ptr_field = self.flattened_local_field_expr(coll_local, 0, modified_locals);
            let len_field = self.flattened_local_field_expr(coll_local, 1, modified_locals);
            let cap_field = self.flattened_local_field_expr(coll_local, 2, modified_locals);
            let (Some(old_ptr), Some(old_fld_len), Some(old_fld_cap)) =
                (ptr_field, len_field, cap_field)
            else {
                return false;
            };
            let new_fld_len = old_fld_len.bvadd(n_bv.clone());
            let grow_needed = old_fld_cap.clone().bvult(new_fld_len.clone());
            let new_fld_cap = Expr::ite(grow_needed, new_fld_len.clone(), old_fld_cap);
            acc.constraints.push(new_fld_cap.clone().bvuge(new_fld_len.clone()));
            let emitted = self.constrain_flattened_fields_for_call(
                coll_local,
                &[Some(old_ptr), Some(new_fld_len), Some(new_fld_cap), Some(new_data)],
                acc.constraints,
            );
            if emitted {
                acc.dests.push(coll_local);
            }
            return emitted;
        }

        // Path 2: Datatype (Vec as single aggregate state var).
        let vec_idx = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&coll_local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied());
        let Some(vec_idx) = vec_idx else { return false };
        let vec_in = self
            .state_var_mgr
            .state_vars
            .get(vec_idx)
            .map(|(name, sort)| Expr::var(&**name, sort.clone()));
        let Some(vec_in) = vec_in else { return false };

        let Some(fields) = ChcVecFields::extract(vec_in) else { return false };
        let ChcVecFields { vec_sort, ptr, len, cap, data } = fields;
        if !data.sort().is_array() {
            return false;
        }
        let mut new_data = data;
        for (i, val) in values.iter().enumerate() {
            let idx = old_len.clone().bvadd(Expr::bitvec_const(i as u64, POINTER_WIDTH));
            let val =
                Self::coerce_store_value(new_data.sort(), val.clone(), false, &self.diagnostics);
            new_data = new_data.store(idx, val);
        }
        let new_len_field = len.bvadd(n_bv);
        let grow_needed = cap.clone().bvult(new_len_field.clone());
        let new_cap_field = Expr::ite(grow_needed, new_len_field.clone(), cap);
        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
        else {
            return false;
        };
        let dt_name = vec_sort.datatype_name().expect("ChcVecFields ensures datatype sort");
        acc.constraints.push(Self::build_vec_datatype_eq(
            &dt_name,
            vec![ptr, new_len_field, new_cap_field, new_data],
            &out_name,
            &out_sort,
        ));
        acc.dests.push(coll_local);
        true
    }

    /// Zero-extend a bitvec expression to POINTER_WIDTH.
    fn widen_to_ptr_width(expr: &Expr) -> Expr {
        let w = expr.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
        if w == POINTER_WIDTH {
            expr.clone()
        } else if w < POINTER_WIDTH {
            expr.clone().zero_extend(POINTER_WIDTH - w)
        } else {
            expr.clone().extract(POINTER_WIDTH - 1, 0)
        }
    }
}
