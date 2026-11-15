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
use super::range_span::{RangeLen, RangeStep, fold_range_count, range_span};
use super::codegen_call_vec_ops::ProjectedVecState;
use super::codegen_ctx::types::CollectionProjectionKind;

/// The most elements an append of a constant count stores one by one: the
/// range's own values for an integer range, a fresh array's otherwise. A
/// longer append leaves `data` a fresh array.
const MAX_APPEND_STORE_ELEMS: u64 = 64;


/// What an append stores in a Vec's `data` (`write_appended_vec_fields`).
pub(in crate::codegen_ay::chc) enum AppendedElements<'a> {
    /// `start + i` for `i` in `0..n`, as `width`-bit values (a constant range).
    Range { start: &'a Expr, width: u32, n: u64 },
    /// Unknown values: `data` becomes a fresh array, minted under the given
    /// sound-havoc reason with the array as its freed variable (Rule E).
    Fresh(crate::codegen_ay::chc::codegen_ctx::SoundHavocReason),
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// VecExtendRange: extend Vec from a Range/RangeInclusive iterator.
    ///
    /// Reads the range's bounds from args[1], adds its exact element count
    /// (`range_span.rs`) to the Vec's length, and writes the Vec's own fields
    /// (`write_range_extended_vec_fields`).
    ///
    /// Returns the condition under which the call does not panic with
    /// "capacity overflow", for the caller to state as a check; the length
    /// update assumes it. `None` when nothing was modelled (the length is
    /// left unconstrained, a sound havoc). Part of #3607 D3.
    pub(in crate::codegen_ay::chc) fn vec_op_extend_range(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) -> Option<Expr> {
        let coll_local = collection_local?;
        let len_var_name = self.collections.len_state.get_len_var(coll_local).cloned()?;
        let old_len = self.collection_current_len(&len_var_name);
        debug!(coll_local, %len_var_name, "VecExtendRange: entry");

        // The element type orders the bounds: signed, unsigned or `char`.
        let Some((step, inclusive)) = args
            .get(1)
            .and_then(|op| op.ty(self.body.locals()).ok())
            .and_then(RangeStep::of_range_ty)
        else {
            debug!(coll_local, "VecExtendRange: not a Range / RangeInclusive of integers or char");
            self.record_sound_fallback_reason("vec_extend_range_step_unmodelled");
            self.mark_collection_len_modified(&len_var_name);
            return None;
        };

        // Resolve range start/end from args[1] (the Range/RangeInclusive struct).
        let (range_start, range_end) = match self.resolve_range_bounds(args, 1, modified_locals) {
            Some(pair) => pair,
            None => {
                // Cannot resolve range bounds — leave len unconstrained (sound).
                debug!(coll_local, "VecExtendRange: range bounds unresolved");
                self.record_sound_fallback_reason("vec_extend_range_bounds_unresolved");
                self.mark_collection_len_modified(&len_var_name);
                return None;
            }
        };

        // `start..end` yields `Step::steps_between(start, end)` elements in
        // the element type's own order, and `start..=end` one more unless it
        // is exhausted (`range_span.rs`). The length was `end - start + 1`
        // for both before round 4 and then compared zero-extended bounds
        // unsigned, so `-2i8..3` added no element and `2i8..-1` 253 (walker
        // fail-closed repair round 5, `range_extend_kinds_dual.rs`). A
        // `RangeInclusive`'s `exhausted` flag is false for a literal that is
        // current where it is read (`extract_range_const_field_from_mir`),
        // read from the range's state otherwise, and when neither answers
        // the length fails closed.
        let arg_local = match args.get(1) {
            Some(Operand::Copy(place) | Operand::Move(place)) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        };
        let exhausted = if inclusive {
            arg_local.and_then(|local| self.range_inclusive_exhausted(local, modified_locals))
        } else {
            Some(Expr::bool_const(false))
        };
        let Some(exhausted) = exhausted else {
            debug!(coll_local, "VecExtendRange: RangeInclusive exhaustion unknown — fail closed");
            self.record_sound_fallback_reason("vec_extend_range_exhaustion_unresolved");
            self.mark_collection_len_modified(&len_var_name);
            return None;
        };
        let Some(span) = range_span(step, &range_start, &range_end) else {
            debug!(coll_local, ?step, "VecExtendRange: a bound is not an element-width bitvector — fail closed");
            self.record_sound_fallback_reason("vec_extend_range_bound_sort");
            self.mark_collection_len_modified(&len_var_name);
            return None;
        };
        let RangeLen { len: range_len, too_long } = span.len(inclusive, exhausted.clone());
        // Constant-fold the length when the bounds and the exhaustion are
        // concrete (AY doesn't fold), which `write_range_extended_vec_fields` relies on.
        let range_len = match exhausted.value() {
            ay_bindings::ExprValue::BoolConst(exhausted) => {
                match fold_range_count(step, &range_start, &range_end, inclusive, *exhausted) {
                    Some(count) => Expr::bitvec_const(count, POINTER_WIDTH),
                    None => range_len,
                }
            }
            _ => range_len,
        };
        debug!(?range_start, ?range_end, ?range_len, "VecExtendRange: computed range_len");

        // `extend` reserves the whole count before its loop, and the
        // reservation panics with "capacity overflow" when the count has no
        // upper bound (`too_long`), when `len + count` overflows, or when the
        // grown capacity, `max(2 * cap, len + count)`, is past
        // `isize::MAX / size_of::<T>()` (`RawVec::grow_amortized`,
        // `Layout::array`). The length used to be assumed not to wrap, so
        // `v.extend(0u64..u64::MAX)` verified clean where Kani fails (walker
        // fail-closed repair round 5, `range_extend_kinds_dual.rs`). Without
        // a capacity, any capacity of at least the length is allowed: the
        // grown capacity can only be past the limit when `len + count`
        // exceeds half of it.
        let new_len = old_len.clone().bvadd(range_len.clone());
        let elem_bytes = u64::from(step.width() / 8).max(1);
        let max_cap = Expr::bitvec_const((i64::MAX as u64) / elem_bytes, POINTER_WIDTH);
        let half_max_cap = Expr::bitvec_const((i64::MAX as u64) / elem_bytes / 2, POINTER_WIDTH);
        let wraps = new_len.clone().bvult(old_len.clone());
        let cap_var = self.collections.len_state.get_cap_var(coll_local).cloned();
        let old_cap = cap_var.as_ref().map(|name| self.collection_current_cap(name));
        let grow_fails = match &old_cap {
            Some(cap) => {
                let needs_grow = wraps.clone().or(cap.clone().bvult(new_len.clone()));
                needs_grow.and(
                    wraps
                        .clone()
                        .or(new_len.clone().bvugt(max_cap))
                        .or(cap.clone().bvugt(half_max_cap)),
                )
            }
            None => wraps.or(new_len.clone().bvugt(half_max_cap)),
        };
        let no_capacity_panic = too_long.or(grow_fails).not();
        acc.constraints.push(no_capacity_panic.clone());
        self.collection_len_set(&len_var_name, new_len.clone(), acc);

        // Cap growth: `extend_trusted` reserves the count, RawVec's amortized
        // growth (`shared::vec_capacity`). It was `max(cap, new_len)`, so
        // `Vec::<u8>::new(); v.extend(0u8..3); v.capacity() == 3` verified
        // clean where Kani fails (std gives 8; walker fail-closed review,
        // round 2 of the repair after the merge with main,
        // `vec_capacity_growth_dual.rs`).
        if let (Some(cap_var_name), Some(old_cap)) = (cap_var, old_cap) {
            let new_cap = self.vec_reserved_cap(
                Some(self.body.locals()[coll_local].ty),
                &old_cap,
                &new_len,
                crate::codegen_ay::shared::vec_capacity::VecGrowth::Amortized,
                acc.constraints,
            );
            self.collection_cap_set(&cap_var_name, new_cap.clone(), acc);
            Self::emit_cap_ge_len(new_cap, new_len, acc.constraints);
        }

        // The Vec's own fields: length, capacity and the stored elements.
        self.write_range_extended_vec_fields(
            coll_local,
            step,
            &range_start,
            &range_len,
            modified_locals,
            acc,
        );
        Some(no_capacity_panic)
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

    /// Write the extended Vec's own fields: its `len` is the old one plus the
    /// range's count, its `cap` at least that, and its `data` holds the range's
    /// elements from the old length on.
    ///
    /// The elements are stored exactly when the count is a constant of at most
    /// [`MAX_APPEND_STORE_ELEMS`] (every count for an integer range, one for
    /// `char`, whose step skips the surrogate gap). Otherwise the appended
    /// slots hold a fresh array's values (`appended_data`), an identified sound
    /// havoc: a counterexample that reads them is not certified.
    ///
    /// Only a one-element range was written before, and every other count left
    /// the fields as they were: the side-state length was right, so `v.len()`
    /// was, but an index check reads the field, so `v.extend(0u8..3);
    /// assert!(v[0] == 0)` failed `index out of bounds` certified Genuine where
    /// Kani proves it (walker fail-closed review, round 1 of the repair after
    /// the merge with main; `range_extend_index_dual.rs`).
    fn write_range_extended_vec_fields(
        &mut self,
        coll_local: usize,
        step: RangeStep,
        range_start: &Expr,
        range_len: &Expr,
        modified_locals: &HashSet<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        use ay_bindings::ExprValue;

        let concrete_len = match range_len.value() {
            ExprValue::BitVecConst { value, .. } => u64::try_from(value).ok(),
            _ => None,
        };
        let exact_count = concrete_len.filter(|&n| match step {
            RangeStep::Char => n == 1,
            RangeStep::Signed(_) | RangeStep::Unsigned(_) => n <= MAX_APPEND_STORE_ELEMS,
        });
        let elements = match (exact_count, range_start.sort().bitvec_width()) {
            (Some(n), Some(width)) => AppendedElements::Range { start: range_start, width, n },
            _ => AppendedElements::Fresh(
                crate::codegen_ay::chc::codegen_ctx::sound_havoc::VEC_EXTEND_RANGE_ELEMENTS_UNMODELLED,
            ),
        };
        self.write_appended_vec_fields(
            coll_local,
            range_len,
            elements,
            "vec_extend_range_fields_unwritten",
            modified_locals,
            acc,
        );
    }

    /// Write a Vec's own fields after `count` elements were appended: `len`
    /// plus `count`, `cap` as `RawVec::grow_amortized` leaves it, and `data`
    /// per `elements` (`appended_data`). Both Vec representations (the
    /// projected scalar fields and the datatype).
    /// `unwritten` is recorded, fail-closed, when the fields cannot be read:
    /// left as they were they would be the OLD length, which an index check
    /// reads.
    pub(in crate::codegen_ay::chc) fn write_appended_vec_fields(
        &mut self,
        coll_local: usize,
        count: &Expr,
        elements: AppendedElements<'_>,
        unwritten: &'static str,
        modified_locals: &HashSet<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        use ay_bindings::ExprValue;

        // An empty append changes nothing.
        if matches!(count.value(), ExprValue::BitVecConst { value, .. } if *value == 0u8.into()) {
            return;
        }

        // Path 1: Projected (flattened scalar fields) — mirrors VecPush projected path.
        if self.collections.projection_locals.get(&coll_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let Some((ptr, old_fld_len, old_fld_cap, old_data)) =
                self.extract_projected_vec_fields(coll_local, modified_locals)
            else {
                self.record_sound_fallback_reason(unwritten);
                return;
            };
            if !old_data.sort().is_array() {
                self.record_sound_fallback_reason(unwritten);
                return;
            }
            let new_data = self.appended_data(old_data, &old_fld_len, count, elements);
            let new_fld_len = old_fld_len.bvadd(count.clone());
            let new_fld_cap = self.vec_reserved_cap(
                Some(self.body.locals()[coll_local].ty),
                &old_fld_cap,
                &new_fld_len,
                crate::codegen_ay::shared::vec_capacity::VecGrowth::Amortized,
                acc.constraints,
            );
            Self::emit_cap_ge_len(new_fld_cap.clone(), new_fld_len.clone(), acc.constraints);
            if !self.constrain_projected_vec_fields_for_call(
                coll_local,
                ProjectedVecState { ptr, len: new_fld_len, cap: new_fld_cap, data: new_data },
                acc.constraints,
                acc.dests,
            ) {
                self.record_sound_fallback_reason(unwritten);
                return;
            }
            debug!(coll_local, "appended Vec fields written via projected path");
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
                self.record_sound_fallback_reason(unwritten);
                return;
            }
            let new_data = self.appended_data(data, &len, count, elements);
            let new_len_field = len.bvadd(count.clone());
            let new_cap_field = self.vec_reserved_cap(
                Some(self.body.locals()[coll_local].ty),
                &cap,
                &new_len_field,
                crate::codegen_ay::shared::vec_capacity::VecGrowth::Amortized,
                acc.constraints,
            );

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
                debug!(coll_local, "appended Vec fields written via Datatype path");
            } else {
                self.record_sound_fallback_reason(unwritten);
            }
        }
    }

    /// `data` with `count` appended elements stored from `old_len` on.
    ///
    /// A range of a constant count stores its own values. Unknown values
    /// (`Fresh`) are a fresh array `F`'s, an identified sound havoc, and the
    /// old elements stay: for a constant count `n` up to
    /// [`MAX_APPEND_STORE_ELEMS`], `data[old_len + i] = F[i]` for `i < n`;
    /// for a symbolic or longer count, `F` itself. Round 1 made `data` a fresh
    /// array for every unknown append, so `vec![5, 6];
    /// v.extend_from_slice(&a); v[0] == 5` for a symbolic `a` failed closed
    /// where main and Kani prove it (walker fail-closed review, round 2 of the
    /// repair after the merge with main, `range_extend_index_dual.rs` `p`
    /// rows).
    fn appended_data(
        &mut self,
        data: Expr,
        old_len: &Expr,
        count: &Expr,
        elements: AppendedElements<'_>,
    ) -> Expr {
        use ay_bindings::ExprValue;
        let slot = |i: u64| old_len.clone().bvadd(Expr::bitvec_const(i, POINTER_WIDTH));
        let reason = match elements {
            AppendedElements::Range { start, width, n } => {
                let mut new_data = data;
                for i in 0..n {
                    let val = start.clone().bvadd(Expr::bitvec_const(i, width));
                    // Part of #4212: coerce range element to match data array sort.
                    let val = Self::coerce_store_value(new_data.sort(), val, false, &self.diagnostics);
                    new_data = new_data.store(slot(i), val);
                }
                return new_data;
            }
            AppendedElements::Fresh(reason) => reason,
        };
        let name = super::codegen_ctx::globals::chc_fresh_name("vec_appended_data");
        let fresh = crate::codegen_ay::chc::codegen_ctx::Havoc::mint(
            self,
            reason,
            name,
            data.sort().clone(),
        );
        let fresh_slots = |data: Expr, n: u64| {
            let mut new_data = data;
            for i in 0..n {
                let value = fresh.clone().select(Expr::bitvec_const(i, POINTER_WIDTH));
                new_data = new_data.store(slot(i), value);
            }
            new_data
        };
        match count.value() {
            ExprValue::BitVecConst { value, .. } => match u64::try_from(value) {
                Ok(n) if n <= MAX_APPEND_STORE_ELEMS => fresh_slots(data, n),
                _ => fresh,
            },
            // A symbolic count: the stores above at the old length on, under a
            // guard that the count fits, keep the old elements exactly, and
            // ay d80d17a90 timed out on every form of it (4, 8 and 16 slots;
            // the guard on the whole array or on its base). Unguarded, the
            // stores are sound only with a slot per element the count can
            // reach (256 for a `u8` range): the safe row proves, and the bug
            // rows time out at 64 and 256 slots (walker fail-closed review,
            // round 2, `q1_sym_append.rs`). The fresh array fails closed in a
            // second.
            _ => fresh,
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
    /// Mirrors [`Self::write_range_extended_vec_fields`] but takes concrete element VALUES —
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
            let new_fld_cap = self.vec_reserved_cap(
                Some(self.body.locals()[coll_local].ty),
                &old_fld_cap,
                &new_fld_len,
                crate::codegen_ay::shared::vec_capacity::VecGrowth::Amortized,
                acc.constraints,
            );
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
        let new_cap_field = self.vec_reserved_cap(
            Some(self.body.locals()[coll_local].ty),
            &cap,
            &new_len_field,
            crate::codegen_ay::shared::vec_capacity::VecGrowth::Amortized,
            acc.constraints,
        );
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
}
