// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Constraint emission utilities for flattened tuple/enum/struct locals.
//!
//! Extracted from `codegen_stmt_flatten.rs` for 500-LOC compliance (Part of #3199, D3).
//! Provides `constrain_flattened_fields`, `constrain_flattened_pair`, and the core
//! constraint replacement logic used by both block-level and call-handler paths.

use ay_bindings::{Expr, Sort};
use std::collections::{HashMap, HashSet};
use tracing::{debug, warn};

use super::ChcCtx;
use super::codegen_call_coerce::{CallCoerce, coerce_eq_constraint};
use super::codegen_rules::CodegenRules;
use super::stmt_accumulator::{StmtAccumulator, replace_constraint_in};
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};
use trust_mc_core::chc::RelationApp;

enum RawEnumPayloadRecovery {
    Recovered(Vec<Option<Expr>>),
    Ambiguous,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Number of scalar state variables for a flattened local.
    pub(in crate::codegen_ay::chc) fn flattened_field_count(&self, local_idx: usize) -> usize {
        self.flatten.flattened_local_field_count.get(&local_idx).copied().unwrap_or(2)
    }

    /// Key used by `StmtAccumulator` for per-field replacement on flattened locals.
    pub(in crate::codegen_ay::chc) fn flattened_field_constraint_key(
        &self,
        local_idx: usize,
        field_idx: usize,
    ) -> usize {
        if field_idx == 0 { local_idx } else { local_idx + field_idx * self.body.locals().len() }
    }

    /// Constrain a flattened local's N scalar state vars.
    ///
    /// Emits `fldK_out == valK` constraints for each provided value,
    /// replacing any previous constraints for the same fields to avoid UNSAT
    /// from contradictory conjuncts in the same block.
    ///
    /// `values` contains `Option<Expr>` per field — `None` means the field is
    /// unconstrained (e.g., payload of `None` variant). Stale constraints for
    /// `None` fields are cleared.
    ///
    /// Returns `true` if at least one constraint was emitted.
    ///
    /// Part of #3517: accepts `StmtAccumulator` instead of raw triple.
    pub(in crate::codegen_ay::chc) fn constrain_flattened_fields(
        &mut self,
        local_idx: usize,
        values: &[Option<Expr>],
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let emitted = self.constrain_flattened_fields_core(
            local_idx,
            values,
            acc.constraints,
            acc.last_constraint_for_local,
        );
        acc.modified.insert(local_idx);
        emitted
    }

    /// Constrain flattened fields without modifying a `HashSet` (Part of #2267).
    ///
    /// Call-handler variant: callers use `extra_dests` instead of cloning
    /// `modified_locals` just for the `modified.insert(local_idx)` side effect.
    /// Eliminates one `HashSet<usize>` clone per call-handler invocation.
    ///
    /// Part of #3517: internalizes `last_constraint_for_local` — each field key
    /// within a single call is unique (`i * locals_len`), so no cross-call
    /// deduplication is needed. All callers previously created fresh HashMaps.
    pub(in crate::codegen_ay::chc) fn constrain_flattened_fields_for_call(
        &mut self,
        local_idx: usize,
        values: &[Option<Expr>],
        constraints: &mut Vec<Expr>,
    ) -> bool {
        let mut last_constraint_for_local = HashMap::new();
        self.constrain_flattened_fields_core(
            local_idx,
            values,
            constraints,
            &mut last_constraint_for_local,
        )
    }

    pub(in crate::codegen_ay::chc) fn coerce_flatten_slot_value(
        out_sort: &Sort,
        value: Expr,
    ) -> Option<Expr> {
        let value_sort = value.sort().clone();
        if value_sort == *out_sort {
            return Some(value);
        }
        if value_sort.is_bitvec() && out_sort.is_bitvec() {
            return Some(coerce_bitvec_width_safe(
                value,
                out_sort.bitvec_width()?,
                SignExtension::ZeroExtend,
            ));
        }
        if value_sort.is_bool() && out_sort.is_bitvec() {
            let width = out_sort.bitvec_width()?;
            return Some(Expr::ite(
                value,
                Expr::bitvec_const(1u64, width),
                Expr::bitvec_const(0u64, width),
            ));
        }
        if value_sort.is_bitvec() && out_sort.is_bool() {
            return Some(value.ne(Expr::bitvec_const(0u64, value_sort.bitvec_width()?)));
        }
        if value_sort.is_int() && out_sort.is_bitvec() {
            return Some(value.int2bv(out_sort.bitvec_width()?));
        }
        if value_sort.is_bitvec() && out_sort.is_int() {
            return Some(value.bv2int());
        }
        // Part of #4022: BV → Array reinterpretation for extracted BV payload
        // fragments in BV-flattened enums with Array-typed fields.
        if value_sort.is_bitvec() && out_sort.is_array() {
            return Self::reinterpret_fixed_layout_expr(&value, out_sort);
        }
        None
    }

    /// Build equality constraints for a flattened call destination.
    ///
    /// When the destination local is flattened (`flattened_tuple_locals`), decomposes
    /// `result_expr` into leaf values via `collect_leaf_exprs` and creates one equality
    /// constraint per state variable slot. Returns `Some(constraints)` if the destination
    /// was flattened and constraints were built, `None` if the destination is not flattened.
    ///
    /// Part of #3173: fixes under-constrained flattened destinations in closure
    /// and virtual call handlers, which previously only constrained fld0 via
    /// `resolve_destination`.
    pub(in crate::codegen_ay::chc) fn build_flattened_destination_constraints(
        &mut self,
        dest_local: usize,
        result_expr: Expr,
    ) -> Option<Vec<Expr>> {
        self.build_flattened_destination_field_constraints(dest_local, result_expr)
            .map(|constraints| constraints.into_iter().map(|(_, constraint)| constraint).collect())
    }

    pub(in crate::codegen_ay::chc) fn build_flattened_destination_field_constraints(
        &mut self,
        dest_local: usize,
        result_expr: Expr,
    ) -> Option<Vec<(usize, Expr)>> {
        if !self.flatten.flattened_tuple_locals.contains(&dest_local) {
            return None;
        }

        let leaf_values = if let Some(values) =
            self.build_enum_bv_destination_values(dest_local, &result_expr)
        {
            values
        } else if let Some(values) =
            self.build_enum_bv_bitvec_destination_values(dest_local, &result_expr)
        {
            // Part of #3994: inline-return reads of BV-flattened enums use
            // `reconstruct_flattened_bare_read()` which concatenates
            // tag/payload slots into a single BV. Split that BV back into
            // per-slot values before constraining the destination fields.
            values
        } else if let Some(values) =
            self.decompose_datatype_for_flattened_dest(dest_local, &result_expr)
        {
            // Part of #3901: Decompose multi-constructor Datatype ITE results
            // into scalar tag + payload via recursive ITE walker.
            values
        } else if let Some(recovery) =
            self.recover_enum_payload_from_raw_value(dest_local, &result_expr)
        {
            // Part of #4022: when a call handler returns the raw payload
            // (e.g., Array for [u8; 8]) instead of the enum wrapper,
            // recover the enum tag only when layout metadata proves the
            // payload belongs to a unique constructor. Otherwise emit a
            // sound fallback rather than misbinding the raw payload to fld0.
            match recovery {
                RawEnumPayloadRecovery::Recovered(values) => values,
                RawEnumPayloadRecovery::Ambiguous => {
                    warn!(
                        fn_name = %self.fn_name,
                        dest_local,
                        result_sort = ?result_expr.sort(),
                        "build_flattened_destination_constraints: ambiguous raw enum payload, sound fallback"
                    );
                    self.record_sound_fallback_reason("flatten_raw_enum_payload_ambiguous");
                    return Some(vec![(0, Expr::bool_const(true))]);
                }
            }
        } else {
            let mut leaf_values = Vec::new();
            super::codegen_stmt_flatten::collect_leaf_exprs(&result_expr, &mut leaf_values);
            leaf_values
        };

        // Part of #3768: graceful fallback instead of panic
        let vec_idx = self.try_state_idx_for_local(dest_local)?;
        let mut constraints = Vec::new();

        for (i, val_opt) in leaf_values.iter().enumerate() {
            if let Some(val) = val_opt {
                if let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(vec_idx + i).cloned()
                {
                    let out_var = Expr::var(&*out_name, out_sort.clone());
                    if let Some(eq) = coerce_eq_constraint(&out_var, val.clone(), &out_sort, false)
                    {
                        constraints.push((i, eq));
                        // Cache concrete value coerced to the state var's sort.
                        // Part of #4068: raw val may have a wider sort (e.g., BV128)
                        // than the state var (Bool). Without coercion, downstream
                        // reconstruct_flattened_bare_read sees the wrong sort and
                        // fails to reconstruct the local.
                        let cached = Self::coerce_flatten_slot_value(&out_sort, val.clone())
                            .unwrap_or_else(|| val.clone());
                        self.encode.flattened_field_env.insert((dest_local, i), cached);
                    } else if *val.sort() == out_sort {
                        // Part of #discriminant_128bits: Direct equality fallback.
                        // coerce_eq_constraint returned None despite matching sorts
                        // (observed for Bool==Bool in Option<NonZero<u128>>). Use
                        // direct Expr::eq as a belt-and-suspenders fix.
                        debug!(
                            fn_name = %self.fn_name,
                            dest_local,
                            field = i,
                            sort = ?out_sort,
                            "build_flattened_destination_constraints: \
                             coerce_eq_constraint returned None for matching sorts, using direct eq"
                        );
                        constraints.push((i, out_var.clone().eq(val.clone())));
                        self.encode.flattened_field_env.insert((dest_local, i), val.clone());
                    } else {
                        warn!(
                            fn_name = %self.fn_name,
                            dest_local,
                            field = i,
                            val_sort = ?val.sort(),
                            out_sort = ?out_sort,
                            "build_flattened_destination_constraints: sort mismatch, sound fallback"
                        );
                        constraints.push((i, Expr::bool_const(true)));
                        self.record_sound_fallback_reason("flatten_dest_sort_mismatch");
                    }
                }
            }
        }

        debug!(
            fn_name = %self.fn_name,
            dest_local,
            leaf_count = leaf_values.len(),
            constraint_count = constraints.len(),
            "build_flattened_destination_constraints: decomposed flattened call result (#3173)"
        );
        Some(constraints)
    }

    /// Recover enum slot values when a call handler returns the raw payload
    /// instead of the full enum wrapper.
    ///
    /// Safe recovery requires layout metadata proving that exactly one
    /// constructor owns the shared payload slot. This covers Option-like and
    /// unit-aware enum layouts while rejecting ambiguous same-sort Result-like
    /// layouts where a raw payload does not identify the variant.
    ///
    /// Part of #4022: fixes `flatten_dest_sort_mismatch` for Array-typed payloads
    /// (e.g., `[u8; 8]` encoded as `Array(BV64→BV8)`) where `collect_leaf_exprs`
    /// treats the Array as a single leaf misaligned against the Bool discriminant.
    fn recover_enum_payload_from_raw_value(
        &self,
        dest_local: usize,
        result_expr: &Expr,
    ) -> Option<RawEnumPayloadRecovery> {
        let field_count = self.flattened_field_count(dest_local);
        if field_count != 2 {
            return None;
        }
        let vec_idx = self.try_state_idx_for_local(dest_local)?;
        let (_, fld0_sort) = self.state_var_mgr.output_state_vars.get(vec_idx)?;
        let (_, fld1_sort) = self.state_var_mgr.output_state_vars.get(vec_idx + 1)?;

        // Field 0 must be Bool (discriminant) and result must match field 1 sort.
        if !fld0_sort.is_bool() {
            return None;
        }
        let result_sort = result_expr.sort();
        if *result_sort != *fld1_sort {
            return None;
        }

        let Some(layout) = self.flatten.enum_bv_layouts.get(&dest_local) else {
            return self
                .flatten
                .flattened_enum_discr
                .contains_key(&dest_local)
                .then_some(RawEnumPayloadRecovery::Ambiguous);
        };
        if layout.num_constructors != 2 || layout.max_payload_slots != 1 {
            return Some(RawEnumPayloadRecovery::Ambiguous);
        }

        let payload_ctors: Vec<usize> = layout
            .ctor_field_slot
            .iter()
            .enumerate()
            .filter_map(|(ctor_idx, field_slots)| {
                field_slots.iter().copied().any(|slot| slot == 0).then_some(ctor_idx)
            })
            .collect();
        let [payload_ctor] = payload_ctors.as_slice() else {
            return Some(RawEnumPayloadRecovery::Ambiguous);
        };
        let discr_expr = Expr::bool_const(*payload_ctor == 1);

        debug!(
            fn_name = %self.fn_name,
            dest_local,
            payload_ctor = *payload_ctor,
            result_sort = ?result_sort,
            "recover_enum_payload_from_raw_value: payload sort match with unique constructor"
        );
        Some(RawEnumPayloadRecovery::Recovered(vec![Some(discr_expr), Some(result_expr.clone())]))
    }

    /// Core implementation shared by block-level and call-handler variants.
    fn constrain_flattened_fields_core(
        &mut self,
        local_idx: usize,
        values: &[Option<Expr>],
        constraints: &mut Vec<Expr>,
        last_constraint_for_local: &mut HashMap<usize, usize>,
    ) -> bool {
        // Part of #3768: graceful fallback instead of panic
        let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
            return false;
        };
        let mut emitted = false;

        for (i, val_opt) in values.iter().enumerate() {
            let fld_key = self.flattened_field_constraint_key(local_idx, i);

            if let Some(val) = val_opt {
                if let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(vec_idx + i).cloned()
                {
                    let out_var = Expr::var(&*out_name, out_sort.clone());
                    if let Some(eq) = coerce_eq_constraint(&out_var, val.clone(), &out_sort, false)
                    {
                        replace_constraint_in(constraints, last_constraint_for_local, fld_key, eq);
                        // Cache the concrete value coerced to state var sort.
                        // Part of #4068: raw val may differ in sort from the
                        // state var. Coercing prevents downstream bare-read
                        // reconstruction from seeing the wrong sort.
                        // (Prior comment on tautology prevention: still applies —
                        // we cache the value, not the output var, to avoid
                        // tautologies on re-emission.)
                        let cached = Self::coerce_flatten_slot_value(&out_sort, val.clone())
                            .unwrap_or_else(|| val.clone());
                        self.encode.flattened_field_env.insert((local_idx, i), cached);
                        emitted = true;
                    } else {
                        warn!(
                            fn_name = %self.fn_name,
                            local_idx,
                            vec_idx,
                            field = i,
                            out_name = %out_name,
                            val_sort = ?val.sort(),
                            out_sort = ?out_sort,
                            "constrain_flattened_fields: sort mismatch, skipping field constraint"
                        );
                        replace_constraint_in(
                            constraints,
                            last_constraint_for_local,
                            fld_key,
                            Expr::bool_const(true),
                        );
                        self.record_sound_fallback_reason("flatten_field_sort_mismatch");
                    }
                } else {
                    warn!(
                        fn_name = %self.fn_name,
                        local_idx,
                        vec_idx,
                        field = i,
                        output_state_len = self.state_var_mgr.output_state_vars.len(),
                        "constrain_flattened_fields: missing output slot, skipping field constraint"
                    );
                    replace_constraint_in(
                        constraints,
                        last_constraint_for_local,
                        fld_key,
                        Expr::bool_const(true),
                    );
                    self.record_sound_fallback_reason("flatten_field_missing_output_slot");
                }
            } else {
                // Clear stale constraint for this field
                if let Some(&prev) = last_constraint_for_local.get(&fld_key) {
                    constraints[prev] = Expr::bool_const(true);
                }
            }
        }

        emitted
    }

    /// Constrain a flattened local's two scalar state vars (fld0, fld1).
    /// Convenience wrapper for 2-field enums/tuples.
    ///
    /// Part of #3517: accepts `StmtAccumulator` instead of raw triple.
    pub(in crate::codegen_ay::chc) fn constrain_flattened_pair(
        &mut self,
        local_idx: usize,
        val0: Expr,
        val1: Option<Expr>,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        self.constrain_flattened_fields(local_idx, &[Some(val0), val1], acc)
    }

    /// Shape a bool-valued flattened call field to the destination slot sort.
    ///
    /// Flattened Option/Result/tuple destinations sometimes encode their
    /// discriminant/flag slots as Bool, BV, or Int depending on the destination
    /// local's lowered shape. Call handlers use this helper before
    /// `emit_flattened_call_fields` when the semantic value is logically Bool.
    pub(in crate::codegen_ay::chc) fn reshape_flattened_bool_field_for_call(
        &self,
        dest_local: usize,
        field_idx: usize,
        value: Expr,
    ) -> Expr {
        // Part of #3768: graceful fallback instead of panic
        let Some(vec_idx) = self.try_state_idx_for_local(dest_local) else {
            return value;
        };
        let Some((_, out_sort)) = self.state_var_mgr.output_state_vars.get(vec_idx + field_idx)
        else {
            return value;
        };

        if out_sort.is_bool() {
            value
        } else if let Some(width) = out_sort.bitvec_width() {
            Expr::ite(value, Expr::bitvec_const(1u64, width), Expr::bitvec_const(0u64, width))
        } else if out_sort.is_int() {
            Expr::ite(value, Expr::int_const(1), Expr::int_const(0))
        } else {
            value
        }
    }

    /// Emit a flattened call result: constrain per-field values and emit goto rule.
    ///
    /// Checks if `dest_local` is flattened. If so, constrains each field using
    /// `constrain_flattened_fields_for_call` (which handles coercion, sound fallback,
    /// and `flattened_field_env` updates), builds output args, and emits a goto rule.
    ///
    /// Returns `true` if the destination was flattened and the rule was emitted.
    /// Returns `false` if the destination is not flattened (caller should use
    /// standard emission via `emit_stub_call_result` or similar).
    ///
    /// Part of #3631: centralizes the check-constrain-emit pattern that was previously
    /// hand-rolled in multiple call handlers (option_copied, checked_size_align,
    /// dyn_object model functions, etc.), each missing different aspects of the
    /// shared constraint protocol (flattened_field_env updates, sound_fallback
    /// recording, stale constraint clearing).
    pub(in crate::codegen_ay::chc) fn emit_flattened_call_fields(
        &mut self,
        dest_local: usize,
        field_values: &[Option<Expr>],
        from_app: &RelationApp,
        target: usize,
        modified_locals: &HashSet<usize>,
        stmt_constraints: &[Expr],
    ) -> bool {
        if !self.flatten.flattened_tuple_locals.contains(&dest_local) {
            return false;
        }
        let mut constraints = Vec::new();
        self.constrain_flattened_fields_for_call(dest_local, field_values, &mut constraints);
        let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            from_app,
            target,
            &new_output_args,
            stmt_constraints,
            constraints,
        );
        true
    }
}
