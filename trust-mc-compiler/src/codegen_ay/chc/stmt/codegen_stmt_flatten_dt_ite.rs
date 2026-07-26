// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Decompose ITE-merged Datatype expressions into scalar tag + payload values.
//!
//! Part of #3901: Extracted from `codegen_stmt_flatten_constrain.rs` for 500-LOC
//! compliance. Provides `decompose_datatype_for_flattened_dest` (method on ChcCtx)
//! and `decompose_dt_ite_to_scalars` (recursive ITE walker).

use ay_bindings::{Expr, Sort};
use tracing::debug;

use super::ChcCtx;

/// Per-constructor payload layout for a flattened enum destination.
///
/// FLATTEN_ITE_HETERO (VERIFY of char_validity gap): a flattened enum local lays
/// its constructor payloads out in one of two ways, and an ITE of constructors
/// must place each variant's leaves at the SAME slots the layout uses so the
/// reconstruction `ite(tag, Ctor_0(slots_0), Ctor_1(slots_1))` is bit-exact:
///
/// * **disjoint / concatenated** (heterogeneous `Result<T,E>` with `T != E`):
///   slots are `[tag, variant0_leaves.., variant1_leaves.., ..]`, so
///   `payload_slots == Σ leaf_count(variant_k)` and variant `k` starts at the
///   running sum of the earlier variants' leaf counts.
/// * **shared** (same-sort `Result<T,T>`, `Option<T>`): every variant reuses the
///   same payload slots, so `payload_slots == max_k leaf_count(variant_k)` and
///   every variant starts at offset 0.
struct PayloadLayout {
    /// Starting payload-slot offset for each constructor, indexed by ctor idx.
    ctor_offset: Vec<usize>,
    /// Bool-tag convention: `tag(ctor_idx) = (ctor_idx == true_variant)`.
    /// `None` preserves the legacy `ctor_idx == 1` convention (used only when the
    /// destination has no `flattened_enum_discr` entry, i.e. not Option/Result).
    true_variant: Option<u64>,
}

/// Number of scalar leaves a value of `sort` decomposes into, mirroring
/// `collect_leaf_exprs`: a single-constructor datatype expands into the leaves
/// of its fields; everything else (scalar, or a multi-constructor datatype) is a
/// single leaf. Used to compute per-variant payload offsets from the declared
/// constructor field sorts.
fn count_leaf_sorts(sort: &Sort) -> usize {
    if let Some(dt) = sort.datatype_sort()
        && dt.constructors.len() == 1
    {
        return dt.constructors[0].fields.iter().map(|f| count_leaf_sorts(&f.sort)).sum();
    }
    1
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Decompose a multi-constructor Datatype expression for a flattened destination.
    ///
    /// Part of #3901: When `build_enum_bv_destination_values` returns `None` (e.g.,
    /// because `enum_bv_layouts` doesn't contain the dest_local), this provides
    /// an alternative decomposition by recursively walking ITE branches to extract
    /// DatatypeConstructor arguments as scalars. Unlike `field_select` (which
    /// produces PDR-incompatible accessor terms), this builds pure scalar ITEs.
    pub(in crate::codegen_ay::chc) fn decompose_datatype_for_flattened_dest(
        &self,
        dest_local: usize,
        result_expr: &Expr,
    ) -> Option<Vec<Option<Expr>>> {
        let dt = result_expr.sort().datatype_sort()?;
        if dt.constructors.len() < 2 {
            return None; // Single-constructor handled by collect_leaf_exprs
        }

        let field_count = self.flatten.flattened_local_field_count.get(&dest_local).copied()?;
        if field_count < 2 {
            return None; // Need at least tag + 1 payload slot
        }
        let payload_slots = field_count - 1;

        // FLATTEN_ITE_HETERO: derive the per-variant slot layout from the declared
        // constructor field sorts so each variant's payload lands in its OWN slots
        // (disjoint layout) or a shared slot (shared layout). Without this, a
        // heterogeneous `Result` (Ok's char BV32 vs Err's Bool placeholder) would
        // collide both payloads at slot 0 and the ITE merge would bail on the sort
        // mismatch — falling back to a sound havoc (the char_validity gap).
        let layout = self.payload_layout_for_dest(dest_local, dt, payload_slots);

        // Recursively decompose the ITE tree into per-slot scalar values. When the
        // result is a literal constructor/ITE tree this yields pure scalar ITEs.
        // When it is an OPAQUE Datatype value (e.g. the `?`-operator residual
        // `Break_field_0(cf)` — a DatatypeSelector — or a bare Var), fall back to
        // decomposing via datatype ACCESSORS (tester + field selectors), which is
        // the exact semantic inverse of construction (no over-approximation).
        let (tag, payload) = match decompose_dt_ite_to_scalars(
            result_expr,
            dt,
            payload_slots,
            &layout,
        ) {
            Some(tp) => tp,
            None => self.decompose_datatype_via_accessors(result_expr, dt, payload_slots, &layout)?,
        };

        // Part of #3768: graceful fallback instead of panic
        let vec_idx = self.try_state_idx_for_local(dest_local)?;
        let mut values = Vec::with_capacity(field_count);

        // Coerce tag to output slot sort.
        let (_, tag_out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx)?;
        let tag_coerced = Self::coerce_flatten_slot_value(tag_out_sort, tag)?;
        values.push(Some(tag_coerced));

        for (i, slot_val) in payload.into_iter().enumerate() {
            if let Some(val) = slot_val {
                let (_, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx + 1 + i)?;
                let coerced = Self::coerce_flatten_slot_value(out_sort, val)?;
                values.push(Some(coerced));
            } else {
                values.push(None);
            }
        }

        debug!(
            dest_local,
            field_count,
            num_constructors = dt.constructors.len(),
            "decompose_datatype_for_flattened_dest: decomposed ITE tree to scalars (#3901)"
        );

        Some(values)
    }

    /// Compute the per-constructor payload layout (see [`PayloadLayout`]).
    ///
    /// Exactness: the offsets reproduce the slot layout `collect_result_local`
    /// (and the flatten decl helpers) declared for this local, so
    /// `ite(tag, Ctor_0(slots_0), Ctor_1(slots_1))` reconstructs the original
    /// datatype value bit-for-bit. If the declared `payload_slots` matches neither
    /// the disjoint nor the shared shape, fall back to the legacy all-zero offsets
    /// (identical to the prior behavior) so this change is a pure precision gain.
    fn payload_layout_for_dest(
        &self,
        dest_local: usize,
        dt: &ay_bindings::sort::DatatypeSort,
        payload_slots: usize,
    ) -> PayloadLayout {
        let leaf_counts: Vec<usize> = dt
            .constructors
            .iter()
            .map(|c| c.fields.iter().map(|f| count_leaf_sorts(&f.sort)).sum())
            .collect();
        let total: usize = leaf_counts.iter().sum();
        let max: usize = leaf_counts.iter().copied().max().unwrap_or(0);

        let ctor_offset = if payload_slots == total && total != max {
            // Disjoint / concatenated layout: variant k starts after the earlier
            // variants' leaves.
            let mut offsets = Vec::with_capacity(leaf_counts.len());
            let mut running = 0usize;
            for &c in &leaf_counts {
                offsets.push(running);
                running += c;
            }
            offsets
        } else {
            // Shared layout (payload_slots == max) OR an unrecognized layout: keep
            // every variant at offset 0 (the legacy placement). Unrecognized
            // layouts thus preserve the exact prior behavior.
            vec![0usize; leaf_counts.len()]
        };

        // Bool tag polarity comes from the declared enum discriminant so it agrees
        // with the aggregate-construction path (`Pattern 3`), which writes
        // `tag = (variant_idx == true_variant)`. Result → true_variant 0 (Ok=true);
        // Option → true_variant 1 (Some=true). Absent (non-enum flattened DT) keeps
        // the legacy `ctor_idx == 1` convention.
        let true_variant = self.flatten.flattened_enum_discr.get(&dest_local).map(|(t, _)| *t);

        PayloadLayout { ctor_offset, true_variant }
    }

    /// Decompose an OPAQUE 2-constructor Datatype value via datatype accessors.
    ///
    /// When `decompose_dt_ite_to_scalars` cannot walk the expression to literal
    /// constructor leaves (e.g. the value is a `DatatypeSelector` such as the
    /// `?`-operator residual `Break_field_0(cf)`, or a bare `Var`), we still know
    /// the value's declared datatype. The tag is the constructor tester and each
    /// payload slot is the corresponding field selector — the exact semantic
    /// inverse of construction, so this is SOUND (no over-approximation) and lets
    /// the flattened destination be constrained precisely instead of dropped.
    ///
    /// Restricted to:
    /// * **2-constructor** enums so the tag is a single Bool (matching the
    ///   `decompose_dt_ite_to_scalars` Bool-tag convention), and
    /// * **disjoint** payload layouts (each slot owned by exactly one variant), so
    ///   a field selector for the owning variant lands in its own slot and the
    ///   non-owning variant's slot is a genuine don't-care. Shared layouts
    ///   (`Option<T>`, `Result<T,T>`) return `None` and keep the prior sound
    ///   fallback, since a shared slot would need a tag-guarded `ite` of the two
    ///   variants' selectors.
    fn decompose_datatype_via_accessors(
        &self,
        result_expr: &Expr,
        dt: &ay_bindings::sort::DatatypeSort,
        payload_slots: usize,
        layout: &PayloadLayout,
    ) -> Option<(Expr, Vec<Option<Expr>>)> {
        if dt.constructors.len() != 2 {
            return None; // Bool-tag convention only.
        }
        // Disjoint layout only: distinct per-constructor offsets. A shared layout
        // (all offsets 0) is left to the sound fallback.
        if layout.ctor_offset.iter().all(|&o| o == layout.ctor_offset[0]) {
            return None;
        }

        // Tag = (value is the true-variant constructor). Matches the concrete-leaf
        // convention `tag = (ctor_idx == true_variant)`.
        let true_variant = layout.true_variant.unwrap_or(1) as usize;
        let true_ctor = dt.constructors.get(true_variant)?;
        let tag = result_expr
            .clone()
            .try_is_constructor(dt.name.clone(), true_ctor.name.clone())
            .ok()?;

        let mut payload: Vec<Option<Expr>> = vec![None; payload_slots];
        for (ctor_idx, ctor) in dt.constructors.iter().enumerate() {
            let base = *layout.ctor_offset.get(ctor_idx)?;
            let mut leaf_i = 0usize;
            for field in &ctor.fields {
                // Selecting a field of the non-owning variant yields an unspecified
                // value in SMT, but that slot is a don't-care (the tag selects the
                // variant), so this is exact for the reconstruction.
                let selected = result_expr
                    .clone()
                    .try_field_select(dt.name.clone(), field.name.clone(), field.sort.clone())
                    .ok()?;
                let mut leaves = Vec::new();
                super::codegen_stmt_flatten::collect_leaf_exprs(&selected, &mut leaves);
                for leaf in leaves {
                    let slot = base + leaf_i;
                    leaf_i += 1;
                    if slot >= payload_slots {
                        break;
                    }
                    if payload[slot].is_none() {
                        payload[slot] = leaf;
                    }
                }
            }
        }
        Some((tag, payload))
    }
}

/// Recursively decompose a Datatype ITE expression into scalar tag + payload values.
///
/// Part of #3901: Walks through nested ITE expressions where each leaf is a
/// DatatypeConstructor application. Produces:
/// - tag: Bool (for 2-constructor) or BV (for N-constructor) identifying the active variant
/// - payload: Vec of per-slot scalar values (None for unused slots)
///
/// Returns None if the expression cannot be decomposed (not an ITE of DatatypeConstructors).
fn decompose_dt_ite_to_scalars(
    expr: &Expr,
    dt: &ay_bindings::sort::DatatypeSort,
    payload_slots: usize,
    layout: &PayloadLayout,
) -> Option<(Expr, Vec<Option<Expr>>)> {
    use ay_bindings::ExprValue;

    match expr.value() {
        ExprValue::DatatypeConstructor { constructor_name, args, .. } => {
            // Leaf: a concrete constructor application.
            let ctor_idx = dt.constructors.iter().position(|c| c.name == *constructor_name)?;

            // Tag value. For 2-constructor enums the Bool polarity follows the
            // declared discriminant (`true_variant`); absent it, the legacy
            // `ctor_idx == 1` convention is preserved.
            let tag = if dt.constructors.len() == 2 {
                let true_variant = layout.true_variant.unwrap_or(1);
                Expr::bool_const(ctor_idx as u64 == true_variant)
            } else {
                Expr::bitvec_const(ctor_idx as u64, 8)
            };

            // Payload: extract constructor args into this variant's OWN slots (via
            // the layout offset), so a heterogeneous enum's variants do not collide.
            let base = *layout.ctor_offset.get(ctor_idx)?;
            let mut payload: Vec<Option<Expr>> = vec![None; payload_slots];
            let mut flat_args = Vec::new();
            for arg in args {
                super::codegen_stmt_flatten::collect_leaf_exprs(arg, &mut flat_args);
            }
            for (i, val) in flat_args.into_iter().enumerate() {
                let slot = base + i;
                if slot >= payload_slots {
                    break;
                }
                payload[slot] = val;
            }
            Some((tag, payload))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            // ITE: recursively decompose both branches, then merge at scalar level.
            let (then_tag, then_payload) =
                decompose_dt_ite_to_scalars(then_expr, dt, payload_slots, layout)?;
            let (else_tag, else_payload) =
                decompose_dt_ite_to_scalars(else_expr, dt, payload_slots, layout)?;

            let tag = Expr::ite(cond.clone(), then_tag, else_tag);

            let mut payload = Vec::with_capacity(payload_slots);
            for i in 0..payload_slots {
                let merged = match (&then_payload[i], &else_payload[i]) {
                    (Some(t), Some(e)) => {
                        // A slot shared by both branches (shared layout, or the same
                        // variant on both arms): merge with the branch condition.
                        // Differently-sorted leaves at the same slot mean the layout
                        // could not be resolved to disjoint slots; bail to the sound
                        // over-approximation path rather than build an ill-sorted ite.
                        if t.sort() != e.sort() {
                            return None;
                        }
                        Some(Expr::ite(cond.clone(), t.clone(), e.clone()))
                    }
                    // A slot owned by exactly one variant (disjoint layout): the
                    // discriminant selects that variant, so the other arm's value at
                    // this slot is a don't-care. Take the owning arm's value.
                    (Some(t), None) => Some(t.clone()),
                    (None, Some(e)) => Some(e.clone()),
                    (None, None) => None,
                };
                payload.push(merged);
            }
            Some((tag, payload))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn count_leaf_sorts_scalar_is_one() {
        assert_eq!(count_leaf_sorts(&Sort::bool()), 1);
        assert_eq!(count_leaf_sorts(&Sort::bitvec(32)), 1);
    }
}
