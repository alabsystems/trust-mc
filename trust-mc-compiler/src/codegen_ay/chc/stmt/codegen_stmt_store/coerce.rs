// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Sort coercion for array store values.
//!
//! Part of #2244: array `.store()` calls in AY assert that the value sort
//! matches the element sort. When flattening changes local sorts, the value
//! passed to `.store()` may have the wrong BV width or Bool/BV mismatch.

mod option_store;

use ay_bindings::{Expr, Sort};
use tracing::warn;

use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::{
    SignExtension, coerce_bitvec_width_safe, flatten_datatype_to_bitvec,
};
use trust_mc_codegen_types::types::flattenable_datatype_sort_width;

use super::super::codegen_ctx::diagnostics::{CellCounter, ChcDiagnostics};
use super::super::{ChcCtx, chc_fresh_name, declare_pending_var};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Coerce a value to match an array's element sort before `.store()`.
    ///
    /// Returns the coerced value, or the original if sorts already match or
    /// coercion is not possible (the AY defense-in-depth will handle other cases).
    ///
    /// When the value is replaced with an unconstrained fresh symbolic (sort
    /// mismatch that can't be coerced), the store is still emitted with the
    /// symbolic value (sound over-approximation; Part of #3099).
    /// Part of #2976: `signed` controls whether BV widening uses sign-extend
    /// (true) or zero-extend (false). Callers should derive signedness from
    /// the source MIR type via `ty_signedness_shallow`.
    pub(in crate::codegen_ay::chc) fn coerce_store_value(
        arr_sort: &Sort,
        value: Expr,
        signed: bool,
        diagnostics: &ChcDiagnostics,
    ) -> Expr {
        if let Some(arr) = arr_sort.array_sort() {
            let elem_sort = &arr.element_sort;
            let val_sort = value.sort();
            if *val_sort == *elem_sort {
                return value;
            }
            // Part of #2894: Vec/String↔BitVec coercion via shared helper.
            if let Some(coerced) =
                crate::codegen_ay::store_coercion::coerce_vec_string_store_value(arr_sort, &value)
            {
                return coerced;
            }
            // BV width mismatch — Part of #2976: use caller-provided signedness
            if val_sort.is_bitvec()
                && elem_sort.is_bitvec()
                && let Some(target_width) = elem_sort.bitvec_width()
            {
                return coerce_bitvec_width_safe(
                    value,
                    target_width,
                    SignExtension::for_signedness(signed),
                );
            }
            // Bool → BV
            if val_sort.is_bool()
                && elem_sort.is_bitvec()
                && let Some(bits) = elem_sort.bitvec_width()
            {
                return Expr::ite(
                    value,
                    Expr::bitvec_const(1u64, bits),
                    Expr::bitvec_const(0u64, bits),
                );
            }
            // BV → Bool
            if val_sort.is_bitvec()
                && elem_sort.is_bool()
                && let Some(width) = val_sort.bitvec_width()
            {
                return value.ne(Expr::bitvec_const(0u64, width));
            }
            if let Some(unwrapped) =
                crate::codegen_ay::types::unwrap_single_field_datatype_to_sort(&value, elem_sort)
            {
                return unwrapped;
            }
            // Int → BV (Part of #2875: Int-lifted locals stored to BV arrays)
            if val_sort.is_int()
                && let Some(target_width) = elem_sort.bitvec_width()
            {
                return value.int2bv(target_width);
            }
            // BV → Int (Part of #2875: BV values stored to Int-sorted arrays)
            // Part of #3055: use signed/unsigned conversion based on source type.
            if val_sort.is_bitvec() && elem_sort.is_int() {
                return if signed { value.bv2int_signed() } else { value.bv2int() };
            }
            // Dyn_Trait DT → BV128 store coercion with correct fat-pointer field order.
            // Convention: [vtable:64 | data_ptr:64] (vtable upper, ptr lower).
            // Must intercept before general flatten which uses MSB-first field order.
            if val_sort.is_datatype()
                && elem_sort.is_bitvec()
                && let Some(target_width) = elem_sort.bitvec_width()
                && target_width == 2 * crate::codegen_ay::types::POINTER_WIDTH
                && let Some(dt) = val_sort.datatype_sort()
                && let Some(cons) = dt.constructors.first()
                && cons.fields.iter().any(|f| f.name == "fld_ptr")
                && cons.fields.iter().any(|f| f.name == "fld_vtable")
            {
                // Wave 4: declared roles (`fld_ptr` / `fld_vtable`) reported
                // to `PtrRepr` as `(Loc, Val)`, which owns the
                // `[vtable:upper | ptr:lower]` convention. The two operands are
                // same-sorted and adjacent, so a bare `concat` here is one
                // transposition away from storing the vtable id in the slot
                // every consumer reads as the data pointer.
                let data = Loc::of_address(value.clone().field_select(
                    &dt.name,
                    "fld_ptr",
                    ay_bindings::Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH),
                ));
                let meta = Val::of_value(value.clone().field_select(
                    &dt.name,
                    "fld_vtable",
                    ay_bindings::Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH),
                ));
                if let Some(packed) = PtrRepr::from_declared_roles(data, meta).into_packed() {
                    return packed;
                }
            }
            // Part of #2876, #2244: Datatype → BitVec flattening for nested structs.
            // When translate_ty encodes a struct as a Datatype but memory arrays
            // expect a flat BitVec, recursively extract leaf BV fields and concat.
            // This recovers store precision instead of substituting an unconstrained
            // symbolic, turning spurious CTREX into PROOF.
            if val_sort.is_datatype()
                && elem_sort.is_bitvec()
                && let Some(target_width) = elem_sort.bitvec_width()
                && let Some(flattened) = flatten_datatype_to_bitvec(&value, target_width)
            {
                return flattened;
            }
            // Part of #3984: Datatype wider than target — flatten to natural width,
            // then truncate. For IndexRange (2×BV64=BV128) stored to mem_u64 (BV64),
            // this preserves the low-order field rather than substituting a fully
            // unconstrained symbolic. Still an over-approximation (high bits lost),
            // but tighter than unconstrained. The per-field memory mirror
            // (mirror_aggregate_field_stores_to_memory) stores individual fields at
            // correct offsets for precise reads; this truncated store covers the
            // whole-value read path.
            //
            // Part of #3871 D3: For Dyn_Trait fat pointers (fld_ptr, fld_vtable),
            // extract fld_ptr (the data pointer) instead of the low bits (which
            // would be fld_vtable). Consumers loading from Box<dyn T> memory arrays
            // expect the data pointer, not the vtable discriminant. The vtable is
            // tracked separately via vtable state variables.
            if val_sort.is_datatype()
                && elem_sort.is_bitvec()
                && let Some(target_width) = elem_sort.bitvec_width()
                && let Some(natural_width) = flattenable_datatype_sort_width(&val_sort)
                && natural_width > target_width
            {
                if let Some(dt_name) = val_sort.datatype_name()
                    && dt_name.starts_with("Dyn_")
                    && target_width == 64
                {
                    let dt_name = dt_name.to_owned();
                    return value.field_select(&dt_name, "fld_ptr", ay_bindings::Sort::bitvec(64));
                }
                if let Some(full_bv) = flatten_datatype_to_bitvec(&value, natural_width) {
                    return coerce_bitvec_width_safe(
                        full_bv,
                        target_width,
                        SignExtension::for_signedness(signed),
                    );
                }
            }
            // Part of #3596: try layout-preserving reinterpretation before
            // falling to unconstrained symbolic. Handles Datatype(Array) → BV
            // (repr-SIMD structs) and Array element-width mismatches.
            if let Some(reinterpreted) = Self::reinterpret_fixed_layout_expr(&value, elem_sort) {
                return reinterpreted;
            }
            // StorageMarkers can introduce Option payload sorts that differ only
            // by CHC's zero-width array abstraction. Preserve the discriminant
            // instead of replacing the whole Option with a fresh symbolic.
            if let Some(coerced) =
                option_store::coerce_option_like_store_value(&value, elem_sort, signed)
            {
                return coerced;
            }
            // Datatype (or other incompatible sort) → target sort:
            // Substitute a fresh symbolic of the correct element sort.
            // This is a sound over-approximation: the store happens but the value
            // is unconstrained, which is strictly better than dropping the entire
            // store (which leaves the array with stale reads).
            // Part of #2244: prevents panics in ay_bindings store assertions.
            if val_sort.is_datatype() || (*val_sort != *elem_sort) {
                let sym_name = chc_fresh_name("__store_val");
                warn!(
                    expected_sort = ?elem_sort,
                    actual_sort = ?val_sort,
                    sym_name = %sym_name,
                    "CHC: coerce_store_value substituted fresh symbolic — \
                     value forgotten, replaced with unconstrained (Part of #2244, #2616)"
                );
                // Part of #3099: DO NOT increment store_dropped_transition here.
                // This path is a sound over-approximation: the store is emitted as
                // store(arr, addr, fresh_sym) where fresh_sym is universally quantified
                // in the CHC rule. The solver must prove the property for ALL possible
                // values of fresh_sym, which is strictly stronger than proving it for
                // the specific value. A PROOF under this encoding is always valid.
                // The previous .inc() call (#2616) was correct that *dropping* a store
                // entirely is unsound, but this path does NOT drop the store — it
                // substitutes an unconstrained value, which preserves soundness.
                //
                // Part of #2317: declare the fresh symbolic so Z3 doesn't report
                // "unknown constant __store_val_N".
                diagnostics.aggregate_encoding_gap.inc();
                return declare_pending_var(sym_name, elem_sort.clone());
            }
        }
        value
    }
}
