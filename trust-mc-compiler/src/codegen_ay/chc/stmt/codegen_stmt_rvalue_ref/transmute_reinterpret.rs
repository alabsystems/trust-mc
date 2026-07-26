// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Layout-sensitive transmute and fixed-layout reinterpretation helpers.
//!
//! Contains:
//! - `reinterpret_fixed_layout_expr`
//! - `transmute_requires_layout_fallback`

use ay_bindings::{Expr, Sort};
use rustc_public::ty::Ty;

use super::super::ChcCtx;
use crate::codegen_ay::types::{
    datatype_field_select, unwrap_single_field_datatype, unwrap_single_field_datatype_to_sort,
};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Part of #3457/#3596: layout-preserving reinterpretation for fixed layouts.
    ///
    /// Handles these cases for `CastKind::Transmute` and repr-SIMD array views:
    /// - **Array→same Array**: identity
    /// - **Datatype(single Array field)→Array**: extract the field
    /// - **Array→Datatype(single Array field)**: reconstruct the wrapper
    /// - **Array→BV**: `[u8; 4]` → `u32` — select each element and concat
    ///   (little-endian: element at index 0 is LSB).
    /// - **BV→Array**: `u32` → `[u8; 4]` — extract bit slices into array stores.
    ///
    /// Returns `None` if the sorts do not match one of the supported
    /// fixed-layout reinterpretation patterns.
    pub(in crate::codegen_ay::chc) fn reinterpret_fixed_layout_expr(
        src_expr: &Expr,
        target_sort: &Sort,
    ) -> Option<Expr> {
        if src_expr.sort() == target_sort {
            return Some(src_expr.clone());
        }

        if let Some(unwrapped) = unwrap_single_field_datatype_to_sort(src_expr, target_sort) {
            return Some(unwrapped);
        }

        if src_expr.sort().is_array()
            && let Some(target_dt) = target_sort.datatype_sort()
            && target_dt.constructors.len() == 1
            && target_dt.constructors[0].fields.len() == 1
        {
            let constructor = &target_dt.constructors[0];
            let field = &constructor.fields[0];
            if field.sort == *src_expr.sort() {
                return Some(Expr::datatype_constructor(
                    &*target_dt.name,
                    &*constructor.name,
                    vec![src_expr.clone()],
                    target_sort.clone(),
                ));
            }
        }

        // Case 1: Array(BV_idx, BV_elem) → BV(N)
        if let Some(arr_sort) = src_expr.sort().array_sort() {
            if let (Some(idx_width), Some(elem_width), Some(target_width)) = (
                arr_sort.index_sort.bitvec_width(),
                arr_sort.element_sort.bitvec_width(),
                target_sort.bitvec_width(),
            ) {
                if elem_width > 0 && target_width % elem_width == 0 {
                    let count = target_width / elem_width;
                    // Little-endian: byte[0] is LSB, byte[count-1] is MSB.
                    // Build BV by concatenating from MSB to LSB.
                    let mut result =
                        src_expr.clone().select(Expr::bitvec_const((count - 1) as u64, idx_width));
                    for i in (0..count - 1).rev() {
                        let elem = src_expr.clone().select(Expr::bitvec_const(i as u64, idx_width));
                        result = result.concat(elem);
                    }
                    return Some(result);
                }
            }
        }

        // Case 2: BV(N) → Array(BV_idx, BV_elem)
        if let Some(arr_sort) = target_sort.array_sort() {
            if let (Some(src_width), Some(idx_width), Some(elem_width)) = (
                src_expr.sort().bitvec_width(),
                arr_sort.index_sort.bitvec_width(),
                arr_sort.element_sort.bitvec_width(),
            ) {
                if elem_width > 0 && src_width % elem_width == 0 {
                    let count = src_width / elem_width;
                    // Start with a constant array of zeros, then store each
                    // extracted byte slice at its index.
                    let zero_elem = Expr::bitvec_const(0u64, elem_width);
                    let mut arr = Expr::const_array(Sort::bitvec(idx_width), zero_elem);
                    for i in 0..count {
                        let lo = i * elem_width;
                        let hi = lo + elem_width - 1;
                        let byte_val = src_expr.clone().extract(hi, lo);
                        let idx = Expr::bitvec_const(i as u64, idx_width);
                        arr = arr.store(idx, byte_val);
                    }
                    return Some(arr);
                }
            }
        }

        // Case 3: BV(N) → Datatype(multi-field struct) via bit extraction.
        // Part of #3252/#1351: transmute from flat BV to struct with BV fields.
        // E.g., BV32 → Pair { fst: BV16, snd: BV16 } extracts bit slices.
        // Little-endian: first field occupies the lowest bits.
        if let (Some(src_width), Some(target_dt)) =
            (src_expr.sort().bitvec_width(), target_sort.datatype_sort())
        {
            if target_dt.constructors.len() == 1 {
                let constructor = &target_dt.constructors[0];
                let all_bv = constructor.fields.iter().all(|f| f.sort.bitvec_width().is_some());
                if all_bv && !constructor.fields.is_empty() {
                    let total_field_bits: u32 = constructor
                        .fields
                        .iter()
                        .map(|f| f.sort.bitvec_width().expect("invariant: all_bv guard"))
                        .sum();
                    if total_field_bits <= src_width {
                        let mut field_exprs = Vec::with_capacity(constructor.fields.len());
                        let mut bit_offset: u32 = 0;
                        for field in &constructor.fields {
                            let fw = field.sort.bitvec_width().expect("invariant: all_bv guard");
                            let val = src_expr.clone().extract(bit_offset + fw - 1, bit_offset);
                            field_exprs.push(val);
                            bit_offset += fw;
                        }
                        return Some(Expr::datatype_constructor(
                            &*target_dt.name,
                            &*constructor.name,
                            field_exprs,
                            target_sort.clone(),
                        ));
                    }
                }
            }
        }

        // Case 4: Array(BV_idx, BV_elem) → Datatype(multi-field struct) via BV.
        // Part of #3252: transmute from byte array to struct. E.g.,
        // [u8; 4] → Pair { fst: u16, snd: u16 }.
        // Chain: concat array elements to flat BV, then extract fields.
        if let (Some(arr_sort), Some(target_dt)) =
            (src_expr.sort().array_sort(), target_sort.datatype_sort())
        {
            if let (Some(idx_width), Some(elem_width)) =
                (arr_sort.index_sort.bitvec_width(), arr_sort.element_sort.bitvec_width())
            {
                if target_dt.constructors.len() == 1 && elem_width > 0 {
                    let constructor = &target_dt.constructors[0];
                    let all_bv = constructor.fields.iter().all(|f| f.sort.bitvec_width().is_some());
                    if all_bv && !constructor.fields.is_empty() {
                        let total_field_bits: u32 = constructor
                            .fields
                            .iter()
                            .map(|f| f.sort.bitvec_width().expect("invariant: all_bv guard"))
                            .sum();
                        if total_field_bits % elem_width == 0 {
                            let count = total_field_bits / elem_width;
                            // Little-endian concat: byte[count-1] :: ... :: byte[0]
                            let mut flat_bv = src_expr
                                .clone()
                                .select(Expr::bitvec_const((count - 1) as u64, idx_width));
                            for i in (0..count - 1).rev() {
                                let elem = src_expr
                                    .clone()
                                    .select(Expr::bitvec_const(i as u64, idx_width));
                                flat_bv = flat_bv.concat(elem);
                            }
                            // Extract fields from flat BV (reuse Case 3 logic).
                            let mut field_exprs = Vec::with_capacity(constructor.fields.len());
                            let mut bit_offset: u32 = 0;
                            for field in &constructor.fields {
                                let fw =
                                    field.sort.bitvec_width().expect("invariant: all_bv guard");
                                let val = flat_bv.clone().extract(bit_offset + fw - 1, bit_offset);
                                field_exprs.push(val);
                                bit_offset += fw;
                            }
                            return Some(Expr::datatype_constructor(
                                &*target_dt.name,
                                &*constructor.name,
                                field_exprs,
                                target_sort.clone(),
                            ));
                        }
                    }
                }
            }
        }

        // Case 6: Datatype(multi-field struct) → BV(N) via field extraction + concat.
        // Reverse of Case 3. E.g., Pair { fst: BV16, snd: BV16 } → BV32.
        // Little-endian: first field occupies the lowest bits, last field MSB.
        if let (Some(src_dt), Some(target_width)) =
            (src_expr.sort().datatype_sort(), target_sort.bitvec_width())
        {
            if src_dt.constructors.len() == 1 {
                let constructor = &src_dt.constructors[0];
                let all_bv = constructor.fields.iter().all(|f| f.sort.bitvec_width().is_some());
                if all_bv && !constructor.fields.is_empty() {
                    let total_field_bits: u32 = constructor
                        .fields
                        .iter()
                        .map(|f| f.sort.bitvec_width().expect("invariant: all_bv guard"))
                        .sum();
                    if total_field_bits <= target_width {
                        // Extract fields and concat: last field is MSB, first field is LSB.
                        let n = constructor.fields.len();
                        let last_field = datatype_field_select(src_expr.clone(), 0, n - 1)
                            .expect("field exists");
                        let mut result = last_field;
                        for i in (0..n - 1).rev() {
                            let field = datatype_field_select(src_expr.clone(), 0, i)
                                .expect("field exists");
                            result = result.concat(field);
                        }
                        // Zero-pad if total field bits < target width (alignment padding).
                        if total_field_bits < target_width {
                            let pad_width = target_width - total_field_bits;
                            result = Expr::bitvec_const(0u64, pad_width).concat(result);
                        }
                        return Some(result);
                    }
                }
            }
        }

        // Case 7: Datatype(multi-field struct) → Array(BV_idx, BV_elem) via BV.
        // Reverse of Case 4. Chain: flatten Datatype to BV (Case 6), then split
        // into array elements (Case 2). E.g., Pair { fst: u16, snd: u16 } → [u8; 4].
        if let (Some(src_dt), Some(arr_sort)) =
            (src_expr.sort().datatype_sort(), target_sort.array_sort())
        {
            if let (Some(idx_width), Some(elem_width)) =
                (arr_sort.index_sort.bitvec_width(), arr_sort.element_sort.bitvec_width())
            {
                if src_dt.constructors.len() == 1 && elem_width > 0 {
                    let constructor = &src_dt.constructors[0];
                    let all_bv = constructor.fields.iter().all(|f| f.sort.bitvec_width().is_some());
                    if all_bv && !constructor.fields.is_empty() {
                        let total_field_bits: u32 = constructor
                            .fields
                            .iter()
                            .map(|f| f.sort.bitvec_width().expect("invariant: all_bv guard"))
                            .sum();
                        if total_field_bits % elem_width == 0 {
                            // First flatten to BV (Case 6 logic).
                            let n = constructor.fields.len();
                            let last_field = datatype_field_select(src_expr.clone(), 0, n - 1)
                                .expect("field exists");
                            let mut flat_bv = last_field;
                            for i in (0..n - 1).rev() {
                                let field = datatype_field_select(src_expr.clone(), 0, i)
                                    .expect("field exists");
                                flat_bv = flat_bv.concat(field);
                            }
                            // Then split BV into array elements (Case 2 logic).
                            let count = total_field_bits / elem_width;
                            let zero_elem = Expr::bitvec_const(0u64, elem_width);
                            let mut arr = Expr::const_array(Sort::bitvec(idx_width), zero_elem);
                            for i in 0..count {
                                let lo = i * elem_width;
                                let hi = lo + elem_width - 1;
                                let byte_val = flat_bv.clone().extract(hi, lo);
                                let idx = Expr::bitvec_const(i as u64, idx_width);
                                arr = arr.store(idx, byte_val);
                            }
                            return Some(arr);
                        }
                    }
                }
            }
        }

        // Case 8: Datatype(mixed BV+Array+Bool fields) → BV(N).
        // Part of #2244/#2616: handles structs like Pair<[u8; 5], [u16; 3]> where
        // Array-sorted fields represent fixed-size inline arrays and Bool-sorted
        // fields represent ZST arrays (e.g. [(); N]). Only handles the
        // single-Array-field case where element count is unambiguous from the
        // target width budget. Multi-Array-field cases require Rust type info
        // not available at this layer.
        if let (Some(src_dt), Some(target_width)) =
            (src_expr.sort().datatype_sort(), target_sort.bitvec_width())
        {
            if src_dt.constructors.len() == 1 {
                let constructor = &src_dt.constructors[0];
                let has_array = constructor.fields.iter().any(|f| f.sort.is_array());
                let all_supported = constructor.fields.iter().all(|f| {
                    f.sort.bitvec_width().is_some() || f.sort.is_array() || f.sort.is_bool()
                });
                if has_array && all_supported && !constructor.fields.is_empty() {
                    let array_fields: Vec<_> = constructor
                        .fields
                        .iter()
                        .enumerate()
                        .filter(|(_, f)| f.sort.is_array())
                        .collect();
                    // Only handle single-Array-field case (element count unambiguous).
                    if array_fields.len() == 1 {
                        // Compute BV budget: total of BV fields + Bool→BV8 or Bool→0.
                        // Try with Bool=8 first (normal encoding), fall back to Bool=0.
                        let bv_total_with_bool: u32 = constructor
                            .fields
                            .iter()
                            .map(|f| {
                                if let Some(w) = f.sort.bitvec_width() {
                                    w
                                } else if f.sort.is_bool() {
                                    8u32
                                } else {
                                    0u32
                                }
                            })
                            .sum();
                        let bv_total_skip_bool: u32 = constructor
                            .fields
                            .iter()
                            .map(|f| f.sort.bitvec_width().unwrap_or(0))
                            .sum();
                        let (bv_total, bool_as_bv8) = if bv_total_with_bool <= target_width {
                            (bv_total_with_bool, true)
                        } else if bv_total_skip_bool <= target_width {
                            (bv_total_skip_bool, false)
                        } else {
                            // BV fields alone exceed target — cannot flatten.
                            (0, false)
                        };
                        if bv_total > 0 && target_width >= bv_total {
                            let (arr_idx, arr_field) = array_fields[0];
                            if let Some(arr_sort) = arr_field.sort.array_sort() {
                                if let (Some(idx_width), Some(elem_width)) = (
                                    arr_sort.index_sort.bitvec_width(),
                                    arr_sort.element_sort.bitvec_width(),
                                ) {
                                    let array_budget = target_width - bv_total;
                                    // Try exact fit first, then search with padding.
                                    let elem_count =
                                        if elem_width > 0 && array_budget % elem_width == 0 {
                                            Some(array_budget / elem_width)
                                        } else if elem_width > 0 && array_budget > 0 {
                                            // Search for element count with alignment padding.
                                            let max_count = array_budget / elem_width;
                                            (1..=max_count)
                                                .rev()
                                                .find(|c| c * elem_width <= array_budget)
                                        } else {
                                            None
                                        };
                                    if let Some(count) = elem_count {
                                        // Build per-field BV expressions.
                                        let n = constructor.fields.len();
                                        let mut field_bvs: Vec<Expr> = Vec::with_capacity(n);
                                        for (fi, field) in constructor.fields.iter().enumerate() {
                                            let field_expr =
                                                datatype_field_select(src_expr.clone(), 0, fi)
                                                    .expect("field exists");
                                            if fi == arr_idx {
                                                // Array→BV: concat elements little-endian.
                                                if count == 0 {
                                                    continue;
                                                }
                                                let mut arr_bv =
                                                    field_expr.clone().select(Expr::bitvec_const(
                                                        (count - 1) as u64,
                                                        idx_width,
                                                    ));
                                                for i in (0..count - 1).rev() {
                                                    let elem = field_expr.clone().select(
                                                        Expr::bitvec_const(i as u64, idx_width),
                                                    );
                                                    arr_bv = arr_bv.concat(elem);
                                                }
                                                field_bvs.push(arr_bv);
                                            } else if field.sort.is_bool() {
                                                if bool_as_bv8 {
                                                    let bv_expr = Expr::ite(
                                                        field_expr,
                                                        Expr::bitvec_const(1u64, 8),
                                                        Expr::bitvec_const(0u64, 8),
                                                    );
                                                    field_bvs.push(bv_expr);
                                                }
                                                // else: skip Bool (0 bits)
                                            } else if let Some(_w) = field.sort.bitvec_width() {
                                                field_bvs.push(field_expr);
                                            }
                                        }
                                        if !field_bvs.is_empty() {
                                            // Concat: last=MSB, first=LSB.
                                            let last = field_bvs.len() - 1;
                                            let mut result = field_bvs[last].clone();
                                            for i in (0..last).rev() {
                                                result = result.concat(field_bvs[i].clone());
                                            }
                                            // Zero-pad to target width.
                                            let result_width: u32 = field_bvs
                                                .iter()
                                                .map(|e| e.sort().bitvec_width().unwrap_or(0))
                                                .sum();
                                            if result_width < target_width {
                                                let pad = target_width - result_width;
                                                result =
                                                    Expr::bitvec_const(0u64, pad).concat(result);
                                            }
                                            return Some(result);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Case 5: Transitive — Datatype(single field) → target via unwrap + recurse.
        // Part of #3596: repr-SIMD structs are Datatype(Array) but memory arrays
        // expect flat BV. Unwrap the Datatype to get the inner field, then apply
        // the appropriate reinterpretation (e.g., Array→BV concat for Case 1).
        // This handles CustomSimd([u8; 10]) → BV(80).
        if let Some(unwrapped) = unwrap_single_field_datatype(src_expr) {
            if let Some(result) = Self::reinterpret_fixed_layout_expr(&unwrapped, target_sort) {
                return Some(result);
            }
        }

        None
    }

    /// Part of #3808/#3809: multi-field cross-ADT transmutes need rustc layout parity.
    ///
    /// Delegates to the shared helper in `shared::transmute_layout` so that
    /// CHC and BMC use the same layout-compatibility contract.
    pub(super) fn transmute_requires_layout_fallback(
        &self,
        src_ty: Ty,
        target_ty: Ty,
        src_sort: &Sort,
        target_sort: &Sort,
    ) -> bool {
        crate::codegen_ay::shared::transmute_layout::transmute_requires_layout_fallback(
            src_ty,
            target_ty,
            src_sort,
            target_sort,
            |ty| self.resolve_body_ty(ty),
        )
    }
}
