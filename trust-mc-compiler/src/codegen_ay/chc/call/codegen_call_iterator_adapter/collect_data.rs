// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! IterCollect data constraint builders for iterator adapter chains.
//!
//! Extracted from `codegen_call_iterator_adapter_helpers.rs` per 500 LOC threshold.
//! Moved into directory module per #4129.
//!
//! Contains:
//! - `try_translate_iter_map_closure`: resolve IterMap closure body to AY expression
//! - `try_constrain_iter_collect_data`: build data constraints at collect
//!
//! Part of #3348: IterCollect closure body analysis for transform chains.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::{ClosureKind, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::names::struct_sort;
use crate::codegen_ay::types::ptr_sort;

use super::super::codegen_ctx::types::ClosureTemplate;
use super::super::inline_body::translate_closure_inline_body;
use super::super::stubs_option_helpers::OptionHelpers;
use super::super::{ChcCtx, chc_fresh_name, declare_pending_var};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Try to translate an IterMap closure body into a AY expression template.
    ///
    /// Resolves the closure from `args[1]` (the map function argument),
    /// translates its body with `select(src_data[i], idx)` as element parameters,
    /// and returns a `ClosureTemplate` with the shared index variable.
    ///
    /// Handles:
    /// - Single-source chains: closure takes one element → `select(src[0], idx)`
    /// - Zip chains: closure takes a tuple → `Tuple(select(src[0], idx), select(src[1], idx))`
    ///
    /// Returns `None` if closure resolution or body translation fails (falls back
    /// to fully symbolic data at IterCollect).
    ///
    /// Part of #3348: IterCollect closure body analysis for transform chains.
    pub(in crate::codegen_ay::chc) fn try_translate_iter_map_closure(
        &mut self,
        args: &[Operand],
        source_data_arrays: &[Expr],
    ) -> Option<ClosureTemplate> {
        let closure_arg = args.get(1)?;

        // Resolve the closure type from the operand.
        let closure_ty = closure_arg.ty(self.body.locals()).ok()?;
        let (def, closure_args) = match closure_ty.kind() {
            TyKind::RigidTy(RigidTy::Closure(def, args)) => (def, args),
            _ => {
                debug!("iter_map_closure: arg[1] is not a Closure type");
                return None;
            }
        };

        // Resolve the closure Instance and get its MIR body.
        let mut closure_body = None;
        for kind in [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce] {
            if let Ok(instance) = Instance::resolve_closure(def, &closure_args, kind)
                && let Some(body) = instance.body()
            {
                closure_body = Some(body);
                break;
            }
        }
        let closure_body = closure_body?;

        // Create a shared index variable for array select operations.
        let idx_var_name = chc_fresh_name("iter_map_idx");
        let idx = Expr::var(idx_var_name.clone(), ptr_sort());

        // Build element expressions: select(src_data[i], idx) for each source array.
        let elem_sorts: Vec<Sort> = source_data_arrays
            .iter()
            .filter_map(|arr| arr.sort().array_sort().map(|a| a.element_sort.clone()))
            .collect();

        if elem_sorts.len() != source_data_arrays.len() {
            debug!("iter_map_closure: could not determine element sorts for all source arrays");
            return None;
        }

        let element_selects: Vec<Expr> =
            source_data_arrays.iter().map(|arr| arr.clone().select(idx.clone())).collect();

        // Build the closure parameter expression.
        // Single-source: pass element directly as the parameter.
        // Multi-source (zip): construct a tuple Datatype for the closure parameter.
        let param = if element_selects.len() == 1 {
            element_selects[0].clone()
        } else {
            // Build a tuple sort: Tuple(fld_0: ElemSort0, fld_1: ElemSort1, ...)
            let fields: Vec<(String, Sort)> = elem_sorts
                .iter()
                .enumerate()
                .map(|(i, s)| (format!("fld_{i}"), s.clone()))
                .collect();
            let tuple_name = format!(
                "IterMapTuple_{}",
                elem_sorts.iter().map(sort_short_label).collect::<Vec<_>>().join("_")
            );
            let tuple_sort = struct_sort(tuple_name.clone(), fields);
            let ctor_name = format!("mk_{tuple_name}");
            Expr::datatype_constructor(&tuple_name, &ctor_name, element_selects, tuple_sort)
        };

        // Translate the closure body with the parameterized element(s).
        // No captures for now — handles the bv_bitblast patterns where closures
        // are pure (|(&a, &b)| a ^ b, |&b| !b).
        let captures: Vec<Expr> = Vec::new();
        let body_expr = translate_closure_inline_body(
            self,
            &closure_body,
            std::slice::from_ref(&param),
            &captures,
            0, // bb_idx placeholder — used only for debug logging
            0, // inline_depth: top-level dispatch
        )?;

        debug!(
            idx_var = %idx_var_name,
            num_sources = source_data_arrays.len(),
            body_sort = %body_expr.sort(),
            "iter_map_closure: translated closure body to AY expression (#3348)"
        );

        Some(ClosureTemplate { idx_var_name, body_expr })
    }

    /// Build the data array expression for IterCollect, using adapter source data
    /// when available to constrain the result precisely.
    ///
    /// Returns the data expression to use for the result Vec. Three cases:
    /// - **Identity chain at position zero**: returns source data directly.
    /// - **Transform chain** (has closure template): symbolic data — PDR cannot handle
    ///   forall quantifiers in CHC rules, so element values are unconstrained (sound).
    ///   Length is precisely constrained by the caller.
    /// - **Fallback**: unconstrained symbolic data + sound fallback counter.
    ///
    /// Part of #3348: IterCollect data constraints.
    pub(in crate::codegen_ay::chc) fn try_constrain_iter_collect_data(
        &mut self,
        dest_local: usize,
        data_sort: &Sort,
        _remaining_len: &Expr,
        adapter_src: Option<&super::super::codegen_ctx::types::AdapterSourceData>,
        iterator_at_start: bool,
        _extra_constraints: &mut Vec<Expr>,
    ) -> Expr {
        // Case 1: Identity chain at position zero — copy source data directly.
        if let Some(src) = adapter_src {
            if iterator_at_start && !src.has_transform && src.data_arrays.len() == 1 {
                let source_data = &src.data_arrays[0];
                if *source_data.sort() == *data_sort {
                    debug!(
                        dest_local,
                        "IterCollect: identity chain — using source data directly (#3348)"
                    );
                    return source_data.clone();
                }
            }
        }

        // Case 2: Concrete element replay — build exact data array from
        // pre-evaluated final output elements (e.g., filter_map(parse().ok())).
        // Part of #3692: concrete filter_map replay for parse.rs PROOF.
        if let Some(src) = adapter_src {
            if iterator_at_start
                && !src.has_transform
                && let Some(ref elems) = src.concrete_elems
            {
                if let Some(arr_sort) = data_sort.array_sort() {
                    let elem_sort = arr_sort.element_sort.clone();
                    let idx_sort = arr_sort.index_sort.clone();
                    let base = Expr::const_array(
                        idx_sort,
                        declare_pending_var(
                            format!("iter_collect_default_{dest_local}"),
                            elem_sort.clone(),
                        ),
                    );
                    let data = elems.iter().enumerate().fold(base, |arr, (i, elem)| {
                        let idx =
                            Expr::bitvec_const(i as u128, crate::codegen_ay::types::POINTER_WIDTH);
                        let coerced = self
                            .coerce_value_to_sort(elem.clone(), &elem_sort, true)
                            .unwrap_or_else(|| elem.clone());
                        arr.store(idx, coerced)
                    });
                    debug!(
                        dest_local,
                        num_elems = elems.len(),
                        "IterCollect: concrete element replay — exact data array (#3692)"
                    );
                    return data;
                }
            }
        }

        // Case 3: Transform chain with closure template.
        // PDR (CHC solver) cannot handle forall quantifiers in CHC rules —
        // the quantified element-wise constraint blocks invariant synthesis.
        // Use symbolic data (sound over-approximation): length is precisely
        // constrained by the caller, element values are unconstrained.
        // Part of #3348: forall blocks PDR proof (confirmed experimentally).
        if let Some(src) = adapter_src {
            if src.closure_template.is_some() {
                debug!(
                    dest_local,
                    "IterCollect: transform chain — symbolic data (forall blocks PDR) (#3348)"
                );
                return declare_pending_var(
                    format!("iter_collect_data_{dest_local}"),
                    data_sort.clone(),
                );
            }
        }

        // Case 3: Fallback — unconstrained symbolic data.
        self.record_sound_fallback_reason("iter_collect_symbolic_fallback");
        declare_pending_var(format!("iter_collect_data_{dest_local}"), data_sort.clone())
    }

    /// Try to extract concrete element values from a AY store-chain array.
    ///
    /// Walks the `store(store(..., idx, val), idx, val)` chain to extract
    /// `count` elements at consecutive indices 0..count. Returns `None` if
    /// any element is missing or indices are non-concrete.
    ///
    /// Part of #3692: concrete filter_map replay infrastructure.
    pub(in crate::codegen_ay::chc) fn try_extract_store_chain_elements(
        array: &Expr,
        count: usize,
    ) -> Option<Vec<Expr>> {
        use ay_bindings::ExprValue;
        let mut elements: Vec<Option<Expr>> = vec![None; count];
        let mut current = array;
        loop {
            match current.value() {
                ExprValue::Store { array, index, value } => {
                    if let ExprValue::BitVecConst { value: idx_val, .. } = index.value() {
                        if let Ok(idx) = usize::try_from(idx_val.clone()) {
                            if idx < count {
                                elements[idx] = Some(value.clone());
                            }
                        }
                    }
                    current = array;
                }
                ExprValue::ConstArray { .. } | ExprValue::Var { .. } => break,
                _ => return None,
            }
        }
        elements.into_iter().collect()
    }

    /// Count the depth of a store-chain array expression.
    ///
    /// Returns the number of `store()` operations wrapping a base
    /// `const_array`/`var`. Used as a fallback to determine element count
    /// when `remaining_len` is symbolic (e.g., `ite(len >= pos, len - pos, 0)`).
    ///
    /// Part of #3189: concrete replay with symbolic remaining_len.
    pub(in crate::codegen_ay::chc) fn count_store_chain_depth(array: &Expr) -> Option<usize> {
        use ay_bindings::ExprValue;
        let mut depth = 0usize;
        let mut current = array;
        loop {
            match current.value() {
                ExprValue::Store { array, .. } => {
                    depth += 1;
                    current = array;
                }
                ExprValue::ConstArray { .. } | ExprValue::Var { .. } => {
                    return if depth > 0 { Some(depth) } else { None };
                }
                _ => return None,
            }
        }
    }

    /// Try to extract concrete UTF-8 string content from a AY expression
    /// representing an &str (Slice_bv8 Datatype or a byte-backing array).
    ///
    /// Walks the fld_data store chain to extract concrete BV8 byte values,
    /// then converts to a Rust String. Returns `None` if any byte is
    /// non-concrete or the result is not valid UTF-8.
    ///
    /// Part of #3692: concrete IntParse evaluation.
    pub(in crate::codegen_ay::chc) fn try_extract_str_from_expr(elem: &Expr) -> Option<String> {
        use ay_bindings::ExprValue;

        // Try Datatype path: Slice_bv8(fld_ptr, fld_len, fld_data)
        if let Some(dt_name) = elem.sort().datatype_name() {
            let len_sort = Self::get_dt_field_sort(elem, "fld_len")?;
            let len_expr = elem.clone().field_select(dt_name, "fld_len", len_sort);
            let len = match len_expr.value() {
                ExprValue::BitVecConst { value, .. } => usize::try_from(value.clone()).ok()?,
                _ => return None,
            };
            if len > 256 {
                return None; // Safety limit
            }
            let data_sort = Self::get_dt_field_sort(elem, "fld_data")?;
            let data = elem.clone().field_select(dt_name, "fld_data", data_sort);
            return Self::try_extract_bytes_from_store_chain(&data, len);
        }

        // Try direct array path
        if elem.sort().array_sort().is_some() {
            // Need a length hint — can't determine from array alone
            return None;
        }

        None
    }

    /// Extract concrete bytes from a AY array store chain.
    ///
    /// Walks `store(store(const, 0, b0), 1, b1)` to get bytes [b0, b1, ...].
    fn try_extract_bytes_from_store_chain(data: &Expr, len: usize) -> Option<String> {
        use ay_bindings::ExprValue;
        let mut bytes = vec![0u8; len];
        let mut found = vec![false; len];
        let mut current = data;
        loop {
            match current.value() {
                ExprValue::Store { array, index, value } => {
                    if let ExprValue::BitVecConst { value: idx_val, .. } = index.value()
                        && let ExprValue::BitVecConst { value: byte_val, .. } = value.value()
                    {
                        if let (Ok(idx), Ok(byte)) =
                            (usize::try_from(idx_val.clone()), u8::try_from(byte_val.clone()))
                        {
                            if idx < len && !found[idx] {
                                bytes[idx] = byte;
                                found[idx] = true;
                            }
                        }
                    }
                    current = array;
                }
                ExprValue::ConstArray { value, .. } => {
                    // Fill any unfound positions with the constant value.
                    if let ExprValue::BitVecConst { value: byte_val, .. } = value.value() {
                        if let Ok(byte) = u8::try_from(byte_val.clone()) {
                            for (i, f) in found.iter().enumerate() {
                                if !f {
                                    bytes[i] = byte;
                                }
                            }
                        }
                    }
                    break;
                }
                ExprValue::Var { .. } => {
                    // If any byte is not found, the string is not fully concrete.
                    if found.iter().any(|f| !f) {
                        return None;
                    }
                    break;
                }
                _ => return None,
            }
        }
        String::from_utf8(bytes).ok()
    }

    /// Try to concretely evaluate a filter_map closure over concrete source
    /// elements. Currently handles the `|s| s.parse::<T>().ok()` pattern
    /// where T is an integer type.
    ///
    /// Returns a Vec of concrete output values (Some results only, None filtered).
    /// Returns `None` if the closure cannot be concretely evaluated.
    ///
    /// Part of #3692: concrete filter_map replay for parse.rs PROOF.
    /// Check if the filter_map closure contains an IntParse (FromStr) call.
    ///
    /// Part of #3189: extracted from try_concrete_filter_map_int_parse for reuse.
    pub(in crate::codegen_ay::chc) fn has_int_parse_closure(&self, args: &[Operand]) -> bool {
        let Some(closure_arg) = args.get(1) else { return false };
        let Ok(closure_ty) = closure_arg.ty(self.body.locals()) else { return false };
        let TyKind::RigidTy(RigidTy::Closure(def, closure_args)) = closure_ty.kind() else {
            return false;
        };
        for kind in [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce] {
            if let Ok(instance) = Instance::resolve_closure(def, &closure_args, kind)
                && let Some(body) = instance.body()
            {
                for bb in &body.blocks {
                    if let rustc_public::mir::TerminatorKind::Call { func, .. } =
                        &bb.terminator.kind
                    {
                        if let Some(callee_path) = self.resolve_callee_path(func) {
                            // Part of #3189: match both `FromStr::from_str` (direct trait call)
                            // and `<str>::parse` (convenience method that delegates to from_str).
                            // The closure `|s| s.parse::<i32>().ok()` produces MIR calling
                            // `core::str::<impl str>::parse`, not `from_str` directly.
                            if callee_path.contains("from_str")
                                || callee_path.contains("FromStr")
                                || callee_path.contains("::parse")
                            {
                                return true;
                            }
                        }
                    }
                }
                return false;
            }
        }
        false
    }

    pub(in crate::codegen_ay::chc) fn try_concrete_filter_map_int_parse(
        &self,
        args: &[Operand],
        concrete_source_elems: &[Expr],
        target_bv_width: u32,
    ) -> Option<Vec<Expr>> {
        if !self.has_int_parse_closure(args) {
            return None;
        }

        // Evaluate each source element concretely.
        let mut output = Vec::new();
        for elem in concrete_source_elems {
            let text = Self::try_extract_str_from_expr(elem)?;
            // Parse as integer at codegen time.
            // Use i128 to handle all integer widths, then truncate to BV.
            if let Ok(parsed) = text.parse::<i128>() {
                // Check if value fits in target width (signed).
                let max = (1i128 << (target_bv_width - 1)) - 1;
                let min = -(1i128 << (target_bv_width - 1));
                if parsed >= min && parsed <= max {
                    output.push(Expr::bitvec_const(parsed, target_bv_width));
                }
                // Value overflows target width → Err → filtered out by .ok()
            }
            // Parse failure → Err → None → filtered out by .ok()
        }

        debug!(
            source_count = concrete_source_elems.len(),
            output_count = output.len(),
            target_bv_width,
            "try_concrete_filter_map_int_parse: concrete replay (#3692)"
        );
        Some(output)
    }
}

/// Short label for a AY Sort, used for generating unique Datatype names.
fn sort_short_label(sort: &Sort) -> &'static str {
    if sort.is_bool() {
        "Bool"
    } else if sort.is_bitvec() {
        "BV"
    } else if sort.is_int() {
        "Int"
    } else {
        "X"
    }
}
