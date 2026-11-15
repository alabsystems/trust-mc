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

use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::codegen_ctx::{ExactVar, Havoc, sound_havoc};
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
use super::super::{ChcCtx, chc_fresh_name};

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
                && let Some(body) = instance.callee_body()
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
                        ExactVar::nondet(
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
                return Havoc::mint(
                    self,
                    sound_havoc::UNTRACKED_COLLECTION_STATE,
                    format!("iter_collect_data_{dest_local}"),
                    data_sort.clone(),
                );
            }
        }

        // Case 3: Fallback — unconstrained symbolic data.
        let booked = self.record_sound_fallback_reason("iter_collect_symbolic_fallback");
        Havoc::booked(booked, format!("iter_collect_data_{dest_local}"), data_sort.clone())
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

    /// The body of the closure argument `args[1]`, resolved.
    fn closure_arg_body(&self, args: &[Operand]) -> Option<rustc_public::mir::Body> {
        let closure_ty = args.get(1)?.ty(self.body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::Closure(def, closure_args)) = closure_ty.kind() else {
            return None;
        };
        [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce]
            .into_iter()
            .find_map(|kind| Instance::resolve_closure(def, &closure_args, kind).ok())?
            .callee_body()
    }

    /// The calls of a closure body in block order, each with its callee
    /// path, its arguments and its destination local, when every call's
    /// destination is a whole local; `None` otherwise.
    fn closure_body_calls(
        &self,
        body: &rustc_public::mir::Body,
    ) -> Option<Vec<(String, Vec<Operand>, usize)>> {
        let mut calls = Vec::new();
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, destination, .. } =
                &block.terminator.kind
            {
                if !destination.projection.is_empty() {
                    return None;
                }
                calls.push((self.resolve_callee_path(func)?, args.clone(), destination.local));
            }
        }
        Some(calls)
    }

    /// Does the operand of a closure body derive, through copies and
    /// dereferences only, from the closure's item argument (local 2), never
    /// from its environment?
    fn closure_operand_is_item(body: &rustc_public::mir::Body, operand: &Operand) -> bool {
        use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind};
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            return false;
        };
        if !place.projection.iter().all(|p| matches!(p, ProjectionElem::Deref)) {
            return false;
        }
        let mut local = place.local;
        for _ in 0..6 {
            if local == 2 {
                return true;
            }
            let defs: Vec<&Rvalue> = body
                .blocks
                .iter()
                .flat_map(|block| &block.statements)
                .filter_map(|stmt| match &stmt.kind {
                    StatementKind::Assign(lhs, rhs) if lhs.local == local && lhs.projection.is_empty() => {
                        Some(rhs)
                    }
                    _ => None,
                })
                .collect();
            let [def] = defs.as_slice() else {
                return false;
            };
            let src = match def {
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) => src,
                Rvalue::CopyForDeref(src) => src,
                Rvalue::Ref(_, _, src) => src,
                _ => return false,
            };
            if !src.projection.iter().all(|p| matches!(p, ProjectionElem::Deref)) {
                return false;
            }
            local = src.local;
        }
        false
    }

    /// Is the closure argument `args[1]` exactly `|s| s.chars()`: one call,
    /// `str::chars` of its item argument, returned? The concrete `flat_map`
    /// model yields the chars of each string; any other closure (`|s|
    /// s.chars().rev()`, a captured string's chars) yields others, and
    /// `flat_map(|s| s.chars().rev()).next() == Some('H')` over `["Hx", ..]`
    /// verified clean where Kani fails (walker fail-closed repair round 5,
    /// `iter_concrete_source_dual.rs`).
    pub(in crate::codegen_ay::chc) fn closure_is_str_chars(&self, args: &[Operand]) -> bool {
        let Some(body) = self.closure_arg_body(args) else { return false };
        let Some(calls) = self.closure_body_calls(&body) else { return false };
        let [(path, call_args, dest)] = calls.as_slice() else { return false };
        path.ends_with("<impl str>::chars")
            && *dest == 0
            && call_args.first().is_some_and(|arg| Self::closure_operand_is_item(&body, arg))
    }

    /// The integer type `T` (bit width, signedness) when the closure argument
    /// `args[1]` is exactly `|s| s.parse::<T>().ok()`: a `str::parse` of its
    /// item argument whose result `Result::ok` returns. The concrete
    /// `filter_map` replay parses each string as `T`; it took any closure
    /// that CALLED a parse as `parse::<i32>().ok()` (walker fail-closed
    /// repair round 5, `iter_concrete_source_dual.rs`). `None` for any other
    /// shape, and for 128-bit `T` (parsed exactly only up to `i128`).
    pub(in crate::codegen_ay::chc) fn int_parse_ok_closure_target(&self, args: &[Operand]) -> Option<(u32, bool)> {
        use rustc_public::ty::{IntTy, UintTy};
        let body = self.closure_arg_body(args)?;
        let calls = self.closure_body_calls(&body)?;
        let [(parse_path, parse_args, parse_dest), (ok_path, ok_args, ok_dest)] = calls.as_slice() else {
            return None;
        };
        if !(parse_path.contains("<impl str>::parse")
            && parse_args.first().is_some_and(|arg| Self::closure_operand_is_item(&body, arg))
            && ok_path.contains("Result") && ok_path.ends_with("::ok")
            && *ok_dest == 0
            && matches!(ok_args.first(), Some(Operand::Copy(p) | Operand::Move(p))
                if p.local == *parse_dest && p.projection.is_empty()))
        {
            return None;
        }
        // `T` is the payload of the closure's `Option<T>` return.
        let ret_ty = body.locals().first()?.ty;
        let TyKind::RigidTy(RigidTy::Adt(_, ret_args)) = ret_ty.kind() else { return None };
        let rustc_public::ty::GenericArgKind::Type(t) = ret_args.0.first()? else { return None };
        let pointer = crate::codegen_ay::types::POINTER_WIDTH;
        Some(match t.kind() {
            TyKind::RigidTy(RigidTy::Int(int)) => (
                match int {
                    IntTy::I8 => 8,
                    IntTy::I16 => 16,
                    IntTy::I32 => 32,
                    IntTy::I64 => 64,
                    IntTy::Isize => pointer,
                    IntTy::I128 => return None,
                },
                true,
            ),
            TyKind::RigidTy(RigidTy::Uint(uint)) => (
                match uint {
                    UintTy::U8 => 8,
                    UintTy::U16 => 16,
                    UintTy::U32 => 32,
                    UintTy::U64 => 64,
                    UintTy::Usize => pointer,
                    UintTy::U128 => return None,
                },
                false,
            ),
            _ => return None,
        })
    }

    /// Concretely evaluate a filter_map closure `|s| s.parse::<T>().ok()`
    /// over concrete source strings: the values that parse as `T` (Rust's
    /// integer `FromStr` accepts exactly what `i128` parsing accepts within
    /// `T`'s range). `None` when the closure is not that shape
    /// ([`Self::int_parse_ok_closure_target`]).
    ///
    /// Part of #3692: concrete filter_map replay for parse.rs PROOF.
    pub(in crate::codegen_ay::chc) fn try_concrete_filter_map_int_parse(
        &self,
        args: &[Operand],
        concrete_source_elems: &[Expr],
    ) -> Option<Vec<Expr>> {
        let (width, signed) = self.int_parse_ok_closure_target(args)?;
        let texts: Vec<String> = concrete_source_elems
            .iter()
            .map(|elem| Self::try_extract_str_from_expr(elem))
            .collect::<Option<_>>()?;
        let output = Self::parse_ints_like_from_str(&texts, width, signed);
        debug!(
            source_count = concrete_source_elems.len(),
            output_count = output.len(),
            width,
            signed,
            "try_concrete_filter_map_int_parse: concrete replay (#3692)"
        );
        Some(output)
    }

    /// The integers of width `width` and signedness `signed` that
    /// `str::parse` accepts among `texts`, in order.
    pub(in crate::codegen_ay::chc) fn parse_ints_like_from_str(
        texts: &[String],
        width: u32,
        signed: bool,
    ) -> Vec<Expr> {
        let (min, max) = if signed {
            (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
        } else {
            (0i128, (1i128 << width) - 1)
        };
        texts
            .iter()
            .filter_map(|text| text.parse::<i128>().ok())
            .filter(|value| *value >= min && *value <= max)
            .map(|value| Expr::bitvec_const(value, width))
            .collect()
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
