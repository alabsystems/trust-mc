// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! IterMap/IterFilter/IterFilterMap adapter constructor dispatch.
//!
//! Extracted from `codegen_call_iterator_adapter` per #4129 (500 LOC threshold).

use ay_bindings::Expr;
use tracing::debug;

use crate::codegen_ay::chc::stub_codegen::stubs_option_helpers::OptionHelpers;
use crate::codegen_ay::stubs::StubKind;

use super::super::ChcCtx;
use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_ctx::types::AdapterSourceData;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle IterMap/IterFilter/IterFilterMap constructor adapters.
    pub(in crate::codegen_ay::chc) fn codegen_iter_constructor(
        &mut self,
        cx: &ChcCallContext<'_>,
        stub: StubKind,
        dest_local: usize,
        dest_vec_idx: usize,
    ) -> Option<Expr> {
        let args = cx.args;
        let modified_locals = cx.modified_locals;

        let Some((inner_iter, iter_local)) =
            self.iterator_receiver_expr_and_local(args, modified_locals)
        else {
            self.collections.adapter_remaining_len.remove(&dest_local);
            self.collections.adapter_source_data.remove(&dest_local);
            self.collections.adapter_at_start.remove(&dest_local);
            self.record_sound_fallback_reason("iter_constructor_receiver_unmodelled");
            return None;
        };
        let source_data =
            iter_local.and_then(|local| self.collections.adapter_source_data.get(&local).cloned());
        let source_len = args
            .first()
            .and_then(|arg| arg.ty(self.body.locals()).ok())
            .and_then(|ty| self.typed_iterator_remaining_len(&inner_iter, ty));
        // A reused destination must not retain a previous chain's evidence.
        self.collections.adapter_remaining_len.remove(&dest_local);
        self.collections.adapter_source_data.remove(&dest_local);
        let inner_at_start = iter_local
            .is_some_and(|local| self.collections.adapter_at_start.contains(&local))
            || self.iterator_position_is_definitely_zero(&inner_iter);
        if inner_at_start {
            self.collections.adapter_at_start.insert(dest_local);
        } else {
            self.collections.adapter_at_start.remove(&dest_local);
        }

        // Map preserves item cardinality. Filter, FilterMap and Flatten do
        // not; neither may Chars' byte count become an exact item sidecar.
        if matches!(stub, StubKind::IterMap)
            && let Some(rl) = source_len.clone()
        {
            self.collections.adapter_remaining_len.insert(dest_local, rl);
        }

        // Part of #3348: Propagate adapter_source_data from inner iterator.
        // Adapters that can change values or cardinality must not replay cached
        // concrete source elements unless this constructor recomputes them exactly.
        if let Some(src_data) = source_data {
            let adapter_changes_output =
                matches!(stub, StubKind::IterMap | StubKind::IterFilter | StubKind::IterFilterMap);
            let is_map = matches!(stub, StubKind::IterMap | StubKind::IterFilterMap);
            let mut new_data = AdapterSourceData {
                data_arrays: src_data.data_arrays,
                has_transform: adapter_changes_output || src_data.has_transform,
                closure_template: src_data.closure_template,
                concrete_elems: if adapter_changes_output || src_data.has_transform {
                    None
                } else {
                    src_data.concrete_elems
                },
            };

            // Part of #3348: For IterMap, try to translate the closure body
            // to a AY expression parameterized by a shared index variable.
            // Enables IterCollect to build element-wise forall constraints.
            if is_map {
                new_data.closure_template =
                    self.try_translate_iter_map_closure(args, &new_data.data_arrays);
            }

            // Part of #3692: For IterFilterMap with concrete source data,
            // try to evaluate the filter_map closure concretely. When the
            // source Vec has concrete &str elements and the closure is
            // parse::<T>().ok(), evaluate at codegen time to build exact
            // output elements.
            if matches!(stub, StubKind::IterFilterMap)
                && new_data.concrete_elems.is_none()
                && !new_data.data_arrays.is_empty()
                && inner_at_start
            {
                // Determine element count: prefer concrete remaining_len,
                // fall back to evaluating symbolic BV expressions,
                // then counting store-chain depth (#3189).
                let count = source_len
                    .and_then(|rl| {
                        if let ay_bindings::ExprValue::BitVecConst { value: len_val, .. } =
                            rl.value()
                        {
                            usize::try_from(len_val.clone()).ok()
                        } else {
                            // Part of #3189: evaluate concrete BV expressions.
                            Self::try_eval_concrete_bv_usize(&rl)
                        }
                    })
                    .or_else(|| Self::count_store_chain_depth(&new_data.data_arrays[0]));
                // Path 1: AY store chain extraction (Slice_bv8 elements).
                if let Some(count) = count
                    && count <= 16
                    && let Some(source_elems) =
                        Self::try_extract_store_chain_elements(&new_data.data_arrays[0], count)
                {
                    if let Some(filtered) =
                        self.try_concrete_filter_map_int_parse(args, &source_elems)
                    {
                        new_data.concrete_elems = Some(filtered);
                        new_data.has_transform = false;
                        debug!(
                            dest_local,
                            source_count = count,
                            "IterFilterMap: AY concrete replay succeeded (#3692)"
                        );
                    }
                }
                // Path 2: Part of #3189 — MIR fallback. When count
                // extraction fails (symbolic state variables) or AY
                // elements are BV64 pointers, read the strings of the
                // literal the iterator was built over (traced exactly,
                // `concrete_strs_of_iter_source`), for a closure that is
                // exactly `|s| s.parse::<T>().ok()`.
                if new_data.concrete_elems.is_none()
                    && let Some((width, signed)) = self.int_parse_ok_closure_target(args)
                    && let Some(strs) =
                        iter_local.and_then(|local| self.concrete_strs_of_iter_source(local, 16))
                {
                    new_data.concrete_elems =
                        Some(Self::parse_ints_like_from_str(&strs, width, signed));
                    new_data.has_transform = false;
                    debug!(
                        dest_local,
                        source_count = strs.len(),
                        output_count = new_data.concrete_elems.as_ref().map_or(0, |v| v.len()),
                        "IterFilterMap: MIR concrete replay (#3189)"
                    );
                }
            }

            self.collections.adapter_source_data.insert(dest_local, new_data);
        }

        let (_, out_sort) = self.state_var_mgr.output_state_vars.get(dest_vec_idx)?;

        debug!("[4112-DIAG] constructor: stub={stub:?} out_sort={out_sort:?}");
        // Part of #4112: For IterFlatten with opaque BV64 sort (FlatMap/FlattenCompat),
        // construct_adapter_with_inner_iter fails because BV64 has no fld_iter field.
        // Model the iterator as a BV64 position counter initialized to 0.
        // Extract concrete chars from MIR string array for FlattenNext dispatch.
        if matches!(stub, StubKind::IterFlatten) && out_sort.bitvec_width().is_some() {
            if inner_at_start
                && self.closure_is_str_chars(args)
                && let Some(strs) =
                    iter_local.and_then(|local| self.concrete_strs_of_iter_source(local, 16))
            {
                debug!("[4112-DIAG] constructor: extracted strings={strs:?}");
                let all_chars: Vec<Expr> = strs
                    .iter()
                    .flat_map(|s| s.chars())
                    .map(|c| Expr::bitvec_const(c as u64, 32))
                    .collect();
                if !all_chars.is_empty() {
                    self.collections.flatten_outer_len.insert(dest_local, strs.len());
                    let data = AdapterSourceData {
                        data_arrays: vec![],
                        has_transform: false,
                        closure_template: None,
                        concrete_elems: Some(all_chars),
                    };
                    self.collections.adapter_source_data.insert(dest_local, data);
                    debug!(
                        dest_local,
                        char_count = self
                            .collections
                            .adapter_source_data
                            .get(&dest_local)
                            .and_then(|d| d.concrete_elems.as_ref())
                            .map_or(0, |v| v.len()),
                        "IterFlatten: concrete flat_map chars stored (#4112)"
                    );
                }
            }
            let width = out_sort.bitvec_width().expect("invariant: BV sort confirmed above");
            return Some(Expr::bitvec_const(0u64, width));
        }

        let out_sort = out_sort.clone();
        if matches!(stub, StubKind::IterMap)
            && let Some(dt) = out_sort.datatype_sort()
            && let Some(ctor) = dt.constructors.first()
            && dt.constructors.len() == 1
            && ctor.fields.len() == 2
            && ctor.fields.iter().all(|field| matches!(field.name.as_str(), "fld_iter" | "fld_f"))
        {
            // Map::new stores exactly the iterator and callable operands. Keep
            // the closure's actual captures so its native body can run later;
            // a fresh closure field would change the adapter's semantics.
            let callable = self.translate_operand_with_modified(args.get(1)?, modified_locals)?;
            let fields: Option<Vec<_>> = ctor
                .fields
                .iter()
                .map(|field| {
                    let value = if field.name == "fld_iter" {
                        inner_iter.clone()
                    } else {
                        callable.clone()
                    };
                    self.coerce_value_to_sort(value, &field.sort, false)
                })
                .collect();
            return Some(Expr::datatype_constructor(
                &dt.name,
                &ctor.name,
                fields?,
                out_sort.clone(),
            ));
        }
        self.construct_adapter_with_inner_iter(&out_sort, inner_iter)
    }
}
