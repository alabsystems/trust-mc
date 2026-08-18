// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec iterator stub implementations, extracted from stubs_iterators.rs per #2246.
//!
//! Converted from include!() to proper module per #2595.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::Operand;
use tracing::debug;

use crate::codegen_ay::chc::call::SLICE_BACKING_REBASE_MAX_ELEMS;

use super::stubs::StubKind;
use super::stubs_util_collections::{IterConstructConfig, IterNextParts};
use super::types::{CtorFieldExt, POINTER_WIDTH, ptr_sort};
use super::{ChcCtx, CollectionCallResult, StubTranslateArgs};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // =========================================================================
    // Vec iterator stub interception (Part of #1811)
    // =========================================================================

    /// Accepted Vec iterator stub variants.
    const VEC_ITER_STUBS: &'static [StubKind] =
        &[StubKind::VecIntoIter, StubKind::VecIter, StubKind::VecIterMut, StubKind::IntoIterNext];

    /// Detects if a function call is a Vec iterator method using def-path lookup.
    ///
    /// Part of #1811: Vec iterator CHC stubs for correct element sort inference.
    pub(in crate::codegen_ay::chc) fn detect_vec_iter_stub(
        &self,
        func: &Operand,
    ) -> Option<StubKind> {
        self.detect_stub_filtered(func, Self::VEC_ITER_STUBS, "vec_iter")
    }

    /// Translates a Vec iterator operation to SMT expressions.
    ///
    /// Vec is modeled as struct (ptr, len, cap, data) where data is Array<usize, T>.
    /// VecIntoIter is modeled as struct (vec, pos) for iteration.
    ///
    /// Part of #1811: CHC codegen for Vec iterator operations with correct element sort.
    ///
    /// # Contracts
    ///
    /// REQUIRES: `stub` is a Vec iterator StubKind (VecIntoIter, VecIter, VecIterMut, IntoIterNext).
    /// REQUIRES: `args` contains operands matching the stub's arity.
    /// REQUIRES: `modified_locals` tracks locals modified in the current statement.
    /// ENSURES: Returns Some with valid SMT expressions for supported operations.
    /// ENSURES: Returns None if arguments are insufficient or sort derivation fails.
    /// ENSURES: VecIntoIter/VecIter/VecIterMut create iterator struct from Vec.
    /// ENSURES: IntoIterNext advances position and returns Option<T>.
    ///
    /// D3 table-driven dispatch (Part of #2304).
    pub(in crate::codegen_ay::chc) fn translate_vec_iter_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        _dest_local: Option<usize>,
    ) -> Option<CollectionCallResult> {
        let ctx = StubTranslateArgs { args, modified_locals, dest_local: _dest_local };
        stub_dispatch!(self, stub, &ctx, "translate_vec_iter_call",
            StubKind::VecIntoIter
            | StubKind::VecIter
            | StubKind::VecIterMut  => translate_vec_into_iter_construct,
            StubKind::IntoIterNext  => translate_vec_into_iter_next,
        )
    }

    // ===== Vec iterator handlers (D3 table-driven, Part of #2304) =====

    /// Vec::into_iter/iter/iter_mut — creates iterator struct from Vec.
    /// Part of #2874: Uses get_collection_arg for projected Vec reconstruction.
    fn translate_vec_into_iter_construct(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        let arg = ctx.args.first()?;
        let vec = self.get_collection_arg(arg, ctx.modified_locals)?;

        // When the collection is a bare Array (from [T; N] array literal),
        // wrap it in a Slice Datatype with the correct length extracted from
        // the MIR type. Without this, make_vec_into_iter_chc wraps the Array
        // with fld_len=0, causing next() to always return None.
        let vec = if vec.sort().is_array() { self.wrap_bare_array_in_slice(arg, vec) } else { vec };

        // Part of #1930: Explicit failure on sort mismatch instead of bitvec fallback
        if let Some(iter) = self.make_vec_into_iter_chc(vec.clone()) {
            let source_local = self.record_iter_source(ctx, arg);
            self.record_adapter_source_data_from_vec(ctx.dest_local, source_local, &vec);
            if let Some(dest_local) = ctx.dest_local {
                self.collections.adapter_at_start.insert(dest_local);
            }
            return Some(CollectionCallResult::read_only(iter));
        }

        // Part of #3012: When the argument is a bv64 reference from VecAsSlice,
        // the sort is not a Datatype and make_vec_into_iter_chc fails. Look up
        // the full Slice view stored by vec_op_as_slice in const_ref_slice_views.
        if let Operand::Copy(place) | Operand::Move(place) = arg {
            let ref_local: usize = place.local;
            let target_local =
                self.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local);
            let slice_opt = self.ref_resolution.const_ref_slice_views.get(&target_local).cloned();
            if let Some(slice) = slice_opt {
                if let Some(iter) = self.make_vec_into_iter_chc(slice.clone()) {
                    debug!(
                        ref_local,
                        target_local, "VecIter: constructed from const_ref_slice_views (#3012)"
                    );
                    let source_local = self.record_iter_source(ctx, arg);
                    self.record_adapter_source_data_from_vec(ctx.dest_local, source_local, &slice);
                    if let Some(dest_local) = ctx.dest_local {
                        self.collections.adapter_at_start.insert(dest_local);
                    }
                    return Some(CollectionCallResult::read_only(iter));
                }
            }
        }

        // Part of #4318: slice iteration through dyn/unsized projection can leave
        // the receiver as a BV128 fat pointer even when slice backing metadata is
        // available. Recover a concrete Slice<T> value from that metadata before
        // failing closed so IntoIterator for &[T] stays on the local stub path.
        if let Some(slice) = self.recover_slice_iter_source(arg, ctx.modified_locals) {
            if let Some(iter) = self.make_vec_into_iter_chc(slice.clone()) {
                debug!("VecIter: reconstructed Slice from slice backing metadata (#4318)");
                let source_local = self.record_iter_source(ctx, arg);
                self.record_adapter_source_data_from_vec(ctx.dest_local, source_local, &slice);
                if let Some(dest_local) = ctx.dest_local {
                    self.collections.adapter_at_start.insert(dest_local);
                }
                return Some(CollectionCallResult::read_only(iter));
            }
        }

        Some(self.unsound_sort_mismatch_failure("VecIntoIter construction", vec.sort()))
    }

    fn recover_slice_iter_source(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let backing = self.resolve_slice_backing(arg, modified_locals)?;
        let target_sort = backing.data.as_expr().sort().clone();
        let data = if Self::is_zero_pointer_width_bitvec(backing.offset.as_expr()) {
            backing.data.as_expr().clone()
        } else {
            self.record_aggregate_gap("vec_iter_slice_backing_rebase");
            self.rebase_slice_backing_to_zero_based_array(
                &backing,
                &target_sort,
                "__vec_iter_slice_data",
                SLICE_BACKING_REBASE_MAX_ELEMS,
            )?
        };
        let elem_sort = data.sort().array_sort()?.element_sort.clone();
        let slice_sort_name = crate::codegen_ay::names::slice_sort_name(
            &crate::codegen_ay::names::sort_short_name(&elem_sort),
        );
        let slice_fields: Vec<(String, Sort)> = vec![
            ("fld_ptr".to_string(), ptr_sort()),
            ("fld_len".to_string(), ptr_sort()),
            ("fld_data".to_string(), data.sort().clone()),
        ];
        let slice_sort = Sort::struct_type(&slice_sort_name, slice_fields);
        self.declare_datatype_sort_if_needed(&slice_sort);
        let ctor_name = crate::codegen_ay::names::resolve_ctor_name(&slice_sort, &slice_sort_name);
        Some(Expr::datatype_constructor(
            &slice_sort_name,
            ctor_name,
            vec![Expr::bitvec_const(0u64, POINTER_WIDTH), backing.len.into_expr(), data],
            slice_sort,
        ))
    }

    /// Record the source collection for an iterator destination local.
    /// Part of #3348: Enables VecExtendFromSlice to resolve source length from
    /// iterator arguments by tracing back to the source Vec.
    fn record_iter_source(&mut self, ctx: &StubTranslateArgs<'_>, arg: &Operand) -> Option<usize> {
        let Some(dest_local) = ctx.dest_local else {
            return None;
        };
        let arg_local = match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return None,
        };
        // Resolve through ref_targets to find the actual collection local.
        let resolved =
            self.ref_resolution.ref_targets.get(&arg_local).map_or(arg_local, |rt| rt.local);
        // Also check slice_to_vec_local: if the arg is a slice from VecAsSlice,
        // trace to the original Vec local.
        let collection_local =
            self.ref_resolution.slice_to_vec_local.get(&resolved).copied().unwrap_or(resolved);
        self.ref_resolution.iter_to_collection_local.insert(dest_local, collection_local);
        Some(collection_local)
    }

    /// Record the source Vec data array for an iterator destination local.
    ///
    /// Extracts `fld_data` from the Vec expression and stores it in
    /// `adapter_source_data` so downstream IterMap/IterZip/IterCollect can
    /// access the source data array for element-wise constraints.
    ///
    /// Part of #3348: IterCollect element-wise constraints (Step 4 infrastructure).
    fn record_adapter_source_data_from_vec(
        &mut self,
        dest_local: Option<usize>,
        source_local: Option<usize>,
        vec: &Expr,
    ) {
        let Some(dest_local) = dest_local else {
            return;
        };
        if let Some((data, _elem_sort)) = self.extract_vec_data_with_sort(vec) {
            use crate::codegen_ay::chc::codegen_ctx::types::AdapterSourceData;
            let concrete_elems = source_local
                .and_then(|local| self.collections.adapter_source_data.get(&local))
                .and_then(|source| source.concrete_elems.clone())
                .or_else(|| self.extract_concrete_vec_elems_from_expr(vec, &data));
            self.collections.adapter_source_data.insert(
                dest_local,
                AdapterSourceData {
                    data_arrays: vec![data],
                    has_transform: false,
                    closure_template: None,
                    concrete_elems,
                },
            );
            debug!(
                dest_local,
                source_local,
                concrete_count = self
                    .collections
                    .adapter_source_data
                    .get(&dest_local)
                    .and_then(|source| source.concrete_elems.as_ref())
                    .map(Vec::len),
                "adapter_source_data: recorded Vec fld_data for iterator"
            );
        }
    }

    fn extract_concrete_vec_elems_from_expr(&self, vec: &Expr, data: &Expr) -> Option<Vec<Expr>> {
        let vec_sort = vec.sort();
        let dt = vec_sort.datatype_sort()?;
        let len_field = dt.constructors.first()?.field("fld_len")?;
        let len_expr = vec.clone().field_select(&dt.name, "fld_len", len_field.sort.clone());
        let count = Self::try_eval_concrete_bv_usize(&len_expr)?;
        if count == 0 || count > 16 {
            return None;
        }
        let elems = Self::try_extract_store_chain_elements(data, count)?;
        if elems.iter().all(|elem| {
            matches!(
                elem.value(),
                ExprValue::BoolConst(_)
                    | ExprValue::BitVecConst { .. }
                    | ExprValue::IntConst(_)
                    | ExprValue::RealConst(_)
            )
        }) {
            Some(elems)
        } else {
            None
        }
    }

    /// IntoIter<T>::next(&mut self) -> Option<T>.
    /// Part of #1811, Part of #2304 (IT2 skeleton extraction).
    fn translate_vec_into_iter_next(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        // Part of #3984: Try ArrayIntoIter path first. ArrayIntoIter uses
        // a PolymorphicIter nested structure (fld_inner.fld_alive.fld_start/end)
        // instead of Vec's flat fld_vec/fld_pos layout. The stub lookup routes
        // both array and Vec IntoIter::next() to IntoIterNext, so we must
        // differentiate here by checking the sort structure.
        if let Some(result) = self.translate_array_into_iter_next(ctx) {
            return Some(result);
        }

        self.translate_iter_next_skeleton(
            ctx.args,
            ctx.modified_locals,
            "VecIntoIter",
            |this, iter, dt_name| {
                // Part of #1930: Propagate None on sort mismatch
                let vec_sort = this.infer_vec_sort_from_iter(iter)?;
                let vec = iter.clone().field_select(dt_name, "fld_vec", vec_sort);
                let pos = iter.clone().field_select(dt_name, "fld_pos", ptr_sort());

                // Vec length from nested struct (VecIntoIter has no fld_len)
                let len =
                    vec.clone().field_select(this.infer_vec_type_name(&vec), "fld_len", ptr_sort());

                // element = vec.data[pos]
                let (data, _elem_sort) = this.extract_vec_data_with_sort(&vec)?;
                let elem = data.select(pos);
                debug!("IntoIterNext actual_sort={}", elem.sort());

                Some(IterNextParts {
                    element: elem,
                    element_fields: None,
                    len,
                    fields_before_pos: vec![vec],
                    fields_after_pos: vec![],
                    constraints: vec![],
                })
            },
        )
    }

    /// Creates a VecIntoIter struct for CHC mode.
    ///
    /// Part of #1811: Iterator struct with correct element sort propagation.
    /// Part of #3012: When the input is a Slice (from VecAsSlice), uses a distinct
    /// sort name "SliceIter_<elem>" to avoid AY sort name collision with Vec-backed
    /// "VecIntoIter_<elem>" (same field layout but different fld_vec sort).
    pub(in crate::codegen_ay::chc) fn make_vec_into_iter_chc(&mut self, vec: Expr) -> Option<Expr> {
        let vec_sort = vec.sort().clone();

        // Part of #4112: If the input is already a bare Array sort (e.g., from
        // a fixed-size array like `["H", "i"]`), wrap it in a Slice Datatype
        // so the iterator construction can proceed. Without this, `.iter()` on
        // array literals fails with "non-datatype sort".
        if let Some(arr) = vec_sort.array_sort() {
            let elem_sort = arr.element_sort.clone();
            let elem_short = crate::codegen_ay::names::sort_short_name(&elem_sort);
            let slice_sort_name = crate::codegen_ay::names::slice_sort_name(&elem_short);
            let slice_fields: Vec<(std::borrow::Cow<'static, str>, Sort)> = vec![
                ("fld_ptr".into(), ptr_sort()),
                ("fld_len".into(), ptr_sort()),
                ("fld_data".into(), vec_sort),
            ];
            let slice_sort = Sort::struct_type(&slice_sort_name, slice_fields);
            self.declare_datatype_sort_if_needed(&slice_sort);
            let ctor_name =
                crate::codegen_ay::names::resolve_ctor_name(&slice_sort, &slice_sort_name);
            let slice_expr = Expr::datatype_constructor(
                &slice_sort_name,
                ctor_name,
                vec![
                    Expr::bitvec_const(0u64, super::types::POINTER_WIDTH),
                    Expr::bitvec_const(0u64, super::types::POINTER_WIDTH),
                    vec,
                ],
                slice_sort.clone(),
            );
            let mut iter_name = String::with_capacity(10 + elem_short.len());
            iter_name.push_str("SliceIter_");
            iter_name.push_str(&elem_short);
            let iter_fields = crate::codegen_ay::names::vec_into_iter_fields(slice_sort);
            let ctor_fields = vec![slice_expr, Self::iter_position_zero()];
            return Some(self.make_collection_iter(IterConstructConfig {
                iter_sort_name: &iter_name,
                iter_fields,
                ctor_fields,
            }));
        }

        // Determine element sort from Vec's fld_data array
        // Part of #1930: Return None on sort mismatch instead of falling back to bitvec(32)
        let elem_sort = vec_sort.datatype_sort().and_then(|dt| {
            dt.constructors
                .first()?
                .fields
                .iter()
                .find(|f| f.name == "fld_data")
                .and_then(|f| f.sort.array_sort())
                .map(|arr| arr.element_sort.clone())
        })?;

        let elem_short = crate::codegen_ay::names::sort_short_name(&elem_sort);
        // Part of #3012: Use "SliceIter_" prefix when the inner collection is a Slice
        // (from VecAsSlice bv64 path) to avoid sort name collision with Vec-backed
        // VecIntoIter which has a different fld_vec sort.
        let is_slice = vec_sort.datatype_name().map_or(false, |n| n.starts_with("Slice_"));
        let iter_sort_name = if is_slice {
            let mut s = String::with_capacity(10 + elem_short.len());
            s.push_str("SliceIter_");
            s.push_str(&elem_short);
            s
        } else {
            crate::codegen_ay::names::vec_into_iter_sort_name(&elem_short)
        };

        let iter_fields = crate::codegen_ay::names::vec_into_iter_fields(vec_sort);
        let ctor_fields = vec![vec, Self::iter_position_zero()];
        Some(self.make_collection_iter(IterConstructConfig {
            iter_sort_name: &iter_sort_name,
            iter_fields,
            ctor_fields,
        }))
    }

    /// Infers the Vec sort from a VecIntoIter expression.
    ///
    /// Part of #1930: Returns None instead of fallback on sort mismatch.
    pub(in crate::codegen_ay::chc) fn infer_vec_sort_from_iter(&self, iter: &Expr) -> Option<Sort> {
        let dt = iter.sort().datatype_sort()?;
        for ctor in &dt.constructors {
            for field in &ctor.fields {
                if field.name == "fld_vec" {
                    return Some(field.sort.clone());
                }
            }
        }
        None
    }

    /// Infers the Vec type name from a Vec expression.
    pub(in crate::codegen_ay::chc) fn infer_vec_type_name<'a>(&self, vec: &'a Expr) -> &'a str {
        vec.sort().datatype_name().unwrap_or("Vec")
    }

    /// Extracts Vec's data array and its element sort.
    ///
    /// Part of #1811: Critical for correct Option<T> construction.
    pub(in crate::codegen_ay::chc) fn extract_vec_data_with_sort(
        &self,
        vec: &Expr,
    ) -> Option<(Expr, Sort)> {
        let vec_sort = vec.sort();
        let dt = vec_sort.datatype_sort()?;
        let data_field = dt.constructors.first()?.field("fld_data")?;

        let elem_sort = data_field.sort.array_sort()?.element_sort.clone();

        let data = vec.clone().field_select(&dt.name, "fld_data", data_field.sort.clone());
        Some((data, elem_sort))
    }
}
