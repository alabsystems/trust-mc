// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! HashMap iterator stub implementations, extracted from stubs_iterators.rs per #2246.
//!
//! Converted from include!() to proper module per #2595.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use std::collections::HashSet;

use super::names;
use super::stubs::StubKind;
use super::stubs_util_collections::{IterConstructConfig, IterNextParts};
use super::types::{CtorFieldExt, bool_sort, ptr_sort};
use super::{ChcCtx, CollectionCallResult, StubTranslateArgs};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // =========================================================================
    // HashMap iterator stub interception (Part of #1812)
    // =========================================================================

    /// Accepted HashMap iterator stub variants (direct matches).
    const HASHMAP_ITER_STUBS: &'static [StubKind] = &[
        StubKind::HashMapIntoIter,
        StubKind::HashMapIter,
        StubKind::HashMapKeys,
        StubKind::HashMapValues,
        StubKind::HashMapIterNext,
        // TrustMcMap reuses HashMap iterator semantics in CHC mode.
        StubKind::TrustMcMapIntoIter,
        StubKind::TrustMcMapIterNext,
    ];

    /// Detects if a function call is a HashMap iterator method using def-path lookup.
    ///
    /// Part of #1812: HashMap iterator CHC stubs for membership invariant tests.
    /// TrustMcMap iterator stubs are mapped onto their HashMap equivalents.
    pub(in crate::codegen_ay::chc) fn detect_hashmap_iter_stub(
        &self,
        func: &Operand,
    ) -> Option<StubKind> {
        let stub = self.detect_stub_filtered(func, Self::HASHMAP_ITER_STUBS, "hashmap_iter")?;
        // Map TrustMcMap variants to HashMap equivalents (same SMT array model).
        match stub {
            StubKind::TrustMcMapIntoIter => Some(StubKind::HashMapIntoIter),
            StubKind::TrustMcMapIterNext => Some(StubKind::HashMapIterNext),
            other => Some(other),
        }
    }

    /// Translates a HashMap iterator operation to SMT expressions.
    ///
    /// Part of #3057: DT-free parallel-array encoding.
    /// HashMap data is `Array(K, V)`, presence is `Array(K, Bool)`.
    /// HashMapIntoIter is modeled as struct (data, present, keys, pos, len).
    ///
    /// Part of #1812: CHC codegen for HashMap iterator operations.
    ///
    /// # Contracts
    ///
    /// REQUIRES: `stub` is a HashMap iterator StubKind (HashMapIntoIter, HashMapIter, HashMapKeys, HashMapValues, HashMapIterNext).
    /// REQUIRES: `args` contains operands matching the stub's arity.
    /// REQUIRES: `modified_locals` tracks locals modified in the current statement.
    /// ENSURES: Returns Some with valid SMT expressions for supported operations.
    /// ENSURES: Returns None if arguments are insufficient or sort derivation fails.
    /// ENSURES: HashMapIntoIter/HashMapIter create iterator struct from HashMap.
    /// ENSURES: HashMapKeys/HashMapValues create key/value iterators.
    /// ENSURES: HashMapIterNext advances position and returns Option<(K, V)>.
    ///
    /// D3 table-driven dispatch (Part of #2304).
    pub(in crate::codegen_ay::chc) fn translate_hashmap_iter_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        dest_local: Option<usize>,
    ) -> Option<CollectionCallResult> {
        let ctx = StubTranslateArgs { args, modified_locals, dest_local };
        stub_dispatch!(self, stub, &ctx, "translate_hashmap_iter_call",
            StubKind::HashMapIntoIter   => translate_hashmap_into_iter_construct,
            StubKind::HashMapIter
            | StubKind::HashMapKeys
            | StubKind::HashMapValues   => translate_hashmap_iter_ref_construct,
            StubKind::HashMapIterNext   => translate_hashmap_iter_next,
        )
    }

    // ===== HashMap iterator handlers (D3 table-driven, Part of #2304) =====

    /// HashMap::into_iter(self) — consumes HashMap, creates iterator.
    ///
    /// Part of #3057: resolves both data and present arrays for the iterator.
    fn translate_hashmap_into_iter_construct(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        let data = self.translate_operand_with_modified(ctx.args.first()?, ctx.modified_locals)?;
        let present = self.get_hashmap_present_arg(ctx.args.first()?, ctx.modified_locals);
        let tracked_len =
            self.get_collection_len_var(ctx.args.first()?, ctx.modified_locals).map(|(_, len)| len);

        let data_sort = data.sort().clone();
        if let Some(iter) =
            self.make_hashmap_into_iter_chc(data, present, ctx.dest_local, tracked_len)
        {
            Some(CollectionCallResult::read_only(iter))
        } else {
            Some(self.unsound_sort_mismatch_failure("HashMapIntoIter construction", &data_sort))
        }
    }

    /// HashMap::iter/keys/values — borrows HashMap, creates iterator.
    ///
    /// Part of #3057: resolves data + present arrays from the HashMap local.
    fn translate_hashmap_iter_ref_construct(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        let data = self.get_hashmap_arg(ctx.args.first()?, ctx.modified_locals)?;
        let present = self.get_hashmap_present_arg(ctx.args.first()?, ctx.modified_locals);
        let tracked_len =
            self.get_collection_len_var(ctx.args.first()?, ctx.modified_locals).map(|(_, len)| len);

        let data_sort = data.sort().clone();
        if let Some(iter) =
            self.make_hashmap_into_iter_chc(data, present, ctx.dest_local, tracked_len)
        {
            Some(CollectionCallResult::read_only(iter))
        } else {
            Some(self.unsound_sort_mismatch_failure("HashMapIntoIter construction", &data_sort))
        }
    }

    /// HashMapIntoIter<K, V>::next(&mut self) -> Option<(K, V)>.
    ///
    /// Part of #1812, Part of #2304 (IT2 skeleton extraction).
    /// Part of #3057: DT-free — membership from present array, value from data array.
    fn translate_hashmap_iter_next(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_iter_next_skeleton(
            ctx.args,
            ctx.modified_locals,
            "HashMapIntoIter",
            |this, iter, dt_name| {
                let (data, present, keys, pos, len, _key_sort, _value_sort) =
                    this.extract_hashmap_iter_all_fields(iter, dt_name)?;

                let key = keys.clone().select(pos);
                // DT-free: value is directly from data array, no Option unwrapping.
                let value = data.clone().select(key.clone());
                // SOUNDNESS (Part of #1813, #3057): membership from presence array.
                let is_member = present.clone().select(key.clone());

                // Part of #3057: pass key and value as separate fields instead of
                // constructing a Tuple DT via make_tuple_chc. The consumer uses
                // result_fields directly for flattened destinations, avoiding the
                // DT+BV theory combination that triggers ay#1766.
                Some(IterNextParts {
                    element: key.clone(),
                    element_fields: Some(vec![key, value]),
                    len: len.clone(),
                    fields_before_pos: vec![data, present, keys],
                    fields_after_pos: vec![len],
                    constraints: vec![is_member],
                })
            },
        )
    }

    /// Creates a HashMapIntoIter struct for CHC mode.
    ///
    /// Part of #1812: Iterator struct with (data, present, keys, pos, len).
    /// Part of #1814: Use tracked_len if provided, otherwise symbolic.
    /// Part of #3057: DT-free — data is `Array(K,V)`, present is `Array(K,Bool)`.
    pub(in crate::codegen_ay::chc) fn make_hashmap_into_iter_chc(
        &mut self,
        data: Expr,
        present: Option<Expr>,
        _dest_local: Option<usize>,
        tracked_len: Option<Expr>,
    ) -> Option<Expr> {
        // Get key and value sorts from the data array sort.
        // Part of #1930: Return None on sort mismatch instead of falling back to bitvec.
        let arr = data.sort().array_sort()?;
        let key_sort = arr.index_sort.clone();
        // DT-free: value sort is directly the array element sort (no Option wrapper).
        let value_sort = arr.element_sort.clone();

        // Build presence array — use tracked if available, else symbolic fallback.
        let present_expr = present.unwrap_or_else(|| {
            // Part of #3447: Record that HashMap iterator present array is
            // unconstrained (tracked present not available — membership unknown).
            self.record_sound_fallback_reason("hashmap_iter_present_unknown");
            let sym_name = super::chc_fresh_name("hashmap_iter_present");
            super::declare_pending_var(sym_name, Sort::array(key_sort.clone(), bool_sort()))
        });

        // Build iterator sort name based on key/value sorts.
        let key_name = crate::codegen_ay::names::sort_short_name(&key_sort);
        let val_name = crate::codegen_ay::names::sort_short_name(&value_sort);
        let iter_sort_name = names::hashmap_into_iter_sort_name(&key_name, &val_name);

        // Create symbolic keys array: Array<usize, K>
        let (keys, keys_sort) = self.make_symbolic_iter_keys("hashmap_iter_keys", key_sort);

        // Part of #1814: Use tracked length if provided, otherwise symbolic.
        let len = self.tracked_len_or_fresh(tracked_len, "hashmap_iter_len");
        let present_sort = present_expr.sort().clone();
        let iter_fields = names::hashmap_iter_fields(data.sort().clone(), present_sort, keys_sort);
        let ctor_fields = vec![data, present_expr, keys, Self::iter_position_zero(), len];
        Some(self.make_collection_iter(IterConstructConfig {
            iter_sort_name: &iter_sort_name,
            iter_fields,
            ctor_fields,
        }))
    }

    /// Extracts all fields (data, present, keys, pos, len) and sorts from a HashMapIntoIter.
    ///
    /// Part of #3057: DT-free 5-field iterator (fld_data, fld_present, fld_keys, fld_pos, fld_len).
    /// Returns (data, present, keys, pos, len, key_sort, value_sort).
    pub(in crate::codegen_ay::chc) fn extract_hashmap_iter_all_fields(
        &self,
        iter: &Expr,
        dt_name: &str,
    ) -> Option<(Expr, Expr, Expr, Expr, Expr, Sort, Sort)> {
        let dt = iter.sort().datatype_sort()?;
        let ctor = dt.constructors.first()?;

        let data_field = ctor.field("fld_data")?;
        let present_field = ctor.field("fld_present")?;
        let keys_field = ctor.field("fld_keys")?;

        let data = iter.clone().field_select(dt_name, "fld_data", data_field.sort.clone());
        let present = iter.clone().field_select(dt_name, "fld_present", present_field.sort.clone());
        let keys = iter.clone().field_select(dt_name, "fld_keys", keys_field.sort.clone());
        let pos = iter.clone().field_select(dt_name, "fld_pos", ptr_sort());
        let len = iter.clone().field_select(dt_name, "fld_len", ptr_sort());

        // Extract key sort from keys array (Array<usize, K>).
        let key_sort = keys_field.sort.array_sort()?.element_sort.clone();

        // DT-free: value sort is directly the data array's element sort.
        let value_sort = data_field.sort.array_sort()?.element_sort.clone();

        Some((data, present, keys, pos, len, key_sort, value_sort))
    }

    // make_tuple_chc removed — Part of #3057: DT-free encoding passes key
    // and value as separate fields via result_fields, avoiding intermediate
    // tuple Datatype construction that triggers ay#1766 (DT+BV).
    // extract_option_payload removed earlier — same rationale.
}
