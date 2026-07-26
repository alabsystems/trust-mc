// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! HashSet translation helpers.
//! Converted from include!() to proper module per #2595.
//!
//! Extracted from stubs_hashset.rs per #2246.
//! Consolidated to shared set helpers per #2308.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;

use super::stubs_util_collections::{IterConstructConfig, IterNextParts};
use super::{ChcCtx, CollectionCallResult, StubTranslateArgs, record_type_sort_fallback};
use super::{
    names,
    stubs::StubKind,
    types::{CtorFieldExt, POINTER_WIDTH, int_sort, ptr_sort},
};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translates a HashSet operation to SMT expressions.
    ///
    /// HashSet is modeled as `Array<Key, Bool>`:
    /// - true = present (in set)
    /// - false = absent (not in set)
    ///
    /// Part of #1751: CHC codegen for iterator membership tests.
    /// Part of #2308: Insert/contains/remove/len/is_empty delegated to shared set helpers.
    /// D3 table-driven dispatch (Part of #2304).
    pub(in crate::codegen_ay::chc) fn translate_hashset_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        dest_local: Option<usize>,
    ) -> Option<CollectionCallResult> {
        let ctx = StubTranslateArgs { args, modified_locals, dest_local };
        // IntoIter/Iter need the original stub to distinguish resolve strategy,
        // so they share a single handler that branches internally.
        stub_dispatch!(self, stub, &ctx, "translate_hashset_call",
            StubKind::HashSetNew       => translate_hashset_new,
            StubKind::HashSetInsert    => translate_hashset_insert,
            StubKind::HashSetContains  => translate_hashset_contains,
            StubKind::HashSetRemove    => translate_hashset_remove,
            StubKind::HashSetLen       => translate_hashset_len,
            StubKind::HashSetIsEmpty   => translate_hashset_is_empty,
            StubKind::HashSetClear     => translate_hashset_clear,
            StubKind::HashSetClone     => translate_hashset_clone,
            StubKind::HashSetIntoIter  => translate_hashset_into_iter,
            StubKind::HashSetIter      => translate_hashset_iter,
            StubKind::HashSetIterNext  => translate_hashset_iter_next,
        )
    }

    // ===== HashSet handlers (D3 table-driven, Part of #2304) =====

    /// HashSet::new() — Part of #1814: New sets start with length 0.
    fn translate_hashset_new(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        let len_zero = Some(Expr::bitvec_const(0u64, POINTER_WIDTH));
        self.translate_set_new_common(ctx.dest_local, len_zero).or_else(|| {
            record_type_sort_fallback("HashSet::new key sort");
            let empty_set = Expr::const_array(int_sort(), Expr::bool_const(false));
            Some(CollectionCallResult::new_collection(
                empty_set,
                Some(Expr::bitvec_const(0u64, POINTER_WIDTH)),
            ))
        })
    }

    fn translate_hashset_insert(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_insert_full("HashSet", ctx.args, ctx.modified_locals, true)
    }

    fn translate_hashset_contains(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_contains_full("HashSet", ctx.args, ctx.modified_locals)
    }

    fn translate_hashset_remove(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_remove_full("HashSet", ctx.args, ctx.modified_locals, true)
    }

    fn translate_hashset_len(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_len_full("hashset", ctx.args, ctx.modified_locals)
    }

    fn translate_hashset_is_empty(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_is_empty_full("hashset", ctx.args, ctx.modified_locals)
    }

    /// HashSet::clear() — Part of #1814: Clear sets length to 0.
    fn translate_hashset_clear(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        let len_zero = Some(Expr::bitvec_const(0u64, POINTER_WIDTH));
        self.translate_set_clear_common(ctx.args, ctx.modified_locals, len_zero)
    }

    fn translate_hashset_clone(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_clone_common(ctx.args, ctx.modified_locals)
    }

    /// HashSet::into_iter() — consumes set, creates iterator.
    fn translate_hashset_into_iter(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        let set = self.translate_operand_with_modified(ctx.args.first()?, ctx.modified_locals)?;
        let tracked_len =
            self.get_collection_len_var(ctx.args.first()?, ctx.modified_locals).map(|(_, len)| len);
        let iter = self.make_hashset_into_iter(set, ctx.dest_local, tracked_len)?;
        Some(CollectionCallResult::read_only(iter))
    }

    /// HashSet::iter() — borrows set, creates iterator.
    fn translate_hashset_iter(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        let set = self.resolve_set_arg_from_ref(ctx.args.first()?, ctx.modified_locals)?;
        let tracked_len =
            self.get_collection_len_var(ctx.args.first()?, ctx.modified_locals).map(|(_, len)| len);
        let iter = self.make_hashset_into_iter(set, ctx.dest_local, tracked_len)?;
        Some(CollectionCallResult::read_only(iter))
    }

    /// HashSetIntoIter<K>::next(&mut self) -> Option<K>.
    /// Part of #1813, Part of #2304 (IT2 skeleton extraction).
    fn translate_hashset_iter_next(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_iter_next_skeleton(
            ctx.args,
            ctx.modified_locals,
            "HashSetIntoIter",
            |this, iter, dt_name| {
                let (set, keys, _key_sort) = this.extract_hashset_iter_fields(iter, dt_name)?;
                let pos = iter.clone().field_select(dt_name, "fld_pos", ptr_sort());
                let len = iter.clone().field_select(dt_name, "fld_len", ptr_sort());
                let key = keys.clone().select(pos);
                let is_member = set.clone().select(key.clone());

                Some(IterNextParts {
                    element: key,
                    element_fields: None,
                    len: len.clone(),
                    fields_before_pos: vec![set, keys],
                    fields_after_pos: vec![len],
                    constraints: vec![is_member],
                })
            },
        )
    }

    /// Extracts set, keys, and key_sort from a HashSetIntoIter.
    ///
    /// Part of #1813: Helper for HashSet iterator next.
    fn extract_hashset_iter_fields(
        &self,
        iter: &Expr,
        dt_name: &str,
    ) -> Option<(Expr, Expr, Sort)> {
        let dt = iter.sort().datatype_sort()?;
        let ctor = dt.constructors.first()?;

        // Find set and keys fields
        let set_field = ctor.field("fld_set")?;
        let keys_field = ctor.field("fld_keys")?;

        let set = iter.clone().field_select(dt_name, "fld_set", set_field.sort.clone());
        let keys = iter.clone().field_select(dt_name, "fld_keys", keys_field.sort.clone());

        // Extract key sort from keys array (Array<usize, K>)
        let key_sort = keys_field.sort.array_sort()?.element_sort.clone();

        Some((set, keys, key_sort))
    }

    /// Creates a HashSet iterator struct.
    ///
    /// Part of #1751: Iterator membership invariant for CHC mode.
    /// Part of #1814: Use tracked_len if provided, otherwise symbolic.
    fn make_hashset_into_iter(
        &mut self,
        set: Expr,
        _dest_local: Option<usize>,
        tracked_len: Option<Expr>,
    ) -> Option<Expr> {
        let key_sort = set.sort().array_sort()?.index_sort.clone();
        let iter_sort_name = crate::codegen_ay::names::hashset_into_iter_sort_name(
            &crate::codegen_ay::names::sort_short_name(&key_sort),
        );

        let (keys, keys_sort) = self.make_symbolic_iter_keys("hashset_iter_keys", key_sort);

        // Part of #1814: Use tracked length if provided, otherwise symbolic
        let len = self.tracked_len_or_fresh(tracked_len, "hashset_iter_len");
        let iter_fields = names::hashset_iter_fields(set.sort().clone(), keys_sort);
        let ctor_fields = vec![set, keys, Self::iter_position_zero(), len];
        Some(self.make_collection_iter(IterConstructConfig {
            iter_sort_name: &iter_sort_name,
            iter_fields,
            ctor_fields,
        }))
    }
}
