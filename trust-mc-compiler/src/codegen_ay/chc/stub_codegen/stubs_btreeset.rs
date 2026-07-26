// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC stub implementations for BTreeSet types.
//! Converted from include!() to proper module per #2595.
//!
//! Split from stubs_collections.rs per #2139 for reviewability.
//! Consolidated to shared set helpers per #2308.

use super::stubs::StubKind;
use super::types::POINTER_WIDTH;
use super::{ChcCtx, CollectionCallResult, StubTranslateArgs};
use ay_bindings::Expr;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // =========================================================================
    // BTreeSet stub interception (Part of #1659)
    // D3 table-driven dispatch (Part of #2304)
    // =========================================================================

    /// Translates a BTreeSet operation to SMT expressions.
    ///
    /// BTreeSet is modeled as `Array<Key, Bool>` (per codegen_types_adt.rs:128):
    /// - Key sort derived from generic parameter
    /// - Bool: true = present, false = absent
    ///
    /// Part of #1659: CHC codegen for Phase 4 perf suite.
    /// Part of #2323: Aligned to Array<Key, Bool> encoding (was Datatype-wrapped).
    /// Part of #2308: Delegated insert/contains/remove to shared set helpers.
    pub(in crate::codegen_ay::chc) fn translate_btreeset_call(
        &mut self,
        stub: StubKind,
        args: &[rustc_public::mir::Operand],
        modified_locals: &std::collections::HashSet<usize>,
        dest_local: Option<usize>,
    ) -> Option<CollectionCallResult> {
        let ctx = StubTranslateArgs { args, modified_locals, dest_local };
        stub_dispatch!(self, stub, &ctx, "translate_btreeset_call",
            StubKind::BTreeSetNew      => translate_btreeset_new,
            StubKind::BTreeSetInsert   => translate_btreeset_insert,
            StubKind::BTreeSetContains => translate_btreeset_contains,
            StubKind::BTreeSetRemove   => translate_btreeset_remove,
            StubKind::BTreeSetLen      => translate_btreeset_len,
            StubKind::BTreeSetIsEmpty  => translate_btreeset_is_empty,
            StubKind::BTreeSetClear    => translate_btreeset_clear,
            StubKind::BTreeSetClone    => translate_btreeset_clone,
        )
    }

    // ===== BTreeSet handlers (D3 table-driven, Part of #2304) =====

    fn translate_btreeset_new(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        let len_zero = Some(Expr::bitvec_const(0u64, POINTER_WIDTH));
        self.translate_set_new_common(ctx.dest_local, len_zero)
    }

    fn translate_btreeset_insert(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_insert_full("BTreeSet", ctx.args, ctx.modified_locals, true)
    }

    fn translate_btreeset_contains(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_contains_full("BTreeSet", ctx.args, ctx.modified_locals)
    }

    fn translate_btreeset_remove(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_remove_full("BTreeSet", ctx.args, ctx.modified_locals, true)
    }

    fn translate_btreeset_len(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_len_full("btreeset", ctx.args, ctx.modified_locals)
    }

    fn translate_btreeset_is_empty(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_is_empty_full("btreeset", ctx.args, ctx.modified_locals)
    }

    fn translate_btreeset_clear(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        let len_zero = Some(Expr::bitvec_const(0u64, POINTER_WIDTH));
        self.translate_set_clear_common(ctx.args, ctx.modified_locals, len_zero)
    }

    fn translate_btreeset_clone(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_clone_common(ctx.args, ctx.modified_locals)
    }
}
