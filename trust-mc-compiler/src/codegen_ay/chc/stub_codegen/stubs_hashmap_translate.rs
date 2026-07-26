// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! HashMap/BTreeMap/TrustMcMap translation helpers.
//! Converted from include!() to proper module per #2595.
//!
//! Part of #3057: DT-free parallel-array encoding. HashMap<K,V> is modeled as:
//! - data array: Array(K, V)     — maps keys to values (main state variable)
//! - present:    Array(K, Bool)  — maps keys to membership (auxiliary state variable)
//!
//! No Datatype sorts involved.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::debug;

use super::codegen_expr_signedness::arg_signedness_or_fallback;
use super::{
    ChcCtx, CollectionCallResult, StubTranslateArgs, chc_fresh_name, declare_pending_var,
    record_type_sort_fallback,
};
use super::{
    stubs::StubKind,
    types::{POINTER_WIDTH, int_sort},
};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translates a HashMap call to a AY expression.
    ///
    /// Part of #788: HashMap interception for CHC codegen.
    /// Part of #3057: DT-free parallel-array encoding.
    pub(in crate::codegen_ay::chc) fn translate_hashmap_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        dest_local: Option<usize>,
    ) -> Option<CollectionCallResult> {
        let ctx = StubTranslateArgs { args, modified_locals, dest_local };
        stub_dispatch!(self, stub, &ctx, "translate_hashmap_call",
            StubKind::HashMapNew         => translate_map_new,
            StubKind::HashMapInsert      => translate_map_insert_full,
            StubKind::HashMapGet
            | StubKind::HashMapGetMut    => translate_map_get_full,
            StubKind::HashMapContainsKey => translate_map_contains_full,
            StubKind::HashMapRemove      => translate_map_remove_full,
            StubKind::HashMapLen         => translate_map_len,
            StubKind::HashMapIsEmpty     => translate_map_is_empty,
            StubKind::HashMapClear       => translate_map_clear_full,
            StubKind::HashMapClone       => translate_map_clone_full,
            StubKind::HashMapDrop        => translate_map_drop,
        )
    }

    /// Drop for abstracted map values has no observable state transition.
    fn translate_map_drop(&mut self, _ctx: &StubTranslateArgs<'_>) -> Option<CollectionCallResult> {
        Some(CollectionCallResult {
            map_update: None,
            map_update_fields: None,
            result: None,
            result_is_some: None,
            len_update: None,
            present_update: None,
            result_fields: None,
            constraints: vec![],
            force_error: false,
            aux_targets_dest: false,
        })
    }

    /// HashMap::new() → const_array(key_sort, default_val) with length 0.
    ///
    /// Part of #3057: No Option DT. The data array has a default value (symbolic),
    /// and the present array (handled by CollectionCallResult.present_update) is
    /// initialized to all-false in the state var registration.
    fn translate_map_new(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<CollectionCallResult> {
        let new_data = ctx
            .dest_local
            .and_then(|dest| {
                // Part of #3348: output_state_vars is indexed by state var index,
                // NOT by raw MIR local index. Use try_state_idx_for_local to map.
                let vec_idx = self.state_var_mgr.try_state_idx_for_local(dest)?;
                self.state_var_mgr.output_state_vars.get(vec_idx)
            })
            .and_then(|(_, sort)| {
                let arr = sort.array_sort()?;
                // Part of #3447: Record that HashMap default value is unconstrained
                // (symbolic value for unmapped keys — sound over-approximation).
                self.record_aggregate_gap("hashmap_default_value_unconstrained");
                let default_name = chc_fresh_name("hashmap_default");
                let default_val = declare_pending_var(default_name, arr.element_sort.clone());
                Some(Expr::const_array(arr.index_sort.clone(), default_val))
            })
            .unwrap_or_else(|| {
                record_type_sort_fallback("HashMap::new key+value sorts");
                // Part of #3447: Record that HashMap default value is unconstrained
                // (type-sort fallback already recorded above; this captures the
                // encoding gap for the symbolic default value itself).
                self.record_aggregate_gap("hashmap_default_type_sort_fallback");
                let default_name = chc_fresh_name("hashmap_default");
                let default_val = declare_pending_var(default_name, int_sort());
                Expr::const_array(int_sort(), default_val)
            });

        // Present array: const_array(key_sort, false) — no keys present initially.
        let present_update = new_data
            .sort()
            .array_sort()
            .map(|arr| Expr::const_array(arr.index_sort.clone(), Expr::bool_const(false)));

        Some(CollectionCallResult {
            map_update: None,
            map_update_fields: None,
            result: Some(new_data),
            result_is_some: None,
            len_update: Some(Expr::bitvec_const(0u64, POINTER_WIDTH)),
            present_update,
            result_fields: None,
            constraints: vec![],
            force_error: false,
            aux_targets_dest: true,
        })
    }

    /// Resolve data array, normalized key, and key signedness for keyed HashMap operations.
    fn resolve_map_and_key(
        &mut self,
        map_operand: &Operand,
        key_operand: &Operand,
        modified_locals: &HashSet<usize>,
        caller: &str,
    ) -> Option<(Expr, Expr, bool)> {
        let data = self.get_hashmap_arg(map_operand, modified_locals)?;
        let (key, key_is_signed) =
            self.resolve_map_key(key_operand, &data, modified_locals, caller)?;
        Some((data, key, key_is_signed))
    }

    /// Length update for insert: `ite(was_absent, old_len + 1, old_len)`.
    fn map_insert_len_update(
        &self,
        map_operand: &Operand,
        modified_locals: &HashSet<usize>,
        was_absent: &Expr,
    ) -> Option<Expr> {
        self.get_collection_len_var(map_operand, modified_locals).map(|(_, old_len)| {
            let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
            let new_len = old_len.clone().bvadd(one);
            Expr::ite(was_absent.clone(), new_len, old_len)
        })
    }

    /// Length update for remove: `ite(was_present, old_len - 1, old_len)`.
    fn map_remove_len_update(
        &self,
        map_operand: &Operand,
        modified_locals: &HashSet<usize>,
        was_present: &Expr,
    ) -> Option<Expr> {
        self.get_collection_len_var(map_operand, modified_locals).map(|(_, old_len)| {
            let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
            let new_len = old_len.clone().bvsub(one);
            Expr::ite(was_present.clone(), new_len, old_len)
        })
    }

    /// insert(k, v) → Option<V>: store(key, val), present=true, return old value.
    fn translate_map_insert_full(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        if ctx.args.len() < 3 {
            return None;
        }
        let (data, key, key_is_signed) = self.resolve_map_and_key(
            &ctx.args[0],
            &ctx.args[1],
            ctx.modified_locals,
            "translate_map_insert",
        )?;
        let val = self.translate_operand_with_modified(&ctx.args[2], ctx.modified_locals)?;

        // Present check: was the key already in the map?
        let present = self.get_hashmap_present_arg(&ctx.args[0], ctx.modified_locals)?;
        // Part of #3057: coerce key to match present array's index sort
        // (may differ from data array's sort if present was resolved via fallback).
        // Part of #3105: use actual key signedness instead of hardcoded unsigned.
        let pkey = self.convert_key_to_array_index(
            key.clone(),
            &present.sort().array_sort()?.index_sort,
            key_is_signed,
        );
        let was_present = present.clone().select(pkey.clone());
        let was_absent = was_present.clone().not();

        // Previous value at key (undefined if !was_present — caller handles).
        let prev_value = data.clone().select(key.clone());

        // Data update: store new value.
        // Part of #4212: coerce value to match data array element sort before store.
        let val = ChcCtx::coerce_store_value(data.sort(), val, false, &self.diagnostics);
        let new_data = data.store(key, val);

        // Present update: mark key as present.
        let new_present = present.store(pkey, Expr::bool_const(true));

        let len_update = self.map_insert_len_update(&ctx.args[0], ctx.modified_locals, &was_absent);

        Some(CollectionCallResult {
            map_update: Some(new_data),
            map_update_fields: None,
            result: Some(prev_value),
            result_is_some: Some(was_present),
            len_update,
            present_update: Some(new_present),
            result_fields: None,
            constraints: vec![],
            force_error: false,
            aux_targets_dest: false,
        })
    }

    /// get/get_mut(k) → Option<&V>: (present.select(key), data.select(key)).
    fn translate_map_get_full(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        if ctx.args.len() < 2 {
            return None;
        }
        let (data, key, key_is_signed) = self.resolve_map_and_key(
            &ctx.args[0],
            &ctx.args[1],
            ctx.modified_locals,
            "translate_map_get",
        )?;
        let present = self.get_hashmap_present_arg(&ctx.args[0], ctx.modified_locals)?;
        // Part of #3057: coerce key for present array (may have different index sort)
        // Part of #3105: use actual key signedness instead of hardcoded unsigned.
        let pkey = self.convert_key_to_array_index(
            key.clone(),
            &present.sort().array_sort()?.index_sort,
            key_is_signed,
        );
        let is_present = present.select(pkey);
        let value = data.select(key);

        Some(CollectionCallResult {
            map_update: None,
            map_update_fields: None,
            result: Some(value),
            result_is_some: Some(is_present),
            len_update: None,
            present_update: None,
            result_fields: None,
            constraints: vec![],
            force_error: false,
            aux_targets_dest: false,
        })
    }

    /// Full contains_key flow for HashMap (DT-free, Part of #3057).
    ///
    /// contains_key(&self, k) → present.select(key).
    fn translate_map_contains_full(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        if ctx.args.len() < 2 {
            return None;
        }
        let (_, key, key_is_signed) = self.resolve_map_and_key(
            &ctx.args[0],
            &ctx.args[1],
            ctx.modified_locals,
            "translate_map_contains",
        )?;
        let present = self.get_hashmap_present_arg(&ctx.args[0], ctx.modified_locals)?;
        // Part of #3057: coerce key for present array (may have different index sort)
        // Part of #3105: use actual key signedness instead of hardcoded unsigned.
        let pkey = self.convert_key_to_array_index(
            key,
            &present.sort().array_sort()?.index_sort,
            key_is_signed,
        );
        Some(CollectionCallResult::read_only(present.select(pkey)))
    }

    /// remove(k) → Option<V>: present=false, return old value (data unchanged).
    fn translate_map_remove_full(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        if ctx.args.len() < 2 {
            return None;
        }
        let (data, key, key_is_signed) = self.resolve_map_and_key(
            &ctx.args[0],
            &ctx.args[1],
            ctx.modified_locals,
            "translate_map_remove",
        )?;
        let present = self.get_hashmap_present_arg(&ctx.args[0], ctx.modified_locals)?;
        // Part of #3057: coerce key for present array (may have different index sort)
        // Part of #3105: use actual key signedness instead of hardcoded unsigned.
        let pkey = self.convert_key_to_array_index(
            key.clone(),
            &present.sort().array_sort()?.index_sort,
            key_is_signed,
        );
        let was_present = present.clone().select(pkey.clone());
        let prev_value = data.select(key);

        // Present update: mark key as absent. Data array is NOT updated —
        // stale data at absent keys is harmless and avoids a default-value dependency.
        let new_present = present.store(pkey, Expr::bool_const(false));

        let len_update =
            self.map_remove_len_update(&ctx.args[0], ctx.modified_locals, &was_present);

        Some(CollectionCallResult {
            map_update: None,
            map_update_fields: None,
            result: Some(prev_value),
            result_is_some: Some(was_present),
            len_update,
            present_update: Some(new_present),
            result_fields: None,
            constraints: vec![],
            force_error: false,
            aux_targets_dest: false,
        })
    }

    /// HashMap::len() → delegates to shared set_len_full with "hashmap" domain.
    fn translate_map_len(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<CollectionCallResult> {
        self.translate_set_len_full("hashmap", ctx.args, ctx.modified_locals)
    }

    /// HashMap::is_empty() → delegates to shared set_is_empty_full with "hashmap" domain.
    fn translate_map_is_empty(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        self.translate_set_is_empty_full("hashmap", ctx.args, ctx.modified_locals)
    }

    /// Full clear flow for HashMap (DT-free, Part of #3057).
    ///
    /// Replaces data array with symbolic defaults, resets present to all-false, length to 0.
    fn translate_map_clear_full(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        let data = self.get_hashmap_arg(ctx.args.first()?, ctx.modified_locals)?;
        let arr = data.sort().array_sort()?;
        // Part of #3447: cleared default element is unconstrained.
        self.record_aggregate_gap("hashmap_clear_default_unconstrained");
        let default_name = chc_fresh_name("hashmap_clear_default");
        let default_val = declare_pending_var(default_name, arr.element_sort.clone());
        let cleared_data = Expr::const_array(arr.index_sort.clone(), default_val);
        // Use present array's own index sort (may differ from data's in fallback).
        let present_idx = self
            .get_hashmap_present_arg(ctx.args.first()?, ctx.modified_locals)
            .and_then(|p| Some(p.sort().array_sort()?.index_sort.clone()))
            .unwrap_or_else(|| arr.index_sort.clone());
        let cleared_present = Expr::const_array(present_idx, Expr::bool_const(false));

        Some(CollectionCallResult {
            map_update: Some(cleared_data),
            map_update_fields: None,
            result: None,
            result_is_some: None,
            len_update: Some(Expr::bitvec_const(0u64, POINTER_WIDTH)),
            present_update: Some(cleared_present),
            result_fields: None,
            constraints: vec![],
            force_error: false,
            aux_targets_dest: false,
        })
    }

    /// Clone for HashMap — identity in SMT (value semantics).
    ///
    /// Part of #3348: Clone must also copy presence and len auxiliary vars to
    /// the destination. Without this, the cloned BTreeMap loses membership
    /// tracking and subsequent insert/get operations have disconnected presence.
    fn translate_map_clone_full(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<CollectionCallResult> {
        let source_operand = ctx.args.first()?;
        let data = self.get_hashmap_arg(source_operand, ctx.modified_locals)?;
        let present_update = self.get_hashmap_present_arg(source_operand, ctx.modified_locals);
        let len_update =
            self.get_collection_len_var(source_operand, ctx.modified_locals).map(|(_, expr)| expr);
        debug!(
            present = present_update.is_some(),
            len = len_update.is_some(),
            "translate_map_clone_full: copying aux vars to dest (#3348)"
        );
        Some(CollectionCallResult {
            map_update: None,
            map_update_fields: None,
            result: Some(data),
            result_is_some: None,
            len_update,
            present_update,
            result_fields: None,
            constraints: vec![],
            force_error: false,
            aux_targets_dest: true,
        })
    }

    /// Resolves a HashMap key: translate operand → normalize to array index sort.
    /// Returns `(coerced_key, key_is_signed)` so callers can reuse signedness
    /// for secondary coercions (e.g., present-array index sort).
    fn resolve_map_key(
        &mut self,
        operand: &Operand,
        data: &Expr,
        modified_locals: &HashSet<usize>,
        caller: &str,
    ) -> Option<(Expr, bool)> {
        let key_raw = self.translate_hashmap_key(operand, modified_locals)?;
        let key_is_signed = arg_signedness_or_fallback(
            operand,
            self.body.locals(),
            caller,
            crate::codegen_ay::shared::SignednessFallbackKind::Comparison,
        );
        let key = self.convert_key_to_array_index(
            key_raw,
            &data.sort().array_sort()?.index_sort,
            key_is_signed,
        );
        Some((key, key_is_signed))
    }
}
