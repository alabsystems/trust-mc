// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Collection and allocation call result types.
//!
//! Extracted from `types.rs` — Part of #4206.

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use std::collections::HashSet;

/// Result of translating a collection operation (Part of #788).
/// Separates collection updates from result values for operations like insert/remove.
/// Extended with length tracking for #1814 and presence tracking for #3057.
pub(in crate::codegen_ay::chc) struct CollectionCallResult {
    /// New data-array state (mutating operations only).
    pub(in crate::codegen_ay::chc) map_update: Option<Expr>,
    /// New flattened collection/iterator state for projected locals.
    ///
    /// Used when the translator can update scalar projection slots directly and
    /// avoid constructing a datatype only to decompose it again.
    pub(in crate::codegen_ay::chc) map_update_fields: Option<(usize, Vec<Option<Expr>>)>,
    /// Result value to store in destination (if any).
    /// For DT-free HashMap ops that return Option<V>: this is the payload `V`.
    pub(in crate::codegen_ay::chc) result: Option<Expr>,
    /// For DT-free HashMap returns where the result is a flattened Option<V>
    /// (Part of #3057): provides the `is_some` Bool expression. When present,
    /// `apply_collection_result` writes fld0=result_is_some, fld1=result
    /// instead of attempting DT Option decomposition.
    pub(in crate::codegen_ay::chc) result_is_some: Option<Expr>,
    /// New length value expression (Part of #1814).
    /// For insert: ite(was_absent, old_len + 1, old_len)
    /// For remove: ite(was_present, old_len - 1, old_len)
    /// For clear/new: bv_const(0)
    pub(in crate::codegen_ay::chc) len_update: Option<Expr>,
    /// New presence-array state for HashMap DT-free encoding (Part of #3057).
    /// For insert: present.store(key, true)
    /// For remove: present.store(key, false)
    /// For clear: const_array(key_sort, false)
    pub(in crate::codegen_ay::chc) present_update: Option<Expr>,
    /// Individual element fields for composite results (Part of #3057).
    /// For HashMap iterator next(): [key, value] — avoids constructing
    /// intermediate tuple Datatype that triggers ay#1766 (DT+BV).
    /// When present, consumers use these directly instead of decomposing `result`.
    pub(in crate::codegen_ay::chc) result_fields: Option<Vec<Expr>>,
    /// Additional soundness constraints (Part of #1813).
    pub(in crate::codegen_ay::chc) constraints: Vec<Expr>,
    /// Emit a conservative `error()` rule instead of a successor transition.
    ///
    /// Used by `forced_failure()` callers that intentionally fail closed when a
    /// collection translation encounters an unexpected sort/layout. Encoding that
    /// intent as a body `false` constraint was unsound for CHC because it killed
    /// the rule instead of surfacing the path as an error.
    pub(in crate::codegen_ay::chc) force_error: bool,
    /// When true, auxiliary updates (len, present) target the destination local
    /// instead of the source collection. Set by clone-like operations where the
    /// destination IS the new collection. Part of #3348.
    pub(in crate::codegen_ay::chc) aux_targets_dest: bool,
}

impl CollectionCallResult {
    /// Read-only collection call result: no map mutation, no length/present update, no constraints.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn read_only(result: Expr) -> Self {
        Self {
            map_update: None,
            map_update_fields: None,
            result: Some(result),
            result_is_some: None,
            len_update: None,
            present_update: None,
            result_fields: None,
            constraints: vec![],
            force_error: false,
            aux_targets_dest: false,
        }
    }

    /// New collection construction: returns a fresh collection with optional initial length.
    ///
    /// Used by `HashMap::new`, `HashSet::new`, and set-new fallback paths where the
    /// result is an empty collection value with no map mutation.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn new_collection(
        result: Expr,
        len_update: Option<Expr>,
    ) -> Self {
        Self {
            map_update: None,
            map_update_fields: None,
            result: Some(result),
            result_is_some: None,
            len_update,
            present_update: None,
            result_fields: None,
            constraints: vec![],
            force_error: false,
            aux_targets_dest: false,
        }
    }

    /// Mutating operation with a result value: updates collection state and returns a value.
    ///
    /// Used by `insert` (returns previous value), `remove` (returns removed value),
    /// and similar operations that both modify the collection and produce a result.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn mutating(
        map_update: Expr,
        result: Expr,
        len_update: Option<Expr>,
    ) -> Self {
        Self {
            map_update: Some(map_update),
            map_update_fields: None,
            result: Some(result),
            result_is_some: None,
            len_update,
            present_update: None,
            result_fields: None,
            constraints: vec![],
            force_error: false,
            aux_targets_dest: false,
        }
    }

    /// Clear operation: replaces collection state with no result value.
    ///
    /// Used by `clear()` and similar operations that reset the collection
    /// without producing a return value.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn clear(map_update: Expr, len_update: Option<Expr>) -> Self {
        Self {
            map_update: Some(map_update),
            map_update_fields: None,
            result: None,
            result_is_some: None,
            len_update,
            present_update: None,
            result_fields: None,
            constraints: vec![],
            force_error: false,
            aux_targets_dest: false,
        }
    }

    /// Forced verification failure: no state change, emit `error()` instead of goto.
    ///
    /// Used when a sort mismatch or unexpected encoding is detected and the
    /// translator intentionally wants to fail closed rather than over-approximate.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn forced_failure() -> Self {
        Self {
            map_update: None,
            map_update_fields: None,
            result: None,
            result_is_some: None,
            len_update: None,
            present_update: None,
            result_fields: None,
            constraints: vec![],
            force_error: true,
            aux_targets_dest: false,
        }
    }
}

/// Result of translating a heap allocation intrinsic call.
///
/// Part of #1100: AY heap allocation model.
pub(in crate::codegen_ay::chc) struct AllocTransitionBranch {
    /// Branch-specific result value to store in the destination local.
    ///
    /// When `None`, `AllocCallResult::result` is used as the shared default.
    pub(in crate::codegen_ay::chc) result: Option<Expr>,
    /// Additional transition constraints for this branch.
    ///
    /// Realloc uses this to emit separate moved/in-place CHC rules instead of
    /// encoding heap metadata updates with array-valued ITE expressions.
    pub(in crate::codegen_ay::chc) constraints: Vec<Expr>,
}

/// Result of translating a heap allocation intrinsic call.
///
/// Part of #1100: AY heap allocation model.
pub(in crate::codegen_ay::chc) struct AllocCallResult {
    /// Result value to store in destination (pointer for alloc/realloc, None for dealloc).
    pub(in crate::codegen_ay::chc) result: Option<Expr>,
    /// Heap state constraints using store() pattern (SSA-style updates):
    /// - obj_valid__out = store(obj_valid, id, true/false)
    /// - obj_size__out = store(obj_size, id, size)
    pub(in crate::codegen_ay::chc) heap_constraints: Vec<Expr>,
    /// Memory safety checks that must hold (emit error rule on violation).
    /// Part of #1173, #1174, #1176, #1177, #1178: heap validity/bounds checks.
    /// Violation: from_rel ∧ constraints ∧ !check → error()
    pub(in crate::codegen_ay::chc) safety_checks: Vec<Expr>,
    /// Allocation object ID assigned to the result pointer (Part of #3273).
    /// Used by `codegen_call_alloc` to record known alloc IDs for pointer
    /// tracing in realloc.
    pub(in crate::codegen_ay::chc) alloc_obj_id: Option<u32>,
    /// Branch-sensitive transition rules to emit instead of a single rule.
    ///
    /// When empty, `result` and `heap_constraints` form the only transition.
    pub(in crate::codegen_ay::chc) transition_branches: Vec<AllocTransitionBranch>,
}

/// Common arguments bundle for stub translation functions.
///
/// Part of #2304 (D3 table-driven dispatch): replaces the 3-5 parameter
/// spread across `translate_*` signatures with a single borrowed struct.
/// Each domain handler table uses `fn(&mut ChcCtx, &StubTranslateArgs) -> Option<R>`
/// as its uniform signature.
pub(in crate::codegen_ay::chc) struct StubTranslateArgs<'a> {
    /// MIR operands passed to the stub call.
    pub(in crate::codegen_ay::chc) args: &'a [Operand],
    /// Set of local indices modified in the current block (for output arg selection).
    pub(in crate::codegen_ay::chc) modified_locals: &'a HashSet<usize>,
    /// Destination local index for the call result (if any).
    pub(in crate::codegen_ay::chc) dest_local: Option<usize>,
}
