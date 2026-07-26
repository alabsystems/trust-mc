// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Heap allocation and type-array management helpers.
//!
//! Extracted from heap_state.rs for 500-line file-size compliance.
//! Part of #4206.

use ay_bindings::{Expr, Sort};
use std::sync::Arc;

use super::heap_state::ChcHeapState;

impl ChcHeapState {
    /// Allocates a fresh object ID for a new allocation.
    ///
    /// Returns `None` if allocation ID would overflow u32::MAX, matching the
    /// BMC path's `fresh_alloc_id()` graceful-failure pattern. Callers emit
    /// a warning and skip the allocation rather than crashing the compiler.
    pub(in crate::codegen_ay::chc) fn next_alloc_id(&mut self) -> Option<u32> {
        let id = self.next_alloc_id;
        self.next_alloc_id = id.checked_add(1)?;
        Some(id)
    }

    /// Reserves a heap allocation ID for predeclaring heap regions.
    ///
    /// Returns `None` on allocation ID overflow.
    pub(in crate::codegen_ay::chc) fn reserve_heap_alloc_id(&mut self) -> Option<u32> {
        let id = self.next_alloc_id()?;
        self.preallocated_heap_ids.push_back(id);
        Some(id)
    }

    /// Gets the next heap allocation ID, honoring any preallocated IDs.
    ///
    /// Returns `None` on allocation ID overflow (only reachable when
    /// preallocated queue is empty and `next_alloc_id` overflows).
    pub(in crate::codegen_ay::chc) fn next_heap_alloc_id(&mut self) -> Option<u32> {
        if let Some(id) = self.preallocated_heap_ids.pop_front() {
            return Some(id);
        }
        self.next_alloc_id()
    }

    /// Sets the next allocation ID counter. Test-only: enables overflow testing
    /// without iterating through u32::MAX allocations. Part of #2735.
    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(in crate::codegen_ay::chc) fn set_next_alloc_id(&mut self, id: u32) {
        self.next_alloc_id = id;
    }

    /// Returns the stack-local index that owns `obj_id`, if any.
    ///
    /// Stack locals are assigned object IDs during entry allocation and tracked in
    /// `local_addresses`. Heap allocations are not present in this map.
    pub(in crate::codegen_ay::chc) fn local_idx_for_obj_id(&self, obj_id: u32) -> Option<usize> {
        // Part of #2793: O(1) reverse-index lookup replacing O(N) linear scan.
        self.obj_id_to_local.get(&obj_id).copied()
    }

    /// Returns all obj_ids that are stack-local allocations (never freed).
    ///
    /// Part of #3159: Used by the dealloc stub to prevent the solver from
    /// assigning a symbolic dealloc pointer an obj_id that aliases with
    /// a stack local. Stack locals are valid for the entire function
    /// lifetime -- they are never freed.
    pub(in crate::codegen_ay::chc) fn stack_local_obj_ids(&self) -> Vec<u32> {
        self.obj_id_to_local.keys().copied().collect()
    }

    /// Inserts a local address mapping and updates the reverse index.
    /// Part of #2793: Encapsulates local_addresses mutation to keep
    /// obj_id_to_local in sync.
    pub(in crate::codegen_ay::chc) fn insert_local_address(
        &mut self,
        local_idx: usize,
        obj_id: u32,
        addr_name: String,
    ) {
        self.local_addresses.insert(local_idx, (obj_id, addr_name));
        self.obj_id_to_local.insert(obj_id, local_idx);
    }

    /// Records a concrete heap allocation size for a constant allocation ID.
    pub(in crate::codegen_ay::chc) fn record_heap_alloc_size(&mut self, obj_id: u32, size: u32) {
        self.known_heap_alloc_sizes.insert(obj_id, size);
    }

    /// Returns the concrete size of a heap allocation when it is known.
    pub(in crate::codegen_ay::chc) fn heap_alloc_size(&self, obj_id: u32) -> Option<u32> {
        self.known_heap_alloc_sizes.get(&obj_id).copied()
    }

    /// Marks a fresh obj_id as the backing buffer of a provably-valid,
    /// over-approximated collection constructor (see field docs).
    pub(in crate::codegen_ay::chc) fn mark_provably_valid_backing(&mut self, obj_id: u32) {
        self.provably_valid_backing_ids.insert(obj_id);
    }

    /// Whether `obj_id` is a provably-valid collection backing buffer.
    pub(in crate::codegen_ay::chc) fn is_provably_valid_backing(&self, obj_id: u32) -> bool {
        self.provably_valid_backing_ids.contains(&obj_id)
    }

    /// Gets or creates a type-indexed memory array for the given type key.
    ///
    /// Type-indexed arrays partition memory by type signature for scalability.
    /// Each array has sort `(Array bv64 elem_sort)` where bv64 is the address.
    ///
    /// Returns `(input_array_name, output_array_name, element_sort, is_new)`.
    /// When `is_new` is true, the array was just created and the caller MUST
    /// register it as a state variable pair via `push_state_var_pair_arc` to
    /// avoid "unknown constant" errors in Z3 (#2970).
    /// Names are `Arc<str>` to allow O(1) sharing across maps. Part of #2267 D3.
    pub(in crate::codegen_ay::chc) fn get_or_create_type_array(
        &mut self,
        type_key: &str,
        elem_sort: Sort,
        fn_name: &str,
    ) -> (Arc<str>, String, Sort, bool) {
        if let Some((arr_name, sort)) = self.type_arrays.get(type_key) {
            let o = crate::codegen_ay::names::out_name(arr_name);
            return (Arc::clone(arr_name), o, sort.clone(), false);
        }

        // Create new type array -- paired name generation from one buffer (Part of #2267).
        let (arr_name, out_name) = crate::codegen_ay::names::mem_array_name_pair(fn_name, type_key);
        self.type_arrays.insert(type_key.into(), (Arc::clone(&arr_name), elem_sort.clone()));
        self.array_name_to_elem_sort.insert(Arc::clone(&arr_name), elem_sort.clone());
        (arr_name, out_name, elem_sort, true)
    }

    /// Record that a block accesses heap metadata arrays (obj_valid, obj_size).
    ///
    /// Called when a block performs SELECT or STORE on obj_valid/obj_size.
    /// Part of #3436: per-block metadata liveness tracking. Blocks NOT recorded
    /// here can have obj_valid/obj_size pruned from their relation signatures.
    pub(in crate::codegen_ay::chc) fn mark_metadata_accessed(&mut self, bb_idx: usize) {
        self.metadata_accessed_blocks.insert(bb_idx);
    }

    /// Mark a type-indexed array as read (SELECT operation) in a specific block.
    ///
    /// Part of #3184: Arrays marked as read survive dead-array pruning.
    /// Part of #3436: Per-block tracking enables error-path-aware pruning --
    /// arrays read ONLY in blocks that cannot reach Return are error-path-only
    /// and can be pruned alongside write-only arrays.
    pub(in crate::codegen_ay::chc) fn mark_type_array_read(
        &mut self,
        arr_name: &Arc<str>,
        bb_idx: usize,
    ) {
        self.read_used_type_arrays.entry(Arc::clone(arr_name)).or_default().insert(bb_idx);
    }

    /// Mark a type-indexed array as written (STORE operation) in a specific block.
    ///
    /// Part of #3184: Write-only arrays can be pruned from relation signatures.
    /// Part of #3436: Per-block write tracking enables per-block liveness.
    pub(in crate::codegen_ay::chc) fn mark_type_array_written(
        &mut self,
        arr_name: &Arc<str>,
        bb_idx: usize,
    ) {
        self.write_used_type_arrays.entry(Arc::clone(arr_name)).or_default().insert(bb_idx);
    }

    /// Allocates a fresh object ID for a promoted constant.
    ///
    /// Promoted constants share the same `obj_valid` / `obj_size` namespace as
    /// heap and stack objects, so they must consume IDs from the same counter to
    /// avoid collisions.
    pub(in crate::codegen_ay::chc) fn next_promoted_const_obj_id(&mut self) -> Option<u32> {
        self.next_alloc_id()
    }

    /// Returns the split-pointer address for the promoted constant memory region.
    /// Part of #2958: Use proper obj_id so `obj_valid[extract(63,32,addr)]` checks pass.
    pub(in crate::codegen_ay::chc) fn promoted_const_address(&self) -> Expr {
        self.promoted_const_address_for(self.promoted_const_obj_id)
    }

    /// Returns the split-pointer base address for a promoted constant object ID.
    pub(in crate::codegen_ay::chc) fn promoted_const_address_for(&self, obj_id: u32) -> Expr {
        Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32))
    }
}
