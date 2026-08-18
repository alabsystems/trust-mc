// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC heap state tracking for memory modeling.
//! Converted from include!() to proper module per #2595.
//!
//! This module contains the ChcHeapState struct which tracks:
//! - Type-indexed memory arrays for scalable memory modeling
//! - Region-partitioned arrays for heap allocations
//! - SSA-style store chain accumulation
//! - Memory safety check tracking
//!
//! Extracted from codegen.rs per #1508 to improve maintainability.
//! Store chain and region methods split to sibling modules per design D2
//! (file-decomposition-500loc-compliance):
//! - `heap_store_chains.rs` -- store chain accumulation and draining
//! - `heap_regions.rs` -- region array management + sort_to_type_suffix
//! - `heap_state_alloc.rs` -- allocation + type-array management (Part of #4206)

use ay_bindings::{Expr, Sort};
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;

/// Heap state tracking for CHC memory modeling.
///
/// Enables abstract heap model for proving ALL of Rust, including references,
/// raw pointers, BigInt, HashMap, and arbitrary data structures.
///
/// Part of #869: CHC Ref/AddressOf encoding limitation fix.
#[derive(Debug, Default)]
pub(in crate::codegen_ay::chc) struct ChcHeapState {
    /// Type-indexed arrays: type_key -> (array_name, element_sort).
    /// Uses type signatures to partition memory for scalability.
    /// Array names use `Arc<str>` to share across `array_name_to_elem_sort` without cloning.
    pub(in crate::codegen_ay::chc) type_arrays: HashMap<Arc<str>, (Arc<str>, Sort)>,

    /// Next allocation object ID (compile-time counter).
    /// Each allocation gets a unique ID for freshness.
    pub(in crate::codegen_ay::chc) next_alloc_id: u32,

    /// Local variable addresses: local_idx -> (obj_id, address_var_name).
    /// Maps stack locals to their allocation ID and symbolic address name.
    pub(in crate::codegen_ay::chc) local_addresses: HashMap<usize, (u32, String)>,

    /// Reverse index: obj_id -> local_idx. Part of #2793: O(1) lookup
    /// replacing O(N) linear scan in `local_idx_for_obj_id`.
    pub(in crate::codegen_ay::chc) obj_id_to_local: HashMap<u32, usize>,

    /// Pending memory update constraints for current block.
    /// Collected during statement translation, emitted in rules.
    pub(in crate::codegen_ay::chc) pending_updates: Vec<Expr>,

    /// Pending memory safety checks for current block.
    /// Part of #1173, #1174, #1176: heap validity/bounds checks.
    pub(in crate::codegen_ay::chc) pending_checks: Vec<Expr>,

    /// Pending KINDED safety checks for the current block: conditions that
    /// carry an explicit `PropertyKind` and Kani-parity description (e.g. the
    /// rvalue-offset lane's "Offset in bytes overflows isize"). Drained by the
    /// rule emitters (transition_gen / fragment_gen) via
    /// `emit_error_rule_for_condition_with_kind` so the failing check gets a
    /// named per-property report line + exact-derivation attribution instead
    /// of the anonymous aggregate.
    pub(in crate::codegen_ay::chc) pending_kinded_checks:
        Vec<(Expr, trust_mc_core::violation::PropertyKind, Option<String>)>,

    /// Tracks which type-indexed arrays have been modified in the current block.
    /// After a store to arr_out, subsequent loads should use arr_out not arr_in.
    /// Part of #905: Fix SSA-style memory array tracking for loads after stores.
    pub(in crate::codegen_ay::chc) modified_arrays: HashSet<Arc<str>>,

    /// Accumulated store expressions for each array within current block (#1447).
    /// Instead of emitting one constraint per store (which creates inconsistent constraints),
    /// we accumulate nested store expressions and emit a single constraint at block end:
    /// `arr_out = store(store(arr_in, addr1, val1), addr2, val2)`
    /// Key: type_key (e.g., "i32")
    /// Value: (arr_out_name, accumulated_store_expr)
    pub(in crate::codegen_ay::chc) store_chains: HashMap<Arc<str>, (Arc<str>, Expr)>,

    /// Seeds from previously drained store chains. Part of #3528.
    ///
    /// When `drain_store_chains` emits constraints and clears `store_chains`,
    /// subsequent `build_memory_store` calls (e.g., in call handler Mem-level
    /// bridges) need to chain on top of the drained expression. Without seeds,
    /// they start from the input array, producing a conflicting constraint for
    /// the same `__out` variable.
    ///
    /// Key: type_key (same as `store_chains`)
    /// Value: the accumulated store expression from the previous drain
    pub(in crate::codegen_ay::chc) drained_store_chain_seeds: HashMap<Arc<str>, Expr>,

    /// Tracks if metadata arrays (obj_valid, obj_size) were modified in current block.
    /// Part of #1100 follow-up: Ensures output_args include __out versions after allocation.
    pub(in crate::codegen_ay::chc) metadata_arrays_modified: bool,

    /// Region-partitioned arrays for heap allocations (#1443).
    ///
    /// Maps allocation obj_id -> (region_array_name, element_sort).
    /// Per designs/archive/2026-02-01-heap-modeling-phase4.md Option B:
    /// Each heap allocation gets its own disjoint region array, preserving
    /// non-aliasing information that the flat array loses.
    ///
    /// Key: obj_id from heap allocation
    /// Value: (array_name like "_fn_region_1_bv8", element Sort)
    /// Note: Regions are never freed; they're statically partitioned per allocation site.
    pub(in crate::codegen_ay::chc) region_arrays: HashMap<u32, (Arc<str>, Sort)>,

    /// Reverse index: array_input_name -> element_sort. Part of #2793: O(1)
    /// lookup in `expected_store_chain_output_sort` replacing O(T+R) linear
    /// scan of `type_arrays` and `region_arrays` values.
    /// Keys use `Arc<str>` shared with `type_arrays`/`region_arrays` name values.
    pub(in crate::codegen_ay::chc) array_name_to_elem_sort: HashMap<Arc<str>, Sort>,

    /// Preallocated heap object IDs for relation signature setup.
    /// Used to keep heap allocations consistent with predeclared region arrays.
    pub(in crate::codegen_ay::chc) preallocated_heap_ids: VecDeque<u32>,

    /// Object ID reserved for the promoted constant memory region.
    /// Part of #2958: Promoted constants need a valid obj_id so bounds
    /// checks on `obj_valid[extract(63,32,addr)]` pass.
    pub(in crate::codegen_ay::chc) promoted_const_obj_id: u32,

    /// Base addresses used by `mirror_array_elements_to_flat_memory` per type key.
    /// Part of #3095: Stores the address expression used for flat-memory mirroring
    /// so that `build_into_vec_data_array` can read from the exact same address,
    /// avoiding pointer aliasing issues where PDR can't unify distinct
    /// symbolic variables that happen to have the same concrete value.
    pub(in crate::codegen_ay::chc) mirror_base_addrs: HashMap<Arc<str>, Expr>,

    /// Heap object IDs produced by `alloc_zeroed`.
    ///
    /// Part of #3685: typed reads may otherwise upgrade a raw `bv8` region to a
    /// late-created typed region with no zero-init constraints. Tracking zeroed
    /// allocations lets load-side code return the typed zero value until a write
    /// actually materializes a region/type array state for that object.
    pub(in crate::codegen_ay::chc) zeroed_heap_objects: HashSet<u32>,

    /// Concrete heap allocation sizes known at codegen time.
    ///
    /// This is a side-channel for solver-simplifying access bounds checks on
    /// constant object IDs. The authoritative heap metadata remains obj_size.
    pub(in crate::codegen_ay::chc) known_heap_alloc_sizes: HashMap<u32, u32>,

    /// Fresh heap object IDs minted for the backing buffer of an
    /// over-approximated, PROVABLY-VALID collection constructor (e.g.
    /// `<[T]>::into_vec` / `bounded_any`). Their allocation is known-live under
    /// safe-Rust preconditions, so `heap_access_checks` treats them as
    /// trivially valid (like stack locals) instead of emitting an
    /// `obj_valid[id]` select that would ride a free `obj_valid__out` and
    /// produce a spurious use-after-free counterexample.
    ///
    /// SOUNDNESS: only ids constructed by a provably-allocating collection stub
    /// are added here; a `Vec::from_raw_parts` pointer is never registered, so a
    /// genuinely-dangling Vec still fails its drop-validity check.
    pub(in crate::codegen_ay::chc) provably_valid_backing_ids: HashSet<u32>,

    /// Heap objects whose value for a specific type currently lives in a
    /// type-indexed overlay rather than the raw `bv8` region.
    ///
    /// Part of #3677: realloc's moved-copy constraints preserve destination
    /// values by writing type arrays. Later loads of that exact
    /// `(obj_id, type_key)` pair must prefer the typed array, but unrelated
    /// objects of the same type must still upgrade their own regions normally.
    pub(in crate::codegen_ay::chc) type_overlay_heap_objects: HashMap<u32, HashSet<Arc<str>>>,

    /// Tracks type array names actually read (SELECT), with per-block indices.
    /// Maps array_name -> set of basic block indices that read from the array.
    /// Arrays NOT in this map have their stored values never observed -- dead.
    /// Arrays whose reads ALL occur in error-only blocks can also be pruned.
    /// Part of #3184: read-only pruning. Part of #3436: error-path pruning.
    pub(in crate::codegen_ay::chc) read_used_type_arrays: HashMap<Arc<str>, HashSet<usize>>,

    /// Tracks type array names actually written (STORE), with per-block indices.
    /// Maps array_name -> set of basic block indices that write to the array.
    /// Write-only arrays (in this map but NOT in `read_used_type_arrays`)
    /// are dead: the solver need not maintain invariants over them.
    /// Part of #3184: dead array parameter elimination.
    /// Part of #3436: per-block write tracking enables per-block liveness.
    pub(in crate::codegen_ay::chc) write_used_type_arrays: HashMap<Arc<str>, HashSet<usize>>,

    /// Tracks which blocks access heap metadata arrays (obj_valid, obj_size).
    /// Part of #3436: per-block metadata liveness enables pruning obj_valid/obj_size
    /// from block relations that don't perform heap operations. Blocks NOT in this
    /// set carry obj_valid/obj_size as dead parameters, inflating arity.
    pub(in crate::codegen_ay::chc) metadata_accessed_blocks: HashSet<usize>,

    /// Part of #3608: Block-scoped store-to-load forwarding. Key: `(obj_id << 32) | offset`.
    /// Value: `(store_bb, stored_expr, store_type_key)`. Invalidated on symbolic
    /// stores (#3664).
    ///
    /// # Why the type key is recorded
    ///
    /// The map is keyed by `(obj_id, offset)` ALONE, across every type array, so
    /// the forwarded datum can have been written through a completely different
    /// Rust type than the one now reading it. `load_ptr_from_memory` used to
    /// report every forwarded term as [`crate::codegen_ay::provenance::MaybeLoc::Unknown`]
    /// for exactly that reason, and its one discriminating consumer
    /// (`recover_unsafe_cell_referent_address`) then re-tagged it as an address
    /// on a width test — a `u64` stored at the same address passes.
    ///
    /// The store side does know which type array it wrote, and that is the same
    /// evidence the typed-array select lane calls provenance: an array keyed by
    /// `ptr_T`/`ref_T` holds pointer data by the memory model's own definition.
    /// Recording it lets the load compare keys and answer `Known` when they
    /// match and `Unknown` when they do not, instead of guessing from a width.
    /// The value operand itself stays untyped (the wave-13 note in
    /// `provenance.rs`); this is the *declared type of the store*, not a tag on
    /// the datum.
    pub(in crate::codegen_ay::chc) store_forward_map: HashMap<u64, (usize, Expr, Arc<str>)>,

    /// Part of #3871: Persistent cross-block pointer forwarding for nested
    /// heap allocations (Box<Box<T>>). Key: `(obj_id << 32) | offset`.
    pub(in crate::codegen_ay::chc) region_pointer_forwards: HashMap<u64, Expr>,

    /// Cross-block vtable forwarding for wrapper-dyn values stored on the heap.
    ///
    /// Part of #4193: `Box::new(inner_box_dyn)` stores only the thin pointer in
    /// typed memory arrays, so later loads of that wrapper value lose the dyn
    /// payload's vtable. Keep the vtable side-channel keyed by the same
    /// constant-address split pointer used by `region_pointer_forwards`.
    pub(in crate::codegen_ay::chc) region_vtable_forwards: HashMap<u64, Expr>,

    /// Symbolic-address variant of `region_vtable_forwards`.
    ///
    /// Part of #4193: inline box stores often use exact symbolic pointer
    /// expressions (for example `fld_ptr(dyn_box)` or a typed-memory select
    /// rooted at that pointer) rather than a concrete `obj_id << 32` literal.
    /// Preserve those exact address expressions so later reads through the
    /// same symbolic address can recover the stored wrapper dyn vtable.
    pub(in crate::codegen_ay::chc) region_vtable_forward_exprs: HashMap<String, Expr>,
}

#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) struct HeapTransientRuleState {
    pub(super) pending_updates: Vec<Expr>,
    pub(super) pending_checks: Vec<Expr>,
    pub(super) modified_arrays: HashSet<Arc<str>>,
    pub(super) store_chains: HashMap<Arc<str>, (Arc<str>, Expr)>,
    pub(super) drained_store_chain_seeds: HashMap<Arc<str>, Expr>,
    pub(super) metadata_arrays_modified: bool,
    pub(super) mirror_base_addrs: HashMap<Arc<str>, Expr>,
    pub(super) store_forward_map: HashMap<u64, (usize, Expr, Arc<str>)>,
    pub(super) region_pointer_forwards: HashMap<u64, Expr>,
    pub(super) region_vtable_forwards: HashMap<u64, Expr>,
    pub(super) region_vtable_forward_exprs: HashMap<String, Expr>,
    pub(super) known_heap_alloc_sizes: HashMap<u32, u32>,
    pub(super) provably_valid_backing_ids: HashSet<u32>,
}

impl ChcHeapState {
    pub(in crate::codegen_ay::chc) fn new() -> Self {
        // obj_id 0 = null, obj_id 1 = promoted constants, normal allocs start at 2.
        Self {
            type_arrays: HashMap::new(),
            next_alloc_id: 2, // 0 = null, 1 = promoted constants
            local_addresses: HashMap::new(),
            obj_id_to_local: HashMap::new(),
            pending_updates: Vec::new(),
            pending_checks: Vec::new(),
            pending_kinded_checks: Vec::new(),
            modified_arrays: HashSet::new(),
            store_chains: HashMap::new(),
            drained_store_chain_seeds: HashMap::new(),
            metadata_arrays_modified: false,
            region_arrays: HashMap::new(),
            array_name_to_elem_sort: HashMap::new(),
            preallocated_heap_ids: VecDeque::new(),
            promoted_const_obj_id: 1,
            mirror_base_addrs: HashMap::new(),
            zeroed_heap_objects: HashSet::new(),
            known_heap_alloc_sizes: HashMap::new(),
            provably_valid_backing_ids: HashSet::new(),
            type_overlay_heap_objects: HashMap::new(),
            read_used_type_arrays: HashMap::new(),
            write_used_type_arrays: HashMap::new(),
            metadata_accessed_blocks: HashSet::new(),
            store_forward_map: HashMap::new(),
            region_pointer_forwards: HashMap::new(),
            region_vtable_forwards: HashMap::new(),
            region_vtable_forward_exprs: HashMap::new(),
        }
    }

    /// Invalidate all store-to-load forwarding entries.
    ///
    /// Called on Vec resize/realloc so forwarded values from before the resize
    /// don't bypass data array invalidation. Part of #3647.
    pub(in crate::codegen_ay::chc) fn invalidate_store_forwards(&mut self) {
        self.store_forward_map.clear();
        self.region_pointer_forwards.clear();
        self.region_vtable_forwards.clear();
        self.region_vtable_forward_exprs.clear();
    }

    /// Resets pending memory safety checks (called at block boundaries).
    pub(in crate::codegen_ay::chc) fn reset_pending_checks(&mut self) {
        self.pending_checks.clear();
        self.pending_kinded_checks.clear();
    }

    #[must_use]
    pub(in crate::codegen_ay::chc) fn snapshot_transient_rule_state(
        &self,
    ) -> HeapTransientRuleState {
        HeapTransientRuleState {
            pending_updates: self.pending_updates.clone(),
            pending_checks: self.pending_checks.clone(),
            modified_arrays: self.modified_arrays.clone(),
            store_chains: self.store_chains.clone(),
            drained_store_chain_seeds: self.drained_store_chain_seeds.clone(),
            metadata_arrays_modified: self.metadata_arrays_modified,
            mirror_base_addrs: self.mirror_base_addrs.clone(),
            store_forward_map: self.store_forward_map.clone(),
            region_pointer_forwards: self.region_pointer_forwards.clone(),
            region_vtable_forwards: self.region_vtable_forwards.clone(),
            region_vtable_forward_exprs: self.region_vtable_forward_exprs.clone(),
            known_heap_alloc_sizes: self.known_heap_alloc_sizes.clone(),
            provably_valid_backing_ids: self.provably_valid_backing_ids.clone(),
        }
    }

    pub(in crate::codegen_ay::chc) fn restore_transient_rule_state(
        &mut self,
        snapshot: &HeapTransientRuleState,
    ) {
        self.pending_updates = snapshot.pending_updates.clone();
        self.pending_checks = snapshot.pending_checks.clone();
        self.modified_arrays = snapshot.modified_arrays.clone();
        self.store_chains = snapshot.store_chains.clone();
        self.drained_store_chain_seeds = snapshot.drained_store_chain_seeds.clone();
        self.metadata_arrays_modified = snapshot.metadata_arrays_modified;
        self.mirror_base_addrs = snapshot.mirror_base_addrs.clone();
        self.store_forward_map = snapshot.store_forward_map.clone();
        self.region_pointer_forwards = snapshot.region_pointer_forwards.clone();
        self.region_vtable_forwards = snapshot.region_vtable_forwards.clone();
        self.region_vtable_forward_exprs = snapshot.region_vtable_forward_exprs.clone();
        self.known_heap_alloc_sizes = snapshot.known_heap_alloc_sizes.clone();
        self.provably_valid_backing_ids = snapshot.provably_valid_backing_ids.clone();
    }

    /// Marks a type-indexed array as modified (for SSA-style tracking).
    pub(in crate::codegen_ay::chc) fn mark_array_modified(&mut self, type_key: &str) {
        // Avoid allocating for repeated writes to the same type key in a block.
        if !self.modified_arrays.contains(type_key) {
            self.modified_arrays.insert(type_key.into());
        }
    }

    /// Checks if a type-indexed array has been modified in the current block.
    pub(in crate::codegen_ay::chc) fn is_array_modified(&self, type_key: &str) -> bool {
        self.modified_arrays.contains(type_key)
    }

    /// Records the base address used by `mirror_array_elements_to_flat_memory` for a type key.
    /// Part of #3095: Ensures `build_into_vec_data_array` can read from the exact same
    /// address that was used for the store, avoiding pointer aliasing issues.
    pub(in crate::codegen_ay::chc) fn set_mirror_base_addr(
        &mut self,
        type_key: &str,
        base_addr: Expr,
    ) {
        self.mirror_base_addrs.insert(type_key.into(), base_addr);
    }

    /// Returns the mirror base address for a type key, if recorded in this block.
    pub(in crate::codegen_ay::chc) fn get_mirror_base_addr(&self, type_key: &str) -> Option<&Expr> {
        self.mirror_base_addrs.get(type_key)
    }

    pub(in crate::codegen_ay::chc) fn mark_heap_obj_zeroed(&mut self, obj_id: u32) {
        self.zeroed_heap_objects.insert(obj_id);
    }

    pub(in crate::codegen_ay::chc) fn is_heap_obj_zeroed(&self, obj_id: u32) -> bool {
        self.zeroed_heap_objects.contains(&obj_id)
    }

    pub(in crate::codegen_ay::chc) fn mark_heap_obj_type_overlay(
        &mut self,
        obj_id: u32,
        type_key: &str,
    ) {
        self.type_overlay_heap_objects.entry(obj_id).or_default().insert(type_key.into());
    }

    pub(in crate::codegen_ay::chc) fn heap_obj_prefers_type_overlay(
        &self,
        obj_id: u32,
        type_key: &str,
    ) -> bool {
        self.type_overlay_heap_objects.get(&obj_id).is_some_and(|keys| keys.contains(type_key))
    }

    /// Look up a type array by type key. Returns (array_name, element_sort).
    /// Part of #3159: virtual dispatch inline memory load support.
    pub(in crate::codegen_ay::chc) fn lookup_type_array(
        &self,
        type_key: &str,
    ) -> Option<(&Arc<str>, &Sort)> {
        self.type_arrays.get(type_key).map(|(n, s)| (n, s))
    }

    /// Resets modified array tracking (called at block boundaries).
    /// Part of #3551: Also clears drained_store_chain_seeds to prevent cross-block leak.
    /// Part of #3664: Also clears store_forward_map to prevent stale forwarding across blocks.
    pub(in crate::codegen_ay::chc) fn reset_modified_arrays(&mut self) {
        self.modified_arrays.clear();
        self.store_chains.clear();
        self.drained_store_chain_seeds.clear();
        self.metadata_arrays_modified = false;
        self.mirror_base_addrs.clear();
        self.store_forward_map.clear();
    }

    /// Marks metadata arrays (obj_valid, obj_size) as modified.
    /// Part of #1100 follow-up: Called when allocation/deallocation occurs.
    pub(in crate::codegen_ay::chc) fn mark_metadata_arrays_modified(&mut self) {
        self.metadata_arrays_modified = true;
    }

    /// Checks if metadata arrays were modified in the current block.
    pub(in crate::codegen_ay::chc) fn are_metadata_arrays_modified(&self) -> bool {
        self.metadata_arrays_modified
    }
}
