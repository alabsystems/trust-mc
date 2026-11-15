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
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::sync::Arc;

/// Heap state tracking for CHC memory modeling.
///
/// Enables abstract heap model for proving ALL of Rust, including references,
/// raw pointers, BigInt, HashMap, and arbitrary data structures.
///
/// Part of #869: CHC Ref/AddressOf encoding limitation fix.
#[derive(Debug, Default)]
pub(in crate::codegen_ay::chc) struct ChcHeapState {
    /// Native deferred allocations have an exact MIR site. An unhandled site
    /// cannot leave a FIFO reservation for a different allocator to consume.
    pub(in crate::codegen_ay::chc) native_uninit_reservations: HashMap<usize, u32>,
    /// Type-indexed arrays: type_key -> (array_name, element_sort).
    /// Uses type signatures to partition memory for scalability.
    /// Array names use `Arc<str>` to share across `array_name_to_elem_sort` without cloning.
    /// Ordered by type key: several passes iterate it to declare state
    /// variables (relation columns) and emit conjuncts, and a `HashMap` here
    /// gave one harness differently ordered CHC text from run to run.
    pub(in crate::codegen_ay::chc) type_arrays: BTreeMap<Arc<str>, (Arc<str>, Sort)>,

    /// Next allocation object ID (compile-time counter).
    /// Each allocation gets a unique ID for freshness.
    pub(in crate::codegen_ay::chc) next_alloc_id: u32,

    /// Local variable addresses: local_idx -> (obj_id, address_var_name).
    /// Maps stack locals to their allocation ID and symbolic address name.
    pub(in crate::codegen_ay::chc) local_addresses: HashMap<usize, (u32, String)>,

    /// Reverse index: obj_id -> local_idx. Part of #2793: O(1) lookup
    /// replacing O(N) linear scan in `local_idx_for_obj_id`.
    pub(in crate::codegen_ay::chc) obj_id_to_local: HashMap<u32, usize>,

    /// Address-taken stack locals whose observed address is a nondeterministic
    /// base state variable (heap/stack_address.rs).
    pub(in crate::codegen_ay::chc) stack_bases: Vec<super::stack_address::StackBase>,

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

    /// Tracks whether `obj_valid` was written in the current block, so later
    /// reads and writes in the block chain on `obj_valid__out`.
    /// Part of #1100 follow-up: Ensures output_args include __out versions after allocation.
    ///
    /// Tracked per lane, with [`Self::obj_size_modified`]: a site that writes
    /// one lane (a null or dangling pointer invalidates `obj_valid` only,
    /// `into_boxed_str` resizes `obj_size` only) must leave the other lane's
    /// INPUT variable in the head. Marking both put an `__out` the rule never
    /// binds into the head, which is a havoc of that lane (see
    /// `ChcCtx::mark_obj_valid_modified`).
    pub(in crate::codegen_ay::chc) obj_valid_modified: bool,

    /// Tracks whether `obj_size` was written in the current block (see
    /// [`Self::obj_valid_modified`]).
    pub(in crate::codegen_ay::chc) obj_size_modified: bool,

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
    /// Ordered by object id, for the same reason as `type_arrays`.
    pub(in crate::codegen_ay::chc) region_arrays: BTreeMap<u32, (Arc<str>, Sort)>,

    /// Reverse index: array_input_name -> element_sort. Part of #2793: O(1)
    /// lookup in `expected_store_chain_output_sort` replacing O(T+R) linear
    /// scan of `type_arrays` and `region_arrays` values.
    /// Keys use `Arc<str>` shared with `type_arrays`/`region_arrays` name values.
    pub(in crate::codegen_ay::chc) array_name_to_elem_sort: HashMap<Arc<str>, Sort>,

    /// Preallocated heap object IDs for relation signature setup.
    /// Used to keep heap allocations consistent with predeclared region arrays.
    pub(in crate::codegen_ay::chc) preallocated_heap_ids: VecDeque<u32>,

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

    /// Heap object IDs produced by the direct `libc::malloc` model.
    ///
    /// Part of #3175: a raw C allocation is untyped storage whose ONLY readers
    /// are the memory arrays (region / type overlay). That is what makes a
    /// whole-object `libc::memset` fill expressible: every reader of the object
    /// sees the stores. It is NOT true of a stack local's address object (read
    /// through its state variable) nor of a collection's backing buffer (read
    /// through the collection's logical data array), so the memset model admits
    /// only the objects recorded here rather than any object with a known size.
    pub(in crate::codegen_ay::chc) c_malloc_objects: HashSet<u32>,

    /// Concrete heap allocation sizes known at codegen time.
    ///
    /// This is a side-channel for solver-simplifying access bounds checks on
    /// constant object IDs. The authoritative heap metadata remains obj_size.
    pub(in crate::codegen_ay::chc) known_heap_alloc_sizes: HashMap<u32, u32>,

    /// Requested alignment guaranteed by an actual allocator operation.
    /// Unknown layouts remain unknown when speculative paths are combined;
    /// pointer bits and a matching pointee sort provide no such guarantee.
    pub(super) heap_alloc_alignments: HashMap<u32, Option<u64>>,

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

    /// Heap object ids allocated while a block INSIDE a modifies-frame extent
    /// was being encoded, keyed by frame index.
    ///
    /// DFCC freshness: storage the checked function itself created is
    /// assignable whatever the `modifies` clause says, and that is as true of a
    /// `Box::new` inside the function as of a stack local. Only stack locals
    /// were exempt, so `#[kani::modifies(a)] fn f(a: &mut u32) { let mut bx =
    /// Box::new(0); *bx = 1; *a = *bx; }` was accused: its
    /// `proof_for_contract` harness was FAILED [AY:CTREX_CAT:Genuine] on a
    /// `memory_safety` check (negative/modifies_frame_shapes.rs
    /// ::box_local_store_safe, measured on main and on m3/soundness-fixes-2).
    pub(in crate::codegen_ay::chc) frame_fresh_heap_objs: HashMap<usize, HashSet<u32>>,

    /// The modifies frame the block now being encoded belongs to, if any.
    /// Set at block entry; read by `next_heap_alloc_id`.
    pub(in crate::codegen_ay::chc) current_modifies_frame: Option<usize>,

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

    /// Writes recorded in the current rule: every [`Self::accumulate_store`],
    /// plus each write through a deref the inline walker executes, including
    /// the ones it applies to a local or skips ([`Self::note_write`]). Only
    /// its growth over a span means anything ([`Self::write_mark`],
    /// [`Self::written_since`]); a drop consumer asks whether the body it
    /// walked wrote. Part of the transient rule state, so a rolled-back
    /// speculative walk takes its writes with it.
    write_generation: u64,

    /// Memory EFFECTS recorded in the current rule: every
    /// [`Self::accumulate_store`] and every allocation-metadata write
    /// ([`Self::mark_obj_valid_modified`] and friends), plus the walker's
    /// mutable-static mirror ([`Self::note_memory_effect`]). Unlike
    /// [`Self::write_generation`] it does not count writes the walker applies
    /// to a local, so its growth over a walked branch arm means the arm left an
    /// effect the host applies unguarded (`inline_walk_guard.rs`). Transient,
    /// like `write_generation`.
    effect_generation: u64,

    /// Objects that took a store of a sort different from their region
    /// array's (`try_store_to_region`'s true mismatch branch): the store went
    /// to the type-indexed array only, so a later region read of the object
    /// misses it. Monotone for the harness; NOT transient.
    pub(in crate::codegen_ay::chc) region_diverged: HashSet<u32>,
    /// Objects read through their region array (`try_load_from_region`), so a
    /// divergence recorded after the read (in encoding order) is still caught.
    /// Monotone for the harness; NOT transient.
    pub(in crate::codegen_ay::chc) region_loaded_objs: HashSet<u32>,
    /// Region objects that took a store of a field's sort, and of their own
    /// sort, outside a store writing both views (`heap_unsize_alias.rs`).
    /// Monotone for the harness; NOT transient.
    pub(in crate::codegen_ay::chc) field_view_store_objs: HashSet<u32>,
    pub(in crate::codegen_ay::chc) whole_view_store_objs: HashSet<u32>,
    /// Depth of `with_coherent_object_stores`.
    pub(in crate::codegen_ay::chc) coherent_object_stores: u32,
    /// Every typed-memory write and read of a heap object, judged once the
    /// body is encoded (`heap_view_ledger.rs`). Monotone for the harness: a
    /// snapshot restore keeps it, since restored branch arms of a walk still
    /// encode real paths, and a write kept from a rolled-back attempt only
    /// makes the judgement more conservative.
    pub(in crate::codegen_ay::chc) view_ledger: super::heap_view_ledger::HeapViewLedger,
    /// The block being encoded (set by `encode_block_statements`), so an
    /// allocation made during encoding can record where it was made.
    pub(in crate::codegen_ay::chc) encode_bb: usize,
    /// The block each heap object was allocated in while blocks were encoded.
    pub(in crate::codegen_ay::chc) alloc_block: HashMap<u32, usize>,
    /// For each bounds check through a symbolic object lane: the block it was
    /// encoded in and the next allocation id at that time
    /// (`symbolic_lane_size`, the size choice of `symbolic_lane_bounds`).
    pub(in crate::codegen_ay::chc) symbolic_lane_checks: std::cell::RefCell<Vec<(usize, u32)>>,
    /// The locals whose address the body takes (`symbolic_lane_size`).
    pub(in crate::codegen_ay::chc) address_taken_locals: std::cell::OnceCell<HashSet<usize>>,
    /// Heap allocations whose size is symbolic: the allocator stored a
    /// non-constant size in `obj_size` (`record_known_heap_alloc_size_expr`).
    /// Monotone for the harness; NOT transient (an id of a rolled-back walk
    /// names no object a pointer can reach).
    pub(in crate::codegen_ay::chc) symbolic_size_heap_ids: HashSet<u32>,
    /// Every object an integer-to-pointer result named by a constant,
    /// non-null object lane that is no literal address
    /// (`invalidate_int_to_ptr_object`), with whether an object of that number
    /// had been allocated when the cast was encoded. An access through such a
    /// lane reads `obj_valid`, where the invalidation landed, and fails closed
    /// when the object's validity is not the invalidation's to decide: a stack
    /// slot or a provably-valid backing (whose accesses otherwise take
    /// validity as given), or an object allocated after the cast (whose
    /// allocation re-validates it) (`heap_access_checks`). Monotone for the
    /// harness; NOT transient.
    pub(in crate::codegen_ay::chc) int_to_ptr_named_lanes: HashMap<u32, bool>,
    /// Constant object lanes some access check took to be valid without
    /// reading `obj_valid` (a stack slot, a provably-valid backing), so an
    /// integer-to-pointer cast naming one that is encoded after such an
    /// access, which a loop may run before it, fails closed at the cast
    /// (`invalidate_int_to_ptr_object`). Also every constant lane any access
    /// check was encoded through, for a cast naming an object not yet
    /// allocated. Monotone for the harness; NOT transient.
    pub(in crate::codegen_ay::chc) assumed_valid_lanes: std::cell::RefCell<HashSet<u32>>,
    /// `Vec::with_capacity` buffers whose `Vec` may grow, each with the freed
    /// Bool its recorded size is checked under (`taint_vec_capacity_size`).
    /// Monotone for the harness; NOT transient.
    pub(in crate::codegen_ay::chc) vec_capacity_size_taints: HashMap<u32, Expr>,
    pub(in crate::codegen_ay::chc) accessed_const_lanes: std::cell::RefCell<HashSet<u32>>,
    /// Fresh values the walker returns for a read it fails closed on
    /// (`havoc_for_place`, whose reason is FailClose). An access through a
    /// pointer built from one takes no symbolic-lane bound
    /// (`heap_access_checks`). Monotone for the harness; NOT transient.
    pub(in crate::codegen_ay::chc) fail_closed_havocs: HashSet<String>,
    /// Set while the walker reads a receiver's fields ahead of its body
    /// (`inline_field_map.rs::extend_field_map_for_param`). Those reads are
    /// eager: every field of the receiver's pointee type is read whether the
    /// body reads it or not, at whatever address the receiver term holds,
    /// so their accesses are not the program's. A read through a symbolic
    /// object lane takes no bound then (`heap_access_checks`), as before
    /// lostwrite round 1; a field the field map reads as a scalar never took
    /// any check.
    pub(in crate::codegen_ay::chc) preloading_self_fields: bool,
    /// Per object, each unsize alias decision: its block and whether the
    /// whole view was republished. Monotone for the harness; NOT transient.
    pub(in crate::codegen_ay::chc) unsize_alias_decisions: HashMap<u32, Vec<(usize, bool)>>,

    /// Objects allocated while the outermost inline walk is active (`Some`
    /// only then; `with_inline_walk_write_mark` sets and clears it). No state
    /// variable of the host holds such an object, so a walker store into it
    /// is exact for the host (`classify_inline_walk_lane_store`, F3 widened).
    /// Grows only; a rolled-back speculative walk leaves its ids, which name
    /// objects nothing else allocated.
    pub(in crate::codegen_ay::chc) inline_walk_alloc_ids: Option<HashSet<u32>>,

    /// Rule C's backstop (design trust-mc-reds-final §4.3,
    /// `memory_cell_backstop.rs`): every type-indexed store at a constant
    /// address, as `(address, type key)`, in every block, in encoding order.
    /// Rolled back with a speculative walk (its length is part of the
    /// transient rule state), so a discarded store does not count.
    pub(in crate::codegen_ay::chc) constant_cell_stores: Vec<(u64, Arc<str>)>,
    /// Every type-indexed select at a constant address. Rolled back like
    /// [`Self::constant_cell_stores`].
    pub(in crate::codegen_ay::chc) constant_cell_loads: Vec<ConstantCellLoad>,
}

/// A type-indexed select at a constant address (Rule C's backstop).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct ConstantCellLoad {
    /// `(obj_id << 32) | offset`, the select's index.
    pub(in crate::codegen_ay::chc) addr: u64,
    /// The type key the select read under.
    pub(in crate::codegen_ay::chc) type_key: Arc<str>,
    /// The array variable the select read (its current input name).
    pub(in crate::codegen_ay::chc) array: Arc<str>,
}

/// [`ChcHeapState::write_generation`] at one point, to compare against later.
/// A mark taken later in the same rule is greater exactly when a write was
/// recorded (and kept) in between.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::codegen_ay::chc) struct HeapWriteMark(u64);

#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) struct HeapTransientRuleState {
    pub(super) pending_updates: Vec<Expr>,
    pub(super) pending_checks: Vec<Expr>,
    pub(super) modified_arrays: HashSet<Arc<str>>,
    pub(super) store_chains: HashMap<Arc<str>, (Arc<str>, Expr)>,
    pub(super) drained_store_chain_seeds: HashMap<Arc<str>, Expr>,
    pub(super) obj_valid_modified: bool,
    pub(super) obj_size_modified: bool,
    pub(super) mirror_base_addrs: HashMap<Arc<str>, Expr>,
    pub(super) store_forward_map: HashMap<u64, (usize, Expr, Arc<str>)>,
    pub(super) region_pointer_forwards: HashMap<u64, Expr>,
    pub(super) region_vtable_forwards: HashMap<u64, Expr>,
    pub(super) region_vtable_forward_exprs: HashMap<String, Expr>,
    pub(super) known_heap_alloc_sizes: HashMap<u32, u32>,
    pub(super) heap_alloc_alignments: HashMap<u32, Option<u64>>,
    pub(super) provably_valid_backing_ids: HashSet<u32>,
    pub(super) write_generation: u64,
    pub(super) effect_generation: u64,
    pub(super) constant_cell_stores_len: usize,
    pub(super) constant_cell_loads_len: usize,
}

impl ChcHeapState {
    pub(in crate::codegen_ay::chc) fn new() -> Self {
        // obj_id 0 = null, obj_id 1 = promoted constants, normal allocs start at 2.
        Self {
            native_uninit_reservations: HashMap::new(),
            type_arrays: BTreeMap::new(),
            next_alloc_id: 2, // 0 = null, 1 = promoted constants
            local_addresses: HashMap::new(),
            obj_id_to_local: HashMap::new(),
            stack_bases: Vec::new(),
            pending_updates: Vec::new(),
            pending_checks: Vec::new(),
            pending_kinded_checks: Vec::new(),
            modified_arrays: HashSet::new(),
            store_chains: HashMap::new(),
            drained_store_chain_seeds: HashMap::new(),
            obj_valid_modified: false,
            obj_size_modified: false,
            region_arrays: BTreeMap::new(),
            array_name_to_elem_sort: HashMap::new(),
            preallocated_heap_ids: VecDeque::new(),
            mirror_base_addrs: HashMap::new(),
            zeroed_heap_objects: HashSet::new(),
            c_malloc_objects: HashSet::new(),
            known_heap_alloc_sizes: HashMap::new(),
            heap_alloc_alignments: HashMap::new(),
            provably_valid_backing_ids: HashSet::new(),
            type_overlay_heap_objects: HashMap::new(),
            read_used_type_arrays: HashMap::new(),
            write_used_type_arrays: HashMap::new(),
            metadata_accessed_blocks: HashSet::new(),
            store_forward_map: HashMap::new(),
            region_pointer_forwards: HashMap::new(),
            region_vtable_forwards: HashMap::new(),
            region_vtable_forward_exprs: HashMap::new(),
            frame_fresh_heap_objs: HashMap::new(),
            current_modifies_frame: None,
            write_generation: 0,
            effect_generation: 0,
            region_diverged: HashSet::new(),
            region_loaded_objs: HashSet::new(),
            field_view_store_objs: HashSet::new(),
            whole_view_store_objs: HashSet::new(),
            coherent_object_stores: 0,
            view_ledger: Default::default(),
            encode_bb: 0,
            alloc_block: HashMap::new(),
            symbolic_lane_checks: Default::default(),
            address_taken_locals: Default::default(),
            preloading_self_fields: false,
            symbolic_size_heap_ids: HashSet::new(),
            int_to_ptr_named_lanes: HashMap::new(),
            assumed_valid_lanes: Default::default(),
            vec_capacity_size_taints: HashMap::new(),
            accessed_const_lanes: Default::default(),
            fail_closed_havocs: HashSet::new(),
            unsize_alias_decisions: HashMap::new(),
            inline_walk_alloc_ids: None,
            constant_cell_stores: Vec::new(),
            constant_cell_loads: Vec::new(),
        }
    }

    /// Record a write to memory the rule's heap arrays may not show (see
    /// `write_generation`).
    pub(in crate::codegen_ay::chc) fn note_write(&mut self) {
        self.write_generation += 1;
    }

    /// Record a memory effect that is not a heap-array store (see
    /// `effect_generation`); every store already counts through
    /// [`Self::accumulate_store`].
    pub(in crate::codegen_ay::chc) fn note_memory_effect(&mut self) {
        self.effect_generation += 1;
    }

    /// Whether `obj_id` was allocated during the active inline walk (see
    /// `inline_walk_alloc_ids`).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn inline_walk_allocated(&self, obj_id: u32) -> bool {
        self.inline_walk_alloc_ids.as_ref().is_some_and(|ids| ids.contains(&obj_id))
    }

    /// The memory-effect count now (see `effect_generation`).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn effect_mark(&self) -> u64 {
        self.effect_generation
    }

    /// The write count now, for [`Self::written_since`].
    #[must_use]
    pub(in crate::codegen_ay::chc) fn write_mark(&self) -> HeapWriteMark {
        HeapWriteMark(self.write_generation)
    }

    /// Whether a write was recorded after `mark` was taken (and not rolled
    /// back since).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn written_since(&self, mark: HeapWriteMark) -> bool {
        self.write_generation > mark.0
    }

    /// How many writes were recorded after `mark` was taken (and not rolled
    /// back since).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn writes_since(&self, mark: HeapWriteMark) -> u64 {
        self.write_generation.saturating_sub(mark.0)
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
            obj_valid_modified: self.obj_valid_modified,
            obj_size_modified: self.obj_size_modified,
            mirror_base_addrs: self.mirror_base_addrs.clone(),
            store_forward_map: self.store_forward_map.clone(),
            region_pointer_forwards: self.region_pointer_forwards.clone(),
            region_vtable_forwards: self.region_vtable_forwards.clone(),
            region_vtable_forward_exprs: self.region_vtable_forward_exprs.clone(),
            known_heap_alloc_sizes: self.known_heap_alloc_sizes.clone(),
            heap_alloc_alignments: self.heap_alloc_alignments.clone(),
            provably_valid_backing_ids: self.provably_valid_backing_ids.clone(),
            write_generation: self.write_generation,
            effect_generation: self.effect_generation,
            constant_cell_stores_len: self.constant_cell_stores.len(),
            constant_cell_loads_len: self.constant_cell_loads.len(),
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
        self.obj_valid_modified = snapshot.obj_valid_modified;
        self.obj_size_modified = snapshot.obj_size_modified;
        self.mirror_base_addrs = snapshot.mirror_base_addrs.clone();
        self.store_forward_map = snapshot.store_forward_map.clone();
        self.region_pointer_forwards = snapshot.region_pointer_forwards.clone();
        self.region_vtable_forwards = snapshot.region_vtable_forwards.clone();
        self.region_vtable_forward_exprs = snapshot.region_vtable_forward_exprs.clone();
        self.known_heap_alloc_sizes = snapshot.known_heap_alloc_sizes.clone();
        self.heap_alloc_alignments = snapshot.heap_alloc_alignments.clone();
        self.provably_valid_backing_ids = snapshot.provably_valid_backing_ids.clone();
        self.write_generation = snapshot.write_generation;
        self.effect_generation = snapshot.effect_generation;
        // The logs only grow between a snapshot and its restore.
        self.constant_cell_stores.truncate(snapshot.constant_cell_stores_len);
        self.constant_cell_loads.truncate(snapshot.constant_cell_loads_len);
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

    /// Record `obj_id` as the result of the direct `libc::malloc` model.
    /// See [`Self::c_malloc_objects`].
    pub(in crate::codegen_ay::chc) fn mark_c_malloc_obj(&mut self, obj_id: u32) {
        self.c_malloc_objects.insert(obj_id);
    }

    /// Whether `obj_id` is a raw C allocation from the `libc::malloc` model.
    pub(in crate::codegen_ay::chc) fn is_c_malloc_obj(&self, obj_id: u32) -> bool {
        self.c_malloc_objects.contains(&obj_id)
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
        self.obj_valid_modified = false;
        self.obj_size_modified = false;
        self.mirror_base_addrs.clear();
        self.store_forward_map.clear();
    }

    /// Marks both metadata arrays (obj_valid, obj_size) as modified.
    /// Part of #1100 follow-up: Called when allocation/deallocation occurs.
    pub(in crate::codegen_ay::chc) fn mark_metadata_arrays_modified(&mut self) {
        self.effect_generation += 1;
        self.obj_valid_modified = true;
        self.obj_size_modified = true;
    }

    /// Marks only `obj_valid` as modified (see [`Self::obj_valid_modified`]).
    pub(in crate::codegen_ay::chc) fn mark_obj_valid_modified(&mut self) {
        self.effect_generation += 1;
        self.obj_valid_modified = true;
    }

    /// Marks only `obj_size` as modified (see [`Self::obj_valid_modified`]).
    pub(in crate::codegen_ay::chc) fn mark_obj_size_modified(&mut self) {
        self.effect_generation += 1;
        self.obj_size_modified = true;
    }

    /// Checks if either metadata array was modified in the current block.
    pub(in crate::codegen_ay::chc) fn are_metadata_arrays_modified(&self) -> bool {
        self.obj_valid_modified || self.obj_size_modified
    }

    /// Checks if `obj_valid` was modified in the current block.
    pub(in crate::codegen_ay::chc) fn is_obj_valid_modified(&self) -> bool {
        self.obj_valid_modified
    }

    /// Checks if `obj_size` was modified in the current block.
    pub(in crate::codegen_ay::chc) fn is_obj_size_modified(&self) -> bool {
        self.obj_size_modified
    }
}
