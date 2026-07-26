// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// ChcCtx field-cluster sub-structs for data encapsulation.
// Part of #2880: extract god-object fields into focused state clusters.
// See designs/2026-02-17-issue-2880-chcctx-cluster-execution.md.

use ay_bindings::{Expr, Sort};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use super::types::{
    AdapterSourceData, ArraySolverAuxState, ChcCollectionLenState, CollectionProjectionKind,
    EmbeddedMapAuxKey, EmbeddedMapAuxState,
};

/// Dead-local tracking state for per-block liveness analysis.
///
/// Encapsulates the forward must-analysis results (`dead_locals_at_entry`)
/// and the mutable per-block dead-local set (`dead_locals`).
///
/// Part of #2880 P1: LivenessState extraction (2 fields -> 1 cluster field).
pub(in crate::codegen_ay::chc) struct LivenessState {
    /// Locals that are definitely dead at each basic block entry.
    ///
    /// Computed via forward must-analysis over StorageLive/StorageDead statements.
    /// This avoids traversal-order artifacts where deadness from unrelated blocks
    /// pollutes the current block's scope state.
    pub(in crate::codegen_ay::chc) dead_locals_at_entry: Vec<HashSet<usize>>,

    /// Tracks dead locals while encoding the current block.
    /// Initialized from `dead_locals_at_entry[bb]` and updated as statements
    /// are processed in order.
    pub(in crate::codegen_ay::chc) dead_locals: HashSet<usize>,
}

impl LivenessState {
    pub(in crate::codegen_ay::chc) fn new(dead_locals_at_entry: Vec<HashSet<usize>>) -> Self {
        Self { dead_locals_at_entry, dead_locals: HashSet::new() }
    }
}

/// Layout metadata for a multi-constructor enum flattened to BV state vars.
///
/// State vars: `[tag, payload_fld0, payload_fld1, ..., payload_fldN]`
/// where N = `max_payload_slots`. The tag encodes the constructor index.
///
/// Part of #3215: BV-only enum encoding to bypass Z3 PDR ADT accessor limitation.
#[derive(Debug, Clone)]
pub(in crate::codegen_ay::chc) struct EnumBvLayout {
    /// Number of constructors in the enum.
    pub num_constructors: usize,
    /// Number of bits in the tag (1 for 2 ctors, ceil(log2(N)) for N > 2).
    pub tag_bits: u32,
    /// Per-constructor: cumulative leaf offset for each field.
    /// `ctor_field_slot[ctor_idx][field_idx]` = payload slot index for that field.
    /// Unit/ZST placeholder fields use `OMITTED_FIELD_SLOT`.
    pub ctor_field_slot: Vec<Vec<usize>>,
    /// Total payload state vars (max leaf count across constructors).
    pub max_payload_slots: usize,
    /// Actual discriminant values per constructor index, for mapping tag -> MIR discriminant.
    /// `discriminants[ctor_idx]` = the MIR discriminant value for constructor `ctor_idx`.
    pub discriminants: Vec<u64>,
}

impl EnumBvLayout {
    pub(in crate::codegen_ay::chc) const OMITTED_FIELD_SLOT: usize = usize::MAX;

    pub(in crate::codegen_ay::chc) fn payload_slot(
        &self,
        ctor_idx: usize,
        field_idx: usize,
    ) -> Option<usize> {
        let slot = *self.ctor_field_slot.get(ctor_idx)?.get(field_idx)?;
        (slot != Self::OMITTED_FIELD_SLOT).then_some(slot)
    }
}

/// Flattened-local metadata for compound Datatype -> scalar state var decomposition.
///
/// Tracks which MIR locals have been flattened from Datatype sorts into
/// N consecutive scalar state variables, along with per-local field counts
/// and enum discriminant mappings.
///
/// Part of #2880 P2: FlattenState extraction (3 fields -> 1 cluster field).
pub(in crate::codegen_ay::chc) struct FlattenState {
    /// MIR locals flattened from compound Datatype sorts into N consecutive
    /// scalar state variables (fld0..fldN-1).
    /// Part of #2214: Datatype sorts in CHC relations block PDR.
    pub(in crate::codegen_ay::chc) flattened_tuple_locals: HashSet<usize>,

    /// Number of scalar state variables per flattened local.
    /// Locals not in this map default to 2 (backward compat with early flattening).
    /// Part of #2214: N-field struct flattening (String=3, Vec=4, etc.).
    pub(in crate::codegen_ay::chc) flattened_local_field_count: HashMap<usize, usize>,

    /// Discriminant mapping for flattened enum locals (Option, Result).
    /// Maps local_idx -> (discr_when_true, discr_when_false) for the Bool
    /// proxy at fld0.
    /// Part of #2214.
    pub(in crate::codegen_ay::chc) flattened_enum_discr: HashMap<usize, (u64, u64)>,

    /// Layout metadata for multi-constructor enums flattened to BV state vars.
    /// Maps local_idx -> EnumBvLayout.
    /// Part of #3215: BV-only enum encoding to bypass Z3 PDR ADT accessor limitation.
    pub(in crate::codegen_ay::chc) enum_bv_layouts: HashMap<usize, EnumBvLayout>,
}

impl FlattenState {
    pub(in crate::codegen_ay::chc) fn new() -> Self {
        Self {
            flattened_tuple_locals: HashSet::new(),
            flattened_local_field_count: HashMap::new(),
            flattened_enum_discr: HashMap::new(),
            enum_bv_layouts: HashMap::new(),
        }
    }
}

// RefResolution moved to clusters_ref_resolution.rs per #4206.

/// State variable management for CHC relation signatures.
///
/// Encapsulates the 7 fields that define, index, and scope the CHC state
/// variable vectors (input/output vars, local-to-index mapping, name indices,
/// declared-name dedup set, per-block live sets).
///
/// Part of #2880 P4: StateVarManager extraction (7 fields -> 1 cluster field).
pub(in crate::codegen_ay::chc) struct StateVarManager {
    /// Input state variables (locals at block entry).
    /// Maps local index to (name, sort).
    pub(in crate::codegen_ay::chc) state_vars: Vec<(Arc<str>, Sort)>,

    /// Output state variables (locals at block exit).
    /// Maps local index to (name__out, sort).
    pub(in crate::codegen_ay::chc) output_state_vars: Vec<(Arc<str>, Sort)>,

    /// Maps MIR local index to state_vars/output_state_vars vector index.
    /// Fix #1924: MIR local indices may not match sequential vector positions.
    /// For flattened tuple locals (Part of #2214), this points to the FIRST
    /// field's index; field 1 is at index + 1.
    pub(in crate::codegen_ay::chc) local_to_state_idx: HashMap<usize, usize>,

    /// Set of declared state variable names for O(1) duplicate checking (Part of #1968).
    /// Part of #2267 D3: Arc<str> keys for O(1) clone sharing on insertion.
    pub(in crate::codegen_ay::chc) declared_state_var_names: HashSet<Arc<str>>,

    /// O(1) name-to-index lookup for state_vars (Part of #2730).
    /// Part of #2267 D3: Arc<str> keys shared with declared_state_var_names.
    state_var_name_index: HashMap<Arc<str>, usize>,

    /// O(1) name-to-index lookup for output_state_vars (Part of #2730).
    /// Part of #2267 D3: Arc<str> keys for O(1) clone sharing.
    output_state_var_name_index: HashMap<Arc<str>, usize>,

    /// Per-block subset of state_vars indices that are live at block entry.
    /// `live_state_indices[bb_idx]` contains the indices into `state_vars`
    /// that should appear in block bb_idx's relation signature.
    /// Populated by `compute_live_state_indices()` after state var collection.
    /// Part of #2214: per-block live-scoped CHC relations.
    pub(in crate::codegen_ay::chc) live_state_indices: Vec<Vec<usize>>,
}

impl StateVarManager {
    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(in crate::codegen_ay::chc) fn new() -> Self {
        Self {
            state_vars: Vec::new(),
            output_state_vars: Vec::new(),
            local_to_state_idx: HashMap::new(),
            declared_state_var_names: HashSet::new(),
            state_var_name_index: HashMap::new(),
            output_state_var_name_index: HashMap::new(),
            live_state_indices: Vec::new(),
        }
    }

    /// Pre-sized constructor: eliminates rehashing for the common case where
    /// state var counts correlate with MIR local/block counts.
    /// Part of #2267: with_capacity constructors for cluster types.
    pub(in crate::codegen_ay::chc) fn with_capacity(num_locals: usize, num_blocks: usize) -> Self {
        Self {
            state_vars: Vec::with_capacity(num_locals),
            output_state_vars: Vec::with_capacity(num_locals),
            local_to_state_idx: HashMap::with_capacity(num_locals),
            declared_state_var_names: HashSet::with_capacity(num_locals),
            state_var_name_index: HashMap::with_capacity(num_locals),
            output_state_var_name_index: HashMap::with_capacity(num_locals),
            live_state_indices: Vec::with_capacity(num_blocks),
        }
    }

    /// Find the state_var index for a given variable name (Part of #2552).
    /// O(1) via HashMap (Part of #2730).
    pub(in crate::codegen_ay::chc) fn state_var_index_by_name(&self, name: &str) -> Option<usize> {
        self.state_var_name_index.get(name).copied()
    }

    /// Find the output_state_var index for a given variable name.
    /// O(1) via HashMap (Part of #2730).
    pub(in crate::codegen_ay::chc) fn output_state_var_index_by_name(
        &self,
        name: &str,
    ) -> Option<usize> {
        self.output_state_var_name_index.get(name).copied()
    }

    /// Push a state/output variable pair and update name-to-index maps.
    /// INVARIANT: `out_name` must equal `in_name + "__out"` (#3478).
    /// See `propagate_to_unconstrained_out_vars()` in chc_const_prop_eval.rs.
    /// Part of #2730, #2267 D3.
    /// Part of #3587: idempotent for same-sort duplicates — when MIR inlining
    /// decisions differ (e.g., unwrap panic path present), multiple pre-declaration
    /// passes may converge on the same type-indexed memory array name.
    pub(in crate::codegen_ay::chc) fn push_state_var_pair(
        &mut self,
        in_name: &str,
        out_name: &str,
        sort: Sort,
    ) {
        if let Some(&existing_idx) = self.state_var_name_index.get(in_name) {
            let existing_sort = &self.state_vars[existing_idx].1;
            assert!(
                existing_sort == &sort,
                "duplicate state var name with different sort: {in_name} \
                 (existing: {existing_sort:?}, new: {sort:?})"
            );
            return;
        }
        let idx = self.state_vars.len();
        let in_arc: Arc<str> = Arc::from(in_name);
        let out_arc: Arc<str> = Arc::from(out_name);
        self.state_var_name_index.insert(Arc::clone(&in_arc), idx);
        self.state_vars.push((in_arc, sort.clone()));
        self.output_state_var_name_index.insert(Arc::clone(&out_arc), idx);
        self.output_state_vars.push((out_arc, sort));
    }

    /// Push a state/output variable pair when input name is already `Arc<str>`.
    /// See [`push_state_var_pair`] for the `__out` naming invariant (#3478).
    /// Part of #3587: idempotent for same-sort duplicates (see `push_state_var_pair`).
    pub(in crate::codegen_ay::chc) fn push_state_var_pair_arc(
        &mut self,
        in_name: Arc<str>,
        out_name: &str,
        sort: Sort,
    ) {
        if let Some(&existing_idx) = self.state_var_name_index.get(&*in_name) {
            let existing_sort = &self.state_vars[existing_idx].1;
            assert!(
                existing_sort == &sort,
                "duplicate state var name with different sort: {in_name} \
                 (existing: {existing_sort:?}, new: {sort:?})"
            );
            return;
        }
        let idx = self.state_vars.len();
        let out_arc: Arc<str> = Arc::from(out_name);
        self.state_vars.push((Arc::clone(&in_name), sort.clone()));
        self.state_var_name_index.insert(in_name, idx);
        self.output_state_var_name_index.insert(Arc::clone(&out_arc), idx);
        self.output_state_vars.push((out_arc, sort));
    }

    /// Map MIR local index to CHC state/output vector slot via `local_to_state_idx`.
    ///
    /// Returns `None` when the local has no explicit mapping.
    pub(in crate::codegen_ay::chc) fn try_state_idx_for_local(
        &self,
        local_idx: usize,
    ) -> Option<usize> {
        self.local_to_state_idx.get(&local_idx).copied()
    }
}

/// Per-block encoding state that accumulates during block processing and
/// is cleared between blocks, plus cached entry-rule constraints.
///
/// Groups the 4 block-scoped mutable fields that track expression values,
/// signedness inference, field expressions, and modified-index bookkeeping
/// within a single basic block's encoding pass. Also holds the cached
/// stack allocation constraints used during entry rule generation.
///
/// Part of #2952 Phase 2: EncodeState extraction (5 fields -> 1 cluster field).
pub(in crate::codegen_ay::chc) struct EncodeState {
    /// Tracks inferred signedness for locals within the current block (#1889).
    /// Used to propagate signedness through temporaries when type inference is unavailable.
    pub(in crate::codegen_ay::chc) local_signedness: HashMap<usize, bool>,

    /// Block-local expression environment for CHC encoding (#2055).
    /// Maps local_idx -> current symbolic expression value within the current block.
    pub(in crate::codegen_ay::chc) local_expr_env: HashMap<usize, Expr>,

    /// Per-field expression environment for flattened locals (Part of #2876).
    /// Maps (local_idx, field_idx) -> last-constrained concrete expression.
    pub(in crate::codegen_ay::chc) flattened_field_env: HashMap<(usize, usize), Expr>,

    /// Indices into state_vars that have been modified in the current block.
    /// Part of #2552: centralized output-args propagation.
    pub(in crate::codegen_ay::chc) modified_state_indices: HashSet<usize>,

    /// Cached stack allocation constraints for entry rule.
    /// Computed once during predeclaration and consumed by entry rule generation.
    pub(in crate::codegen_ay::chc) stack_alloc_constraints: Option<Vec<Expr>>,

    /// Cross-block constant propagation for constant-folded call results.
    /// When a math intrinsic (or other call) is constant-folded, the result
    /// is stored here so subsequent blocks can seed `local_expr_env` with
    /// the concrete value. Without this, the target block sees a symbolic
    /// state variable and `bv_float_binop_chc` can't constant-fold downstream
    /// operations (Sub, Abs, comparison), breaking the constant-fold chain.
    /// Part of #3839: fix CTREX(Genuine) in exp.rs/log.rs.
    ///
    /// **Invalidation contract:** call [`Self::invalidate_local_cache()`]
    /// whenever a local is written to. Direct `.remove()` is forbidden
    /// outside `invalidate_local_cache()` (#3938).
    pub(in crate::codegen_ay::chc) const_folded_call_results: HashMap<usize, Expr>,

    /// Locals with exactly one assignment site across the entire function body.
    /// Single-assignment locals have a unique value regardless of execution path,
    /// so cross-block BV constant propagation is sound for them. Multi-assignment
    /// locals (e.g., `y = if cond { 1 } else { 2 }`) are path-dependent and
    /// must NOT be propagated cross-block (false PROOF at merge points, #3905).
    /// Part of #3905: safe cross-block constant propagation.
    pub(in crate::codegen_ay::chc) single_assign_locals: HashSet<usize>,

    /// Locals with exactly one direct MIR assignment site (call destinations
    /// included), WITHOUT the `single_assign_locals` ref-target exclusion.
    ///
    /// Used only by the Box/pointer-wrapper data-pointer provenance forwarding
    /// (`propagate_alloc_ids_for_assign` field-0 lane). A drop-glue container
    /// (`Drop::drop(&mut self)`) is always a `&mut` ref-target, so it is
    /// excluded from `single_assign_locals`; but its storage is still written
    /// exactly once. This set recovers "written exactly once directly" while
    /// `deref_store_target_locals` separately excludes the genuinely-dangerous
    /// stored-through case, keeping the forward sound (see the field-0 lane).
    pub(in crate::codegen_ay::chc) raw_single_assign_locals: HashSet<usize>,

    /// Locals that are the referent of a pointer used as the base of a Deref
    /// STORE (`(*p)… = v`), i.e. locals whose storage may be overwritten
    /// through a pointer. Field-0 provenance forwarding refuses any container
    /// in this set: its data-pointer field could have been reassigned after
    /// construction, making a cached obj_id stale (fail-closed).
    pub(in crate::codegen_ay::chc) deref_store_target_locals: HashSet<usize>,
}

impl EncodeState {
    /// Pre-sized constructor: `clear_block()` retains allocated capacity,
    /// so the first block's allocation covers subsequent blocks.
    /// Part of #2267: with_capacity constructors for cluster types.
    pub(in crate::codegen_ay::chc) fn with_capacity(num_locals: usize) -> Self {
        Self {
            local_signedness: HashMap::with_capacity(num_locals),
            local_expr_env: HashMap::with_capacity(num_locals),
            flattened_field_env: HashMap::with_capacity(num_locals),
            modified_state_indices: HashSet::with_capacity(num_locals),
            stack_alloc_constraints: None,
            const_folded_call_results: HashMap::new(),
            single_assign_locals: HashSet::new(),
            raw_single_assign_locals: HashSet::new(),
            deref_store_target_locals: HashSet::new(),
        }
    }

    /// Clear all block-scoped state for a new block.
    ///
    /// Part of #3474: `flattened_field_env` entries for dead locals are
    /// retained across blocks. When a local is storage-dead at the new
    /// block's entry, its state variables may be excluded from the CHC
    /// relation (liveness pruning), making them universally quantified.
    /// Retaining the env values from the block where the local was last
    /// constrained allows aggregate construction to use concrete expressions
    /// instead of free variables, preventing spurious counterexamples.
    pub(in crate::codegen_ay::chc) fn clear_block(&mut self, dead_at_entry: &HashSet<usize>) {
        self.local_signedness.clear();
        self.local_expr_env.clear();
        // Note: const_folded_call_results is NOT cleared — it persists across
        // blocks so translate_place_with_modified can return concrete BV constants
        // for locals whose values were constant-folded in predecessor blocks.
        // Part of #3839.
        //
        // Retain env entries for dead locals — their state vars may be pruned
        // from the relation, so the env is the only source of concrete values.
        // Clear entries for live locals — they have proper state vars and will
        // get fresh env entries from current-block constraint emission.
        self.flattened_field_env.retain(|&(local_idx, _), _| dead_at_entry.contains(&local_idx));
        self.modified_state_indices.clear();
    }

    /// Invalidate all cross-block caches for a local that was written to.
    ///
    /// MUST be called by every code path that writes to a local (direct
    /// assignment, pointer write, copy, inline call writeback). Forgetting
    /// to call this is a soundness bug — stale cached constants will mask
    /// the written value, producing false PROOFs.
    ///
    /// Part of #3938: centralized cache invalidation guard.
    pub(in crate::codegen_ay::chc) fn invalidate_local_cache(&mut self, local_idx: usize) {
        self.const_folded_call_results.remove(&local_idx);
    }
}

/// Collection and iterator tracking state.
///
/// Groups the 3 fields that track collection lengths/capacities,
/// Datatype-projected collection locals, and Vec capacity stub deduplication.
///
/// Part of #2952 Phase 2: CollectionState extraction (3 fields -> 1 cluster field).
pub(in crate::codegen_ay::chc) struct CollectionState {
    /// Auxiliary length/capacity state for collection locals (Part of #1814).
    /// Tracks per-local length/capacity variables and which have been modified.
    pub(in crate::codegen_ay::chc) len_state: ChcCollectionLenState,

    /// MIR locals whose collection/iterator Datatype sort was projected into
    /// N consecutive scalar/array state variables in the CHC relation signature.
    /// Part of #2874: Live Datatype flattening for collection/iterator types.
    pub(in crate::codegen_ay::chc) projection_locals: HashMap<usize, CollectionProjectionKind>,

    /// Vec locals whose capacity was already modeled by a Vec-level stub.
    /// RawVec stubs skip constraints for locals in this set to prevent dual-path firing.
    /// Part of #1037 V1: RawVec deduplication.
    pub(in crate::codegen_ay::chc) vec_cap_stubs_fired: HashSet<usize>,

    /// Remaining element count for iterator adapter locals whose sort was flattened
    /// to BV64 (preventing structural `fld_pos`/`fld_len` extraction at IterCollect
    /// time). IterMap/IterFilter store the remaining_len extracted from the inner
    /// iterator here; IterCollect reads it as a fallback when
    /// `try_extract_iterator_remaining_len` fails on BV64 iter_expr.
    /// Part of #3381: IterCollect len-constrained Vec for BV64 adapter chains.
    pub(in crate::codegen_ay::chc) adapter_remaining_len: HashMap<usize, Expr>,

    /// Source data arrays tracked through iterator adapter chains.
    ///
    /// When VecIter/VecIntoIter is created, the source Vec's data array expression
    /// is recorded here keyed by the iterator dest_local. Adapter chains (IterMap,
    /// IterFilter, IterZip) propagate source data to their own dest_local so
    /// downstream IterCollect can read it.
    ///
    /// For single-source chains (map/filter), contains one data array.
    /// For zip chains, contains two data arrays (one per source).
    /// The `has_transform` flag indicates whether a non-identity adapter (map/filter)
    /// is present; when false, IterCollect can use the source data directly.
    ///
    /// Part of #3348: IterCollect element-wise constraints (Step 4 infrastructure).
    pub(in crate::codegen_ay::chc) adapter_source_data: HashMap<usize, AdapterSourceData>,

    /// Adapter locals known to be at the start of their tracked source sequence.
    ///
    /// Some adapter chains are represented as opaque BV64 values, so collect-time
    /// code cannot recover `fld_pos == 0` syntactically. This sidecar preserves
    /// the start fact until a `next`/state update consumes the adapter.
    pub(in crate::codegen_ay::chc) adapter_at_start: HashSet<usize>,

    /// Explicit embedded-map aux ownership for struct locals (Part of #3348).
    ///
    /// Maps `(struct_local, field_idx)` → aux state (`present_var`, `len_var`).
    /// Populated at constructor boundaries and propagated through method passthrough
    /// and clone dispatchers. Consulted by `get_hashmap_present_arg()` before the
    /// legacy MIR aggregate scan fallback.
    pub(in crate::codegen_ay::chc) embedded_map_aux:
        HashMap<EmbeddedMapAuxKey, EmbeddedMapAuxState>,

    /// Shadow auxiliary state for `ArraySolver` locals (Part of #4050).
    ///
    /// Maps local_idx → aux state (assign_present, assign_value, scope snapshots).
    /// Populated during state var declaration for locals whose ADT name is `ArraySolver`.
    /// Consulted by the pre-inline ArraySolver method dispatcher to replace loop-based
    /// methods with single SMT array operations.
    pub(in crate::codegen_ay::chc) array_solver_aux: HashMap<usize, ArraySolverAuxState>,
}

impl CollectionState {
    pub(in crate::codegen_ay::chc) fn new() -> Self {
        Self {
            len_state: ChcCollectionLenState::new(),
            projection_locals: HashMap::new(),
            vec_cap_stubs_fired: HashSet::new(),
            adapter_remaining_len: HashMap::new(),
            adapter_source_data: HashMap::new(),
            adapter_at_start: HashSet::new(),
            embedded_map_aux: HashMap::new(),
            array_solver_aux: HashMap::new(),
        }
    }

    /// Register embedded-map aux ownership for a struct field (Part of #3348).
    ///
    /// Records that `struct_local.field_idx` is a map field with the given
    /// auxiliary state variables. Called at constructor boundaries.
    pub(in crate::codegen_ay::chc) fn register_embedded_map_aux(
        &mut self,
        struct_local: usize,
        field_idx: usize,
        state: EmbeddedMapAuxState,
    ) {
        self.embedded_map_aux.insert(EmbeddedMapAuxKey { struct_local, field_idx }, state);
    }

    /// Look up embedded-map aux state for a struct field (Part of #3348).
    pub(in crate::codegen_ay::chc) fn get_embedded_map_aux(
        &self,
        struct_local: usize,
        field_idx: usize,
    ) -> Option<&EmbeddedMapAuxState> {
        self.embedded_map_aux.get(&EmbeddedMapAuxKey { struct_local, field_idx })
    }

    /// Copy all embedded-map aux records from one struct local to another (Part of #3348).
    ///
    /// Used by method passthrough and clone dispatchers when the destination struct
    /// should inherit the source struct's aux state.
    pub(in crate::codegen_ay::chc) fn copy_embedded_map_aux(
        &mut self,
        src_local: usize,
        dest_local: usize,
    ) {
        let entries: Vec<(usize, EmbeddedMapAuxState)> = self
            .embedded_map_aux
            .iter()
            .filter(|(k, _)| k.struct_local == src_local)
            .map(|(k, v)| (k.field_idx, v.clone()))
            .collect();
        for (field_idx, state) in entries {
            self.embedded_map_aux
                .insert(EmbeddedMapAuxKey { struct_local: dest_local, field_idx }, state);
        }
    }
}
