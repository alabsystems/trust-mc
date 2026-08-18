// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Helper types for CHC codegen context — result structs and auxiliary state.
//!
//! Extracted from codegen_ctx.rs per #2408.

use ay_bindings::Expr;
use rustc_public::mir::ProjectionElem;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::args::{ChcStepMode, ChcTrackLevel};

/// Bundled CHC encoding configuration (Part of #3517).
///
/// Groups the 6 solver/encoding knobs that travel together through
/// `mir_to_chc` → `ChcCtx::new`. Using a single parameter object
/// reduces these function signatures from 8–9 params to 4.
#[derive(Clone, Copy, Debug)]
pub(in crate::codegen_ay) struct ChcConfig {
    /// Which MIR locals become CHC state variables.
    pub track_level: ChcTrackLevel,
    /// Small-step (per-BB) vs large-step (fragment) encoding.
    pub step_mode: ChcStepMode,
    /// Promote BV → Int for PDR invariant synthesis.
    pub int_lift: bool,
    /// Emit extra CHC debug tracing.
    pub chc_debug: ChcDebugMode,
    /// Enable wide-memory bounds-checking model.
    pub wide_mem: WideMemMode,
    /// Emit pointer-validity safety checks.
    pub extra_pointer_checks: bool,
    /// Prove safety only: suppress user assertion/panic error rules, keep safety checks.
    /// When true, user-level violations (KaniHook::Assert, Check, Panic, PanicStub)
    /// are skipped, while safety checks (SafetyCheck, SafetyCheckNoAssume,
    /// UnsupportedCheck, MIR Assert terminators) remain fail-closed. Pointer offset
    /// safety checks are also enabled.
    pub prove_safety_only: bool,
    /// Emit memory-safety error rules.
    pub memory_safety_checks: bool,
    /// Narrow each block relation's frame to backward-live columns.
    ///
    /// DEFAULT OFF — opt in with `TRUST_MC_FRAME_NARROWING=1`. It measures net
    /// positive on the corpus (+6 parity, unknown -16, at a 15 s budget) but has a
    /// tail that the free-variable validator cannot see: `prusti/Selection_sort.rs`
    /// goes from 0.54 s to NO VERDICT at a 150 s budget, and
    /// `bounded-arbitrary/hash.rs` from 0.57 s to 95 s, neither of them re-encoding.
    /// Turning a fast proof into a hang is a worse failure for a verifier than
    /// leaving a noise-level parity gain on the table, so it stays opt-in until that
    /// mechanism is understood.
    ///
    /// Also set false by the free-variable retry in `mir_to_chc_internal`: the
    /// restriction is a decl-time MIR approximation and the encoder reads state
    /// through channels MIR cannot see, so a harness whose VC ends up naming a
    /// dropped column is re-encoded with the full frame.
    pub frame_narrowing: bool,
    /// Emit arithmetic overflow error rules.
    pub overflow_checks: bool,
    /// Emit NaN-generation obligations for float binops (`--nan-check`).
    /// OFF by default; NaN is defined behaviour in Rust, not UB.
    pub nan_checks: bool,
    /// Emit error rules for reachable undefined foreign function calls.
    pub undefined_function_checks: bool,
    /// Harness unwind depth for bounded recursive inline (Part of #3929).
    /// When > 0, recursive self-calls are inlined up to this many re-entries
    /// instead of the fixed MAX_INLINE_DEPTH generic guard.
    pub recursive_unwind_depth: u32,
    /// Whether to emit a failing guard when recursive unwind budget is exhausted.
    /// When true, exhausted recursion produces a fail-closed assertion.
    /// When false, exhausted recursion produces a typed over-approximation.
    pub unwinding_assertions: bool,
    /// `-Z uninit-checks` is active: thread the scalar shadow-memory state vars
    /// and encode real verdicts for the mem-init model calls (MEMUB-24/25/27).
    pub uninit_checks: bool,
    /// P2-S1: this harness is a `#[kani::proof_for_contract]` CHECK harness, so
    /// mutable statics and the interior-mutable (UnsafeCell-covered) parts of
    /// immutable statics must be HAVOCKED, not pinned to their initializers.
    /// SOUNDNESS: a contract must hold for ARBITRARY ambient static state
    /// (Kani havocs these via CBMC `--enforce-contract`/DFCC); pinning makes
    /// the check easier than the contract's meaning — a fail-open. Immutable
    /// non-interior-mut statics and promoted constants stay pinned.
    pub contract_static_havoc: bool,
}

impl Default for ChcConfig {
    fn default() -> Self {
        Self {
            track_level: ChcTrackLevel::Reg,
            step_mode: ChcStepMode::Small,
            int_lift: false,
            chc_debug: ChcDebugMode::Off,
            wide_mem: WideMemMode::Off,
            extra_pointer_checks: false,
            prove_safety_only: false,
            memory_safety_checks: true,
            frame_narrowing: false,
            overflow_checks: true,
            nan_checks: false,
            undefined_function_checks: true,
            recursive_unwind_depth: 0,
            unwinding_assertions: true,
            uninit_checks: false,
            contract_static_havoc: false,
        }
    }
}

/// CHC debug tracing mode (Part of #2623).
///
/// Replaces bare `bool` parameter in `mir_to_chc()` for self-documenting call sites.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(in crate::codegen_ay) enum ChcDebugMode {
    /// CHC debug tracing disabled (default).
    Off,
    /// CHC debug tracing enabled via CLI flag.
    On,
}

impl From<bool> for ChcDebugMode {
    fn from(value: bool) -> Self {
        if value { Self::On } else { Self::Off }
    }
}

/// Wide memory model mode (Part of #2623).
///
/// Replaces bare `bool` parameter in `ChcCtx::new()` and `mir_to_chc()`
/// for self-documenting call sites.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(in crate::codegen_ay) enum WideMemMode {
    /// Standard memory model without bounds checking (default).
    Off,
    /// Wide memory model with allocation-size tracking and bounds checking.
    On,
}

impl From<bool> for WideMemMode {
    fn from(value: bool) -> Self {
        if value { Self::On } else { Self::Off }
    }
}

/// Target of a reference for deref chain resolution in value-semantics mode.
/// Part of #1712: Allows resolving `(*ref).field` patterns at Reg/Ptr track level.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) struct RefTarget {
    /// The resolved local index that the reference ultimately points to.
    pub(in crate::codegen_ay::chc) local: usize,
    /// Projections to apply after dereferencing.
    ///
    /// Stored as a `Place`-like projection chain (minus the leading Deref), enabling
    /// resolution of patterns like `&arr[idx]`, `&arr[idx].field`, and `&((*ref).field)`.
    pub(in crate::codegen_ay::chc) projections: Vec<ProjectionElem>,
}

impl RefTarget {
    /// Create a target with projections.
    pub(in crate::codegen_ay::chc) fn with_projections(
        local: usize,
        projections: Vec<ProjectionElem>,
    ) -> Self {
        Self { local, projections }
    }
}

/// Tracks auxiliary length and capacity state for collection locals in CHC encoding.
/// Part of #1814: CHC collection length tracking for iterator count assertions.
/// Part of #2877: CHC Vec capacity tracking for reserve/shrink_to_fit assertions.
///
/// CHC represents HashMap as `Array<K, Option<V>>` and HashSet as `Array<K, Bool>`
/// without embedded length fields, so length must be tracked separately.
/// Vec capacity is also tracked as a state variable since the CHC encoding
/// may not always use a Datatype sort with `fld_cap`.
#[derive(Default, Debug)]
pub(in crate::codegen_ay::chc) struct ChcCollectionLenState {
    /// Maps local index to length variable name for collection locals.
    /// Example: local 3 (HashMap) -> "hashmap_len_local_3".
    /// Uses `Arc<str>` so `.get().cloned()` is a cheap ref-count bump (Part of #2267).
    pub(in crate::codegen_ay::chc) len_var_names: HashMap<usize, Arc<str>>,

    /// Set of length variable names modified in the current block.
    /// Used for output argument selection (similar to modified memory arrays).
    pub(in crate::codegen_ay::chc) modified_len_vars: HashSet<Arc<str>>,

    /// Maps local index to capacity variable name for Vec locals (#2877).
    /// Example: local 1 (Vec) -> "vec_test_fn_cap_1".
    pub(in crate::codegen_ay::chc) cap_var_names: HashMap<usize, Arc<str>>,

    /// Set of capacity variable names modified in the current block.
    pub(in crate::codegen_ay::chc) modified_cap_vars: HashSet<Arc<str>>,

    /// Maps local index to presence-array variable name for HashMap locals (#3057).
    /// Example: local 3 (HashMap) -> "hashmap_test_fn_present_3".
    /// The presence array is `Array(K, Bool)` — tracks key membership.
    pub(in crate::codegen_ay::chc) present_var_names: HashMap<usize, Arc<str>>,

    /// Set of presence-array variable names modified in the current block.
    pub(in crate::codegen_ay::chc) modified_present_vars: HashSet<Arc<str>>,

    /// Task #69: length variables that were EVER constrained by a collection
    /// stub in this function. CUMULATIVE — never cleared at block boundaries.
    /// A current-length bounds guard (slice index) is only meaningful for a
    /// seeded len var: an unseeded one is a free variable, and a guard on it
    /// produces arbitrary counterexamples misclassified as Genuine.
    pub(in crate::codegen_ay::chc) seeded_len_vars: HashSet<Arc<str>>,

    /// Task #69: collection locals whose sidecar/state was bypassed by a
    /// non-stub call path (e.g., a `&mut`-receiver method handled by the
    /// fn-inline translator, which mutates the Vec through raw memory and
    /// never syncs the sidecar length). Bounds guards must not trust the
    /// sidecar length of these locals. CUMULATIVE.
    pub(in crate::codegen_ay::chc) sidecar_untrusted_locals: HashSet<usize>,
}

impl ChcCollectionLenState {
    /// Create a new collection length state tracker.
    pub(in crate::codegen_ay::chc) fn new() -> Self {
        Self::default()
    }

    /// Get the length variable name for a local, if it's a tracked collection.
    pub(in crate::codegen_ay::chc) fn get_len_var(&self, local_idx: usize) -> Option<&Arc<str>> {
        self.len_var_names.get(&local_idx)
    }

    /// Get the capacity variable name for a local, if it's a tracked Vec.
    pub(in crate::codegen_ay::chc) fn get_cap_var(&self, local_idx: usize) -> Option<&Arc<str>> {
        self.cap_var_names.get(&local_idx)
    }

    /// Get the presence-array variable name for a local, if it's a tracked map (#3057).
    pub(in crate::codegen_ay::chc) fn get_present_var(
        &self,
        local_idx: usize,
    ) -> Option<&Arc<str>> {
        self.present_var_names.get(&local_idx)
    }

    /// Mark a length variable as modified for output argument selection.
    /// Task #69: also records the var in the cumulative seeded set — every
    /// collection stub that sets a length routes through here.
    pub(in crate::codegen_ay::chc) fn mark_len_modified(&mut self, len_var_name: &str) {
        if !self.seeded_len_vars.contains(len_var_name) {
            self.seeded_len_vars.insert(Arc::from(len_var_name));
        }
        if !self.modified_len_vars.contains(len_var_name) {
            self.modified_len_vars.insert(Arc::from(len_var_name));
        }
    }

    /// Task #69: was this length variable ever constrained by a collection
    /// stub in this function?
    pub(in crate::codegen_ay::chc) fn is_len_seeded(&self, len_var_name: &str) -> bool {
        self.seeded_len_vars.contains(len_var_name)
    }

    /// Task #69: mark a collection local's sidecar state as bypassed by a
    /// non-stub call path (fn-inline of a mutable-receiver method).
    pub(in crate::codegen_ay::chc) fn mark_sidecar_untrusted(&mut self, local_idx: usize) {
        self.sidecar_untrusted_locals.insert(local_idx);
    }

    /// Task #69: is this collection local's sidecar state trustworthy for
    /// bounds guards?
    pub(in crate::codegen_ay::chc) fn is_sidecar_untrusted(&self, local_idx: usize) -> bool {
        self.sidecar_untrusted_locals.contains(&local_idx)
    }

    /// Task #69: reverse lookup — which local owns this length variable?
    pub(in crate::codegen_ay::chc) fn local_for_len_var(
        &self,
        len_var_name: &str,
    ) -> Option<usize> {
        self.len_var_names
            .iter()
            .find(|(_, name)| &***name == len_var_name)
            .map(|(local, _)| *local)
    }

    /// Mark a capacity variable as modified for output argument selection.
    pub(in crate::codegen_ay::chc) fn mark_cap_modified(&mut self, cap_var_name: &str) {
        if !self.modified_cap_vars.contains(cap_var_name) {
            self.modified_cap_vars.insert(Arc::from(cap_var_name));
        }
    }

    /// Mark a presence-array variable as modified for output argument selection (#3057).
    pub(in crate::codegen_ay::chc) fn mark_present_modified(&mut self, present_var_name: &str) {
        if !self.modified_present_vars.contains(present_var_name) {
            self.modified_present_vars.insert(Arc::from(present_var_name));
        }
    }

    /// Clear modified set at block boundaries.
    pub(in crate::codegen_ay::chc) fn clear_modified(&mut self) {
        self.modified_len_vars.clear();
        self.modified_cap_vars.clear();
        self.modified_present_vars.clear();
    }
}

/// Key for struct-embedded map auxiliary state (Part of #3348).
///
/// When a struct contains a BTreeMap/HashMap field, the map's `present` and `len`
/// auxiliary arrays are tracked separately from the map's data array. This key
/// identifies which struct local and which field within that struct owns the aux
/// state, enabling cross-body constructor and passthrough propagation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(in crate::codegen_ay::chc) struct EmbeddedMapAuxKey {
    pub(in crate::codegen_ay::chc) struct_local: usize,
    pub(in crate::codegen_ay::chc) field_idx: usize,
}

/// Auxiliary state for a struct-embedded map field (Part of #3348).
///
/// Stores the variable names for the map's membership-tracking arrays (`present`)
/// and length counter. These are populated at constructor boundaries and propagated
/// through method passthrough and clone dispatchers.
#[derive(Debug, Clone)]
pub(in crate::codegen_ay::chc) struct EmbeddedMapAuxState {
    #[allow(dead_code)] // populated for future len bridging; present_var used now
    pub(in crate::codegen_ay::chc) len_var: Option<Arc<str>>,
    pub(in crate::codegen_ay::chc) present_var: Option<Arc<str>>,
}

/// Shadow auxiliary state for `ArraySolver` locals (Part of #4050).
///
/// The `ArraySolver` struct uses 6 parallel Vecs to model a push/pop assignment
/// map. Verifying the pop-restores-assignments property through 25+ chained Vec
/// stub invocations causes constraint-loss compounding. Instead, shadow state
/// tracks the logical assignment map and scope snapshots directly in SMT arrays,
/// allowing the dispatcher to replace loop-based methods with single SMT operations.
#[derive(Debug, Clone)]
pub(in crate::codegen_ay::chc) struct ArraySolverAuxState {
    /// `Array(BV32, Bool)` — whether each TermId has an assignment.
    pub(in crate::codegen_ay::chc) assign_present_var: Arc<str>,
    /// `Array(BV32, Bool)` — the assigned value for each TermId.
    pub(in crate::codegen_ay::chc) assign_value_var: Arc<str>,
    /// `Array(BV64, Array(BV32, Bool))` — saved assign_present at each scope depth.
    pub(in crate::codegen_ay::chc) scope_snap_present_var: Arc<str>,
    /// `Array(BV64, Array(BV32, Bool))` — saved assign_value at each scope depth.
    pub(in crate::codegen_ay::chc) scope_snap_value_var: Arc<str>,
    /// `Array(BV64, Vec<TermId>)` — saved visible `assign_terms` Vec at each scope depth.
    pub(in crate::codegen_ay::chc) scope_snap_assign_terms_var: Arc<str>,
    /// `Array(BV64, Vec<bool>)` — saved visible `assign_values` Vec at each scope depth.
    pub(in crate::codegen_ay::chc) scope_snap_assign_values_var: Arc<str>,
    /// `Bool` — shadow of the `dirty` struct field.
    pub(in crate::codegen_ay::chc) dirty_var: Arc<str>,
    /// `BV64` — shadow scope depth tracking `scopes.len()`.
    ///
    /// The `scopes` Vec inside ArraySolver is not tracked as a standalone
    /// collection local, so `get_len_var()` returns None for ArraySolver locals.
    /// This shadow var fills that gap, allowing push/pop to know the current
    /// scope depth without querying the Vec len state.
    pub(in crate::codegen_ay::chc) scope_depth_var: Arc<str>,
}

/// Source data arrays tracked through iterator adapter chains for IterCollect.
///
/// Populated when VecIter/VecIntoIter is created (source Vec's fld_data array).
/// Propagated through iterator adapters to the adapter dest_local.
/// Read by IterCollect to constrain the result Vec's data array.
///
/// Part of #3348: IterCollect element-wise constraints (Step 4 infrastructure).
#[derive(Clone, Debug)]
#[allow(dead_code)] // Fields read in codegen_call_iterator_adapter.rs; clippy staged-index FP
pub(in crate::codegen_ay::chc) struct AdapterSourceData {
    /// Source data array expressions from the original Vec(s).
    /// Single-source chains (iter/map/filter) have one entry.
    /// Zip chains have two entries (one per source iterator).
    pub(in crate::codegen_ay::chc) data_arrays: Vec<Expr>,
    /// Whether a non-identity adapter (map/filter/filter_map) is in the chain.
    /// When false, IterCollect can copy source data directly to result.
    /// When true, result data depends on the closure body or filtering.
    pub(in crate::codegen_ay::chc) has_transform: bool,
    /// Pre-translated closure body expression for IterMap transform chains.
    ///
    /// When an IterMap adapter is in the chain and the closure body can be
    /// inlined to a AY expression, this stores the translated expression
    /// parameterized by a shared index variable. The expression uses
    /// `select(src_data[i], idx)` for element access, so wrapping with
    /// `forall idx: select(result, idx) = closure_expr` gives the element-wise
    /// constraint.
    ///
    /// Part of #3348: IterCollect closure body analysis for transform chains.
    pub(in crate::codegen_ay::chc) closure_template: Option<ClosureTemplate>,
    /// Concrete element values extracted from the source Vec's data array.
    ///
    /// Populated when VecIntoIter is created from a Vec with a small, concrete
    /// store-chain data array. Cleared by adapters that change values or
    /// cardinality, then optionally repopulated when elements are exactly
    /// evaluated through the closure (e.g., filter_map parse + ok).
    /// At IterCollect, used to build the exact output Vec without symbolic
    /// over-approximation.
    ///
    /// Part of #3692: concrete filter_map replay for parse.rs PROOF.
    pub(in crate::codegen_ay::chc) concrete_elems: Option<Vec<Expr>>,
}

/// Pre-translated closure body for element-wise IterCollect constraints.
///
/// Part of #3348: Stores a closure body translated to a AY expression,
/// parameterized by an index variable. Currently used as a marker
/// (is_some() check) at IterCollect — element-wise forall constraints
/// are skipped because PDR cannot handle quantifiers in CHC rules.
/// Fields retained for future element-value constraint work.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub(in crate::codegen_ay::chc) struct ClosureTemplate {
    /// The index variable name used in `select(src_data, idx)` within the expression.
    pub(in crate::codegen_ay::chc) idx_var_name: String,
    /// The translated closure body expression, using `select(src_data[i], idx_var)`
    /// for element access from source data arrays.
    pub(in crate::codegen_ay::chc) body_expr: Expr,
}

/// Tracks a deferred store through an IndexMut-returned `&mut T` reference.
///
/// When `IndexMut::index_mut(slice, idx)` is called, the result is a `&mut T`
/// that, when written to (`*result = val`), must propagate the store back to
/// the Vec's `fld_data` array as `data' = store(data, idx, val)`.
///
/// Part of #3348: Vec IndexMut CHC stub for ay self-verification.
/// Part of #3439: Extended with field_projections for struct-embedded Vec.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) struct CollectionMutRef {
    /// The MIR local index of the Vec being mutated (or the struct containing it).
    pub(in crate::codegen_ay::chc) collection_local: usize,
    /// The BV64 index expression used in the IndexMut call.
    pub(in crate::codegen_ay::chc) index_expr: Expr,
    /// Field projections from `collection_local` to the actual Vec.
    ///
    /// Empty when Vec is a top-level local. Non-empty when the Vec is accessed
    /// through a struct field (e.g., `self.marks[var]` where `self` is a struct
    /// with a Vec `marks` field). In that case, `collection_local` is the struct
    /// local and `field_projections` contains the Field projection to the Vec.
    /// Part of #3439: struct-projected collection IndexMut.
    pub(in crate::codegen_ay::chc) field_projections: Vec<ProjectionElem>,
}

/// Classification of collection/iterator types that are projected into
/// scalar/array state variables instead of Datatype sorts at loop headers.
///
/// Part of #2874: Live Datatype flattening for collection/iterator locals.
/// When a MIR local has one of these types, its Datatype sort is decomposed
/// into N scalar/array fields in the CHC relation signature. Stub call sites
/// reconstruct ephemeral Datatype terms from projections as needed (Step 2).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::codegen_ay::chc) enum CollectionProjectionKind {
    /// `Vec<T>`: projected as (ptr: bv64, len: bv64, cap: bv64, data: Array<bv64, T>).
    Vec,
    /// `vec::IntoIter<T>`: deep-flattened as (ptr: bv64, len: bv64, cap: bv64, data: Array<bv64, T>, pos: bv64).
    /// Flattens through the nested Vec carrier.
    VecIntoIter,
    /// `hash_map::IntoIter<K,V>`: projected as (data: Array<K,V>, present: Array<K,Bool>, keys: Array<bv64,K>, pos: bv64, len: bv64).
    /// Part of #3057: DT-free parallel-array encoding.
    HashMapIntoIter,
    /// `hash_set::IntoIter<K>`: projected as (set: Array<K,Bool>, keys: Array<bv64,K>, pos: bv64, len: bv64).
    HashSetIntoIter,
    /// `array::IntoIter<T, N>`: deep-flattened as (start: bv64, end: bv64, data: Array<bv64, T>).
    /// Layout: IntoIter { fld_inner: PolymorphicIter { fld_alive: IndexRange { start, end }, fld_data } }.
    /// Part of #3711: distinct from VecIntoIter to avoid reconstruction failures.
    ArrayIntoIter,
    /// Single-constructor wrapper around a recognized iterator sort (e.g., `Chars { fld_iter: SliceIter_bv8 }`).
    /// Deep-flattened to the same leaf layout as the inner iterator.
    /// Uses generic `deep_decompose_to_leaves` / `reconstruct_datatype_from_deep_flattened`.
    /// Part of #4114: prevents wrapper iterators from falling through to BV coercion.
    IteratorWrapper,
}

// CollectionCallResult, AllocTransitionBranch, AllocCallResult, StubTranslateArgs
// moved to types_collection_result.rs per #4206.
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) use super::types_collection_result::CollectionCallResult;
pub(in crate::codegen_ay::chc) use super::types_collection_result::{
    AllocCallResult, AllocTransitionBranch,
};
