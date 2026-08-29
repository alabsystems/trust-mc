// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// CHC codegen context — core ChcCtx definitions and entry points.
// Split from mod.rs per #1353; further split per #1508 for reviewability.
// Converted from include!() to proper module per #2595.
// Decomposed into globals/types/mod per #2408.

mod body_resolve;
pub(in crate::codegen_ay) mod diagnostics;
mod diagnostics_global;
mod diagnostics_per_fn;
pub(in crate::codegen_ay::chc) mod globals;
mod int_lift;
mod late_state_vars;
mod resolve_expr;
pub(in crate::codegen_ay::chc) mod types;
mod types_collection_result;
pub(in crate::codegen_ay::chc) use types_collection_result::{
    AllocCallResult, CollectionCallResult, StubTranslateArgs,
};

// Re-export globals for sibling modules in chc/
pub(in crate::codegen_ay::chc) use globals::{
    CHC_DEBUG_FLAG, PENDING_FRESH_VAR_DECLS, UNDEF_COUNTER, chc_debug_enabled, chc_fresh_name,
    declare_pending_var, push_pending_datatype_sort, record_aggregate_encoding_gap_for_fn,
    record_aggregate_gap_reason_for_fn, record_drop_fallback_reason_for_fn,
    record_fp_bitvector_encoding_for_fn, record_kani_mem_overapprox_for_fn,
    record_offset_provenance_unresolved_for_fn, record_ptr_metadata_unconstrained_for_fn,
    record_signedness_fallback_for_fn, record_sound_havoc_drop_for_fn,
    record_static_init_incomplete_for_fn, record_store_dropped_for_fn,
    record_stub_approximation_for_fn, record_translation_drop_for_fn,
    record_translation_drop_site_reason_for_fn, record_type_sort_fallback,
    record_type_sort_fallback_for_fn, record_unhandled_call_for_fn, set_chc_fallback_count_for_fn,
};
// Re-export test-only globals: chc-only at chc scope, cross-module at codegen_ay scope
#[cfg(test)]
pub(in crate::codegen_ay::chc) use globals::get_chc_fallback_counts;
pub(in crate::codegen_ay::chc) use globals::push_pending_var_decl;
#[cfg(test)]
pub(in crate::codegen_ay) use globals::{
    clear_chc_fallback_counts, get_chc_unhandled_call_count, set_chc_fallback_count_for_test,
    set_chc_unhandled_call_count_for_test, set_type_sort_fallback_count_for_test,
};
pub(in crate::codegen_ay) use globals::{
    get_aggregate_encoding_gap_count, get_fp_bitvector_encoding_count,
    get_inferable_predicate_count, get_ptr_metadata_unconstrained_count,
    get_rounding_assertion_bypass_count, get_static_init_incomplete_count,
    get_stub_approximation_count, take_chc_diverging_call_drop_count, take_chc_fallback_counts,
    take_chc_offset_provenance_unresolved_count, take_chc_unhandled_call_count,
    take_drop_fallback_reasons_by_fn, take_error_blocked_fmt_count,
    take_fp_bitvector_encoding_by_fn, take_fp_bitvector_encoding_count,
    take_inferable_predicate_count, take_inferable_summary_names_by_fn,
    take_kani_mem_overapprox_by_fn, take_kani_mem_overapprox_count,
    take_known_stdlib_unconstrained_count, take_offset_provenance_unresolved_by_fn,
    take_ptr_metadata_unconstrained_by_fn, take_ptr_metadata_unconstrained_count,
    take_signedness_fallback_by_fn, take_sound_havoc_drop_by_fn, take_static_init_incomplete_by_fn,
    take_static_init_incomplete_count, take_store_dropped_by_fn, take_translation_drop_by_fn,
    take_translation_drop_site_reasons_by_fn, take_type_sort_fallback_by_fn,
    take_type_sort_fallback_count, take_undef_counter, take_unhandled_call_by_fn,
};

use diagnostics::CellCounter;
pub(in crate::codegen_ay::chc) use diagnostics::ChcDiagnostics;

pub(in crate::codegen_ay::chc) use clusters::{
    CollectionState, EncodeState, FlattenState, LivenessState, StateVarManager,
};

// Re-export types for sibling modules in chc/
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) use types::ChcCollectionLenState;
pub(in crate::codegen_ay) use types::{ChcConfig, ChcDebugMode, WideMemMode};
pub(in crate::codegen_ay::chc) use types::{CollectionProjectionKind, RefTarget};

use ay_bindings::{Expr, Sort};
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{BasicBlockIdx, Body, Rvalue, TerminatorKind, UnwindAction};
use std::cell::OnceCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use tracing::{debug, warn};
use trust_mc_core::chc::ChcVc;

use super::super::stubs::StubRegistry;
use super::super::types::POINTER_WIDTH;
use super::codegen_types::CodegenTypes;
use super::fragment::FragmentAnalysis;
use super::heap_state::ChcHeapState;
use super::memory_model::WideMemManager;
use crate::args::{ChcStepMode, ChcTrackLevel};

/// Per-reason soundness of a sound-fallback site (Part of #unsound-havoc-split).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum FallbackSoundness {
    /// The audit certified this site as a fresh unconstrained havoc: the
    /// destination is left universally quantified (a monotone-conservative
    /// over-approximation that ADDS behaviors and can never remove an error
    /// edge). A PROOF under it is valid for all concrete values, so it does not
    /// qualify the proof.
    SoundHavoc,
    /// SUSPECT/UNSOUND or unlisted: the over-approximation is caller-dependent,
    /// carries stale input, or drops a havoc/obligation, so it cannot be
    /// certified. Fail-closed: any Success harness carrying one is forced to
    /// Unknown.
    FailClose,
}

/// Classify a sound-fallback reason string. Default is `FailClose`: the ONLY
/// reasons blessed as `SoundHavoc` are those the per-site soundness audit rated
/// SOUND_OVERAPPROX, so no new/unlisted reason is ever silently treated as a
/// clean proof. See the audit for the per-reason verdict basis.
pub(in crate::codegen_ay::chc) fn fallback_soundness(reason: &str) -> FallbackSoundness {
    match reason {
        "boxnew_payload_store_drop"
        | "iter_adapter_no_sidecar"
        | "state_idx_missing_simple_assign"
        | "assign_sort_mismatch_bv"
        | "assign_sort_mismatch_nonbv"
        | "state_idx_missing_ref_mirror"
        | "state_idx_missing_deref_store_target"
        | "state_idx_missing_scalar_ref_store"
        | "store_adt_field_offset_unknown"
        | "flatten_field_sort_mismatch"
        | "coroutine_closure_unsupported"
        | "rawptr_operand_translation_failed"
        | "rvalue_len_fallback"
        | "transmute_layout_fallback"
        | "set_discriminant_fallback"
        | "raw_ptr_deref_unresolved_fail_closed"
        | "rvalue_deref_load_unresolved"
        | "assume_guard_dropped"
        | "constraint_invariant_fixup"
        // #4225 unsize-coercion alias store dropped on elem-sort mismatch
        // (unsize_dyn.rs): a DROPPED store only widens behavior — reads of the
        // dyn-tail byte view become unconstrained (fresh) — and no UB check is
        // predicated on the store occurring (source and alias share the same
        // (obj,offset) bounds). ∀-sound; the buggy-variant duals
        // (dual_buggy_outer_coercion/low_byte) stay FAILED. Un-blessed this
        // FailClosed ~20 clean dyn-trait proofs to Unknown via Step C.
        | "unsize_alias_width_mismatch"
        // Task #69 audit (see codegen_call_vec_ops_len.rs::vec_op_clone
        // terminal fallback for the full written audit): the clone destination
        // state var reaches the head as a fresh, unconstrained `__out` havoc
        // (universally quantified — monotone). The only accompanying
        // constraints are the sidecar pins dst_len := src_len (exact real
        // clone semantics) and dst_cap := src_cap (the uniform VecClone stub
        // semantics shared with the fully-modeled paths); no stale-input
        // constraint touches the havocked var, and dest adapter_source_data is
        // invalidated at dispatch. ∀-sound; blessing keeps parity untouched
        // with attribution visible.
        | "vec_clone_dest_unconstrained"
        // Task #78 (walker nested-call fallback, terminator_exec.rs): a call
        // the walker could not inline (no stdlib MIR, unhandled stub) writes a
        // FRESH `__nested_call_overapprox` `declare-var` to the destination.
        // A declare-var is universally quantified over its rule, so the rule
        // must hold for EVERY value the var can take — a superset of what the
        // real callee could return. That is monotone: it can only add
        // behaviours, never remove one, so no proof this admits is a false
        // proof. (The two narrowing shapes that ride the same path — a valid
        // heap backing for provably-allocating collection constructors, and
        // alignment/non-null invariants on a pointer destination — are
        // pre-existing audited decisions gated on their own predicates, not
        // part of this blessing.)
        //
        // Blessed rather than fail-closed because the alternative demotes every
        // CHC harness that touches an un-inlinable stdlib call — nearly all of
        // them — turning clean proofs into Unknown to fix a COUNTEREXAMPLE
        // labelling bug. The SoundHavoc lane is precisely the right one: it is
        // excluded from the proof qualifier (proofs stay clean) while still
        // tagging a dependent counterexample OverApproximation.
        | "nested_call_overapprox"
        // P4-4 audit (emit_math_axiom_goto_extra): PURE math intrinsic
        // (sin/cos/sqrt/exp/powf even-power) — the destination is the call's
        // only effect; it reaches the head as fresh havoc constrained only by
        // proof-STRENGTHENING range axioms that every concrete execution
        // satisfies (module math_range_axioms, NaN/finite-guarded). No memory
        // side effect exists to be identity-retained, so the fallback is a
        // strict over-approximation. ∀-sound. Duals: dual_p4_float_nan.rs
        // (sine value not pinned; powf lower bound refutable) stay FAILED.
        //
        // #4270 / TL18 UPDATE: the destination is now bound to a select over
        // the frozen `call_uf_tbl` (call_uf_table.rs) instead of a bare fresh
        // variable. This does NOT weaken the audit. The table is never
        // constrained anywhere, so for a FIXED key the ∀-quantified table
        // still ranges over every value of the sort — the destination remains
        // universally quantified and no behaviour is removed. What the select
        // adds is CONGRUENCE: two sites with the same intrinsic and the same
        // argument value now get the same result, which is what the real
        // function does (`sin(x) == sin(x)` was previously unprovable because
        // the two sites drew independent havocs). Arguments that differ stay
        // independent — `sin(x) == sin(y)` is still refutable.
        // Bounded-inline SwitchInt branch fallback (switchint.rs
        // `switchint_branch_fallback`): the branch result is a FRESH,
        // universally-quantified variable of the callee's return sort — a
        // certified fresh havoc, not a dropped constraint on an existing var.
        // This site previously recorded NOTHING at all, so blessing it here is
        // a strict INCREASE in accounting: proof behaviour is unchanged (which
        // is what SoundHavoc buys) while every counterexample that reads the
        // freed value is now demoted by `classify_ctrex`, and one that is
        // provably independent of it is re-certified Genuine by
        // `recertify_overapprox_ctrex`. RECEIPT: kani/Intrinsics/Count/ctlz.rs
        // and cttz.rs — the reference loop outruns the replay budget, the
        // residual becomes this variable, and the assertion over it was
        // reported as a genuine failed assertion.
        | "switchint_branch_overapprox"
        | "math_axiom_range_overapprox"
        // #4270 / TL18 audit (see call_uf_table.rs for the full written gate):
        // an ESTABLISHED-pure scalar callee summarised by the frozen congruent
        // table. `established_pure_scalar_callee` reads the callee's MIR body
        // (not its signature shape) and admits it only when the body has no
        // Deref, no reference/raw-pointer constant, no pointer-creating rvalue,
        // no memory intrinsic, no panicking terminator (no `Assert`, so an
        // overflow check is never swallowed) and no nested call outside the
        // same gate or the total/pure bit intrinsics. Such a callee's ONLY
        // observable effect is its return value, which reaches the head as
        // `select` over a table that is never constrained anywhere -- the real
        // function is one interpretation of it, so the term is universally
        // quantified exactly like a fresh havoc, only congruent. No memory
        // side effect exists to be identity-retained. ∀-sound; a callee that
        // can panic, read a static or take a pointer FAILS the gate and keeps
        // the fail-closed `call_dispatch_fallback_prebuilt` havoc.
        => FallbackSoundness::SoundHavoc,
        // NOT blessed: "call_uf_congruent_summary". The UF-summary lane replaces
        // an unconditional fail-closed `return None` in `fallback_dispatch.rs`,
        // so blessing it would let a `Success` stand UN-DEMOTED. Its author
        // could not construct a harness where the lane both fires and the solver
        // decides, i.e. it was argued from code review, never observed. A/B on
        // the kani suite with it blessed vs fail-closed is BYTE-IDENTICAL
        // (parity 472, fp 9, missed_bug 0) — it buys nothing measurable, so it
        // is pure risk surface against a fail-closed net. Bless it only with a
        // harness that demonstrates the lane firing AND the verdict changing.
        // Everything else — including all SUSPECT/UNSOUND reasons (flatten
        // self-loops, drop_fallback, kani_write_any_slim_target_unresolved,
        // call_dispatch_fallback, float_*_fallback, offset_pointee_size_unknown,
        // flattened_fields_unconstrained, flattened_bare_read,
        // proj_no_field_projections, rawptr_fat_metadata_dropped,
        // infer_flattened_discr_*, …) and any reason not yet audited.
        _ => FallbackSoundness::FailClose,
    }
}

/// Context for CHC code generation.
///
/// Holds state needed to translate a MIR body into CHC relations and rules.
pub(in crate::codegen_ay) struct ChcCtx<'tcx, 'body> {
    /// The Rust compiler type context.
    pub(in crate::codegen_ay::chc) tcx: TyCtxt<'tcx>,

    /// The MIR body being translated.
    pub(in crate::codegen_ay::chc) body: &'body Body,

    /// The CHC verification condition being built.
    pub(in crate::codegen_ay::chc) vc: ChcVc,

    /// Map from basic block index to relation name.
    /// Arc<str> values: cloning is O(1) ref-count bump instead of O(n) String copy.
    pub(in crate::codegen_ay::chc) block_relations: HashMap<BasicBlockIdx, Arc<str>>,

    /// Reverse lookup for block relation names.
    /// Keeps `refresh_block_relation_app()` at O(1) instead of scanning
    /// `block_relations` on every rule emission.
    pub(in crate::codegen_ay::chc) rel_name_to_bb: HashMap<Arc<str>, BasicBlockIdx>,

    /// The function name (for generating unique relation names).
    /// Arc<str>: set once at construction, cloned into diagnostics maps at O(1).
    pub(in crate::codegen_ay::chc) fn_name: Arc<str>,

    /// Monomorphized function instance for the body currently being encoded.
    /// Used to resolve body-local generic parameters in heap helpers.
    pub(in crate::codegen_ay::chc) current_instance: Option<Instance>,

    /// State variable management: input/output vars, local-to-index mapping,
    /// name indices, declared-name dedup set, per-block live sets.
    /// Part of #2880 P4: extracted from 7 direct fields to StateVarManager cluster.
    pub(in crate::codegen_ay::chc) state_var_mgr: StateVarManager,

    /// Flattened-local metadata: which locals are decomposed, field counts, enum discr.
    /// Part of #2880 P2: extracted from 3 direct fields to FlattenState cluster.
    pub(in crate::codegen_ay::chc) flatten: FlattenState,

    /// Stub registry for intercepting BigInt and other library calls (Part of #734).
    pub(in crate::codegen_ay::chc) stub_registry: StubRegistry,

    /// Reference resolution state: BigInt/BigRational ref targets, deref chain
    /// targets, static ref mapping, const ref discriminants/values.
    /// Part of #2880 P3: extracted from 8 direct fields to RefResolution cluster.
    pub(in crate::codegen_ay::chc) ref_resolution: RefResolution,

    /// Per-block encoding state: expression env, signedness, field env, modified indices,
    /// and cached stack allocation constraints for entry rule generation.
    /// Part of #2952 Phase 2: EncodeState extraction (5 fields -> 1 cluster field).
    pub(in crate::codegen_ay::chc) encode: EncodeState,

    /// CHC memory tracking precision level.
    /// Controls how memory operations (loads/stores through pointers) are modeled.
    pub(in crate::codegen_ay::chc) track_level: ChcTrackLevel,

    /// CHC encoding step granularity (#112).
    /// `Small`: one predicate per basic block. `Large`: one predicate per cut point.
    pub(in crate::codegen_ay::chc) step_mode: ChcStepMode,

    /// Lift bitvector sorts to integer for loop-header CHC predicates.
    /// When true, scalar BV locals (excluding Range fields) are declared with
    /// Int sort, letting PDR synthesize invariants in LIA instead of BV theory.
    /// Part of #112: designs/2026-03-03-loop-invariant-synthesis.md Direction 2.
    pub(in crate::codegen_ay::chc) int_lift: bool,
    /// Narrow each block relation's frame to backward-live columns (`ChcConfig`).
    pub(in crate::codegen_ay::chc) frame_narrowing: bool,
    pub(in crate::codegen_ay::chc) frame_narrowing_flattened: bool,

    /// Basic block indices identified as loop headers (back-edge targets).
    /// Populated during fragment analysis or block relation declaration.
    /// Used by int_lift to scope sort conversion to loop-relevant predicates.
    /// Part of #112.
    pub(in crate::codegen_ay::chc) loop_headers: HashSet<BasicBlockIdx>,

    /// State var indices that were lifted from BV to Int, with original BV widths
    /// and signedness. Used by entry rule generation to add BV-range bounding
    /// constraints: `0 <= x < 2^w` for unsigned, `-2^(w-1) <= x < 2^(w-1)` for
    /// signed. Key: vec_idx, Value: (orig_bv_width, is_signed).
    /// Part of #112 Direction 2 step 2. Part of #3169: signed bounds fix.
    /// Part of #2267: HashMap for O(1) lookup (was Vec with O(n) linear search).
    pub(in crate::codegen_ay::chc) int_lifted_vars: HashMap<usize, (u32, bool)>,

    /// Fragment analysis result for large-step encoding (#112).
    /// Populated in `declare_block_relations()` when `step_mode == Large`.
    /// Contains cut points, fragment partition, and exit edges used by
    /// `generate_transition_rules()` to emit per-fragment CHC rules.
    pub(in crate::codegen_ay::chc) fragment_analysis: Option<FragmentAnalysis>,

    /// Heap state for abstract memory modeling (Part of #869).
    /// Enables CHC encoding of references, pointers, and heap operations.
    pub(in crate::codegen_ay::chc) heap_state: ChcHeapState,

    /// Collection and iterator tracking state: len/cap vars, projections, dedup.
    /// Part of #2952 Phase 2: CollectionState extraction (3 fields -> 1 cluster field).
    pub(in crate::codegen_ay::chc) collections: CollectionState,

    /// Wide memory manager for bounds checking (Part of #1860).
    /// Initialized when `--ay-wide-mem` flag is set.
    /// Used to generate `is_dereferenceable` constraints before memory accesses.
    /// If `Some`, wide memory mode is enabled; if `None`, standard memory model.
    pub(in crate::codegen_ay::chc) wide_mem_manager: Option<WideMemManager>,

    /// Dead-local tracking state: per-block entry sets + mutable per-block set.
    /// Part of #2880 P1: extracted from 2 direct fields to LivenessState cluster.
    pub(in crate::codegen_ay::chc) liveness: LivenessState,

    /// Set to true when a Ref/AddressOf with projections is encountered at
    /// Reg/Ptr level and requires mem-track. Used by `mir_to_chc` to
    /// auto-promote and retry at Mem level (Part of #2084).
    pub(in crate::codegen_ay::chc) needs_mem_promote: bool,

    /// Count of type/size fallback defaults used during encoding (Part of #2234).
    /// Non-zero means the verifier substituted hard-coded defaults for unresolved
    /// types or sizes — verification results may be unsound.
    pub(in crate::codegen_ay::chc) fallback_count: usize,

    /// Per-context diagnostic counters consolidated from 20+ global atomics.
    /// Part of #2906: counter registry consolidation.
    pub(in crate::codegen_ay::chc) diagnostics: ChcDiagnostics,

    /// Enable extra pointer checks (offset overflow). Part of #3176.
    pub(in crate::codegen_ay::chc) extra_pointer_checks: bool,

    /// Prove safety only: suppress user assertion/panic error rules, keep safety checks.
    /// Part of #4217: --prove-safety-only flag implementation.
    pub(in crate::codegen_ay::chc) prove_safety_only: bool,

    /// `-Z uninit-checks` is active: thread the scalar shadow-memory state vars
    /// and encode real verdicts for mem-init model calls (MEMUB-24/25/27).
    pub(in crate::codegen_ay::chc) uninit_checks: bool,

    /// P2-S1: contract CHECK harness — havoc mutable statics and the
    /// interior-mutable (UnsafeCell-covered) parts of immutable statics
    /// instead of pinning them to initializers (Kani `--enforce-contract`
    /// semantics; pinning is a fail-open for contracts that only hold for
    /// the initializer value). See `collect_static_state_vars`.
    pub(in crate::codegen_ay::chc) contract_static_havoc: bool,

    /// Emit memory-safety error rules.
    pub(in crate::codegen_ay::chc) memory_safety_checks: bool,

    /// Emit arithmetic overflow error rules.
    pub(in crate::codegen_ay::chc) overflow_checks: bool,

    /// Emit NaN-generation obligations for float binops (`--nan-check`).
    pub(in crate::codegen_ay::chc) nan_checks: bool,

    /// Emit error rules for reachable undefined foreign function calls.
    pub(in crate::codegen_ay::chc) undefined_function_checks: bool,

    /// Harness unwind depth for bounded recursive inline (Part of #3929).
    pub(in crate::codegen_ay::chc) recursive_unwind_depth: u32,
    /// Part of #55 piece 3: node budget for const-argument recursion
    /// depth-relief. Counts self-recursive inline entries granted the raised
    /// depth bound; when spent, relief stops and the walk fail-closes on the
    /// existing typed recursion-unwind exhaustion lane.
    pub(in crate::codegen_ay::chc) const_recursion_nodes_spent: usize,

    /// Residual-775 Wall-1 P5.3: per-harness budget counter for virtual-inline
    /// SwitchInt sub-walks. Each unique-target branch walk in
    /// `translate_switchint_ite` spends one node; nested SwitchInts fork
    /// sub-walks multiplicatively, so a pathological body can otherwise burn
    /// the driver watchdog to a hard kill (DriverTimeout). On exhaustion the
    /// SwitchInt takes the SAME sound-overapprox bail path as
    /// `MAX_SWITCHINT_DEPTH`, with a FailClose
    /// `record_sound_fallback_reason("walker_node_budget_exhausted")` so any
    /// resulting verdict is an honest Demoted UNDETERMINED — never a false
    /// Safe. Lives on ChcCtx (like `const_recursion_nodes_spent`) so it
    /// resets per harness codegen.
    pub(in crate::codegen_ay::chc) switchint_walk_nodes_spent: usize,

    /// P2 S3 Stage A (honesty-only): depth of the currently-walking
    /// `kani_register_contract` closure inline, incremented/decremented as a
    /// scope guard around `translate_closure_inline_result` in the two
    /// register_contract dispatchers (`codegen_call_closure/register_contract`
    /// and `codegen_call_virtual_inline/register_contract`). Non-zero means
    /// the walk is under a contract check/replace frame: an UNTRACKED
    /// writeback there silently drops contract-visible state, so the
    /// resulting counterexample/proof is fabricated — the drop site books a
    /// demoting `record_fallback()` instead of continuing silently.
    pub(in crate::codegen_ay::chc) register_contract_walk_depth: usize,

    /// Emit failing guard on recursive unwind exhaustion (Part of #3929).
    /// Currently used only for configuration threading; fail-closed guard
    /// emission is deferred to a follow-up (#3929 stretch).
    #[allow(dead_code)]
    pub(in crate::codegen_ay::chc) unwinding_assertions: bool,

    /// Vtable discriminant per dyn Trait local (Part of #3159). Maps local_idx → vtable Expr.
    /// Populated when Dyn_Trait RHS is coerced to BV64; read by virtual dispatch.
    pub(in crate::codegen_ay::chc) dyn_vtable_ids: HashMap<usize, Expr>,

    /// CHC state variable names for vtable discriminants (Part of #3159).
    /// Maps local_idx → (input_var_name, output_var_name) for path-sensitive
    /// vtable tracking. Unlike `dyn_vtable_ids` (compile-time HashMap that gets
    /// overwritten), these are CHC state variables threaded through rules,
    /// making vtable values path-sensitive across branches.
    /// Part of #2267: Arc<str> avoids deep String clones on vtable state var lookups.
    pub(in crate::codegen_ay::chc) vtable_state_vars: HashMap<usize, (Arc<str>, Arc<str>)>,

    /// Vtable propagation edges: dst_local -> src_local for Copy/Move chains.
    /// Part of #4217: enables backward reachability from dispatch sites to
    /// capture sites, so vtable SVs not on any capture->dispatch path are pruned.
    pub(in crate::codegen_ay::chc) vtable_propagation_edges: HashMap<usize, usize>,

    /// Vtable type metadata: maps vtable_id → (size_bytes, align_bytes).
    /// Populated at Unsize coercion sites when a concrete type is cast to
    /// dyn Trait. Used to constrain vtable_size/vtable_align intrinsics.
    /// Part of #3159: DynTrait category recovery — vtable metadata constraining.
    pub(in crate::codegen_ay::chc) vtable_type_metadata: HashMap<u64, (u64, u64)>,

    /// Pre-declared concrete layouts from Unsize coercion sources.
    /// Populated by the vtable pre-declaration pass with (size, align) pairs
    /// extracted from concrete types before vtable IDs are assigned.
    /// Used as fallback by layout_semantic and size_of_val/align_of_val stubs
    /// when vtable_type_metadata is empty (early-block ordering).
    /// Part of #3347: Separate from vtable_type_metadata to avoid ID collisions.
    pub(in crate::codegen_ay::chc) predeclared_concrete_layouts: Vec<(u64, u64)>,

    /// Known-concrete Layout values: maps local_idx → (size_bytes, align_bytes).
    /// Populated by all semantic layout handlers (LayoutNew, LayoutForValueRaw,
    /// LayoutArray, LayoutArrayInner, LayoutFromSizeAlign{,Unchecked}) when they
    /// produce compile-time-known (size, align) pairs.
    /// Used by alloc_zeroed window bounding (#3107) and realloc layout-pair
    /// recovery (#3641).
    pub(in crate::codegen_ay::chc) known_layout_sizes: HashMap<usize, (u64, u64)>,

    /// Per-local single-writer MIR summary used by the address-provenance walk
    /// (`mir_provable_referent_local`). Built once per body: the walk is asked
    /// the same question at many statements, and rescanning every block per hop
    /// made it quadratic in body size.
    pub(in crate::codegen_ay::chc) provenance_defs:
        std::cell::OnceCell<Vec<Option<crate::codegen_ay::chc::stmt::ProvDef>>>,

    /// Memo for `mir_provable_referent_local`, keyed by `(local, depth)`.
    /// Two of the walk's hops recurse, so without it a single query re-walks
    /// the same locals exponentially (a contract harness spent ~25s there).
    pub(in crate::codegen_ay::chc) provenance_walk_memo:
        std::cell::RefCell<HashMap<(usize, usize), Option<usize>>>,

    /// Known allocation IDs: maps local_idx → heap alloc obj_id (Part of #3273).
    /// Populated by `codegen_call_alloc` when `translate_rust_alloc` returns a
    /// concrete obj_id. Used by `translate_rust_realloc` to resolve symbolic
    /// old pointer obj_ids through MIR assignment tracing.
    pub(in crate::codegen_ay::chc) known_alloc_ids: HashMap<usize, u32>,

    /// Rc/Arc allocation IDs observed through clone.
    ///
    /// Without explicit reference-count state, a cloned Rc/Arc allocation is
    /// non-unique. Dropping one wrapper must not eagerly invalidate the backing
    /// allocation when the pointee has no assertion-visible drop effects.
    pub(in crate::codegen_ay::chc) rc_arc_shared_alloc_ids: HashSet<u32>,

    /// Locals known to hold a concrete stack-local address.
    ///
    /// Kept separate from `known_alloc_ids`: these object IDs name synthetic
    /// stack locals, not heap allocations, so they must not participate in
    /// heap dealloc/ownership reasoning. Deref translation uses these entries
    /// to canonicalize pointer locals before heap access checks.
    pub(in crate::codegen_ay::chc) known_stack_addr_exprs: HashMap<usize, Expr>,

    /// Field-granular data-pointer provenance for Box/pointer-wrapper containers.
    ///
    /// Records that a specific FIELD of a container local holds a pointer into a
    /// concrete heap allocation. Populated (writer) when a container local
    /// receives a heap alloc-id under the single-assignment provenance gate at
    /// construction (`propagate_alloc_ids_for_assign` / `record_alloc_dest`).
    /// Consumed (reader) when a subsequent assignment reads that field
    /// (`X = Copy(container.field)` or `X = Copy((*ref).field)`), so the loaded
    /// local resolves to the heap DATA allocation (`obj_H`) rather than the
    /// container's own stack slot (`obj_C`). Fixes the Box<dyn>/drop-glue
    /// dealloc size/stack-object false positives (dyn_fn_once).
    ///
    /// Key: `(container_local, field_index)`.
    /// Value: `obj_id` of the heap allocation that field points into.
    ///
    /// Soundness: entries are only written when the container is written exactly
    /// once directly and is never stored-through (see the field-0 forward lane);
    /// the reader additionally requires the deref source to be single-assignment.
    pub(in crate::codegen_ay::chc) known_pointer_to_alloc: HashMap<(usize, usize), u32>,

    /// Declared inferable function summaries: callee_name → (arg_sorts, ret_sort).
    /// Deduplicates `Decl::Fun` declarations in the VC for solver-inferable
    /// summaries (Part of #3395). Multiple calls to the same function reuse
    /// the existing uninterpreted function declaration if sorts match.
    pub(in crate::codegen_ay::chc) declared_inferable_fns: HashMap<String, (Vec<Sort>, Sort)>,

    /// Per-VC callee tags for the frozen congruent call-summary table
    /// (`call_uf_table.rs`): mangled callee name -> tag occupying the fixed
    /// high 32 bits of the table key. Sequential and monomorphisation-unique,
    /// so two distinct callees can never select the same table entry (a
    /// collision would ASSERT an equality that need not hold). `BTreeMap` for
    /// deterministic tag assignment across runs.
    pub(in crate::codegen_ay::chc) call_uf_tags: std::collections::BTreeMap<String, u32>,

    /// Locals known to hold a power of 2: maps local_idx → exponent Expr.
    /// Populated by `codegen_pow` when base == 2 (result = `2^exp`).
    /// Consumed by `codegen_euclid` to replace `div_euclid(a, 2^n)` with
    /// `bvashr(a, n)` (signed) or `bvlshr(a, n)` (unsigned), eliminating the
    /// complex ite/bvsdiv decomposition that PDR cannot synthesize invariants for.
    /// Part of #3428.
    pub(in crate::codegen_ay::chc) known_pow2_locals: HashMap<usize, Expr>,

    /// Current basic block index being encoded. Set at the start of
    /// `encode_block_statements` and used by `mark_type_array_read` to record
    /// per-block read tracking for error-path-aware pruning.
    /// Part of #3436: error-path type array pruning.
    pub(in crate::codegen_ay::chc) current_encode_bb: usize,

    /// FC-06: modifies frames (dynamic extents of contract-checked functions)
    /// found by `modifies_frame::prescan_modifies_frames`. Memory stores in
    /// extent blocks are checked against the frame's declared footprint.
    pub(in crate::codegen_ay::chc) modifies_frames: Vec<super::modifies_frame::ModifiesFrame>,

    /// FC-06: extent block index → index into `modifies_frames`.
    pub(in crate::codegen_ay::chc) modifies_frame_by_bb: HashMap<usize, usize>,

    /// FC-29: loop assigns frames (`#[kani::loop_modifies(...)]` regions)
    /// found by `loop_modifies_frame::prescan_loop_modifies_frames`. Register
    /// stores in loop-region blocks are checked against the declared coverage.
    pub(in crate::codegen_ay::chc) loop_modifies_frames:
        Vec<super::loop_modifies_frame::LoopModifiesFrame>,

    /// FC-29: loop-region block index → index into `loop_modifies_frames`
    /// (innermost frame wins for nested loops).
    pub(in crate::codegen_ay::chc) loop_modifies_frame_by_bb: HashMap<usize, usize>,

    /// Suppress heap validity/bounds checks for fresh-allocation stores.
    ///
    /// BoxNew writes into a pointer returned by the current allocation call, so
    /// the destination write is valid by construction. This flag suppresses the
    /// write-side `build_memory_store()` checks while still allowing unrelated
    /// source-load checks (for translated operands) to be recorded and emitted.
    pub(in crate::codegen_ay::chc) suppress_heap_store_checks: bool,

    /// Active fragment-composition output block, if large-step composition is
    /// currently encoding a non-final block.
    ///
    /// Part of #3661/#3655: late-created state vars need the same `__mid_bbN`
    /// output naming as the original state-var snapshot when they are born
    /// during composed block encoding.
    pub(in crate::codegen_ay::chc) fragment_mid_output_bb: Option<usize>,

    /// Maps mangled FnDef names to unique BV64 pointer values.
    /// Ensures distinct monomorphizations (e.g., `poly::<usize>` vs `poly::<isize>`)
    /// get different fn pointer constants for equality/inequality assertions.
    /// Part of #3470: fn pointer identity encoding.
    pub(in crate::codegen_ay::chc) fn_ptr_ids: HashMap<String, Expr>,

    /// Counter for generating unique fn pointer IDs. Part of #3470.
    pub(in crate::codegen_ay::chc) next_fn_ptr_id: u64,

    /// Depth guard for `try_resolve_deref_via_ref_targets` recursion.
    /// Self-referencing ref_targets cause unbounded cycles. Cap at 4 hops
    /// (Pin<&mut T> needs ≤3). Part of #3823.
    #[allow(dead_code)]
    pub(in crate::codegen_ay::chc) deref_resolve_depth: usize,

    /// Pre-computed flattened field expressions for inline self parameter.
    ///
    /// When the fn_inline dispatch caller detects that arg[0] references a
    /// flattened local, it pre-populates this map with `(1, field_idx) → Expr`
    /// entries. `build_self_field_map` consumes the hint if present, giving the
    /// inline walker Array-sorted field values instead of BV64 heap addresses.
    ///
    /// Part of #3830: Bridges flattened state var data into the inline walker.
    pub(in crate::codegen_ay::chc) inline_self_field_hints: Option<HashMap<(usize, usize), Expr>>,

    /// Scoped synthetic addresses for inline locals that need place semantics.
    ///
    /// The body key is the active callee MIR body pointer. Nested inline walks
    /// save/restore this field so address hints only apply to the body that
    /// created them.
    ///
    /// Part of #3906: preserve address identity for address-taken ZST params in
    /// fn-pointer closure inline translation.
    pub(in crate::codegen_ay::chc) inline_local_address_hints:
        Option<(usize, HashMap<usize, Expr>)>,

    /// Scoped vtable schedule for `block_on_with_spawn` D3 dispatch.
    ///
    /// The async spawn runtime stores spawned tasks behind `Pin<Box<dyn Future>>`
    /// in a `Vec`, which loses the concrete vtable identity needed later at the
    /// `Scheduler::run` dyn-poll site. When a `block_on_with_spawn` call can
    /// recover the concrete root/spawned future types up front, it installs this
    /// bounded poll schedule so `Scheduler::run` can reuse those vtable IDs
    /// instead of falling back to a fresh symbolic vtable.
    pub(in crate::codegen_ay::chc) spawn_scheduler_vtable_model: Option<SpawnSchedulerVtableModel>,

    /// Spawn-only dead-state memory keys that can be stubbed during
    /// `block_on_with_spawn` inline translation.
    ///
    /// These are fragment matches rather than exact type keys because MIR type
    /// keys bake generic detail into some carriers (`PhantomData<fnptr...>`,
    /// `AssertUnwindSafe<ExtData>`, `ref_Waker`, ...).
    pub(in crate::codegen_ay::chc) spawn_stubbed_type_key_fragments: HashSet<Arc<str>>,

    /// Precomputed global assignment map (local_idx → last whole-body assignment
    /// Rvalue). A pure function of `body`, built once at construction and reused
    /// across all callers instead of being rebuilt on every raw-pointer deref /
    /// pointer-check suppression query. Part of the null-provenance perf fix:
    /// `build_global_assignment_map` was previously an O(body) rebuild per
    /// raw-ptr deref, making pointer-heavy bodies quadratic. Stored as a plain
    /// field (not a `OnceCell`) to keep `ChcCtx` covariant in `'body` — an
    /// interior-mutability cell holding `&'body Rvalue` would make it invariant.
    pub(in crate::codegen_ay::chc) global_assignment_map: HashMap<usize, &'body Rvalue>,

    /// Memoized set of null-tainted locals: locals that receive a NULL pointer
    /// value on some assignment path (directly via a null constant / `::null`
    /// / `::null_mut`, or transitively through a copy/cast of a null-valued
    /// local). Computed in a single O(body) pass + transitive closure, replacing
    /// the per-deref recursive whole-body scan (`local_null_assign_rec`). O(1)
    /// membership tests thereafter. Same detection semantics as the old scan;
    /// see `compute_null_tainted_locals`. Part of the null-provenance perf fix.
    pub(in crate::codegen_ay::chc) null_tainted_locals_cache: OnceCell<HashSet<usize>>,
}

pub(in crate::codegen_ay::chc) mod clusters;
mod clusters_ref_resolution;
pub(in crate::codegen_ay::chc) use clusters_ref_resolution::RefResolution;

pub(in crate::codegen_ay::chc) struct SpawnSchedulerVtableModel {
    pub(in crate::codegen_ay::chc) poll_vtable_ids: Vec<u64>,
    pub(in crate::codegen_ay::chc) next_poll_idx: usize,
    pub(in crate::codegen_ay::chc) poll_task_indices: Vec<u64>,
    pub(in crate::codegen_ay::chc) next_task_idx: usize,
    pub(in crate::codegen_ay::chc) current_task_vtable_id: Option<u64>,
    pub(in crate::codegen_ay::chc) scheduler_loop_replay_fuel: Option<usize>,
}

impl SpawnSchedulerVtableModel {
    fn vtable_expr(vtable_id: u64) -> Expr {
        Expr::bitvec_const(vtable_id as u128, POINTER_WIDTH)
    }

    pub(in crate::codegen_ay::chc) fn next_vtable_expr(&mut self) -> Option<Expr> {
        if self.poll_vtable_ids.is_empty() {
            return None;
        }
        // Cycle through vtable IDs: the scheduler loop polls each task
        // multiple times in round-robin order, so the same concrete future
        // types repeat. Cycling is sound because the set of concrete types
        // is bounded and known from the harness's spawn calls.
        let vtable_id = self.poll_vtable_ids[self.next_poll_idx % self.poll_vtable_ids.len()];
        self.next_poll_idx += 1;
        self.current_task_vtable_id = Some(vtable_id);
        Some(Self::vtable_expr(vtable_id))
    }

    pub(in crate::codegen_ay::chc) fn next_task_index(&mut self) -> Option<u64> {
        if self.poll_task_indices.is_empty() {
            return None;
        }
        let task_idx = self.poll_task_indices[self.next_task_idx % self.poll_task_indices.len()];
        self.next_task_idx += 1;
        Some(task_idx)
    }

    pub(in crate::codegen_ay::chc) fn current_vtable_expr(&self) -> Option<Expr> {
        self.current_task_vtable_id.map(Self::vtable_expr)
    }

    pub(in crate::codegen_ay::chc) fn clear_current_vtable(&mut self) {
        self.current_task_vtable_id = None;
    }

    pub(in crate::codegen_ay::chc) fn scheduler_loop_replay_fuel(&self) -> Option<usize> {
        self.scheduler_loop_replay_fuel
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Creates a new CHC context for a MIR body.
    ///
    /// REQUIRES: `tcx` is the type context that produced `body`.
    /// REQUIRES: `body` is a valid MIR body for a single function.
    /// REQUIRES: `fn_name` uniquely identifies the function for relation naming.
    /// ENSURES: Returned context has an empty CHC VC and no declared relations.
    /// ENSURES: Returned context has empty state/output vars and stub registries.
    pub(in crate::codegen_ay) fn new(
        tcx: TyCtxt<'tcx>,
        body: &'body Body,
        fn_name: impl Into<Arc<str>>,
        cfg: ChcConfig,
    ) -> Self {
        Self::new_internal(tcx, body, None, fn_name, cfg)
    }

    /// Creates a new CHC context for a known monomorphized instance.
    pub(in crate::codegen_ay) fn new_with_instance(
        tcx: TyCtxt<'tcx>,
        body: &'body Body,
        instance: Instance,
        fn_name: impl Into<Arc<str>>,
        cfg: ChcConfig,
    ) -> Self {
        Self::new_internal(tcx, body, Some(instance), fn_name, cfg)
    }

    fn new_internal(
        tcx: TyCtxt<'tcx>,
        body: &'body Body,
        current_instance: Option<Instance>,
        fn_name: impl Into<Arc<str>>,
        cfg: ChcConfig,
    ) -> Self {
        let fn_name_string: Arc<str> = fn_name.into();
        let dead_locals_at_entry = Self::compute_dead_locals_at_block_entry(body);
        // Build the whole-body last-assignment map once: reused by every
        // raw-pointer null-deref check and pointer-check suppression query
        // (null-provenance perf fix — was O(body) per raw-ptr deref).
        let global_assignment_map = Self::build_global_assignment_map(body);
        let step_mode = cfg.step_mode;
        let int_lift = cfg.int_lift;
        let frame_narrowing = cfg.frame_narrowing;
        let frame_narrowing_flattened = cfg.frame_narrowing && cfg.frame_narrowing_flattened;
        let wide_mem = cfg.wide_mem;
        let extra_pointer_checks = cfg.extra_pointer_checks;
        let prove_safety_only = cfg.prove_safety_only;
        let uninit_checks = cfg.uninit_checks;
        let memory_safety_checks = cfg.memory_safety_checks;
        let overflow_checks = cfg.overflow_checks;
        let nan_checks = cfg.nan_checks;
        let undefined_function_checks = cfg.undefined_function_checks;
        let recursive_unwind_depth = cfg.recursive_unwind_depth;
        let unwinding_assertions = cfg.unwinding_assertions;
        let contract_static_havoc = cfg.contract_static_havoc;
        if step_mode == ChcStepMode::Large {
            debug!(fn_name = %fn_name_string, "CHC: large-step encoding enabled (#112)");
        }
        // Part of #112 Direction 2: When int-lift is active, automatically
        // downgrade track level to Reg. PDR cannot synthesize invariants
        // involving Array theory (memory maps, obj_valid, obj_size). At Mem
        // track level, relations have ~15 parameters including many Array-sorted
        // vars, causing PDR timeout. At Reg track level, only scalar locals
        // appear, giving PDR the reduced-arity LIA-only relations it needs.
        // This is sound: Reg track is a strictly weaker abstraction that
        // over-approximates memory operations.
        let track_level = if int_lift && cfg.track_level > ChcTrackLevel::Reg {
            debug!(
                fn_name = %fn_name_string,
                original = ?cfg.track_level,
                "CHC int-lift: downgrading track level to Reg (Array vars block PDR)"
            );
            ChcTrackLevel::Reg
        } else {
            cfg.track_level
        };
        if int_lift {
            debug!(fn_name = %fn_name_string, "CHC: int-lift enabled (#112 Direction 2)");
        }
        // Initialize wide memory manager if enabled (Part of #1860)
        let wide_mem_manager = if wide_mem == WideMemMode::On {
            debug!(
                "CHC: Using WideMemManager for function {} (bounds checking enabled)",
                fn_name_string
            );
            Some(WideMemManager::new(POINTER_WIDTH))
        } else {
            None
        };

        // Part of #2267: pre-size core data structures from MIR body dimensions.
        // block_relations: 1 entry per basic block (exact).
        // StateVarManager: local_decls correlates with state var count.
        // EncodeState: per-block maps keyed by local index; clear_block() retains capacity.
        let num_blocks = body.blocks.len();
        let num_locals = body.local_decls().count();
        let spawn_stubbed_type_key_fragments = [
            // Waker/Context carriers — semantically dead noop waker state.
            "std_task_Waker",
            "std_task_LocalWaker",
            "std_task_RawWaker",
            "std_task_RawWakerVTable",
            "std_task_Context",
            "core_task_wake_ExtData",
            "std_marker_PhantomData",
            // Part of #4075 D2: scheduler-internal types whose semantics are
            // fully replaced by the spawn vtable model (poll order, task
            // indices, loop fuel). Stubbing these reduces CHC relation width
            // without affecting proof-relevant data flow (AtomicI64, Arc).
            // NOTE: avoid broad fragments like "std_alloc_Global" that match
            // compound type keys (Box_u8_std_alloc_Global, Arc_..._Global).
            "kani_RoundRobin",
            "kani_futures_SchedulingAssumption",
            "kani_futures_JoinHandle",
            "kani_yield_now_YieldNow",
            "core_num_niche_types",
        ]
        .into_iter()
        .map(Arc::<str>::from)
        .collect();

        Self {
            tcx,
            body,
            vc: ChcVc::new(),
            block_relations: HashMap::with_capacity(num_blocks),
            rel_name_to_bb: HashMap::with_capacity(num_blocks),
            fn_name: fn_name_string,
            current_instance,
            state_var_mgr: StateVarManager::with_capacity(num_locals, num_blocks),
            flatten: FlattenState::new(),
            stub_registry: StubRegistry::new(),
            provenance_defs: std::cell::OnceCell::new(),
            provenance_walk_memo: std::cell::RefCell::new(HashMap::new()),
            ref_resolution: RefResolution::new(),
            encode: EncodeState::with_capacity(num_locals),
            track_level,
            step_mode,
            int_lift,
            frame_narrowing,
            frame_narrowing_flattened,
            loop_headers: HashSet::new(),
            int_lifted_vars: HashMap::new(),
            fragment_analysis: None,
            heap_state: ChcHeapState::new(),
            collections: CollectionState::new(),
            wide_mem_manager,
            liveness: LivenessState::new(dead_locals_at_entry),
            needs_mem_promote: false,
            fallback_count: 0,
            diagnostics: ChcDiagnostics::default(),
            extra_pointer_checks,
            prove_safety_only,
            uninit_checks,
            contract_static_havoc,
            memory_safety_checks,
            overflow_checks,
            nan_checks,
            undefined_function_checks,
            dyn_vtable_ids: HashMap::new(),
            vtable_state_vars: HashMap::new(),
            vtable_propagation_edges: HashMap::new(),
            vtable_type_metadata: HashMap::new(),
            predeclared_concrete_layouts: Vec::new(),
            known_layout_sizes: HashMap::new(),
            known_alloc_ids: HashMap::new(),
            rc_arc_shared_alloc_ids: HashSet::new(),
            known_stack_addr_exprs: HashMap::new(),
            known_pointer_to_alloc: HashMap::new(),
            declared_inferable_fns: HashMap::new(),
            call_uf_tags: std::collections::BTreeMap::new(),
            known_pow2_locals: HashMap::new(),
            current_encode_bb: 0,
            modifies_frames: Vec::new(),
            modifies_frame_by_bb: HashMap::new(),
            loop_modifies_frames: Vec::new(),
            loop_modifies_frame_by_bb: HashMap::new(),
            suppress_heap_store_checks: false,
            fragment_mid_output_bb: None,
            fn_ptr_ids: HashMap::new(),
            next_fn_ptr_id: 1,
            deref_resolve_depth: 0,
            inline_self_field_hints: None,
            inline_local_address_hints: None,
            spawn_scheduler_vtable_model: None,
            spawn_stubbed_type_key_fragments,
            recursive_unwind_depth,
            const_recursion_nodes_spent: 0,
            switchint_walk_nodes_spent: 0,
            register_contract_walk_depth: 0,
            unwinding_assertions,
            global_assignment_map,
            null_tainted_locals_cache: OnceCell::new(),
        }
    }

    // Int-lift helpers (lift_bv_to_int_if_enabled, lift_bv_sort_recording_width,
    // project_state_args, int_lift_range_constraints, project_full_output_to_block)
    // extracted to int_lift.rs — Part of #112 Direction 2.

    /// Record a type/size fallback default being used (Part of #2234).
    /// Increments `chc_fallback` (DEMOTED category) — use only for genuinely
    /// unsound fallbacks where constraints are silently dropped.
    ///
    /// P3-uninit: `#[track_caller]` + debug log so per-site attribution of
    /// demoting fallbacks is visible under `TRUST_MC_LOG=trust_mc_compiler=debug`
    /// (the aggregate `chc_fallback=N` marker alone cannot be triaged).
    #[track_caller]
    pub(in crate::codegen_ay::chc) fn record_fallback(&mut self) {
        self.fallback_count += 1;
        tracing::debug!(
            site = %std::panic::Location::caller(),
            fn_name = %self.fn_name,
            "CHC: demoting chc_fallback recorded"
        );
    }

    /// Record an aggregate encoding gap with a per-site reason tag (Part of #4050).
    /// Increments the `aggregate_encoding_gap` counter AND records the reason
    /// in the per-function aggregate gap reasons map for diagnostic triage.
    pub(in crate::codegen_ay::chc) fn record_aggregate_gap(&self, reason: &str) {
        self.diagnostics.aggregate_encoding_gap.inc();
        record_aggregate_gap_reason_for_fn(&self.fn_name, reason);
    }

    /// Record a diagnostic reason for this function WITHOUT touching any
    /// counter.
    ///
    /// [`Self::record_aggregate_gap`] also `inc()`s `aggregate_encoding_gap`,
    /// which feeds CTREX classification — so it cannot be used purely to label
    /// something. This can: it only adds a string to the per-function reason
    /// map, so it is measurement with no behavioural reach.
    ///
    /// Exists because the walker's nested-call over-approximation knows the
    /// callee it gave up on and recorded only that it happened. That cluster is
    /// the largest non-parity population in the corpus (62 rows on 2026-08-23,
    /// 42 of them spurious counterexamples built on an invented return value),
    /// and without the callee it cannot be triaged.
    pub(in crate::codegen_ay::chc) fn note_gap_reason(&self, reason: &str) {
        record_aggregate_gap_reason_for_fn(&self.fn_name, reason);
    }

    /// Part of #4075 D2: noop-waker/context carriers in the spawn runtime are
    /// semantically dead. While the specialized spawn inline path is active,
    /// their memory arrays can be treated as unconstrained loads / no-op stores
    /// so they do not inflate relation signatures or store chains.
    pub(in crate::codegen_ay::chc) fn should_stub_spawn_type_array(&self, type_key: &str) -> bool {
        self.spawn_scheduler_vtable_model.is_some()
            && self
                .spawn_stubbed_type_key_fragments
                .iter()
                .any(|fragment| type_key.contains(fragment.as_ref()))
    }

    /// Record a sound over-approximation fallback (Part of #3099).
    ///
    /// Routes by per-reason soundness (Part of #unsound-havoc-split):
    /// - `FallbackSoundness::SoundHavoc` reasons (audited certified fresh havoc)
    ///   increment `sound_havoc_drop` (the `ChcSoundHavocDrop` category), which
    ///   the driver EXCLUDES from the sound-fallback proof qualifier, so a proof
    ///   whose only fallbacks are SoundHavoc reports a clean success.
    /// - Everything else (default = fail-close) increments
    ///   `place_translation_drop` (the `ChcTranslationDrop` category), which the
    ///   driver fail-closes to Unknown on any Success harness. This is
    ///   STRUCTURALLY fail-closed: any new/unlisted reason is never silently
    ///   blessed as clean.
    ///
    /// Both counters are SOUND_APPROXIMATION-class, so a spurious counterexample
    /// from either is tagged `OverApproximation` (Unknown), never a false proof
    /// or false positive.
    ///
    /// Part of #3794: also records the caller-provided reason in the
    /// translation-drop site map so the six-file cluster rerun can
    /// distinguish which sound-fallback path fires.
    pub(in crate::codegen_ay::chc) fn record_sound_fallback_reason(
        &mut self,
        reason: &'static str,
    ) {
        match fallback_soundness(reason) {
            FallbackSoundness::SoundHavoc => self.diagnostics.sound_havoc_drop.inc(),
            FallbackSoundness::FailClose => self.diagnostics.place_translation_drop.inc(),
        }
        record_translation_drop_site_reason_for_fn(&self.fn_name, reason);
    }

    /// Task #78: like [`record_sound_fallback_reason`], but ALSO records the
    /// SMT-var IDENTITY this approximation freed into the VC artifact.
    ///
    /// Use this at sound-fallback sites where the freed value's destination SMT
    /// variable is known (`freed_var = Some(name)`) or is provably dead — no
    /// live state slot — (`freed_var = None`). Recording the identity makes the
    /// approximation ACCOUNTED, so it does not block the harness's
    /// approximation-identity completeness. Sites that keep calling the plain
    /// [`record_sound_fallback_reason`] stay UNACCOUNTED and correctly force
    /// incompleteness (fail-closed): the driver refuses to certify a tainted
    /// counterexample Genuine unless every approximation was accounted.
    pub(in crate::codegen_ay::chc) fn record_sound_fallback_reason_identified(
        &mut self,
        reason: &'static str,
        freed_var: Option<&str>,
    ) {
        self.record_sound_fallback_reason(reason);
        self.vc.record_approximation_identity(freed_var);
    }

    /// Categorized sound fallback (Part of #3561 Phase 1).
    /// Increments the global `place_translation_drop` counter AND records the
    /// category tag in `sound_fallback_detail` for per-cluster measurement.
    pub(in crate::codegen_ay::chc) fn record_sound_fallback_categorized(
        &mut self,
        category: &'static str,
    ) {
        self.diagnostics.place_translation_drop.inc();
        *self.diagnostics.sound_fallback_detail.entry(category).or_insert(0) += 1;
    }

    /// Record that a SOUND fallback intentionally uses a concrete value.
    /// This is a correctness-sensitive override: it increments both the sound
    /// fallback counter AND the demoted fallback counter, which triggers BMC
    /// cross-check on any resulting PROOF. Part of #4165, #134.
    ///
    /// Use this instead of `record_sound_fallback_reason` when a SOUND site
    /// must return a concrete value rather than a fresh symbolic. The BMC
    /// cross-check ensures no false proof escapes.
    ///
    /// Currently 0 production callers (by design — safety valve for future use).
    #[allow(dead_code)]
    pub(in crate::codegen_ay::chc) fn record_sound_fallback_concrete_override(
        &mut self,
        reason: &'static str,
    ) {
        self.record_sound_fallback_reason(reason);
        self.fallback_count += 1; // Triggers BMC cross-check via verdict_policy
        tracing::warn!(
            "[AY:CORRECTNESS] SOUND fallback uses concrete value at '{}' in {} — \
             BMC cross-check will fire on PROOF",
            reason,
            self.fn_name,
        );
    }

    /// Get the sound fallback count (Part of #3099).
    /// Returns the number of sound over-approximation fallbacks recorded
    /// via `record_sound_fallback_reason()`. Test-only accessor.
    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(in crate::codegen_ay::chc) fn sound_fallback_count(&self) -> usize {
        // Combined count across the fail-close (`place_translation_drop`) and
        // recognized-clean (`sound_havoc_drop`) lanes, so this test accessor
        // keeps its "any sound fallback recorded" semantics after the
        // SoundHavoc split (Part of #unsound-havoc-split).
        self.diagnostics.place_translation_drop.get() + self.diagnostics.sound_havoc_drop.get()
    }

    /// Get the per-category sound fallback detail map (Part of #3561 Phase 1).
    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(in crate::codegen_ay::chc) fn sound_fallback_detail(
        &self,
    ) -> &std::collections::BTreeMap<&'static str, usize> {
        &self.diagnostics.sound_fallback_detail
    }

    /// Return the scoped synthetic address for an inline local, if one exists
    /// for the currently translated MIR body.
    pub(in crate::codegen_ay::chc) fn inline_local_address_hint(
        &self,
        body: &Body,
        local: usize,
    ) -> Option<Expr> {
        let (body_key, hints) = self.inline_local_address_hints.as_ref()?;
        let current_body_key = std::ptr::from_ref::<Body>(body) as usize;
        if *body_key != current_body_key {
            return None;
        }
        hints.get(&local).cloned()
    }

    /// Record that the state variable at the given index was modified (Part of #2552).
    /// Called by memory, region, metadata, and collection-length subsystems.
    ///
    /// Task #69: `idx` MUST be a STATE-VAR index (into
    /// `state_var_mgr.state_vars`), never a MIR local. MIR locals go through
    /// the `extra_dests` channel of `build_output_args` instead (see the
    /// contract in codegen_call_coerce.rs) — mixing the two index spaces
    /// silently leaves constrained `__out` vars out of the rule head.
    pub(in crate::codegen_ay::chc) fn mark_state_var_modified(&mut self, idx: usize) {
        debug_assert!(
            idx < self.state_var_mgr.state_vars.len(),
            "mark_state_var_modified: index {idx} is outside the state-var space \
             (len {}) — was a MIR local passed instead of a state-var index?",
            self.state_var_mgr.state_vars.len()
        );
        self.encode.modified_state_indices.insert(idx);
    }

    /// The state slot of the `static` a `--c-lib` translation unit names by
    /// LINKER SYMBOL.
    ///
    /// C reaches an exported object by symbol, not by Rust path, so the C
    /// front-end's `S` has to resolve through the symbol table the foreign
    /// static declaration registers — never by matching the Rust name, which
    /// `#[link_name]` is free to differ from.
    pub(in crate::codegen_ay::chc) fn foreign_static_slot(&self, symbol: &str) -> Option<usize> {
        self.ref_resolution.c_symbol_static_state_idx.get(symbol).copied()
    }

    /// The expression denoting a state slot's CURRENT value: its output
    /// variable once something in this block has written it, its input
    /// variable otherwise.
    pub(in crate::codegen_ay::chc) fn state_slot_expr(&self, slot: usize) -> Option<Expr> {
        if self.encode.modified_state_indices.contains(&slot) {
            let (name, sort) = self.state_var_mgr.output_state_vars.get(slot)?;
            return Some(Expr::var(&**name, sort.clone()));
        }
        let (name, sort) = self.state_var_mgr.state_vars.get(slot)?;
        Some(Expr::var(&**name, sort.clone()))
    }

    /// Find the state_var index for a given variable name.
    /// Delegates to `StateVarManager::state_var_index_by_name`.
    pub(in crate::codegen_ay::chc) fn state_var_index_by_name(&self, name: &str) -> Option<usize> {
        self.state_var_mgr.state_var_index_by_name(name)
    }

    /// Find the output_state_var index for a given variable name.
    /// Delegates to `StateVarManager::output_state_var_index_by_name`.
    pub(in crate::codegen_ay::chc) fn output_state_var_index_by_name(
        &self,
        name: &str,
    ) -> Option<usize> {
        self.state_var_mgr.output_state_var_index_by_name(name)
    }

    /// Push a state/output variable pair and update name-to-index maps.
    /// Delegates to `StateVarManager::push_state_var_pair`.
    /// Part of #2267: accepts `&str` to avoid unnecessary String allocations.
    pub(in crate::codegen_ay::chc) fn push_state_var_pair(
        &mut self,
        in_name: &str,
        out_name: &str,
        sort: Sort,
    ) {
        self.state_var_mgr.push_state_var_pair(in_name, out_name, sort);
    }

    /// Push a state/output variable pair when the input name is already `Arc<str>`.
    /// Delegates to `StateVarManager::push_state_var_pair_arc`.
    /// Part of #2267: out_name accepts `&str` to avoid unnecessary String allocations.
    pub(in crate::codegen_ay::chc) fn push_state_var_pair_arc(
        &mut self,
        in_name: std::sync::Arc<str>,
        out_name: &str,
        sort: Sort,
    ) {
        self.state_var_mgr.push_state_var_pair_arc(in_name, out_name, sort);
    }

    /// Map MIR local index to CHC state/output vector slot.
    /// Delegates to `StateVarManager::try_state_idx_for_local`.
    pub(in crate::codegen_ay::chc) fn try_state_idx_for_local(
        &self,
        local_idx: usize,
    ) -> Option<usize> {
        self.state_var_mgr.try_state_idx_for_local(local_idx)
    }

    /// Map a MIR local index to the CHC state/output vector slot.
    ///
    /// Fails closed when the local is missing from `local_to_state_idx` to
    /// prevent unsound aliasing (using MIR local index as vec index).
    #[allow(clippy::panic)] // Intentional fail-closed for soundness-critical call sites.
    pub(in crate::codegen_ay::chc) fn state_idx_for_local(&self, local_idx: usize) -> usize {
        if let Some(vec_idx) = self.state_var_mgr.try_state_idx_for_local(local_idx) {
            return vec_idx;
        }

        warn!(
            fn_name = %self.fn_name,
            local_idx,
            state_vars_len = self.state_var_mgr.state_vars.len(),
            output_state_vars_len = self.state_var_mgr.output_state_vars.len(),
            "CHC missing local_to_state_idx entry; refusing unsound local-index fallback"
        );
        panic!(
            "CHC missing local_to_state_idx entry for local {} in function {}",
            local_idx, self.fn_name
        );
    }

    /// Resolve a call destination's MIR local to its output state variable.
    ///
    /// Returns `(state_vec_index, dest_var)` where `dest_var` is an `Expr::var`
    /// for the output slot, or `None` if the destination has no output state variable.
    pub(in crate::codegen_ay::chc) fn resolve_destination(
        &self,
        dest_local: usize,
    ) -> Option<(usize, Expr)> {
        let dest_vec_idx = self.try_state_idx_for_local(dest_local)?;
        self.state_var_mgr
            .output_state_vars
            .get(dest_vec_idx)
            .map(|(out_name, out_sort)| (dest_vec_idx, Expr::var(&**out_name, out_sort.clone())))
    }

    /// Mark a collection length variable as modified and record its state-var index.
    /// Part of #2552/#2557: centralized output-args propagation for len vars.
    pub(in crate::codegen_ay::chc) fn mark_collection_len_modified(&mut self, len_var_name: &str) {
        self.collections.len_state.mark_len_modified(len_var_name);
        if let Some(idx) = self.state_var_index_by_name(len_var_name) {
            self.mark_state_var_modified(idx);
        }
    }

    /// Mark a collection capacity variable as modified and record its state-var index.
    /// Part of #2877: centralized output-args propagation for cap vars.
    pub(in crate::codegen_ay::chc) fn mark_collection_cap_modified(&mut self, cap_var_name: &str) {
        self.collections.len_state.mark_cap_modified(cap_var_name);
        if let Some(idx) = self.state_var_index_by_name(cap_var_name) {
            self.mark_state_var_modified(idx);
        }
    }

    /// Mark a collection presence-array variable as modified and record its state-var index.
    /// Part of #3057: centralized output-args propagation for present vars.
    pub(in crate::codegen_ay::chc) fn mark_collection_present_modified(
        &mut self,
        present_var_name: &str,
    ) {
        self.collections.len_state.mark_present_modified(present_var_name);
        if let Some(idx) = self.state_var_index_by_name(present_var_name) {
            self.mark_state_var_modified(idx);
        }
    }

    /// Mark heap metadata arrays as modified and record their state-var indices.
    /// Part of #2552: keep obj_valid/obj_size propagation index-based.
    /// Part of #3436: also tracks per-block metadata access for liveness pruning.
    pub(in crate::codegen_ay::chc) fn mark_heap_metadata_modified(&mut self) {
        self.heap_state.mark_metadata_arrays_modified();
        self.heap_state.mark_metadata_accessed(self.current_encode_bb);
        for name in ["obj_valid", "obj_size"] {
            if let Some(idx) = self.state_var_index_by_name(name) {
                self.mark_state_var_modified(idx);
            }
        }
    }

    /// Record that the current block reads heap metadata (obj_valid/obj_size)
    /// without necessarily modifying them. Called for safety checks (SELECT on
    /// obj_valid) and bounds checks (SELECT on obj_size).
    /// Part of #3436: per-block metadata liveness tracking.
    pub(in crate::codegen_ay::chc) fn mark_heap_metadata_read(&mut self) {
        self.heap_state.mark_metadata_accessed(self.current_encode_bb);
    }

    /// Mark a type-indexed heap array as modified and record its state-var index.
    /// Part of #2552: centralized propagation for `_fn_mem_{type_key}` arrays.
    pub(in crate::codegen_ay::chc) fn mark_type_array_modified(&mut self, type_key: &str) {
        self.heap_state.mark_array_modified(type_key);
        if let Some((arr_name, _)) = self.heap_state.type_arrays.get(type_key)
            && let Some(idx) = self.state_var_index_by_name(arr_name)
        {
            self.mark_state_var_modified(idx);
        }
    }

    /// Returns sorted unique CFG successors for a terminator.
    pub(in crate::codegen_ay::chc) fn block_successors(kind: &TerminatorKind) -> Vec<usize> {
        let mut succs = match kind {
            TerminatorKind::Goto { target } => vec![*target],
            TerminatorKind::SwitchInt { targets, .. } => {
                let mut succs: Vec<usize> =
                    targets.branches().map(|(_case_val, target)| target).collect();
                succs.push(targets.otherwise());
                succs
            }
            TerminatorKind::Drop { target, unwind, .. } => {
                let mut succs = vec![*target];
                if let UnwindAction::Cleanup(cleanup_bb) = unwind {
                    succs.push(*cleanup_bb);
                }
                succs
            }
            TerminatorKind::Call { target, unwind, .. } => {
                let mut succs: Vec<usize> = target.iter().copied().collect();
                if let UnwindAction::Cleanup(cleanup_bb) = unwind {
                    succs.push(*cleanup_bb);
                }
                succs
            }
            TerminatorKind::Assert { target, unwind, .. } => {
                let mut succs = vec![*target];
                if let UnwindAction::Cleanup(cleanup_bb) = unwind {
                    succs.push(*cleanup_bb);
                }
                succs
            }
            TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::Resume
            | TerminatorKind::Abort => Vec::new(),
            TerminatorKind::InlineAsm { destination, .. } => destination.iter().copied().collect(),
        };
        succs.sort_unstable();
        succs.dedup();
        succs
    }

    /// If `expr` is a bitvec that should be a Datatype for `ty`, unflatten it
    /// and declare the Datatype sort. Returns the (possibly unflattened) expression.
    ///
    /// This pattern occurs after every array `select` where the element type
    /// may have been flattened to bitvec during array construction.
    /// Part of #3296: Extracted from 6 inline copies across deref/store paths.
    pub(in crate::codegen_ay::chc) fn try_unflatten_bv_to_datatype(
        &mut self,
        expr: Expr,
        ty: rustc_public::ty::Ty,
    ) -> Expr {
        if !expr.sort().is_bitvec() {
            return expr;
        }
        let Some(dt_sort) = Self::translate_ty(ty) else { return expr };
        if !dt_sort.is_datatype() {
            return expr;
        }
        match crate::codegen_ay::types::unflatten_bitvec_to_datatype(&expr, &dt_sort) {
            Some(unflat) => {
                self.declare_datatype_sort_if_needed(&dt_sort);
                unflat
            }
            None => expr,
        }
    }

    // Dead local analysis (apply_dead_local_transfer, compute_dead_locals_at_block_entry)
    // extracted to codegen_ctx_dead_locals.rs per #2246.

    // translate() moved to mod.rs to access sibling trait methods (Part of #2595).
}

#[cfg(test)]
mod tests;
