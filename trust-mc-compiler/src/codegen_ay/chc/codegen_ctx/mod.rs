// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// CHC codegen context — core ChcCtx definitions and entry points.
// Split from mod.rs per #1353; further split per #1508 for reviewability.
// Converted from include!() to proper module per #2595.
// Decomposed into globals/types/mod per #2408.

mod body_resolve;
mod fresh_vars;
pub(in crate::codegen_ay::chc) use fresh_vars::{
    Booked, ExactVar, Havoc, SoundHavocReason, sound_havoc,
};
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
    push_pending_datatype_sort, record_aggregate_encoding_gap_for_fn,
    record_aggregate_gap_reason_for_fn, record_assert_untranslatable_for_fn,
    record_drop_fallback_reason_for_fn, record_fp_bitvector_encoding_for_fn,
    record_kani_mem_overapprox_for_fn, record_offset_provenance_unresolved_for_fn,
    record_ptr_metadata_unconstrained_for_fn, record_signedness_fallback_for_fn,
    record_sound_havoc_drop_for_fn, record_static_init_incomplete_for_fn,
    record_store_dropped_for_fn, record_stub_approximation_for_fn, record_translation_drop_for_fn,
    record_translation_drop_site_reason_for_fn, record_type_sort_fallback,
    record_type_sort_fallback_for_fn, record_unhandled_call_for_fn, set_chc_fallback_count_for_fn,
};
// Re-export test-only globals: chc-only at chc scope, cross-module at codegen_ay scope
#[cfg(test)]
pub(in crate::codegen_ay::chc) use globals::get_chc_fallback_counts;
pub(in crate::codegen_ay) use globals::record_bmc_offset_provenance_unresolved_for_fn;
pub(in crate::codegen_ay) use globals::record_bmc_sound_havoc_for_fn;
#[cfg(test)]
pub(in crate::codegen_ay) use globals::{
    clear_chc_fallback_counts, get_chc_unhandled_call_count, set_chc_fallback_count_for_test,
    set_chc_unhandled_call_count_for_test, set_type_sort_fallback_count_for_test,
};
pub(in crate::codegen_ay) use globals::{
    get_aggregate_encoding_gap_count, get_fp_bitvector_encoding_count,
    get_inferable_predicate_count, get_ptr_metadata_unconstrained_count,
    get_rounding_assertion_bypass_count, get_static_init_incomplete_count,
    get_stub_approximation_count, take_assert_untranslatable_by_fn,
    take_chc_diverging_call_drop_count, take_chc_fallback_counts,
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
        // heap/stack_address.rs: a relational comparison of two raw pointers
        // that may be in different allocations, where one allocation has no
        // tracked base address, compares two FRESH declare-vars. A declare-var
        // is universally quantified over its rule, so every order (and
        // equality) of the two addresses is admitted: a superset of the real
        // outcomes, monotone, never a false proof. Tagging a dependent
        // counterexample OverApproximation is right: the fresh pair does not
        // keep two comparisons of the same pointers consistent.
        | "cross_alloc_ptr_order_untracked"
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
        // constraints are the sidecar pins dst_len := src_len and
        // dst_cap := src_len (exact real clone semantics, shared with the
        // fully-modeled paths); no stale-input
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
        // Untyped-view net 2 (stmt/codegen_stmt_store/untyped_view_scan.rs):
        // a raw read of a static's memory under a view the entry rule never
        // seeds and the static store lanes never write (`*(addr_of!(G) as
        // *const u8).add(2)` for `G: [u16; 2]`). The encoding is unchanged:
        // the read selects a typed-memory cell no rule constrains, a
        // universally quantified value of which the real byte is one
        // interpretation, so no proof over it is a false proof. What the free
        // value never is, is evidence: the reason is recorded unaccounted, so
        // a counterexample in the harness is not certified Genuine.
        | "static_memory_read_unseeded_view"
        | "array_byte_view_unmodeled"
        // A bounds check against a `Vec::with_capacity` buffer's recorded size
        // when the `Vec` may grow past it (call/codegen_call_vec_ops/
        // constructors.rs `taint_vec_capacity_size`): the size is `ite(t, 0,
        // bytes)` for a fresh `t` recorded as the freed variable. `t` may be
        // false, so the recorded bound still binds every proof exactly as
        // before, and a violation of it stays reachable; a counterexample that
        // rests on it reads `t` and is not certified (a grown `Vec`'s buffer is
        // larger than the record).
        | "vec_capacity_size_uncertified"
        // The memory image of a niche-encoded flattened enum's tag
        // (call/codegen_call_result_mem.rs `flattened_enum_tag_image`): where
        // the untagged variant is active, the tag bytes are its payload's, and
        // a payload with no byte image leaves them a fresh value, universally
        // quantified, of which the real bytes are one interpretation. A proof
        // over it is a proof; it is recorded with the fresh value's identity,
        // so a counterexample that reads those bytes is not certified Genuine.
        | "enum_tag_image_payload_unknown"
        // The heap view ledger (heap/heap_view_ledger.rs): a read of a heap
        // object under a type key no store of those bytes wrote (`*(p as
        // *const u32)` over a `Box<[u16; 2]>` the program only ever wrote as
        // `u16`). The read selects a typed-memory cell no rule constrains, of
        // which the real bytes are one interpretation, so a proof over it is a
        // proof. It is recorded with the arrays it selected from as the freed
        // identities, so no counterexample that reads them is certified
        // Genuine on its strength (review of fix/chc-lost-writes, lostwrite
        // round 1, finding 3), while one that rests on another check of the
        // same access (its bounds, its initialization) still is (lostwrite
        // track round 1, finding 4: recorded unaccounted, it cost
        // `uninit/vec-read-uninit` its certificate). A read where some store
        // of the bytes wrote its key and another did not may be STALE, not
        // free, and fails closed (`heap_view_read_stale`).
        | "heap_view_read_unwritten"
        // Integer-to-pointer invalidation (expr/codegen_expr_heap.rs
        // `invalidate_int_to_ptr_object`): the lane invalidates `obj_valid` of
        // the object its result names, since the model keeps no set of exposed
        // allocations. That only ADDS violations (every later access of the
        // object fails memory safety), so a proof under it is a proof. What a
        // failure resting on it is not, is evidence when the object was live
        // (Kani keeps the pointer's bits and proves the round trip): the reason
        // is recorded unaccounted, so no counterexample in the harness is
        // certified Genuine (review of fix/chc-lost-writes round 3, finding 1;
        // the BMC lane's `pointer_with_exposed_provenance`).
        | "int_to_ptr_obj_invalidated"
        // Cell store register havoc (call/codegen_call_cell_register.rs,
        // R5): a `Cell` store the lane models exactly (the value lands at the
        // referent's own memory-mirror address) whose register mirror cannot
        // be rebound exactly (an array element, an enum payload, an unmapped
        // offset, a choice between known locals). The register of EVERY local
        // the address can name is left unbound in the rule head -- a fresh,
        // universally quantified value of which the stored value is one
        // interpretation -- and the block's earlier bindings of those slots
        // are rewritten onto the pre-call value first, so nothing pins the
        // havoced slot. Monotone: a proof over it is a proof. The havoced
        // slots are recorded as freed variables, so a counterexample that
        // reads one stays OverApproximation and one independent of them can
        // be certified. RefCell stores (whose lane is not exact) and stores
        // with an unidentified referent record their own fail-closed reasons.
        | "cell_store_register_havoc"
        // Design 3 fn-pointer dispatch (call/fn_ptr_targets.rs
        // `fn_ptr_obligation_default`): the "invalid function pointer"
        // obligation of a set the harness universe completed becomes
        // `ptr ∈ ids ∨ t` for a FRESH boolean `t` recorded as this event's
        // freed variable. `t` occurs in that error rule alone and can always
        // be false, so the error is reachable exactly when `ptr ∉ ids` is: no
        // behaviour is added or removed and no proof changes. What it buys is
        // that the violated obligation reads a freed variable, so
        // `recertify_overapprox_ctrex` never certifies it Genuine (the pointer
        // came from memory, where a type-punned read is unconstrained), while
        // a violation of any other check stays certifiable.
        | "fn_ptr_obligation_value_uncertified"
        // P4-4 audit (emit_math_axiom_goto_extra): PURE math intrinsic
        // (sin/cos/sqrt/exp/powf even-power) — the destination is the call's
        // only effect; it reaches the head as fresh havoc constrained only by
        // proof-STRENGTHENING range axioms that every concrete execution
        // satisfies (module math_range_axioms, NaN/finite-guarded). No memory
        // side effect exists to be identity-retained, so the fallback is a
        // strict over-approximation. ∀-sound. Duals: dual_p4_float_nan.rs
        // (sine value not pinned; powf lower bound refutable) stay FAILED.
        //
        // #4270 / TL18 UPDATE: the destination is now bound to an application
        // of a first-class uninterpreted `declare-fun` symbol
        // (call_uf_table.rs) instead of a bare fresh variable. This does NOT
        // weaken the audit. No axiom about that symbol is emitted anywhere in
        // the problem, so its interpretation ranges over every function of the
        // declared signature — for FIXED arguments the application still ranges
        // over every value of the sort, the destination remains universally
        // quantified, and no behaviour is removed. What the application adds is
        // CONGRUENCE: two sites with the same intrinsic and the same argument
        // value now get the same result, which is what the real function does
        // (`sin(x) == sin(x)` was previously unprovable because the two sites
        // drew independent havocs). Arguments that differ stay independent —
        // `sin(x) == sin(y)` is still refutable. (Before ay 0.23.0 the same
        // congruence was emulated by a frozen `call_uf_tbl` Array column
        // threaded through every relation; the audit above held for the same
        // reason, and the column is gone.)
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
        // Parity-1 second review (float_binop_table.rs `float_binop_chc_term`): a
        // symbolic float Add/Sub/Mul/Div/Rem is a select from a table no rule
        // constrains — a universally quantified value of which the IEEE 754
        // result is one interpretation, so no proof over it is a false proof
        // (the module's original soundness argument, unchanged). What the
        // table never was is EVIDENCE: the solver may pick `tbl[Add, -0, +0]`
        // = -0 where every FPU gives +0, and before this record that pick was
        // certified `[AY:CTREX_CAT:Genuine]` (`(m + 0.0).is_sign_positive()`
        // with `m` either zero, both routes). SoundHavoc is exactly the lane
        // for it: excluded from the proof qualifier, demotes a dependent
        // counterexample to OverApproximation. Recorded once per symbolic
        // select, including the refined ones — a refinement decides its
        // guarded cases and leaves the rest free, and the classifier cannot
        // tell from the count which case a counterexample took.
        | "float_binop_table_overapprox"
        // Kani "not currently supported" check (codegen_call_fallback_emit.rs
        // `emit_kani_unsupported_check`): the call site emits a path-gated
        // `error_p{N}` carrying Kani's own message and NO successor edge —
        // Kani's `assert(false); assume(false)`. It removes no behaviour a proof
        // could rest on: the only executions left without a successor are the
        // ones that reach that error head, so a PROOF requires the call to be
        // unreachable, and then its successor is unreachable too. Recorded
        // UNIDENTIFIED on purpose: an unaccounted reason keeps the
        // approximation-identity evidence incomplete, so
        // `recertify_overapprox_ctrex` can never certify the unsupported check
        // as a Genuine bug — the CHC twin of the BMC lane's
        // `unsupported_foreign_function` taint (dual_77_dependent.rs).
        | "kani_unsupported_construct_check"
        // `kani::float::float_to_int_in_range` whose operand did not translate
        // to a float bitvector (codegen_call_kani.rs): the destination is left
        // out of the rule's constraints and reaches the head as a fresh `__out`
        // havoc, so every rule holds for BOTH boolean answers -- monotone, a
        // proof over it is a proof of the real program. A counterexample may
        // read the wrong answer, which is exactly what this lane tags
        // (OverApproximation) instead of certifying it Genuine.
        | "float_to_int_in_range_nondet"
        // A promoted constant reference whose target object is registered (its
        // address resolves, `pointer_scalar_expr`) but whose contents did not
        // decode (`collect.rs` `try_collect_single_const_ref`): the object's
        // memory cells and `obj_size` are free. Free cells admit every value
        // the real constant has, so a proof over them is a proof; a
        // counterexample may rest on a value or size the constant never has
        // (T1 review, 2026-09-24: a free `obj_size` certified Genuine), so it
        // is recorded UNIDENTIFIED and never certified.
        | "const_ref_contents_unmodeled"
        // D2 (`decl::global_objects`): a FIXED object a constant pointer
        // reaches that is too large to seed cell by cell, or whose read at a
        // type was noted only after the entry rule was emitted (an inlined
        // callee's constant). Its cells are free: free cells admit every value
        // the constant really has, so a proof over them is a proof; a
        // counterexample may rest on a value the object never holds, so it is
        // recorded and never certified — the same audit as
        // `const_ref_contents_unmodeled`, one object wide instead of one window.
        | "const_object_unseeded"
        // D7(b) (`decl::static_path`): a store whose address const-folds into
        // a static the harness keeps a state variable for, but whose bytes no
        // static place path names. The static's state variable is left
        // unbound in the rule head — a fresh, universally quantified value of
        // which the stored one is an instance — and the block's earlier binding
        // of it is dropped first, so nothing pins the havoced slot. Monotone: a
        // proof over it is a proof; a counterexample that reads it is tagged,
        // never certified.
        | "static_store_unrouted"
        // FC-06 frame check on a `&mut T` (or interior-mutable `&T`) argument of a
        // call that MAY write it (modifies_frame.rs::modifies_frame_call_check):
        // an error rule whose violation over-approximates the call's writes. It
        // adds error paths only, and a write the call makes through that
        // reference stays inside the checked `size_of::<T>()` bytes, so a proof
        // over it is a proof; a counterexample is tagged, never certified.
        | "modifies_frame_call_arg_overapprox"
        // Option payload coercion (`coerce_option_payload_expr`,
        // codegen_stmt_aggregate_adt_option.rs): a payload whose sort cannot be
        // coerced to the Option datatype's payload sort becomes a fresh
        // declare-var of that sort, which nothing constrains. It admits the real
        // payload, so a proof over it is a proof; a counterexample that reads it
        // is demoted. The site used to record only `aggregate_encoding_gap`,
        // which no verdict reads. RECEIPT: kani/ThreadLocalRef/main.rs
        // `test_bool` (`thread_local! { static COND: bool = true }`, Kani
        // SUCCESSFUL): the `Option<&bool>` behind `LocalKey::with` arrives as a
        // pointer where the datatype holds a Bool, and "assertion failed: b" was
        // certified Genuine once 7427e34c5 removed an unrelated translation drop
        // from the same harness.
        | "adt_option_payload_sort_mismatch"
        // translate.rs `account_unbound_heap_metadata_outputs`: a transition rule
        // whose head carries an `obj_valid` / `obj_size` output that nothing in
        // its body mentions. The lane is universally quantified there -- a
        // superset of the one real value, monotone, so a proof over it is a
        // proof. A counterexample may rest on a validity or size no allocation
        // has, so it is tagged and never certified (the site that left the
        // lane unbound recorded nothing; see `box_then_null_deref` in
        // tools/soundness-duals/heap_metadata_lane_dual.rs).
        | "heap_metadata_output_unbound"
        // heap/stack_address.rs `far_step_unknown`: a wrapping pointer step
        // from a FAR pointer whose full offset is unknown
        // (`step_wrapping_address_from`) keeps the pointer's object and its
        // exact low 48 offset bits, and takes "far again or back in range" from
        // a fresh 1-bit declare-var. The real outcome is one of its two values,
        // so every behavior of the real step is admitted: monotone, a proof over
        // it is a proof. The var is the freed identity, so only a
        // counterexample that reads it is left uncertified.
        | "wrapping_step_far_unknown"
        // heap/stack_address.rs `apply_far_observation_cuts`: a fail-closed far
        // pointer observation splits each rule of its block into the rule cut to
        // the paths where no observation is fail-closed and a copy whose extra
        // guard (the observation's condition AND a fresh 1-bit declare-var equal
        // to 1) reaches a dedicated error property. The copy only ADDS error
        // edges and the cut removes exactly the paths the copy reports, so no
        // behavior escapes both: a proof needs the copy unreachable, i.e. no far
        // pointer observed. The declare-var is the freed identity, so the copy's
        // property is never certified while every other property reads nothing
        // of it.
        | "far_pointer_observation"
        // The `Iterator::sum` stub (codegen_call_iterator_adapter/reduce.rs
        // `reduce_havoc`, AY alignment review round 2): the value of a sum the
        // stub cannot compute -- a float sum (the lane has no FP theory), a
        // `Sum` impl it does not know, elements past the replay bound or a
        // sequence the replay cannot address -- is a FRESH, universally
        // quantified declare-var of the destination sort, of which the real
        // value is one interpretation: a proof over it is a proof. It is
        // recorded IDENTIFIED, so a counterexample that reads it is demoted and
        // one independent of it can be certified. RECEIPT (all Kani
        // SUCCESSFUL): `[1u32; 12].iter().sum() == 12`, a symbolic-length
        // `a[..n]` sum, and `[1.5f32, 2.25].iter().sum() == 3.75` were
        // counterexamples certified Genuine while the havoc was booked only on
        // `aggregate_encoding_gap`. (`fold` / `try_fold` values use
        // `fresh_adapter_symbol`'s `iter_adapter_symbol_overapprox`.)
        | "iter_sum_value_overapprox"
        // The same stub's conservative overflow rule: `unchecked ∧ t` for a
        // FRESH boolean `t` that occurs in that error rule alone and can always
        // be true, so the rule is reachable exactly when an element the replay
        // did not check is added. It only ADDS error paths (fail-closed for a
        // proof); `t` makes the violated check read a freed variable, so a
        // counterexample through it is never certified Genuine -- the same
        // device as `fn_ptr_obligation_value_uncertified`.
        | "iter_sum_overflow_unchecked"
        // The same device for a `Sum` impl the stub does not model
        // (`SumSummand::Unknown`: a core impl the classification does not
        // know, since a user impl, `Duration` and `Option<T>` take the ordinary
        // call path; never std's `Saturating`, which cannot panic and is
        // replayed exactly, AY alignment round 8, review round 4): an error rule whose violation is
        // a FRESH boolean `t` alone, so the rule is reachable whenever the call
        // is. It stands for every panic of the unencoded body, adds error paths
        // only, and a counterexample through it reads `t`, so it is never
        // certified.
        | "iter_sum_impl_unmodeled"
        // The same device for the closures a call runs and its stub does not
        // encode (AY alignment round 8, review round 5, finding 1;
        // `iter_closure_obligation`): a `Filter`'s predicate or a `Map`'s
        // function under a `next()`, `sum`, `fold` or `collect` stub. Only a
        // closure the obligation-free walk cannot certify gets the rule, whose
        // violation is the fresh boolean alone. (A `fold`'s own closure states
        // its checks per replayed step, and an uncertified reach check where a
        // step is not replayed: reduce.rs `unreplayed_step_check`.)
        | "iter_adapter_closure_unmodeled"
        // The same device for Kani's "NaN on addition" inside a float sum under
        // `--nan-check` (the lane has no FP theory to compute the partial sums
        // the check reads): `has_remaining ∧ t`.
        | "iter_sum_nan_unchecked"
        // Rule E (design trust-mc-reds-final §4.4;
        // stmt/codegen_stmt_aggregate_discr.rs `translate_discriminant`): the
        // discriminant of an enum read through a `Deref` whose referent did not
        // translate is a fresh `declare-var` constrained to the disjunction of
        // `discriminant_for_variant(v)` over EVERY variant (sign-extended to
        // the pointer width, the encoder's value convention;
        // `enum_discriminant_value_set`). A valid enum's discriminant is one of
        // those values, so the symbol ranges over a superset of the real one:
        // monotone, a proof over it is a proof. Two reads of the same place get
        // independent symbols, which only adds behaviours. The symbol's name is
        // recorded as the approximation's identity, so a counterexample that
        // reads it is OverApproximation unless recertified. The same fallback
        // reached on a place with NO `Deref` (where the place itself should
        // have translated) also books `discr_unresolved_direct_place`, which is
        // NOT listed here: fail-closed. Held by
        // chc/tests/test_rule_e_discriminant.rs.
        | "discr_unresolved_referent"
        // #4270 / TL18 audit (see call_uf_table.rs for the full written gate):
        // an ESTABLISHED-pure scalar callee summarised by a first-class
        // uninterpreted function. `established_pure_scalar_callee` reads the
        // callee's MIR body (not its signature shape) and admits it only when
        // the body has no Deref, no reference/raw-pointer constant, no
        // pointer-creating rvalue, no memory intrinsic, no panicking terminator
        // (no `Assert`, so an overflow check is never swallowed) and no nested
        // call outside the same gate or the total/pure bit intrinsics. Such a
        // callee's ONLY observable effect is its return value, which reaches
        // the head as an application of a `declare-fun` symbol that carries no
        // axiom anywhere in the problem -- the real function is one
        // interpretation of it, so the term is universally quantified exactly
        // like a fresh havoc, only congruent. AY's congruence closure is a
        // theory fact about the symbol, NOT a purity proof: the right to model
        // the callee as a function of its arguments comes from the gate and
        // from nowhere else. No memory side effect exists to be
        // identity-retained. ∀-sound; a callee that can panic, read a static or
        // take a pointer FAILS the gate and keeps the fail-closed
        // `call_dispatch_fallback_prebuilt` havoc.
        //
        // Uncertified reach checks of the inline walker
        // (call/codegen_call_virtual_inline/uncertified_check.rs): an
        // obligation the walk reaches but cannot state is recorded as the
        // side-channel check `t`, a FRESH boolean read by that error rule
        // alone and recorded as this event's freed variable. The walker adds
        // its path condition as for any check, and `t` can be false, so the
        // error is reachable exactly when the obligation's site is: a proof
        // requires the site unreachable, and then the obligation it stands
        // for is unreachable too. Nothing is havocked and no behaviour is
        // removed, so a proof over it is a proof. What the record buys is that
        // the violated check reads a freed variable, so it is never certified
        // Genuine (the program does not fail there; the walker could not say
        // whether it does). Measured on the duals and the 737 parity units in
        // docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed".
        | "walker_untranslatable_assert_uncertified"
        // The same record for a diverging call the walker does not model
        // (a user `-> !` function): the check `t` above, and the path's
        // result value, a fresh declare-var on a continuation the program
        // never takes (the call does not return), so every value is
        // admitted and a counterexample reading it is never certified.
        | "walker_diverging_call_uncertified"
        // The same record for a SwitchInt arm the walker could not finish
        // whose abandoned region can carry an obligation (switchint.rs
        // `switchint_branch_fallback`): `t` under the arm's path condition
        // and guard, so the error is reachable exactly when the arm is, and
        // every obligation the region holds lies on paths through the arm.
        | "walker_bailed_arm_obligation_uncertified"
        // The same record for an iterator reduction step the statement path
        // does not replay (`codegen_call_iterator_adapter/reduce.rs`: a
        // `fold` / `sum` step past the replay bound, a `fold` closure the
        // walker could not walk, a `try_fold` closure never walked): `t`
        // under the condition that such a step runs, so the error is
        // reachable exactly when an unchecked step's obligation can be.
        | "iter_reduce_step_uncertified"
        // Kani's unwinding assertion on an iterator reduction's std loop
        // under a declared unwind bound, where the model cannot state it
        // exactly (`reduce.rs`, `push_reduce_unwinding_check`): `t` under
        // the condition that the loop can run past the bound.
        | "iter_reduce_unwind_uncertified"
        // A modelled call whose callee may loop, under a declared unwind
        // bound (`codegen_call.rs`, `model_call_unwinding_check`): the reach
        // check `t` wherever the call is reached, standing for Kani's
        // unwinding assertion on the loop the model does not replay.
        | "model_call_loop_unwind_uncertified"
        // `Vec::extend` from a source whose length the model cannot resolve
        // (`codegen_call_vec_ops_len.rs`, `vec_op_extend_from_slice`): the new
        // length is a fresh value no smaller than the old, freed by this
        // record.
        | "vec_extend_source_len_unresolved"
        // `Vec::extend` from a range whose count is symbolic or past the
        // unroll bound (`codegen_call_vec_ops_extend_range.rs`,
        // `range_extended_data`): the Vec's `data` is a fresh array, freed by
        // this record. Its `len` and `cap` fields are written exactly.
        | "vec_extend_range_elements_unmodelled"
        // The same for `Vec::extend_from_slice` / `extend` from a slice whose
        // length is known and whose values are not (`codegen_call_vec_ops_len.rs`).
        | "vec_extend_slice_elements_unmodelled"
        // A Vec's grown capacity where the model does not know `RawVec`'s
        // growth: the element's size, which fixes the minimum non-zero
        // capacity, is unknown, or the call grows in steps the model does
        // not replay (`splice`) (`codegen_call_vec_ops/shared.rs`,
        // `vec_reserved_cap`, `vec_fresh_grown_cap`): a fresh value of at
        // least the required capacity, freed by this record.
        | "vec_grown_capacity_unmodelled"
        // A collected Vec's capacity where the collect may reuse the source
        // Vec's buffer (a chain over `vec::IntoIter`,
        // `codegen_call_iterator_adapter/collect.rs`, `collected_vec_cap`): a
        // fresh value of at least the length, freed by this record.
        | "vec_collected_capacity_unmodelled"
        // The Vec `split_off` returns (`codegen_call_vec_ops_mutate.rs`,
        // `vec_op_split_off`): its `data` is a fresh array, freed by this
        // record; its length, capacity and the split Vec's length are written
        // exactly.
        | "vec_split_off_elements_unmodelled"
        // A closure `retain`, `dedup_by(_key)` or `sort_by(_key)` runs on the
        // elements, which the Vec models never walk, where it can carry an
        // obligation (`codegen_call_vec.rs`): `t` wherever the call is reached.
        | "vec_closure_step_uncertified"
        // An iterator adapter's fresh value (`fresh_adapter_symbol`,
        // codegen_call_iterator_adapter/helpers.rs): a `fold` / `sum` result,
        // a `next` payload, a filter's keep bit, where the model has no exact
        // term. A fresh `declare-var`, universally quantified over its rule,
        // so it admits the real value and a proof over it is a proof. It used
        // to record only `aggregate_encoding_gap`, which no verdict reads, so a
        // counterexample built on it was certified Genuine: `[1, 2, 3,
        // 4].iter().filter(|x| **x > 100).fold(0u8, wrapping_add) == 0` and
        // `[Wrapping(200u8), ..].iter().fold(Wrapping(0), |a, b| a + b)`, both
        // proved by Kani (walker fail-closed review 6 round 3). Recorded with
        // the symbol as the freed variable: a counterexample that reads it is
        // OverApproximation, one independent of it can still be certified.
        | "iter_adapter_symbol_overapprox"
        // The char `kani_str_chars_nth` returns where the string's bytes may
        // hold a multi-byte char (codegen_call_string_nth.rs,
        // `try_build_str_nth_result_expr`): a fresh `declare-var` of the
        // `Option<char>` sort, which admits the real decoding, recorded with
        // itself as the freed variable.
        | "str_chars_nth_multibyte_overapprox"
        //
        // call/codegen_call_vec_ops_views.rs `vec_op_as_ptr`: a `Vec`'s buffer
        // pointer the encoder cannot resolve (a `Vec` in a struct field it
        // cannot select, an untracked receiver) is a FRESH pointer value: every
        // address is admitted, so a read through it is a superset of the real
        // reads and a proof stands, while a counterexample that rests on it is
        // not certified. It used to be left free with no reason recorded, so a
        // read through `s.v.as_mut_ptr()` certified a false counterexample
        // (third review of round 10 of fix/chc-false-certificates,
        // `r3_dead5.rs` `n02_safe_struct_vec_moved_out_copy_src`).
        | "vec_as_ptr_unresolved"
        //
        // Rule E (fresh_vars.rs, design trust-mc-reds-final §4.4, decision
        // REDS-REST): the reasons a `Havoc::mint` site books. Each one stands
        // for a VALUE the encoding does not compute, replaced by a fresh
        // `declare-var` of the slot's sort. A declare-var is universally
        // quantified over its rule, so the rule holds for every value the real
        // one could be: monotone, it adds behaviours and removes none, and a
        // proof over it is a proof. No check, write or deallocation rides on
        // the value: a site that drops one of those books a lost obligation
        // (Rule D) or a fail-closed reason instead, and a site whose fresh value
        // is pinned, semantically nondeterministic or unobserved is an
        // `ExactVar` and books nothing. What the havoc is not, is evidence: the
        // value is booked with its identity, so a counterexample that reads it
        // is OverApproximation unless `recertify_overapprox_ctrex` certifies
        // it. The classes are in docs/DECISION_QUEUE.md (REDS-REST); a
        // reason's sites share its argument:
        // - untracked_collection_state: a collection stub's length, data,
        //   keys, iterator state or predicate result (Vec::from_iter's length,
        //   retain's length within [0, old len], a HashMap iterator's keys,
        //   `str::starts_with` with no content model);
        // - untracked_pointer_value: an address the model does not pin (a Vec
        //   buffer's base, `Vec::new`'s dangling pointer, a drop's `self`, an
        //   allocator `Ok` payload, an `Option<&mut T>` reference);
        // - untracked_vtable_metadata: size, align, type id or vtable id for a
        //   vtable id no registered type has, or a dyn drop's vtable;
        // - untracked_coroutine_state: a coroutine resume's state, payload,
        //   fields or discriminant the walk does not compute;
        // - untracked_sort_mismatch_value: a value whose sort disagrees with
        //   its slot's (a store, an aggregate field, an array element, a
        //   SwitchInt arm's value), replaced by a value of the slot's sort;
        // - untracked_discriminant: a discriminant ranging over the variants'
        //   discriminant VALUES or a superset (an allocation Result's, a
        //   coroutine's within 256, an enum whose sort is not a datatype);
        // - untracked_call_result: an intrinsic's or library call's result the
        //   model does not compute (memset/write_bytes fills, catch_unwind's
        //   outcome and payload, a non-ASCII `next_code_point`, a formatting
        //   call, `unwrap_unchecked`'s None payload, a datatype field of an
        //   ite branch that is not its constructor term);
        // - untracked_constant_bytes: a constant's bytes or length the encoding
        //   does not read out (a long `&str`'s contents, unreadable fat-pointer
        //   metadata);
        // - untracked_walker_value: a value the inline walker hands back
        //   without computing it (a pointee written through memory only, a
        //   drop placeholder);
        // - untracked_bignum_value: a BigInt/BigRational value the LIA model
        //   does not compute;
        // - memory_cell_unwritten_under_key (Rule C's backstop,
        //   heap/memory_cell_backstop.rs): a constant-address read of a cell
        //   under a type key that no store, and no entry initialization, wrote
        //   at that address, while another key was written there. The typed
        //   array's initial state is unconstrained (the entry rule constrains
        //   only static and promoted-constant cells, which count as writes), so
        //   the read ranges over every value, the real one included.
        // Held by `test_rule_e_constructors::every_sound_havoc_reason_is_audited`.
        | "untracked_collection_state"
        | "untracked_pointer_value"
        | "untracked_vtable_metadata"
        | "untracked_coroutine_state"
        | "untracked_sort_mismatch_value"
        | "untracked_discriminant"
        | "untracked_call_result"
        | "untracked_constant_bytes"
        | "untracked_walker_value"
        | "untracked_bignum_value"
        | "memory_cell_unwritten_under_key"
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

    /// Trust: whether this context has recorded the fail-close reason
    /// `rvalue_reborrow_unsupported` (see `chc::trust_reborrow`). A helper
    /// context whose reasons never reach a harness verdict reads it to decline.
    #[cfg(trust_toolchain)]
    pub(in crate::codegen_ay::chc) reborrow_unsupported_recorded: bool,

    /// The CHC verification condition being built.
    pub(in crate::codegen_ay::chc) vc: ChcVc,

    /// Freed-var identities of sound approximations recorded through `&self`
    /// (`record_sound_fallback_reason_identified_deferred`), moved into `vc`
    /// before finalization.
    pub(in crate::codegen_ay::chc) deferred_approximation_identities:
        std::cell::RefCell<Vec<String>>,

    /// Fail-closed far pointer observations of the block under construction
    /// (`heap/stack_address.rs`, `record_far_observation`), applied by
    /// `apply_far_observation_cuts` when its rules are emitted.
    pub(in crate::codegen_ay::chc) pending_far_observations:
        std::cell::RefCell<Vec<(ay_bindings::Expr, &'static str, bool)>>,

    /// Error relations of fail-closed far pointer observations, marked
    /// approximation-dependent after the dependence analysis
    /// (`mark_far_observation_properties_dependent`).
    pub(in crate::codegen_ay::chc) far_observation_relations: std::cell::RefCell<Vec<String>>,

    /// Whether the translation in progress is one of rustc's null or alignment
    /// check casts, which observe no far pointer (`is_rustc_check_cast_dest`).
    pub(in crate::codegen_ay::chc) far_observation_suppressed: std::cell::Cell<bool>,

    /// Destinations of rustc's check casts (`is_rustc_check_cast_dest`).
    pub(in crate::codegen_ay::chc) far_check_cast_dests: std::cell::OnceCell<HashSet<usize>>,

    /// Whether a block's (or fragment's) rule generation is collecting far
    /// pointer observations (`begin_far_observation_range`).
    pub(in crate::codegen_ay::chc) far_observation_range_active: std::cell::Cell<bool>,

    /// Whether this body may build a far pointer (`far_pointers_possible`).
    pub(in crate::codegen_ay::chc) far_pointers_possible_cache: std::cell::Cell<Option<bool>>,

    /// A far pointer appeared after an observation was translated without
    /// fail-closed conditions (`note_far_producer`); the harness fails closed.
    pub(in crate::codegen_ay::chc) far_prescan_missed: std::cell::Cell<bool>,

    /// An observation was translated while no far pointer was possible yet
    /// (`note_observation_without_far_pointers`).
    pub(in crate::codegen_ay::chc) far_observation_skipped: std::cell::Cell<bool>,

    /// This translation asked for a retry with far pointers possible from the
    /// start (`book_far_pointer_prescan`); its per-function diagnostics are
    /// not recorded, the retry's are.
    pub(in crate::codegen_ay::chc) far_retry_requested: bool,

    /// The full 64-bit offset of each far constant this body built, `None` when
    /// two far constants with one identity had different offsets.
    pub(in crate::codegen_ay::chc) far_literal_t64: std::cell::RefCell<HashMap<u64, Option<u64>>>,

    /// Pointer terms `int_to_ptr_value` built, whose observation is exact
    /// (`may_be_far_observed`).
    pub(in crate::codegen_ay::chc) far_from_integer: std::cell::RefCell<Vec<ay_bindings::Expr>>,

    /// `var_may_hold_far_pointer` answers, per state variable name.
    pub(in crate::codegen_ay::chc) far_var_cache: std::cell::RefCell<HashMap<String, bool>>,

    /// `pointer_local_may_be_far` answers, per local.
    pub(in crate::codegen_ay::chc) far_local_cache:
        std::cell::RefCell<HashMap<(usize, bool), bool>>,

    /// Locals whose address the body takes (`address_taken_locals`).
    pub(in crate::codegen_ay::chc) far_address_taken: std::cell::OnceCell<HashSet<usize>>,

    /// Single definitions a wrapping step's accumulated offset follows
    /// (`wrapping_step_defs`).
    pub(in crate::codegen_ay::chc) far_wrapping_defs: std::cell::OnceCell<
        HashMap<usize, crate::codegen_ay::chc::heap::stack_address::WrappingDef>,
    >,

    /// Layout facts a pointer-to-integer conversion of a possibly UNTRACKED
    /// object relies on (`heap/stack_address.rs`, `ptr_to_int_value`): no
    /// tracked stack object has a byte in that object's identity slot. Recorded
    /// through `&self`, taken into the rule under construction by
    /// [`ChcCtx::take_address_assumptions`].
    pub(in crate::codegen_ay::chc) pending_address_assumptions:
        std::cell::RefCell<Vec<ay_bindings::Expr>>,

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
    /// From `ChcConfig::straightline_discharge`.
    pub(in crate::codegen_ay::chc) straightline_discharge: bool,
    /// Record this translation's per-function diagnostic maps. False for a speculative
    /// re-translation whose VC may be discarded (frame narrowing): the maps ADD per
    /// call, so recording it too double-counts the function.
    pub(in crate::codegen_ay::chc) record_per_fn_diagnostics: bool,
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

    /// `-Z loop-contracts` is active (see `ChcConfig::loop_contracts`).
    pub(in crate::codegen_ay::chc) loop_contracts: bool,

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

    /// The model of the `Iterator::sum` call the iterator-adapter dispatch is
    /// about to encode (`reduce_loop_rule::iter_sum_model`), set by the
    /// dispatch from the call's operand and taken by the `IterSum` arm.
    pub(in crate::codegen_ay::chc) pending_iter_sum_model:
        Option<crate::codegen_ay::reduce_loop_rule::SumModel>,

    /// Set by a call dispatcher that replays the callee's body through the
    /// walker (fn-inline, closure, virtual, fn-pointer, `catch_unwind`), whose
    /// loop replay states Kani's unwinding assertions itself; cleared before
    /// each call terminator's dispatch (`codegen_call.rs`,
    /// `model_call_unwinding_check`).
    pub(in crate::codegen_ay::chc) call_replays_body: bool,

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

    /// Cumulative inline work over the whole harness, including failed
    /// speculative attempts and dyn-drop candidates. This is deliberately
    /// outside heap/ref-resolution snapshots: rollback cannot refund work.
    pub(in crate::codegen_ay::chc) inline_work_budget:
        crate::codegen_ay::chc::call::inline_work_budget::InlineWorkBudget,

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

    /// Phase 0 of the dyn-walker write/read design
    /// (`docs/chc-hole-fix-designs-2026-09-24.md` section 2): the heap write
    /// mark taken at the OUTERMOST active inline walk (or host front door that
    /// walks several bodies). `None` outside every walk. A read through a deref
    /// inside the walk after any write since this mark fails closed
    /// (`inline_walk_guard.rs`).
    pub(in crate::codegen_ay::chc) inline_walk_write_mark:
        Option<crate::codegen_ay::chc::heap_state::HeapWriteMark>,
    pub(in crate::codegen_ay::chc) native_drop_memory:
        Option<super::call::native_drop_memory::NativeDropMemory>,
    #[cfg(all(trust_toolchain, version("1.101")))]
    pub(in crate::codegen_ay::chc) native_init_stores:
        HashMap<usize, super::call::native_init_handoff::NativeInitStore>,
    /// Closed host custody facts, not proof that the payload is initialized.
    /// Capture at the real allocation before later free clears live aliases.
    #[cfg(all(trust_toolchain, version("1.101")))]
    pub(in crate::codegen_ay::chc) native_init_authorized_locals: HashSet<usize>,
    pub(in crate::codegen_ay::chc) inline_walk_param_native_drop_seeds:
        Option<Vec<(usize, super::call::native_drop_memory::NativeDropAddress)>>,
    /// One entry per active inline walk frame (innermost last): the
    /// reference-typed locals of that body whose term is, or may be, an
    /// ADDRESS rather than the referent value the walker's transparent
    /// `Deref` reads it as (`inline_walk_guard.rs`, F2). Monotone per frame.
    pub(in crate::codegen_ay::chc) inline_walk_frames:
        Vec<crate::codegen_ay::chc::call::inline_walk_guard::InlineWalkFrame>,
    /// Address-bound parameter locals the binder of the NEXT walk established
    /// (dyn door, nested walks, fn_inline unreported bindings). Taken by the
    /// walk entry.
    pub(in crate::codegen_ay::chc) inline_walk_param_address_seeds: Option<Vec<usize>>,
    /// Reference parameters whose binders explicitly resolved referent values.
    pub(in crate::codegen_ay::chc) inline_walk_param_referent_seeds: Option<Vec<usize>>,
    /// Typed host owners of reference parameters in the NEXT inline frame.
    pub(in crate::codegen_ay::chc) inline_walk_param_mut_owner_seeds:
        Option<Vec<(usize, super::call::inline_mut_ref_owner::InlineMutRefOwner)>>,
    /// RustCall tuple fields forwarded into the NEXT inline frame.
    pub(in crate::codegen_ay::chc) inline_walk_param_rustcall_mut_owner_seeds:
        Option<Vec<(usize, Vec<Option<super::call::inline_mut_ref_owner::InlineMutRefArg>>)>>,
    pub(in crate::codegen_ay::chc) inline_walk_param_readonly_ref_seeds:
        Option<Vec<(usize, super::call::inline_readonly_ref::ReadonlyRefValue)>>,
    /// Typed native dyn coercion origins bound in the NEXT inline frame.
    pub(in crate::codegen_ay::chc) inline_walk_param_native_dyn_seeds:
        Option<Vec<(usize, super::call::native_dyn_origin::NativeDynOrigin)>>,
    /// Positive native dyn origin returned from a completed inline frame.
    pub(in crate::codegen_ay::chc) inline_walk_returned_native_dyn:
        Option<super::call::native_dyn_origin::NativeDynOrigin>,
    /// Set when a popped walk frame's return local was address-bound, so the
    /// nested call site can tag its destination.
    pub(in crate::codegen_ay::chc) inline_walk_returned_address: bool,
    /// The length an array VALUE has as a slice: an inline walk carries
    /// `&[T; N]` as the array's own term (value semantics), so its unsize to
    /// `&[T]` keeps no metadata half. The cast records `N` against the term
    /// here, and the walker's `PtrMetadata` of that term reads it back
    /// (`inline_shared/rvalue_ptr.rs`). `None` marks a term recorded with two
    /// different lengths: it answers nothing.
    pub(in crate::codegen_ay::chc) inline_array_value_slice_lens:
        HashMap<ay_bindings::Expr, Option<u64>>,
    /// Set when a popped walk frame's return local was address-carrying (an
    /// aggregate that may hold an address in a field), so the nested call
    /// site can mark its destination (F2 residual).
    pub(in crate::codegen_ay::chc) inline_walk_returned_carrying: bool,
    /// Whether the last inline `&place` / `&raw place` took the ADDRESS lane
    /// of `inline_ref_place_to_expr` (read back by the walker's statement
    /// executor to tag the destination).
    pub(in crate::codegen_ay::chc) last_inline_ref_was_address: bool,

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

    /// Per-block reasons of the untyped-view nets
    /// (`stmt/codegen_stmt_store/untyped_view_scan.rs`), built once per body.
    pub(in crate::codegen_ay::chc) untyped_view_scan:
        std::cell::OnceCell<HashMap<usize, Vec<&'static str>>>,

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

    /// Strong-count ghost state of the body's counted Rc/Arc allocation sites
    /// (`rc_strong_count.rs`). Empty unless the pre-scan accounts for every
    /// handle of a body that clones one.
    pub(in crate::codegen_ay::chc) rc_strong_counters: super::rc_strong_count::RcStrongCounters,

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

    /// Per-VC first-class call-summary UF symbols (`call_uf_table.rs`): tag key
    /// (`fn:<mangled name>` or `math:<intrinsic suffix>`) -> the one
    /// `(declare-fun ...)` minted for it.
    ///
    /// Keyed on the MONOMORPHISED mangled name, so `f::<i32>` and `f::<u32>`
    /// are different symbols and can never be equated. Write-once: the first
    /// application fixes the signature, and a later application whose sorts
    /// disagree is refused and keeps its sound havoc (ay-chc type-checks
    /// applications against the declaration, and a mismatch aborts the parse of
    /// the whole problem). `BTreeMap` for deterministic symbol numbering across
    /// runs.
    pub(in crate::codegen_ay::chc) call_uf_symbols:
        std::collections::BTreeMap<String, super::call_uf_table::CallUfSymbol>,

    /// Whether the congruent call-summary lane is enabled for this harness.
    ///
    /// Set once by `collect_call_uf_congruence_lane` during `collect_state_vars`
    /// — before any rule is encoded — when the pre-scan finds a call PAIR that
    /// congruence can pay for. False leaves both summary lanes on their
    /// pre-existing sound havoc.
    pub(in crate::codegen_ay::chc) call_uf_congruence: bool,

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

    /// `subslice_len` entries withheld while encoding the block named here,
    /// because their cached length reads a column outside its relation frame.
    /// See `stmt/codegen_stmt/subslice_len_frame.rs`.
    pub(in crate::codegen_ay::chc) subslice_len_hidden: Option<(usize, Vec<(usize, Expr)>)>,

    /// FC-06: modifies frames (dynamic extents of contract-checked functions)
    /// found by `modifies_frame::prescan_modifies_frames`. Memory stores in
    /// extent blocks are checked against the frame's declared footprint.
    pub(in crate::codegen_ay::chc) modifies_frames: Vec<super::modifies_frame::ModifiesFrame>,

    /// FC-06: extent block index → index into `modifies_frames`.
    pub(in crate::codegen_ay::chc) modifies_frame_by_bb: HashMap<usize, usize>,

    /// FC-06 frame net: per-block certification state for writes the precise
    /// store checks do not see (`modifies_frame_net`).
    pub(in crate::codegen_ay::chc) modifies_frame_net:
        super::modifies_frame_net::ModifiesFrameNetState,
    /// The stores this body makes into statics' memory images, for the
    /// end-of-translation check that the image sync is sound
    /// (`decl::static_path::StaticImageWrites`).
    pub(in crate::codegen_ay::chc) static_image_writes: super::decl::static_path::StaticImageWrites,
    /// Pointer locals whose value depends on the path taken (multiple producers,
    /// or a single copy/cast/reborrow of such a local), computed once per body
    /// (`pointer_value_is_path_dependent`).
    pub(in crate::codegen_ay::chc) path_dependent_pointer_locals: OnceCell<HashSet<usize>>,

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

    /// Every id `fn_ptr_ids` minted, back to the function it designates
    /// (design 3, D1: `call/fn_ptr_targets.rs`). A call through a pointer whose
    /// value is one of these ids runs exactly that function.
    pub(in crate::codegen_ay::chc) fn_ptr_targets:
        HashMap<u64, crate::codegen_ay::fn_ptr_identity::FnPtrTarget>,

    /// Host fn-pointer locals whose every definition is a reification or a
    /// copy of another such local, with the ids they can hold (`None`: not
    /// closed). Computed on demand (`call/fn_ptr_targets.rs`).
    pub(in crate::codegen_ay::chc) fn_ptr_local_domains: HashMap<usize, Option<Vec<u64>>>,

    /// Terms the host produced for a closed fn-pointer local, with the ids
    /// that local can hold (the intersection when several locals produced
    /// one term). A walked call through a pointer bound to one of these terms
    /// has a complete candidate set (`call/fn_ptr_targets.rs`).
    pub(in crate::codegen_ay::chc) fn_ptr_value_domains: HashMap<Expr, Vec<u64>>,

    /// Every dyn coercion the harness can reach, from the reachability
    /// collector (design 3, D2: `kani_middle/dyn_universe.rs`). `None` when
    /// the body is encoded outside a per-harness codegen: every dyn candidate
    /// set is then treated as possibly incomplete.
    pub(in crate::codegen_ay::chc) dyn_universe:
        Option<Arc<crate::kani_middle::dyn_universe::DynUniverse>>,

    /// Per trait, the universe's runtime types in candidate order (the third
    /// phase of `collect_dyn_trait_candidates`), computed once.
    pub(in crate::codegen_ay::chc) dyn_universe_types_by_trait:
        std::cell::RefCell<HashMap<rustc_span::def_id::DefId, Vec<rustc_public::ty::Ty>>>,

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
    /// The slot values of a by-value flattened argument a walked call bound to
    /// a self placeholder, keyed by the placeholder's name. A walked body that
    /// returns the placeholder unchanged returns that argument: the flattened
    /// destination takes these slots (`build_flattened_destination_field_constraints`).
    pub(in crate::codegen_ay::chc) inline_placeholder_slots: HashMap<String, Vec<Expr>>,

    /// Side-channel checks of drop bodies the inline WALKER inlined for a
    /// `Drop` terminator (`inline_drop.rs`, `inline_shared_drop.rs`). Those
    /// helpers answer only a success guard, so they park the walk's
    /// `deferred_checks` here and the walker's `Drop` arm takes back exactly the
    /// entries its own call added (a length mark, so nested drops stack) and
    /// absorbs them into its state. Before this, a walked drop body's checks
    /// were discarded.
    pub(in crate::codegen_ay::chc) inline_drop_deferred_checks:
        Vec<super::call::inline_body::DeferredInlineCheck>,

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

    /// Memoized whole-local producer counts, saturating at 2: for each local,
    /// how many `_l = ...` statements (empty projection) plus `Call`
    /// terminators with destination `_l` the body holds. A pure function of
    /// `body`. `local_has_multiple_whole_definitions` used to rescan the whole
    /// body per query, and the path-insensitive metadata traces ask it once
    /// per hop per statement, which made coroutine-heavy bodies quadratic
    /// (Coroutines/rustc-coroutine-tests/smoke-resume-args.rs). Holds no
    /// `'body` borrow, so the cell keeps `ChcCtx` covariant.
    pub(in crate::codegen_ay::chc) whole_definition_counts: OnceCell<HashMap<usize, u8>>,

    /// Body-only stability of locals used by historical metadata traces. Memoize
    /// the alias/byte-write walk once per queried local, not once per trace hop.
    pub(in crate::codegen_ay::chc) metadata_source_stability:
        std::cell::RefCell<HashMap<usize, bool>>,
}

pub(in crate::codegen_ay::chc) mod clusters;
mod clusters_ref_resolution;
pub(in crate::codegen_ay::chc) use clusters_ref_resolution::{ConstRefObject, RefResolution};

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
        let maybe_dead_locals_at_entry = Self::compute_maybe_dead_locals_at_block_entry(body);
        // Build the whole-body last-assignment map once: reused by every
        // raw-pointer null-deref check and pointer-check suppression query
        // (null-provenance perf fix — was O(body) per raw-ptr deref).
        let global_assignment_map = Self::build_global_assignment_map(body);
        let step_mode = cfg.step_mode;
        let int_lift = cfg.int_lift;
        let frame_narrowing = cfg.frame_narrowing;
        let straightline_discharge = cfg.straightline_discharge;
        // A lost-checks recovery re-encode (`keep_error_obligations`) translates a
        // function whose first encode already recorded its per-function diagnostic
        // maps; the maps ADD per call, so the re-encode must not record them again.
        let record_per_fn_diagnostics = !cfg.keep_error_obligations;
        let frame_narrowing_flattened = cfg.frame_narrowing && cfg.frame_narrowing_flattened;
        let wide_mem = cfg.wide_mem;
        let extra_pointer_checks = cfg.extra_pointer_checks;
        let prove_safety_only = cfg.prove_safety_only;
        let uninit_checks = cfg.uninit_checks;
        let loop_contracts = cfg.loop_contracts;
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
            #[cfg(trust_toolchain)]
            reborrow_unsupported_recorded: false,
            vc: {
                let mut vc = ChcVc::new();
                vc.keep_error_obligations = cfg.keep_error_obligations;
                vc
            },
            block_relations: HashMap::with_capacity(num_blocks),
            rel_name_to_bb: HashMap::with_capacity(num_blocks),
            fn_name: fn_name_string,
            current_instance,
            state_var_mgr: StateVarManager::with_capacity(num_locals, num_blocks),
            flatten: FlattenState::new(),
            stub_registry: StubRegistry::new(),
            provenance_defs: std::cell::OnceCell::new(),
            provenance_walk_memo: std::cell::RefCell::new(HashMap::new()),
            untyped_view_scan: std::cell::OnceCell::new(),
            deferred_approximation_identities: std::cell::RefCell::new(Vec::new()),
            pending_far_observations: std::cell::RefCell::new(Vec::new()),
            far_observation_relations: std::cell::RefCell::new(Vec::new()),
            far_observation_suppressed: std::cell::Cell::new(false),
            far_check_cast_dests: std::cell::OnceCell::new(),
            far_observation_range_active: std::cell::Cell::new(false),
            far_pointers_possible_cache: std::cell::Cell::new(None),
            far_prescan_missed: std::cell::Cell::new(false),
            far_observation_skipped: std::cell::Cell::new(false),
            far_retry_requested: false,
            far_literal_t64: std::cell::RefCell::new(HashMap::new()),
            far_from_integer: std::cell::RefCell::new(Vec::new()),
            far_var_cache: std::cell::RefCell::new(HashMap::new()),
            far_local_cache: std::cell::RefCell::new(HashMap::new()),
            far_address_taken: std::cell::OnceCell::new(),
            far_wrapping_defs: std::cell::OnceCell::new(),
            pending_address_assumptions: std::cell::RefCell::new(Vec::new()),
            ref_resolution: RefResolution::new(),
            encode: EncodeState::with_capacity(num_locals),
            track_level,
            step_mode,
            int_lift,
            frame_narrowing,
            straightline_discharge,
            record_per_fn_diagnostics,
            frame_narrowing_flattened,
            loop_headers: HashSet::new(),
            int_lifted_vars: HashMap::new(),
            fragment_analysis: None,
            heap_state: ChcHeapState::new(),
            collections: CollectionState::new(),
            wide_mem_manager,
            liveness: LivenessState::new(dead_locals_at_entry, maybe_dead_locals_at_entry),
            needs_mem_promote: false,
            fallback_count: 0,
            diagnostics: ChcDiagnostics::default(),
            extra_pointer_checks,
            prove_safety_only,
            uninit_checks,
            loop_contracts,
            contract_static_havoc,
            memory_safety_checks,
            overflow_checks,
            pending_iter_sum_model: None,
            call_replays_body: false,
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
            rc_strong_counters: Default::default(),
            known_stack_addr_exprs: HashMap::new(),
            known_pointer_to_alloc: HashMap::new(),
            declared_inferable_fns: HashMap::new(),
            call_uf_symbols: std::collections::BTreeMap::new(),
            call_uf_congruence: false,
            known_pow2_locals: HashMap::new(),
            current_encode_bb: 0,
            subslice_len_hidden: None,
            modifies_frames: Vec::new(),
            modifies_frame_by_bb: HashMap::new(),
            modifies_frame_net: Default::default(),
            static_image_writes: Default::default(),
            loop_modifies_frames: Vec::new(),
            loop_modifies_frame_by_bb: HashMap::new(),
            suppress_heap_store_checks: false,
            fragment_mid_output_bb: None,
            fn_ptr_ids: HashMap::new(),
            fn_ptr_targets: HashMap::new(),
            fn_ptr_local_domains: HashMap::new(),
            fn_ptr_value_domains: HashMap::new(),
            dyn_universe: crate::kani_middle::dyn_universe::current_harness_universe(),
            dyn_universe_types_by_trait: std::cell::RefCell::new(HashMap::new()),
            deref_resolve_depth: 0,
            inline_self_field_hints: None,
            inline_placeholder_slots: HashMap::new(),
            inline_drop_deferred_checks: Vec::new(),
            inline_local_address_hints: None,
            spawn_scheduler_vtable_model: None,
            spawn_stubbed_type_key_fragments,
            recursive_unwind_depth,
            const_recursion_nodes_spent: 0,
            switchint_walk_nodes_spent: 0,
            inline_work_budget: Default::default(),
            register_contract_walk_depth: 0,
            inline_walk_write_mark: None,
            native_drop_memory: None,
            #[cfg(all(trust_toolchain, version("1.101")))]
            native_init_stores: HashMap::new(),
            #[cfg(all(trust_toolchain, version("1.101")))]
            native_init_authorized_locals: HashSet::new(),
            inline_walk_param_native_drop_seeds: None,
            inline_walk_frames: Vec::new(),
            inline_walk_param_address_seeds: None,
            inline_walk_param_referent_seeds: None,
            inline_walk_param_mut_owner_seeds: None,
            inline_walk_param_rustcall_mut_owner_seeds: None,
            inline_walk_param_readonly_ref_seeds: None,
            inline_walk_param_native_dyn_seeds: None,
            inline_walk_returned_native_dyn: None,
            inline_walk_returned_address: false,
            inline_array_value_slice_lens: HashMap::new(),
            inline_walk_returned_carrying: false,
            last_inline_ref_was_address: false,
            unwinding_assertions,
            global_assignment_map,
            null_tainted_locals_cache: OnceCell::new(),
            whole_definition_counts: OnceCell::new(),
            metadata_source_stability: std::cell::RefCell::new(HashMap::new()),
            path_dependent_pointer_locals: OnceCell::new(),
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
    pub(in crate::codegen_ay::chc) fn record_fallback(&mut self) -> Booked {
        self.fallback_count += 1;
        tracing::debug!(
            site = %std::panic::Location::caller(),
            fn_name = %self.fn_name,
            "CHC: demoting chc_fallback recorded"
        );
        Booked::recorded()
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
    ///
    /// Returns the [`Booked`] token a fresh value standing on this booking is
    /// minted with (`Havoc::booked`, Rule E).
    pub(in crate::codegen_ay::chc) fn record_sound_fallback_reason(
        &self,
        reason: &'static str,
    ) -> Booked {
        match fallback_soundness(reason) {
            FallbackSoundness::SoundHavoc => self.diagnostics.sound_havoc_drop.inc(),
            FallbackSoundness::FailClose => self.diagnostics.place_translation_drop.inc(),
        }
        record_translation_drop_site_reason_for_fn(&self.fn_name, reason);
        Booked::recorded()
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
    ) -> Booked {
        let booked = self.record_sound_fallback_reason(reason);
        self.vc.record_approximation_identity(freed_var);
        booked
    }

    /// [`Self::record_sound_fallback_reason_identified`] for a site reached
    /// through `&self`.
    ///
    /// The float-binop table select (`float_binop_chc_term`) is built inside
    /// expression translation (`translate_binop`, the NaN-check recomputation,
    /// SIMD lanes), all of which borrow the context shared. The reason and its
    /// counter are recorded now, exactly as the plain recorder does; the
    /// identity is queued and moved into the VC by
    /// [`Self::flush_deferred_approximation_identities`] before the harness is
    /// finalized, so each event is accounted exactly once. A context whose
    /// queue is never flushed stays UNACCOUNTED — the fail-closed direction.
    pub(in crate::codegen_ay::chc) fn record_sound_fallback_reason_identified_deferred(
        &self,
        reason: &'static str,
        freed_var: impl Into<String>,
    ) -> Booked {
        let booked = self.record_sound_fallback_reason(reason);
        self.deferred_approximation_identities.borrow_mut().push(freed_var.into());
        booked
    }

    /// Account every identity queued by
    /// [`Self::record_sound_fallback_reason_identified_deferred`].
    pub(in crate::codegen_ay::chc) fn flush_deferred_approximation_identities(&mut self) {
        for freed_var in self.deferred_approximation_identities.take() {
            self.vc.record_approximation_identity(Some(&freed_var));
        }
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

    /// Mark BOTH heap metadata arrays as modified and record their state-var
    /// indices. For a site that writes both `obj_valid__out` and `obj_size__out`.
    /// Part of #2552: keep obj_valid/obj_size propagation index-based.
    /// Part of #3436: also tracks per-block metadata access for liveness pruning.
    ///
    /// A marked lane's `__out` goes into the rule head, and a head `__out` that
    /// no constraint of the rule binds is a HAVOC of that lane (a clause
    /// variable is universally quantified). A site that writes one lane must
    /// therefore mark only that lane ([`Self::mark_obj_valid_modified`],
    /// [`Self::mark_obj_size_modified`]): marking both havocked the lane it left
    /// alone, with no approximation recorded, and a counterexample through that
    /// havoc was certified Genuine (`box_then_null_deref`: `ptr::null()` after
    /// `Box::new` refuted the Box's drop-time size check).
    pub(in crate::codegen_ay::chc) fn mark_heap_metadata_modified(&mut self) {
        self.mark_obj_valid_modified();
        self.mark_obj_size_modified();
    }

    /// Mark only `obj_valid` as modified: for a site whose sole metadata write
    /// is `obj_valid__out = ...` (see [`Self::mark_heap_metadata_modified`]).
    pub(in crate::codegen_ay::chc) fn mark_obj_valid_modified(&mut self) {
        self.heap_state.mark_obj_valid_modified();
        self.heap_state.mark_metadata_accessed(self.current_encode_bb);
        if let Some(idx) = self.state_var_index_by_name("obj_valid") {
            self.mark_state_var_modified(idx);
        }
    }

    /// Mark only `obj_size` as modified: for a site whose sole metadata write
    /// is `obj_size__out = ...` (see [`Self::mark_heap_metadata_modified`]).
    pub(in crate::codegen_ay::chc) fn mark_obj_size_modified(&mut self) {
        self.heap_state.mark_obj_size_modified();
        self.heap_state.mark_metadata_accessed(self.current_encode_bb);
        if let Some(idx) = self.state_var_index_by_name("obj_size") {
            self.mark_state_var_modified(idx);
        }
    }

    /// Record that the current block reads heap metadata (obj_valid/obj_size)
    /// without necessarily modifying them. Called for safety checks (SELECT on
    /// obj_valid) and bounds checks (SELECT on obj_size).
    /// Part of #3436: per-block metadata liveness tracking.
    pub(in crate::codegen_ay::chc) fn mark_heap_metadata_read(&mut self) {
        self.heap_state.mark_metadata_accessed(self.current_encode_bb);
    }

    /// The layout assumptions pointer-to-integer conversions recorded since
    /// the last call (`pending_address_assumptions`), for the rule under
    /// construction, each once. They read no heap metadata.
    pub(in crate::codegen_ay::chc) fn take_address_assumptions(
        &mut self,
    ) -> Vec<ay_bindings::Expr> {
        let taken: Vec<ay_bindings::Expr> =
            self.pending_address_assumptions.borrow_mut().drain(..).collect();
        let mut facts: Vec<ay_bindings::Expr> = Vec::with_capacity(taken.len());
        for fact in taken {
            if !facts.contains(&fact) {
                facts.push(fact);
            }
        }
        facts
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
