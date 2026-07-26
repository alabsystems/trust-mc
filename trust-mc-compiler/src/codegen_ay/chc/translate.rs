// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Top-level MIR-to-CHC translation entry point.
//!
//! Extracted from chc/mod.rs per #3199 (500-LOC compliance).
//! Contains: `ChcCtx::translate()`, `MemPromoteAction`, `reset_chc_session_counters()`.

use std::sync::atomic::Ordering::Relaxed;

use super::codegen_ctx;
use super::codegen_ctx::diagnostics::GLOBAL_COUNTERS;
use super::codegen_ctx::globals::{
    PENDING_DATATYPE_SORTS, PendingFreshVarDeclsPanicGuard, record_recursive_unwind_for_fn,
};
use super::codegen_ctx::{
    ChcCtx, ChcDiagnostics, PENDING_FRESH_VAR_DECLS, chc_debug_enabled,
    record_aggregate_encoding_gap_for_fn, record_fp_bitvector_encoding_for_fn,
    record_kani_mem_overapprox_for_fn, record_offset_provenance_unresolved_for_fn,
    record_ptr_metadata_unconstrained_for_fn,
    record_signedness_fallback_for_fn, record_static_init_incomplete_for_fn,
    record_sound_havoc_drop_for_fn, record_store_dropped_for_fn, record_stub_approximation_for_fn,
    record_translation_drop_for_fn, record_type_sort_fallback_for_fn, record_unhandled_call_for_fn,
    set_chc_fallback_count_for_fn, take_undef_counter,
};
// Trait impls providing methods called on ChcCtx in translate_inner
use super::codegen_rules::CodegenRules;
use super::codegen_rules_entry::CodegenRulesEntry;
use super::prune_relation_args::prune_dead_array_relation_args;
use super::straightline_proof::{discharge_straightline_safety, straightline_discharge_disabled};

/// Whether `translate()` detected that memory promotion is needed.
///
/// When `Promote` is returned, the caller should retry translation at
/// `ChcTrackLevel::Mem` to capture projected Ref/AddressOf operations
/// (Part of #2084).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::codegen_ay) enum MemPromoteAction {
    /// Translation completed without needing memory promotion.
    Keep,
    /// Translation detected projected Ref/AddressOf — retry at `ChcTrackLevel::Mem`.
    Promote,
}

/// Reset all CHC diagnostic and name-generator counters to zero (Part of #2360).
///
/// Call at session start in process-reuse scenarios to prevent stale counter values
/// from leaking across compilations. Returns nothing — drain values are discarded.
pub(in crate::codegen_ay) fn reset_chc_session_counters() {
    take_undef_counter();
    codegen_ctx::ChcDiagnostics::reset_global_counters_for_session();
}

/// Snapshot of global diagnostic counters taken before translation.
/// Used to compute per-function deltas after codegen completes.
struct CounterSnapshot {
    type_sort_fallback: usize,
    signedness_fallback: u64,
    store_dropped: usize,
    unhandled_call: usize,
    place_translation_drop: usize,
    sound_havoc_drop: usize,
    const_translation_drop: usize,
    unsupported_field_projection: usize,
    kani_mem_overapprox: usize,
    ptr_metadata_unconstrained: usize,
    static_init_incomplete: usize,
    fp_bitvector_encoding: usize,
    aggregate_encoding_gap: usize,
    stub_approximation: usize,
}

impl CounterSnapshot {
    fn capture() -> Self {
        Self {
            type_sort_fallback: GLOBAL_COUNTERS.type_sort_fallback.load(Relaxed),
            signedness_fallback: crate::codegen_ay::shared::get_signedness_fallback_count() as u64,
            store_dropped: GLOBAL_COUNTERS.store_dropped_transition.load(Relaxed),
            unhandled_call: GLOBAL_COUNTERS.unhandled_call.load(Relaxed),
            place_translation_drop: GLOBAL_COUNTERS.place_translation_drop.load(Relaxed),
            sound_havoc_drop: GLOBAL_COUNTERS.sound_havoc_drop.load(Relaxed),
            const_translation_drop: GLOBAL_COUNTERS.const_translation_drop.load(Relaxed),
            unsupported_field_projection: GLOBAL_COUNTERS
                .unsupported_field_projection
                .load(Relaxed),
            kani_mem_overapprox: GLOBAL_COUNTERS.kani_mem_overapprox.load(Relaxed),
            ptr_metadata_unconstrained: GLOBAL_COUNTERS.ptr_metadata_unconstrained.load(Relaxed),
            static_init_incomplete: GLOBAL_COUNTERS.static_init_incomplete.load(Relaxed),
            fp_bitvector_encoding: GLOBAL_COUNTERS.fp_bitvector_encoding.load(Relaxed),
            aggregate_encoding_gap: GLOBAL_COUNTERS.aggregate_encoding_gap.load(Relaxed),
            stub_approximation: GLOBAL_COUNTERS.stub_approximation.load(Relaxed),
        }
    }

    /// Compute deltas and record per-function diagnostics (Part of #2906, #2966).
    fn record_deltas(self, fn_name: &str, diagnostics: &ChcDiagnostics) {
        let tsf_delta = GLOBAL_COUNTERS
            .type_sort_fallback
            .load(Relaxed)
            .saturating_sub(self.type_sort_fallback);
        let sf_delta = (crate::codegen_ay::shared::get_signedness_fallback_count() as u64)
            .saturating_sub(self.signedness_fallback) as usize;
        diagnostics.type_sort_fallback.set(tsf_delta);
        diagnostics.signedness_fallback.set(sf_delta);

        record_type_sort_fallback_for_fn(fn_name, tsf_delta);
        record_signedness_fallback_for_fn(fn_name, sf_delta);
        record_store_dropped_for_fn(
            fn_name,
            GLOBAL_COUNTERS
                .store_dropped_transition
                .load(Relaxed)
                .saturating_sub(self.store_dropped),
        );
        record_unhandled_call_for_fn(
            fn_name,
            GLOBAL_COUNTERS.unhandled_call.load(Relaxed).saturating_sub(self.unhandled_call),
        );
        let td_delta = GLOBAL_COUNTERS
            .place_translation_drop
            .load(Relaxed)
            .saturating_sub(self.place_translation_drop)
            + GLOBAL_COUNTERS
                .const_translation_drop
                .load(Relaxed)
                .saturating_sub(self.const_translation_drop)
            + GLOBAL_COUNTERS
                .unsupported_field_projection
                .load(Relaxed)
                .saturating_sub(self.unsupported_field_projection);
        record_translation_drop_for_fn(fn_name, td_delta);
        // Recognized-clean SoundHavoc drops are attributed with the identical
        // per-fn delta mechanism as `place_translation_drop`, so a proof's
        // SoundHavoc/fail-close split is internally consistent
        // (Part of #unsound-havoc-split).
        record_sound_havoc_drop_for_fn(
            fn_name,
            GLOBAL_COUNTERS.sound_havoc_drop.load(Relaxed).saturating_sub(self.sound_havoc_drop),
        );
        record_kani_mem_overapprox_for_fn(
            fn_name,
            GLOBAL_COUNTERS
                .kani_mem_overapprox
                .load(Relaxed)
                .saturating_sub(self.kani_mem_overapprox),
        );
        // marker: offset_isize_overflow_precise. Attribute this context's
        // offset-provenance-unresolved demotion to `fn_name`, so the driver
        // (which falls back to the crate total for an EMPTY per-harness map)
        // charges it ONLY to the harness that produced it — never to a sibling
        // whose own offset site is fully discharged. Use the per-ChcCtx `local`
        // count (`get()`), which is already net of any
        // `discharge_local_into_global()` above (a genuine const-folded UB
        // violation moots this doubt), and non-racy across parallel codegen.
        record_offset_provenance_unresolved_for_fn(
            fn_name,
            diagnostics.offset_provenance_unresolved.get(),
        );
        record_ptr_metadata_unconstrained_for_fn(
            fn_name,
            GLOBAL_COUNTERS
                .ptr_metadata_unconstrained
                .load(Relaxed)
                .saturating_sub(self.ptr_metadata_unconstrained),
        );
        record_static_init_incomplete_for_fn(
            fn_name,
            GLOBAL_COUNTERS
                .static_init_incomplete
                .load(Relaxed)
                .saturating_sub(self.static_init_incomplete),
        );
        record_fp_bitvector_encoding_for_fn(
            fn_name,
            GLOBAL_COUNTERS
                .fp_bitvector_encoding
                .load(Relaxed)
                .saturating_sub(self.fp_bitvector_encoding),
        );
        record_aggregate_encoding_gap_for_fn(
            fn_name,
            GLOBAL_COUNTERS
                .aggregate_encoding_gap
                .load(Relaxed)
                .saturating_sub(self.aggregate_encoding_gap),
        );
        record_stub_approximation_for_fn(
            fn_name,
            GLOBAL_COUNTERS
                .stub_approximation
                .load(Relaxed)
                .saturating_sub(self.stub_approximation),
        );
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// SOUNDNESS fail-close (#67; live probes: loop_assigns_for_ptr_fail at
    /// the v23 gate, fail_missing_recursion_attr at the v24 gate).
    ///
    /// Check sites REGISTERED per-property relations, yet after pruning the
    /// system retains no program (block) rules — the entry-anchored CFG was
    /// silently discarded (walk abort -> zero error rules -> the backward
    /// prune deletes every block rule), leaving a degenerate system whose
    /// rule-less properties all auto-report SUCCESS. A VC with no program can
    /// never legitimately prove a registered check — demote via
    /// `record_fallback` so any PROOF verdict becomes FAILURE. TIC
    /// (template_check) is the one legitimate rules-clearing discharge and is
    /// exempted via `tic_discharged`; the straightline discharge runs after
    /// this check and never fires on an empty system.
    fn fail_close_degenerate_system(&mut self, tic_discharged: bool) {
        if tic_discharged || self.vc.properties.is_empty() {
            return;
        }
        let has_program_rule = self.vc.rules.iter().any(|r| {
            let head: &str = r.head.name.as_ref();
            head != "error" && !head.starts_with("error_p")
        });
        if !has_program_rule {
            tracing::warn!(
                fn_name = %self.fn_name,
                properties = self.vc.properties.len(),
                "CHC: degenerate system — registered properties but no program rules survive pruning; demoting (fail-closed)"
            );
            self.record_fallback();
        }
    }

    /// Drain thread-local fresh vars into the VC, declaring any datatype sorts
    /// those vars reference before they become SMT `declare-var` commands.
    ///
    /// Part of #3945: inline-call over-approximation can synthesize fresh vars
    /// for hashbrown internal datatype sorts that never appear in state vars.
    fn drain_pending_fresh_var_decls_into_vc(&mut self) {
        let pending_var_decls =
            PENDING_FRESH_VAR_DECLS.with(|decls| decls.borrow_mut().drain(..).collect::<Vec<_>>());
        self.declare_pending_var_datatype_sorts(&pending_var_decls);
        for decl in pending_var_decls {
            self.vc.add_var(decl);
        }
        // Part of #4053: drain pending DT sorts from immutable codegen paths
        // (e.g. option_unwrap_value field_select) that cannot access self.vc.
        let pending_dt_sorts =
            PENDING_DATATYPE_SORTS.with(|sorts| sorts.borrow_mut().drain(..).collect::<Vec<_>>());
        for sort in &pending_dt_sorts {
            self.declare_datatype_sort_if_needed(sort);
        }
    }

    /// Translates the MIR body to a CHC verification condition.
    ///
    /// This is the main entry point for CHC code generation.
    ///
    /// REQUIRES: `self` was created from the same `tcx`/`body` pair.
    /// ENSURES: Returned `ChcVc` declares one relation per basic block.
    /// ENSURES: Returned `ChcVc` declares an `error` relation and queries it.
    /// ENSURES: Returned `ChcVc` declares input/output state variables.
    pub(super) fn translate(self) -> (trust_mc_core::chc::ChcVc, MemPromoteAction) {
        let (vc, action, _diagnostics) = self.translate_inner();
        (vc, action)
    }

    /// Like `translate()`, but also returns the per-context diagnostic counters.
    ///
    /// Tests use this to read counters directly from the `ChcCtx` that produced
    /// them — no global atomics or `Mutex<()>` serialization needed.
    #[cfg(test)]
    pub(super) fn translate_with_diagnostics(
        self,
    ) -> (trust_mc_core::chc::ChcVc, MemPromoteAction, ChcDiagnostics) {
        self.translate_inner()
    }

    /// Like `translate()`, but stops before Template-Directed Inductive
    /// Checking (TIC). Used by linearization tests that need to inspect
    /// intermediate rule structure before TIC replaces the VC.
    ///
    /// Part of #3258: TIC clears all rules on success, so tests verifying
    /// linearization artifacts must use this entry point.
    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(super) fn translate_skip_tic(mut self) -> (trust_mc_core::chc::ChcVc, MemPromoteAction) {
        let _guard = PendingFreshVarDeclsPanicGuard::arm();
        let snapshot = CounterSnapshot::capture();

        self.declare_block_relations();
        self.declare_error_relation();
        self.emit_entry_rule();
        self.generate_transition_rules();
        fixup_relation_app_arities(&mut self.vc);
        super::codegen_rules::lemma_hint::emit_loop_invariant_lemmas(&mut self);
        super::codegen_rules::lemma_linearize::apply_linearization(&mut self);
        // Intentionally skip: apply_template_check (TIC)
        self.prune_vc_unused_type_arrays();
        self.normalize_free_array_bases_before_scalarization();
        self.scalarize_const_index_arrays();
        // Part of #4286: `scalarize_const_index_arrays` (and its `apply_const_folding`
        // sub-pass) rebuild each relation's `arg_sorts` from the FIRST rule head
        // that mentions the relation. If another rule's *body* app for the same
        // relation already had stale (shorter) args, that staleness survives
        // because only heads drive the rebuilt arity. Re-run the late-array
        // fixup so any body app that is now shorter than the decl is padded
        // with universally-quantified `__pad_*` vars.
        fixup_relation_app_arities(&mut self.vc);
        self.vc.prune_orphan_block_rules();
        prune_dead_array_relation_args(&mut self.vc);
        fixup_relation_app_arities(&mut self.vc);
        self.fail_close_degenerate_system(false);
        if !straightline_discharge_disabled() && discharge_straightline_safety(&mut self.vc) {
            tracing::debug!("CHC: bounded straight-line proof discharged scalarized VC");
        }
        self.vc.query = trust_mc_core::chc::ChcQuery::new().with_target("error");

        self.drain_pending_fresh_var_decls_into_vc();

        snapshot.record_deltas(&self.fn_name, &self.diagnostics);

        let action =
            if self.needs_mem_promote { MemPromoteAction::Promote } else { MemPromoteAction::Keep };
        (self.vc, action)
    }

    fn translate_inner(mut self) -> (trust_mc_core::chc::ChcVc, MemPromoteAction, ChcDiagnostics) {
        let _guard = PendingFreshVarDeclsPanicGuard::arm();
        let snapshot = CounterSnapshot::capture();

        // Fail-closed under `-Z uninit-checks` for constructs the scalar
        // shadow-memory model does not track (Kani covers these via its
        // points-to delayed-UB pass; trust-mc's is task #24). The demoting
        // `chc_fallback` counter (per-fn, well-plumbed) flips any PROOF to
        // FAILURE for the harness:
        // - union-typed locals: field writes/reads re-shape initialization
        //   and padding with no shadow update (uninit/unions.rs proved Safe
        //   on a program whose padding read is UB).
        // - direct `std::alloc::alloc` calls: the former BLANKET demotion
        //   here is replaced by stub-site accounting (raw-alloc route). The
        //   `__rust_alloc` stub applies the exact shadow effect for its fresh
        //   object (`append_alloc_shadow_constraints`: tracked byte in the
        //   new object => UNINIT), so a stub-tracked allocation is faithfully
        //   modeled; only the untracked dispatch-fallback path still records
        //   the demoting `chc_fallback` (`codegen_call_alloc_fallback`).
        //   Must-keep-FAIL gates: uninit/alloc-to-slice.rs,
        //   uninit/intrinsics/intrinsics.rs.
        if self.uninit_checks {
            if crate::codegen_ay::codegen_function::body_has_union_local(self.body) {
                tracing::debug!(fn_name = %self.fn_name, "uninit-checks: union local — chc_fallback");
                self.record_fallback();
            }
            // - `Vec::set_len` / `String::set_len`: grows the logical length over
            //   RESERVED-but-UNINITIALIZED capacity (typically after
            //   `Vec::with_capacity`), whose alloc is hidden inside the callee so
            //   the raw-alloc stub accounting never fires on the harness. A read
            //   of the grown region is UB but the shadow model marks it
            //   initialized (uninit/vec-read-bad-len.rs proved Safe on an uninit
            //   read).
            if crate::codegen_ay::codegen_function::body_has_vec_set_len_call(self.body) {
                tracing::debug!(fn_name = %self.fn_name, "uninit-checks: Vec::set_len — chc_fallback");
                self.record_fallback();
            }
        }

        // Fail-closed for a QUANTIFIED contract postcondition. A
        // `kani::forall!`/`kani::exists!` inside a `#[kani::ensures]` clause of a
        // `#[kani::proof_for_contract]` harness is asserted (`kani::assert` on the
        // quantifier result) but the unrolled quantifier evaluates VACUOUSLY:
        // the raw-pointer dereferences inside the quantifier closure (e.g.
        // `*ptr.wrapping_byte_offset(k)`) collapse under the scalar encoding so
        // the postcondition assertion cannot witness a violation. This proved a
        // violated contract Safe (expected/quantifiers/contracts_fail.rs). trust-mc
        // cannot yet faithfully enforce a quantified contract postcondition, so
        // demote via chc_fallback — any resulting PROOF becomes FAILURE instead of
        // a false SAFE. Gated on the contract dispatch marker so plain
        // `kani::assert(forall!(...))` quantifier proofs (no contract) are
        // unaffected, and on the quantifier call so non-quantifier contracts are
        // unaffected.
        if crate::codegen_ay::codegen_function::body_has_contract_dispatch(self.body)
            && crate::codegen_ay::codegen_function::body_has_kani_quantifier_call(self.body)
        {
            tracing::debug!(
                fn_name = %self.fn_name,
                "contract proof with quantified postcondition — chc_fallback (fail-closed)"
            );
            self.record_fallback();
        }

        self.declare_block_relations();

        tracing::debug!(
            "translate fn={} locals={} blocks={} bigint_refs={}",
            self.fn_name,
            self.body.local_decls().count(),
            self.body.blocks.len(),
            self.ref_resolution.bigint_ref_targets.len()
        );

        self.declare_error_relation();
        self.emit_entry_rule();
        self.generate_transition_rules();
        fixup_relation_app_arities(&mut self.vc);

        super::codegen_rules::lemma_hint::emit_loop_invariant_lemmas(&mut self);
        super::codegen_rules::lemma_linearize::apply_linearization(&mut self);
        // TIC: If candidate invariants are detected and verified via 3 SMT
        // checks (initiation, consecution, safety), replace the VC with a
        // trivially safe system. Part of #3258.
        let tic_discharged = super::codegen_rules::template_check::apply_template_check(&mut self);
        self.prune_vc_unused_type_arrays();
        self.normalize_free_array_bases_before_scalarization();
        self.scalarize_const_index_arrays();
        // Part of #4286: `scalarize_const_index_arrays` (and its `apply_const_folding`
        // sub-pass) rebuild each relation's `arg_sorts` from the FIRST rule head
        // that mentions the relation. If another rule's *body* app for the same
        // relation already had stale (shorter) args, that staleness survives
        // because only heads drive the rebuilt arity. Re-run the late-array
        // fixup so any body app that is now shorter than the decl is padded
        // with universally-quantified `__pad_*` vars.
        fixup_relation_app_arities(&mut self.vc);
        self.vc.prune_orphan_block_rules();
        prune_dead_array_relation_args(&mut self.vc);
        fixup_relation_app_arities(&mut self.vc);
        self.fail_close_degenerate_system(tic_discharged);
        if !straightline_discharge_disabled() && discharge_straightline_safety(&mut self.vc) {
            tracing::debug!("CHC: bounded straight-line proof discharged scalarized VC");
        }
        self.vc.query = trust_mc_core::chc::ChcQuery::new().with_target("error");

        if chc_debug_enabled() {
            tracing::debug!("=== DUMPING ALL RULES ===");
            for (i, rule) in self.vc.rules.iter().enumerate() {
                tracing::debug!("rule[{}] = {:?}", i, rule);
            }
            tracing::debug!("=== END RULES ===");
        }

        if self.fallback_count > 0 {
            tracing::warn!(
                fn_name = %self.fn_name,
                fallback_count = self.fallback_count,
                "CHC: encoding used type/size fallback defaults — verification may be unsound"
            );
        }
        self.diagnostics.fallback_count.set(self.fallback_count);
        set_chc_fallback_count_for_fn(&self.fn_name, self.fallback_count);
        // Part of #4058 D2: record recursive unwind exhaustion per-function
        // so the compiler can emit SMT markers for the driver.
        let recursive_unwind_count = self.diagnostics.recursive_unwind_exhausted.get();
        if recursive_unwind_count > 0 {
            record_recursive_unwind_for_fn(&self.fn_name, recursive_unwind_count);
        }

        self.drain_pending_fresh_var_decls_into_vc();

        // A copy / copy_nonoverlapping / write_bytes span-access UB check that
        // scalarization const-folded to an UNCONDITIONAL violation is a
        // PRECISE, provenance-independent counterexample: the harness fails
        // genuinely at a fully-concrete misaligned / count-overflow / OOB
        // intrinsic access (the alignment/overflow/bound obligation does not
        // rest on the over-approximated obj_id lane). Discharge exactly THIS
        // function's `offset_provenance_unresolved` contribution so that genuine
        // counterexample is no longer masked as an `EncodingGap` by the
        // provenance-unresolved doubt the same function accumulated while
        // lowering the pointer arithmetic that produced the definitely-bad
        // pointer. Bounding the discharge to this function's `local` share of
        // the crate-global counter leaves sibling harnesses' fail-closed nets
        // intact. SOUNDNESS: this only fires when a check DEFINITELY fails, so
        // the harness fails genuinely — it cannot convert a proof into a false
        // Safe (over-approximate, still-symbolic heap-access CTREX keep their
        // fail-closed demotion; see the corpus write_bytes/volatile cases).
        if self.intrinsic_span_check_folded_definite() {
            self.diagnostics.offset_provenance_unresolved.discharge_local_into_global();
        }

        // Task #78 (OFFSET_PROV_GENUINE_CERT): account the
        // `offset_provenance_unresolved` demotion so the harness's
        // approximation identity is COMPLETE. That demotion SKIPS an
        // allocation-bound / in-bounds check (`ptr_offset_alloc_bound_check`
        // returned None) but frees NO readable SMT state var — the result
        // pointer stays fully constrained by the pointer arithmetic. So each
        // event is accounted with a `None` identity (dead / provably
        // unreadable): it counts toward completeness WITHOUT adding a readable
        // var, letting the driver certify an INDEPENDENT violated check (e.g.
        // the isize-overflow property, which reads only `count` + the pointee
        // size — both concrete) Genuine. The skipped in-bounds obligation
        // ITSELF stays demoted (this only completes the accounting; it never
        // claims to verify the check). Read the LOCAL counter AFTER the
        // intrinsic-span discharge above so a discharged (already-Genuine)
        // offset contributes zero here and cannot double-count. Because the
        // recorded count and the added total below are the SAME value, offset
        // is self-consistent and can never be the source of incompleteness —
        // sound precisely because it frees nothing readable.
        let offset_provenance_freed = self.diagnostics.offset_provenance_unresolved.get();
        for _ in 0..offset_provenance_freed {
            self.vc.record_approximation_identity(None);
        }

        // Task #78: finalize approximation-identity plumbing. The freed-var
        // identities were pushed to `self.vc.approximated_vars` during codegen
        // (SoundFallback dest havoc). Compute the per-property dependence verdict
        // over the finalized rules and set the compiler-side (local best-effort)
        // completeness flag. `unhandled_call` is EXCLUDED from the freeing total:
        // it double-labels a `place_translation_drop` event from the same
        // SoundFallback site (the driver applies the same subtraction against its
        // own per-harness taint total, which is the authoritative gate).
        let sound_approx_freeing_total = self.diagnostics.place_translation_drop.get()
            + self.diagnostics.sound_havoc_drop.get()
            + self.diagnostics.static_init_incomplete.get()
            + self.diagnostics.ptr_metadata_unconstrained.get()
            + self.diagnostics.aggregate_encoding_gap.get()
            + self.diagnostics.stub_approximation.get()
            + self.diagnostics.kani_mem_overapprox.get()
            + offset_provenance_freed;
        self.vc.finalize_approximation_identity(sound_approx_freeing_total);

        snapshot.record_deltas(&self.fn_name, &self.diagnostics);

        let action =
            if self.needs_mem_promote { MemPromoteAction::Promote } else { MemPromoteAction::Keep };
        (self.vc, action, self.diagnostics)
    }

    /// Emit-time normalization is too late once scalarization has rewritten
    /// the array selects needed to recover initialized lanes.
    fn normalize_free_array_bases_before_scalarization(&mut self) {
        let normalized = self.vc.normalize_free_array_bases();
        if normalized > 0 {
            tracing::debug!(
                normalized,
                "CHC: normalized free-var array bases before scalarization"
            );
        }
    }

    /// Whether a tagged intrinsic span-safety property (`error_p{id}`, recorded
    /// by `emit_intrinsic_span_ub_check`) const-folded to an UNCONDITIONAL
    /// violation after scalarization: its check rule (`block ∧ ¬cond → error_p`)
    /// survived pruning with NO residual violation constraint, i.e. it fires
    /// whenever its guarding block relation holds.
    ///
    /// This is only reachable for a fully-concrete (typically stack-allocation)
    /// copy / copy_nonoverlapping / write_bytes access whose alignment /
    /// count-overflow / allocation-bound check evaluated to a definite
    /// violation. A still-symbolic access (e.g. an over-approximated heap
    /// pointer whose offset lane never folds) keeps a non-trivial constraint,
    /// so it does NOT match here and correctly retains its provenance-unresolved
    /// fail-closed demotion.
    fn intrinsic_span_check_folded_definite(&self) -> bool {
        use ay_bindings::ExprValue;
        if self.diagnostics.intrinsic_span_property_ids.is_empty() {
            return false;
        }
        // The emitted VC still carries each span check as a symbolic constraint
        // over the pointer's offset-lane state var; the whole-harness constant
        // propagation that collapses a fully-concrete (stack-allocation) access
        // to a definite violation runs later, in `split_emit_chc`. Replicate
        // that fold on a THROWAWAY clone here so we can detect the collapse
        // while the per-function offset-provenance `local` count is still live.
        //
        // Only a pointer whose offset lane is transitively an identity-chain
        // CONSTANT (i.e. a stack allocation the encoder laid out concretely)
        // folds: `bvurem(concrete_offset, align) == 0` collapses to a literal.
        // An over-approximated heap pointer keeps a genuinely-free offset lane,
        // so its span check never folds and correctly retains its
        // provenance-unresolved fail-closed demotion (see the corpus
        // write_bytes/volatile heap cases, which stay masked).
        let mut folded = self.vc.clone();
        folded.propagate_constants();
        folded.prune_orphan_block_rules();
        folded.prune_dead_identity_scalars();
        folded.normalize_free_array_bases();
        super::scalarize_vc(&mut folded);
        folded.eliminate_trivially_false_rules();

        // A tagged CHECK rule (head `error_p{id}`, guarded by a block relation)
        // whose VIOLATION term folded away fires whenever its block is reached
        // in the propagated concrete state. After the fold, the only surviving
        // body constraints are `true` or state-equality guards `Eq(state_arg,
        // const)` carried from the forward transition (which pin the block's
        // reachable state) — never the violation itself. A still-symbolic
        // (over-approximated heap) access instead keeps its violation as a
        // residual `Not(BvURem …)` / `BvULe(…)` / `obj_size`-select constraint,
        // which is NOT an equality guard, so it correctly does not match here.
        let is_folded_reachability_guard = |e: &ay_bindings::Expr| {
            matches!(e.value(), ExprValue::BoolConst(true) | ExprValue::Eq(_, _))
        };
        self.diagnostics.intrinsic_span_property_ids.iter().any(|id| {
            let rel = format!("error_p{id}");
            folded.rules.iter().any(|rule| {
                rule.head.name.as_str() == rel
                    && rule.body.relation.is_some()
                    && rule.body.constraints.iter().all(&is_folded_reachability_guard)
            })
        })
    }
}

/// Returns `true` iff every block-relation application in `vc` (rule heads and
/// rule body relation apps) has an argument vector that positionally
/// sort-matches that relation's declaration. The nullary `error` relation and
/// any app referencing an undeclared relation are ignored.
///
/// This is the invariant that AY's CHC parser enforces: an application whose
/// argument sorts diverge from the declared predicate signature is rejected
/// ("expected argument sort ...") and reported as UNKNOWN.
pub(in crate::codegen_ay) fn block_relation_apps_consistent(
    vc: &trust_mc_core::chc::ChcVc,
) -> bool {
    use std::collections::HashMap;
    let rel_sorts: HashMap<&str, &[ay_bindings::Sort]> =
        vc.relations.iter().map(|r| (r.name.as_str(), r.arg_sorts.as_slice())).collect();
    let app_ok = |app: &trust_mc_core::chc::RelationApp| -> bool {
        let Some(decl) = rel_sorts.get(app.name.as_str()) else { return true };
        app.args.len() == decl.len() && app.args.iter().zip(decl.iter()).all(|(a, d)| a.sort() == d)
    };
    vc.rules
        .iter()
        .all(|rule| app_ok(&rule.head) && rule.body.relation.as_ref().map_or(true, app_ok))
}

/// Do all applications of each block relation agree on WHICH slot lives at each
/// position?
///
/// [`block_relation_apps_consistent`] compares only sorts, so it is blind to a
/// permutation inside a run of identically-sorted columns — and that permutation
/// is not a cosmetic problem, it silently fabricates proofs. Observed shape
/// (`assert!(it.next().is_none())` over a 3-element slice):
///
/// ```text
/// (declare-rel f__bb2 (Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)))
/// producer: (f__bb2 _6 _8 true #x00000001 e0 e1 e2)          ; slot 3 = Option payload
/// consumer: (f__bb2 _6 _8 _10_fld0 e0 e1 e2 __pad_f__bb2_7)  ; payload column missing, pad at TAIL
/// ```
///
/// Both applications sort-conform, so the sort net passes and
/// [`canonicalize_block_relation_apps`] skips them (it only rewrites
/// NON-conforming apps). But every array column is shifted left by one, so the
/// consumer's own body constraints `e0=1 ∧ e1=2 ∧ e2=3` bind against
/// `(payload, e0, e1)` and demand `1=1 ∧ 1=2 ∧ 2=3`. The body is UNSATISFIABLE,
/// the successor block is unreachable, the error edge is underivable, and the
/// query comes back UNSAT — reported as a clean proof of a FALSE assertion.
///
/// A disagreement here means the frame is corrupt, so the honest answer is to
/// discard the optimized VC rather than prove anything from it. Only
/// `Named`/`Named` conflicts count: constants carry no name, and pads are
/// legitimately absent slots.
pub(in crate::codegen_ay) fn block_relation_slot_names_consistent(
    vc: &trust_mc_core::chc::ChcVc,
) -> bool {
    use ay_bindings::ExprValue;
    use std::collections::HashMap;

    let rel_sorts: HashMap<&str, &[ay_bindings::Sort]> =
        vc.relations.iter().map(|r| (r.name.as_str(), r.arg_sorts.as_slice())).collect();
    let conforms = |app: &trust_mc_core::chc::RelationApp| -> bool {
        rel_sorts.get(app.name.as_str()).is_some_and(|decl| {
            app.args.len() == decl.len()
                && app.args.iter().zip(decl.iter()).all(|(a, d)| a.sort() == d)
        })
    };

    // relation -> position -> first canonical name seen there.
    let mut seen: HashMap<String, Vec<Option<String>>> = HashMap::new();
    let mut ok = true;
    let mut observe = |app: &trust_mc_core::chc::RelationApp| {
        if !ok || !conforms(app) {
            return;
        }
        let entry =
            seen.entry(app.name.to_string()).or_insert_with(|| vec![None; app.args.len()]);
        for (k, arg) in app.args.iter().enumerate() {
            let ExprValue::Var { name } = arg.value() else { continue };
            let Some(base) = canonical_slot_name(name) else { continue };
            match &entry[k] {
                Some(existing) if *existing != base => {
                    tracing::warn!(
                        relation = app.name.as_str(),
                        position = k,
                        expected = existing.as_str(),
                        found = base.as_str(),
                        "CHC: block-relation slot misalignment — applications disagree on which \
                         state variable occupies this column"
                    );
                    ok = false;
                    return;
                }
                Some(_) => {}
                None => entry[k] = Some(base),
            }
        }
    };
    for rule in &vc.rules {
        observe(&rule.head);
        if let Some(ref br) = rule.body.relation {
            observe(br);
        }
    }
    ok
}

/// Strip the encoder's per-slot decorations from a state-variable name to
/// recover its canonical *input* name (the slot identity).
///
/// The MIR→CHC encoder names a slot's input var `_<fn>_<N>` and derives the
/// output/intermediate variants by appending `__out` or `__mid_bb<k>`. Padding
/// fillers are named `__pad_<rel>_<i>` and are NOT slot identities — they map to
/// `None`.
fn canonical_slot_name(name: &str) -> Option<String> {
    if name.starts_with("__pad_") {
        return None;
    }
    let mut base = name;
    if let Some(pos) = base.find("__mid_bb") {
        base = &base[..pos];
    }
    if let Some(stripped) = base.strip_suffix("__out") {
        base = stripped;
    }
    Some(base.to_string())
}

/// Per-position canonical slot identity for one block relation, derived by
/// unioning the *consistent* (declaration-conforming) applications of that
/// relation.
#[derive(Clone)]
enum CanonSlot {
    /// A state-variable slot identified by its canonical input name. At least
    /// one consistent application carried this slot as a named variable here.
    Named(String),
    /// A slot that every consistent application filled with a constant /
    /// compound value (no recoverable name) — matched positionally, in order.
    Const,
    /// A slot every consistent application padded — always re-emitted as a pad.
    Pad,
}

/// Name-based canonicalization of block-relation applications (#argorder).
///
/// The post-emission optimization pipeline (constant propagation, scalarization,
/// dead-arg pruning) edits relation columns per-rule and rebuilds each
/// relation's declared arity from the first application it encounters. When a
/// loop back-edge (or any application) ends up shorter than the declaration, the
/// sort-only arity fixup pads at the tail — it cannot *re-permute*, so a
/// datatype-sorted slot (e.g. `ControlFlow<…>`) sharing a column run with many
/// `(_ BitVec 64)` slots lands at the wrong position. AY then rejects the
/// ill-sorted predicate application.
///
/// This pass repairs that by re-emitting every divergent application in
/// canonical slot order. For each block relation it derives the canonical
/// per-position slot identity by unioning every application that already matches
/// the declaration positionally (a slot is "named" if any conforming app carried
/// a named state variable there), then rewrites each non-conforming application
/// by placing its named arguments at the canonical position they belong to **by
/// name** (re-permuting freely) and its constant/compound arguments positionally
/// in canonical order. Genuinely-absent slots become `__pad_*` vars. Unlike the
/// sort-only realigner this is exact under sort ambiguity.
///
/// Soundness: an application is rewritten only when *every* named argument it
/// carries maps to a known canonical position and *every* constant it carries is
/// consumed — i.e. no value is dropped or placed at an unverifiable position.
/// Anything ambiguous is left untouched for the caller's safety net (the
/// pre-optimization snapshot) to handle.
pub(in crate::codegen_ay) fn canonicalize_block_relation_apps(vc: &mut trust_mc_core::chc::ChcVc) {
    use ay_bindings::{Expr, ExprValue, Sort};
    use std::collections::HashMap;
    use std::sync::Arc;
    use trust_mc_core::chc::RelationApp;

    // Declared signatures (authoritative arity + sorts).
    let rel_sorts: HashMap<String, Vec<Sort>> =
        vc.relations.iter().map(|r| (r.name.to_string(), r.arg_sorts.clone())).collect();

    let app_conforms = |app: &RelationApp| -> bool {
        rel_sorts.get(app.name.as_str()).is_some_and(|decl| {
            app.args.len() == decl.len()
                && app.args.iter().zip(decl.iter()).all(|(a, d)| a.sort() == d)
        })
    };

    // Build the canonical per-position layout for each relation by unioning all
    // conforming applications. A position is `Named(b)` if some conforming app
    // carried base name `b` there; if conforming apps disagree on the name at a
    // position the slot is demoted to `Const` (positional) to stay sound.
    let mut canon: HashMap<String, Vec<CanonSlot>> = HashMap::new();
    {
        // Per relation, per position: the single agreed name (Some), a conflict
        // marker (handled below), and whether any app showed a non-pad value.
        let mut acc: HashMap<String, Vec<(Option<String>, bool, bool, bool)>> = HashMap::new();
        let observe =
            |app: &RelationApp,
             acc: &mut HashMap<String, Vec<(Option<String>, bool, bool, bool)>>| {
                if !app_conforms(app) {
                    return;
                }
                let entry = acc
                    .entry(app.name.to_string())
                    .or_insert_with(|| vec![(None, false, false, false); app.args.len()]);
                for (k, arg) in app.args.iter().enumerate() {
                    // tuple = (agreed_name, conflict, saw_const, saw_pad)
                    match arg.value() {
                        ExprValue::Var { name } => match canonical_slot_name(name) {
                            Some(base) => match &entry[k].0 {
                                Some(existing) if *existing != base => entry[k].1 = true,
                                Some(_) => {}
                                None => entry[k].0 = Some(base),
                            },
                            None => entry[k].3 = true,
                        },
                        _ => entry[k].2 = true,
                    }
                }
            };
        for rule in &vc.rules {
            observe(&rule.head, &mut acc);
            if let Some(ref br) = rule.body.relation {
                observe(br, &mut acc);
            }
        }
        for (name, positions) in acc {
            // Ensure name→position is injective; drop any name claimed by two
            // positions (demote both to Const) to avoid mis-placement.
            let mut seen: HashMap<String, usize> = HashMap::new();
            let mut conflicted: std::collections::HashSet<String> = Default::default();
            for (k, slot) in positions.iter().enumerate() {
                if let (Some(b), false) = (&slot.0, slot.1) {
                    if let Some(prev) = seen.insert(b.clone(), k) {
                        conflicted.insert(b.clone());
                        let _ = prev;
                    }
                }
            }
            let layout: Vec<CanonSlot> = positions
                .into_iter()
                .map(|(agreed, conflict, saw_const, saw_pad)| match agreed {
                    Some(b) if !conflict && !conflicted.contains(&b) => CanonSlot::Named(b),
                    _ if saw_const => CanonSlot::Const,
                    _ if saw_pad => CanonSlot::Pad,
                    _ => CanonSlot::Const,
                })
                .collect();
            canon.insert(name, layout);
        }
    }

    // Re-permute one divergent application against its canonical layout.
    //
    // Named arguments whose canonical position is known (an *anchor*) are placed
    // at that exact position — this is the re-permutation the sort-only fixup
    // cannot do. The remaining arguments (constants, and named slots that are
    // constant-folded in every conforming app, so their position is unknown) are
    // *fillers*: they are placed into the leftover holes in ascending canonical
    // order, sort-matched. Genuinely-absent slots become pads.
    fn realign(app: &RelationApp, layout: &[CanonSlot], decl: &[Sort]) -> Option<Vec<Expr>> {
        let mut name_to_pos: HashMap<&str, usize> = HashMap::new();
        for (k, slot) in layout.iter().enumerate() {
            if let CanonSlot::Named(b) = slot {
                name_to_pos.insert(b.as_str(), k);
            }
        }

        let mut out: Vec<Option<Expr>> = vec![None; layout.len()];
        let mut fillers: Vec<&Expr> = Vec::new();
        // First pass: place every anchor at its exact canonical position.
        for arg in app.args.iter() {
            let anchor_pos = match arg.value() {
                ExprValue::Var { name } => match canonical_slot_name(name) {
                    Some(base) => name_to_pos.get(base.as_str()).copied(),
                    None => {
                        // Pad filler — dropped, recreated below. Skip entirely.
                        continue;
                    }
                },
                _ => None,
            };
            match anchor_pos {
                Some(pos) => {
                    if out[pos].is_some() || arg.sort() != &decl[pos] {
                        return None;
                    }
                    out[pos] = Some(arg.clone());
                }
                None => fillers.push(arg),
            }
        }

        // Second pass: place fillers into the leftover holes, ascending position,
        // matching sort. A leftover filler means a value would be dropped.
        let mut hole = 0usize;
        for f in fillers {
            while hole < layout.len() && (out[hole].is_some() || &decl[hole] != f.sort()) {
                hole += 1;
            }
            if hole >= layout.len() {
                return None;
            }
            out[hole] = Some(f.clone());
            hole += 1;
        }

        // Pad every still-empty canonical position.
        for k in 0..layout.len() {
            if out[k].is_none() {
                out[k] = Some(pad(app.name.as_str(), k, &decl[k]));
            }
        }
        Some(out.into_iter().map(|o| o.expect("filled")).collect())
    }

    // Canonicalization pads use a dedicated prefix so they never collide with
    // the position-indexed `__pad_{rel}_{idx}` vars that an earlier
    // `fixup_relation_app_arities` may already have *declared with a different
    // sort* (the slot at index `idx` could have changed sort when columns were
    // pruned). `add_var` dedups by name and keeps the first declaration, so
    // reusing `__pad_*` here would bind our pad to a stale sort. `__cpad_*`
    // names are fresh, so each is declared with the correct sort below.
    fn pad(rel: &str, idx: usize, sort: &Sort) -> Expr {
        Expr::var(&format!("__cpad_{rel}_{idx}"), sort.clone())
    }

    let mut rewrote = false;
    let mut padded = false;
    for rule in &mut vc.rules {
        let mut fix = |app: &mut RelationApp| {
            let Some(decl) = rel_sorts.get(app.name.as_str()) else { return };
            if app_conforms(app) {
                return; // already canonical
            }
            let Some(layout) = canon.get(app.name.as_str()) else { return };
            if layout.len() != decl.len() {
                return;
            }
            if let Some(new_args) = realign(app, layout, decl) {
                *app = RelationApp::new(app.name.as_str(), new_args);
                rewrote = true;
                padded = true;
            }
        };
        fix(&mut rule.head);
        if let Some(ref mut br) = rule.body.relation {
            fix(br);
        }
    }

    // Declare the `__cpad_*` vars introduced above, each with its slot's
    // current declared sort (mirrors `fixup_relation_app_arities`'s pad-var
    // registration, but with the canonicalization-local prefix).
    if padded {
        use trust_mc_core::chc::VarDecl;
        let pad_vars: Vec<VarDecl> = vc
            .relations
            .iter()
            .flat_map(|rel| {
                rel.arg_sorts.iter().enumerate().map(move |(i, sort)| {
                    VarDecl::new(Arc::from(format!("__cpad_{}_{i}", rel.name)), sort.clone())
                })
            })
            .collect();
        for var in pad_vars {
            vc.add_var(var);
        }
    }
    if rewrote {
        tracing::debug!("canonicalize_block_relation_apps: re-permuted divergent relation apps");
    }
}

/// Part of #3685: Fix arity mismatches caused by late-created type arrays.
///
/// When `push_late_state_var_pair` creates a new type array during block
/// processing, the relation declarations and live sets are updated, but
/// rules emitted for earlier blocks still reference relations with the old
/// (shorter) arity. Z3 rejects these as "unknown constant" because the
/// relation application doesn't match the declared signature.
///
/// This pass walks all rules and pads relation applications to match their
/// declared arity. Padding variables are universally quantified (via
/// `declare-var`), meaning the late array is unconstrained in blocks that
/// predate its creation — which is the correct semantic (those blocks don't
/// touch the array).
pub(in crate::codegen_ay) fn fixup_relation_app_arities(vc: &mut trust_mc_core::chc::ChcVc) {
    use ay_bindings::{Expr, ExprFold, ExprValue, Sort, fold_expr, rebuild_with_children};
    use std::collections::HashMap;
    use std::sync::Arc;
    use trust_mc_core::chc::VarDecl;
    use trust_mc_core::constraints::Constraints;

    let rel_sorts: HashMap<&str, &[Sort]> =
        vc.relations.iter().map(|r| (r.name.as_str(), r.arg_sorts.as_slice())).collect();
    let rel_templates = collect_full_relation_templates(vc, &rel_sorts);

    let mut any_rewritten = false;
    let mut any_padded = false;

    for rule in &mut vc.rules {
        if let Some((new_args, used_padding)) = normalized_relation_args(
            rule.head.name.as_str(),
            (*rule.head.args).clone(),
            &rel_sorts,
            &rel_templates,
        ) {
            rule.head.args = Arc::new(new_args);
            any_rewritten = true;
            any_padded |= used_padding;
        }
        if let Some(ref mut body_rel) = rule.body.relation {
            if let Some((new_args, used_padding)) = normalized_relation_args(
                body_rel.name.as_str(),
                (*body_rel.args).clone(),
                &rel_sorts,
                &rel_templates,
            ) {
                body_rel.args = Arc::new(new_args);
                any_rewritten = true;
                any_padded |= used_padding;
            }
        }
        if rule.body.constraints.iter().any(|expr| expr_may_contain_relation_app(expr, &rel_sorts))
        {
            let mut folder = PadRelationExprs {
                rel_sorts: &rel_sorts,
                rel_templates: &rel_templates,
                any_rewritten: false,
                any_padded: false,
            };
            let rewritten_constraints: Vec<Expr> =
                rule.body.constraints.iter().map(|expr| fold_expr(&mut folder, expr)).collect();
            if folder.any_rewritten {
                any_rewritten = true;
                any_padded |= folder.any_padded;
                rule.body.constraints = Constraints::Owned(rewritten_constraints);
            }
        }
    }

    if any_padded {
        let pad_vars: Vec<VarDecl> = vc
            .relations
            .iter()
            .flat_map(|rel| {
                rel.arg_sorts.iter().enumerate().map(move |(i, sort)| {
                    VarDecl::new(Arc::from(format!("__pad_{}_{i}", rel.name)), sort.clone())
                })
            })
            .collect();
        for var in pad_vars {
            vc.add_var(var);
        }
    }
    if any_rewritten {
        tracing::debug!("fixup_relation_app_arities: normalized stale relation apps (#3685)");
    }

    fn normalized_relation_args(
        rel_name: &str,
        mut args: Vec<Expr>,
        rel_sorts: &HashMap<&str, &[Sort]>,
        rel_templates: &HashMap<String, Vec<Vec<Expr>>>,
    ) -> Option<(Vec<Expr>, bool)> {
        let decl_sorts = rel_sorts.get(rel_name)?;
        let current_len = args.len();
        let expected_len = decl_sorts.len();
        if current_len == expected_len {
            if args.iter().zip(decl_sorts.iter()).all(|(arg, decl_sort)| arg.sort() == decl_sort) {
                return None;
            }
            if let Some(aligned) =
                align_args_to_decl_sorts_with_padding(rel_name, &args, decl_sorts)
            {
                return Some((aligned, true));
            }
            return None;
        }
        if current_len > expected_len
            && let Some(trimmed) =
                trim_relation_args_to_decl(rel_name, &args, decl_sorts, rel_templates)
        {
            return Some((trimmed, false));
        }
        if current_len > expected_len
            && let Some((aligned, used_padding)) =
                align_args_to_decl_sorts_with_skips_and_padding(rel_name, &args, decl_sorts)
        {
            return Some((aligned, used_padding));
        }
        if current_len >= expected_len {
            return None;
        }
        if let Some(aligned) =
            align_args_to_full_template(rel_name, &args, decl_sorts, rel_templates)
        {
            return Some((aligned, true));
        }
        if let Some(aligned) = align_args_to_decl_sorts_with_padding(rel_name, &args, decl_sorts) {
            return Some((aligned, true));
        }
        let arg_sorts_match_prefix = args
            .iter()
            .map(Expr::sort)
            .zip(decl_sorts.iter())
            .all(|(arg_sort, decl_sort)| *arg_sort == *decl_sort);
        let arg_sorts_match_suffix = args
            .iter()
            .map(Expr::sort)
            .zip(decl_sorts[expected_len - current_len..].iter())
            .all(|(arg_sort, decl_sort)| *arg_sort == *decl_sort);
        if arg_sorts_match_suffix && !arg_sorts_match_prefix {
            let missing = expected_len - current_len;
            let mut padded = Vec::with_capacity(expected_len);
            for (idx, sort) in decl_sorts[..missing].iter().enumerate() {
                let var_name = format!("__pad_{rel_name}_{idx}");
                padded.push(Expr::var(&var_name, sort.clone()));
            }
            padded.append(&mut args);
            return Some((padded, true));
        }
        for (i, sort) in decl_sorts[current_len..].iter().enumerate() {
            let idx = current_len + i;
            let var_name = format!("__pad_{rel_name}_{idx}");
            args.push(Expr::var(&var_name, sort.clone()));
        }
        Some((args, true))
    }

    fn align_args_to_decl_sorts_with_padding(
        rel_name: &str,
        args: &[Expr],
        decl_sorts: &[Sort],
    ) -> Option<Vec<Expr>> {
        if args.len() > decl_sorts.len() {
            return None;
        }

        let mut aligned = Vec::with_capacity(decl_sorts.len());
        let mut arg_idx = 0usize;
        let mut inserted_pad = false;

        for (decl_idx, decl_sort) in decl_sorts.iter().enumerate() {
            if let Some(arg) = args.get(arg_idx)
                && arg.sort() == decl_sort
            {
                aligned.push(arg.clone());
                arg_idx += 1;
                continue;
            }

            aligned.push(pad_var(rel_name, decl_idx, decl_sort.clone()));
            inserted_pad = true;
        }

        if !inserted_pad {
            return None;
        }

        if args[arg_idx..].iter().all(|arg| is_generated_pad_arg(rel_name, arg)) {
            return Some(aligned);
        }

        None
    }

    fn align_args_to_decl_sorts_with_skips_and_padding(
        rel_name: &str,
        args: &[Expr],
        decl_sorts: &[Sort],
    ) -> Option<(Vec<Expr>, bool)> {
        if let Some(aligned) =
            align_args_to_decl_sorts_greedy_with_skips_and_padding(rel_name, args, decl_sorts)
        {
            return Some(aligned);
        }

        const SKIP_COST: usize = 1;
        const PAD_COST: usize = 16;
        const INF: usize = usize::MAX / 4;

        let arg_len = args.len();
        let decl_len = decl_sorts.len();
        let mut cost = vec![vec![INF; decl_len + 1]; arg_len + 1];
        cost[arg_len][decl_len] = 0;
        for i in (0..=arg_len).rev() {
            for j in (0..=decl_len).rev() {
                if i == arg_len && j == decl_len {
                    continue;
                }
                if i < arg_len {
                    cost[i][j] = cost[i][j].min(SKIP_COST.saturating_add(cost[i + 1][j]));
                }
                if j < decl_len {
                    cost[i][j] = cost[i][j].min(PAD_COST.saturating_add(cost[i][j + 1]));
                }
                if i < arg_len && j < decl_len && args[i].sort() == &decl_sorts[j] {
                    cost[i][j] = cost[i][j].min(cost[i + 1][j + 1]);
                }
            }
        }
        if cost[0][0] >= INF {
            return None;
        }

        let mut aligned = Vec::with_capacity(decl_len);
        let mut matched = 0usize;
        let mut padded = 0usize;
        let mut i = 0usize;
        let mut j = 0usize;
        while j < decl_len {
            if i < arg_len && args[i].sort() == &decl_sorts[j] && cost[i][j] == cost[i + 1][j + 1] {
                aligned.push(args[i].clone());
                matched += 1;
                i += 1;
                j += 1;
            } else if i < arg_len && cost[i][j] == SKIP_COST.saturating_add(cost[i + 1][j]) {
                i += 1;
            } else {
                aligned.push(pad_var(rel_name, j, decl_sorts[j].clone()));
                padded += 1;
                j += 1;
            }
        }

        if matched == 0 || aligned.len() != decl_len {
            return None;
        }
        let extra_args = arg_len.saturating_sub(decl_len);
        if padded > extra_args + 4 {
            return None;
        }
        Some((aligned, padded > 0))
    }

    fn align_args_to_decl_sorts_greedy_with_skips_and_padding(
        rel_name: &str,
        args: &[Expr],
        decl_sorts: &[Sort],
    ) -> Option<(Vec<Expr>, bool)> {
        let arg_len = args.len();
        let decl_len = decl_sorts.len();
        let mut aligned = Vec::with_capacity(decl_len);
        let mut matched = 0usize;
        let mut padded = 0usize;
        let mut arg_idx = 0usize;

        for decl_idx in 0..decl_len {
            loop {
                if arg_idx >= arg_len {
                    aligned.push(pad_var(rel_name, decl_idx, decl_sorts[decl_idx].clone()));
                    padded += 1;
                    break;
                }
                if args[arg_idx].sort() == &decl_sorts[decl_idx] {
                    aligned.push(args[arg_idx].clone());
                    matched += 1;
                    arg_idx += 1;
                    break;
                }
                if decl_idx + 1 < decl_len && args[arg_idx].sort() == &decl_sorts[decl_idx + 1] {
                    aligned.push(pad_var(rel_name, decl_idx, decl_sorts[decl_idx].clone()));
                    padded += 1;
                    break;
                }
                arg_idx += 1;
            }
        }

        if matched == 0 || aligned.len() != decl_len {
            return None;
        }
        let extra_args = arg_len.saturating_sub(decl_len);
        if padded > extra_args + 4 {
            return None;
        }
        Some((aligned, padded > 0))
    }

    fn is_generated_pad_arg(rel_name: &str, arg: &Expr) -> bool {
        let ExprValue::Var { name } = arg.value() else {
            return false;
        };
        let Some(rest) = name.strip_prefix("__pad_") else {
            return false;
        };
        let Some(index) = rest.strip_prefix(rel_name).and_then(|suffix| suffix.strip_prefix('_'))
        else {
            return false;
        };
        !index.is_empty() && index.bytes().all(|byte| byte.is_ascii_digit())
    }

    fn collect_full_relation_templates(
        vc: &trust_mc_core::chc::ChcVc,
        rel_sorts: &HashMap<&str, &[Sort]>,
    ) -> HashMap<String, Vec<Vec<Expr>>> {
        let mut templates = HashMap::new();
        for rule in &vc.rules {
            collect_relation_app_template(
                rule.head.name.as_str(),
                rule.head.args.as_ref(),
                rel_sorts,
                &mut templates,
            );
            if let Some(body_rel) = &rule.body.relation {
                collect_relation_app_template(
                    body_rel.name.as_str(),
                    body_rel.args.as_ref(),
                    rel_sorts,
                    &mut templates,
                );
            }
            let mut collector = CollectRelationTemplates { rel_sorts, templates: &mut templates };
            for expr in rule.body.constraints.iter() {
                if expr_may_contain_relation_app(expr, rel_sorts) {
                    let _ = fold_expr(&mut collector, expr);
                }
            }
        }
        templates
    }

    fn expr_may_contain_relation_app(expr: &Expr, rel_sorts: &HashMap<&str, &[Sort]>) -> bool {
        let mut stack = vec![expr];
        while let Some(node) = stack.pop() {
            if let ExprValue::FuncApp { name, .. } = node.value()
                && rel_sorts.contains_key(name.as_str())
            {
                return true;
            }
            stack.extend(node.children());
        }
        false
    }

    fn collect_relation_app_template(
        rel_name: &str,
        args: &[Expr],
        rel_sorts: &HashMap<&str, &[Sort]>,
        templates: &mut HashMap<String, Vec<Vec<Expr>>>,
    ) {
        let Some(decl_sorts) = rel_sorts.get(rel_name) else {
            return;
        };
        if !arg_sorts_match_decl(args, decl_sorts) {
            return;
        }
        let entry = templates.entry(rel_name.to_owned()).or_default();
        if !entry.iter().any(|existing| existing.as_slice() == args) {
            entry.push(args.to_vec());
        }
    }

    fn arg_sorts_match_decl(args: &[Expr], decl_sorts: &[Sort]) -> bool {
        args.len() == decl_sorts.len()
            && args.iter().zip(decl_sorts).all(|(arg, decl_sort)| arg.sort() == decl_sort)
    }

    fn trim_relation_args_to_decl(
        rel_name: &str,
        args: &[Expr],
        decl_sorts: &[Sort],
        rel_templates: &HashMap<String, Vec<Vec<Expr>>>,
    ) -> Option<Vec<Expr>> {
        let arg_len = args.len();
        let decl_len = decl_sorts.len();
        if arg_len <= decl_len {
            return None;
        }

        if let Some(templates) = rel_templates.get(rel_name) {
            for template in templates {
                if arg_sorts_match_decl(template, decl_sorts)
                    && args_contain_template_in_order(args, template)
                {
                    return Some(template.clone());
                }
            }
        }
        align_args_to_decl_sorts(args, decl_sorts)
    }

    fn align_args_to_decl_sorts(args: &[Expr], decl_sorts: &[Sort]) -> Option<Vec<Expr>> {
        let arg_len = args.len();
        let decl_len = decl_sorts.len();
        let mut can_match = vec![vec![false; decl_len + 1]; arg_len + 1];
        for row in &mut can_match {
            row[decl_len] = true;
        }
        for i in (0..arg_len).rev() {
            for j in (0..decl_len).rev() {
                can_match[i][j] = can_match[i + 1][j]
                    || (args[i].sort() == &decl_sorts[j] && can_match[i + 1][j + 1]);
            }
        }
        if !can_match[0][0] {
            return None;
        }

        let mut trimmed = Vec::with_capacity(decl_len);
        let mut i = 0;
        for (j, decl_sort) in decl_sorts.iter().enumerate() {
            while i < arg_len {
                if args[i].sort() == decl_sort && can_match[i + 1][j + 1] {
                    trimmed.push(args[i].clone());
                    i += 1;
                    break;
                }
                i += 1;
            }
        }
        (trimmed.len() == decl_len).then_some(trimmed)
    }

    fn align_args_to_full_template(
        rel_name: &str,
        args: &[Expr],
        decl_sorts: &[Sort],
        rel_templates: &HashMap<String, Vec<Vec<Expr>>>,
    ) -> Option<Vec<Expr>> {
        let templates = rel_templates.get(rel_name)?;
        templates
            .iter()
            .find_map(|template| align_args_to_template(rel_name, args, decl_sorts, template))
    }

    fn align_args_to_template(
        rel_name: &str,
        args: &[Expr],
        decl_sorts: &[Sort],
        template: &[Expr],
    ) -> Option<Vec<Expr>> {
        if !arg_sorts_match_decl(template, decl_sorts) || args.len() > template.len() {
            return None;
        }

        let arg_len = args.len();
        let template_len = template.len();
        let mut can_match = vec![vec![false; template_len + 1]; arg_len + 1];
        for slot in &mut can_match[arg_len] {
            *slot = true;
        }
        for i in (0..arg_len).rev() {
            for j in (0..template_len).rev() {
                can_match[i][j] =
                    can_match[i][j + 1] || (args[i] == template[j] && can_match[i + 1][j + 1]);
            }
        }
        if !can_match[0][0] {
            return None;
        }

        let mut matched: Vec<Option<Expr>> = vec![None; template_len];
        let mut j = 0;
        for i in 0..arg_len {
            while j < template_len {
                if args[i] == template[j] && can_match[i + 1][j + 1] {
                    matched[j] = Some(args[i].clone());
                    j += 1;
                    break;
                }
                j += 1;
            }
        }

        let mut aligned = Vec::with_capacity(template_len);
        for (idx, sort) in decl_sorts.iter().enumerate() {
            aligned
                .push(matched[idx].clone().unwrap_or_else(|| pad_var(rel_name, idx, sort.clone())));
        }
        Some(aligned)
    }

    fn args_contain_template_in_order(args: &[Expr], template: &[Expr]) -> bool {
        if template.len() > args.len() {
            return false;
        }
        let mut arg_idx = 0;
        for template_expr in template {
            while arg_idx < args.len() && &args[arg_idx] != template_expr {
                arg_idx += 1;
            }
            if arg_idx == args.len() {
                return false;
            }
            arg_idx += 1;
        }
        true
    }

    fn pad_var(rel_name: &str, idx: usize, sort: Sort) -> Expr {
        let var_name = format!("__pad_{rel_name}_{idx}");
        Expr::var(&var_name, sort)
    }

    struct CollectRelationTemplates<'a, 'b> {
        rel_sorts: &'a HashMap<&'b str, &'b [Sort]>,
        templates: &'a mut HashMap<String, Vec<Vec<Expr>>>,
    }

    impl ExprFold for CollectRelationTemplates<'_, '_> {
        fn fold_post(&mut self, original: &Expr, children: Vec<Expr>) -> Expr {
            if let ExprValue::FuncApp { name, .. } = original.value() {
                collect_relation_app_template(name, &children, self.rel_sorts, self.templates);
            }
            original.clone()
        }
    }

    struct PadRelationExprs<'a> {
        rel_sorts: &'a HashMap<&'a str, &'a [Sort]>,
        rel_templates: &'a HashMap<String, Vec<Vec<Expr>>>,
        any_rewritten: bool,
        any_padded: bool,
    }

    impl ExprFold for PadRelationExprs<'_> {
        fn fold_post(&mut self, original: &Expr, children: Vec<Expr>) -> Expr {
            if let ExprValue::FuncApp { name, .. } = original.value()
                && let Some((args, used_padding)) = normalized_relation_args(
                    name,
                    children.clone(),
                    self.rel_sorts,
                    self.rel_templates,
                )
            {
                self.any_rewritten = true;
                self.any_padded |= used_padding;
                return Expr::func_app_with_sort(name.clone(), args, original.sort().clone());
            }
            rebuild_with_children(original, children)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::fixup_relation_app_arities;
    use ay_bindings::{Expr, ExprValue, Sort};
    use trust_mc_core::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody};

    #[test]
    fn fixup_pads_relation_apps_embedded_in_constraints() {
        let arr_sort = Sort::array(Sort::bv32(), Sort::bool());
        let state = Expr::var("state", Sort::bv64());
        let stale_body_rel = Expr::func_app("bb1", vec![state.clone()]);

        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("bb1", vec![Sort::bv64(), arr_sort.clone()]));
        vc.add_relation(RelationDecl::new("bb2", vec![Sort::bv64(), arr_sort.clone()]));
        vc.add_rule(Rule::new(
            RuleBody::new(None, vec![stale_body_rel]),
            RelationApp::new("bb2", vec![state, Expr::var("arr__out", arr_sort.clone())]),
        ));

        fixup_relation_app_arities(&mut vc);

        let constraint = vc.rules[0].body.constraints.iter().next().expect("constraint");
        match constraint.value() {
            ExprValue::FuncApp { name, args } => {
                assert_eq!(name, "bb1");
                assert_eq!(
                    args.len(),
                    2,
                    "embedded relation app should be padded to declaration arity"
                );
                assert!(
                    matches!(args[1].value(), ExprValue::Var { name } if name == "__pad_bb1_1"),
                    "expected pad variable for late-added array arg, got {:?}",
                    args[1]
                );
            }
            other => panic!("expected embedded relation app, got {other:?}"),
        }
        assert!(
            vc.vars().iter().any(|var| var.name.as_ref() == "__pad_bb1_1"),
            "pad variable should be declared for rebuilt constraint relation apps"
        );
    }

    #[test]
    fn fixup_trims_overlong_relation_apps_embedded_in_constraints() {
        let mem_sort = Sort::array(Sort::bv64(), Sort::bv32());
        let state = Expr::var("state", Sort::bv64());
        let flag = Expr::var("flag", Sort::bool());
        let extra_ptr = Expr::var("extra_ptr", Sort::bv64());
        let extra_nonnull = Expr::var("extra_nonnull", Sort::bv64());
        let extra_valid = Expr::var("extra_valid", Sort::bool());
        let mem = Expr::var("mem", mem_sort.clone());
        let overlong_body_rel = Expr::func_app(
            "bb1",
            vec![state.clone(), flag.clone(), extra_ptr, extra_nonnull, extra_valid, mem.clone()],
        );

        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new(
            "bb1",
            vec![Sort::bv64(), Sort::bool(), mem_sort.clone()],
        ));
        vc.add_relation(RelationDecl::nullary("bb2"));
        vc.add_rule(Rule::new(
            RuleBody::new(None, vec![overlong_body_rel]),
            RelationApp::nullary("bb2"),
        ));

        fixup_relation_app_arities(&mut vc);

        let constraint = vc.rules[0].body.constraints.iter().next().expect("constraint");
        match constraint.value() {
            ExprValue::FuncApp { name, args } => {
                assert_eq!(name, "bb1");
                assert_eq!(
                    args.len(),
                    3,
                    "embedded overlong relation app should be trimmed to declaration arity"
                );
                assert_eq!(args[0], state);
                assert_eq!(args[1], flag);
                assert_eq!(args[2], mem);
            }
            other => panic!("expected embedded relation app, got {other:?}"),
        }
    }

    #[test]
    fn fixup_aligns_overlong_embedded_apps_with_missing_middle_slots() {
        let flag0 = Expr::var("flag0", Sort::bool());
        let ptr1 = Expr::var("ptr1", Sort::bv64());
        let ptr3 = Expr::var("ptr3", Sort::bv64());
        let extra0 = Expr::var("extra0", Sort::bool());
        let extra1 = Expr::var("extra1", Sort::bool());
        let stale_body_rel =
            Expr::func_app("bb1", vec![flag0.clone(), ptr1.clone(), ptr3.clone(), extra0, extra1]);

        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new(
            "bb1",
            vec![Sort::bool(), Sort::bv64(), Sort::bool(), Sort::bv64()],
        ));
        vc.add_relation(RelationDecl::nullary("bb2"));
        vc.add_rule(Rule::new(
            RuleBody::new(None, vec![stale_body_rel]),
            RelationApp::nullary("bb2"),
        ));

        fixup_relation_app_arities(&mut vc);

        let constraint = vc.rules[0].body.constraints.iter().next().expect("constraint");
        match constraint.value() {
            ExprValue::FuncApp { name, args } => {
                assert_eq!(name, "bb1");
                assert_eq!(args.len(), 4);
                assert_eq!(args[0], flag0);
                assert_eq!(args[1], ptr1);
                assert!(
                    matches!(args[2].value(), ExprValue::Var { name } if name == "__pad_bb1_2"),
                    "missing middle slot should receive a pad var, got {:?}",
                    args[2]
                );
                assert_eq!(args[3], ptr3);
            }
            other => panic!("expected embedded relation app, got {other:?}"),
        }
    }

    #[test]
    fn fixup_front_pads_suffix_only_relation_apps() {
        let valid_sort = Sort::array(Sort::bv32(), Sort::bool());
        let size_sort = Sort::array(Sort::bv32(), Sort::bv32());
        let obj_size = Expr::var("obj_size", size_sort.clone());

        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new(
            "bb18",
            vec![Sort::bv64(), valid_sort.clone(), size_sort.clone()],
        ));
        vc.add_relation(RelationDecl::new("bb7", vec![size_sort.clone()]));
        vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::new("bb18", vec![obj_size.clone()])), vec![]),
            RelationApp::new("bb7", vec![obj_size.clone()]),
        ));

        fixup_relation_app_arities(&mut vc);

        let body_rel = vc.rules[0].body.relation.as_ref().expect("body relation");
        assert_eq!(body_rel.args.len(), 3, "body relation should match declared arity");
        assert!(
            matches!(body_rel.args[0].value(), ExprValue::Var { name } if name == "__pad_bb18_0"),
            "suffix-only app should pad missing leading slots"
        );
        assert!(
            matches!(body_rel.args[1].value(), ExprValue::Var { name } if name == "__pad_bb18_1"),
            "suffix-only app should pad all missing leading slots"
        );
        assert_eq!(
            body_rel.args[2], obj_size,
            "suffix-aligned live arg should remain in the trailing position"
        );
    }

    #[test]
    fn fixup_aligns_sparse_stale_apps_to_full_relation_template() {
        let size_sort = Sort::array(Sort::bv32(), Sort::bv32());
        let first_iter_field = Expr::var("_check_position_invariant_6_fld1", Sort::bv32());
        let second_iter_field = Expr::var("_check_position_invariant_14_fld1", Sort::bv32());
        let obj_size = Expr::var("obj_size", size_sort.clone());
        let full_args = vec![
            first_iter_field.clone(),
            Expr::bitvec_const(5u128, 32),
            Expr::bool_const(false),
            Expr::bitvec_const(4u128, 32),
            Expr::bitvec_const(0u128, 64),
            Expr::bool_const(false),
            second_iter_field.clone(),
            Expr::bitvec_const(0x0000_0006_0000_0000u128, 64),
            Expr::bool_const(true),
            Expr::bool_const(false),
            Expr::bool_const(true),
            Expr::bitvec_const(0x0000_000f_0000_0000u128, 64),
            obj_size.clone(),
        ];
        let full_sorts = full_args.iter().map(|arg| arg.sort().clone()).collect::<Vec<_>>();

        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("bb10", full_sorts));
        vc.add_relation(RelationDecl::nullary("bb11"));
        vc.add_rule(Rule::init(Expr::bool_const(true), RelationApp::new("bb10", full_args)));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new(
                    "bb10",
                    vec![first_iter_field.clone(), second_iter_field.clone(), obj_size.clone()],
                )),
                vec![],
            ),
            RelationApp::nullary("bb11"),
        ));

        fixup_relation_app_arities(&mut vc);

        let body_rel = vc.rules[1].body.relation.as_ref().expect("body relation");
        assert_eq!(
            body_rel.args.len(),
            13,
            "sparse stale app should be padded to the declared arity"
        );
        assert_eq!(
            body_rel.args[0], first_iter_field,
            "first live arg should stay in its full-template slot"
        );
        assert_eq!(
            body_rel.args[6], second_iter_field,
            "middle live arg should align to its full-template slot"
        );
        assert_eq!(
            body_rel.args[12], obj_size,
            "trailing array arg should align to its full-template slot"
        );
        assert!(
            matches!(body_rel.args[2].value(), ExprValue::Var { name } if name == "__pad_bb10_2"),
            "missing slots should be filled with declared pad vars"
        );
    }

    #[test]
    fn fixup_inserts_missing_middle_slot_for_sort_mismatched_relation_app() {
        let first = Expr::var("first", Sort::bv32());
        let second = Expr::var("second", Sort::bv32());
        let third = Expr::var("third", Sort::bv32());
        let stale_trailing_pad = Expr::var("__pad_bb5_3", Sort::bv32());

        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("bb5", vec![Sort::bv32(), Sort::bv64(), Sort::bv32()]));
        vc.add_relation(RelationDecl::new("bb6", vec![Sort::bv32()]));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new(
                    "bb5",
                    vec![first.clone(), second.clone(), stale_trailing_pad],
                )),
                vec![],
            ),
            RelationApp::new("bb6", vec![third]),
        ));

        fixup_relation_app_arities(&mut vc);

        let body_rel = vc.rules[0].body.relation.as_ref().expect("body relation");
        assert_eq!(body_rel.args.len(), 3, "body relation should keep declared arity");
        assert_eq!(body_rel.args[0], first);
        assert!(
            matches!(body_rel.args[1].value(), ExprValue::Var { name } if name == "__pad_bb5_1"),
            "missing middle BV64 slot should receive the pad var, got {:?}",
            body_rel.args[1]
        );
        assert_eq!(body_rel.args[2], second);
    }

    #[test]
    fn fixup_trims_overlong_relation_apps_after_prune() {
        let mem_sort = Sort::array(Sort::bv64(), Sort::bv32());

        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new(
            "bb17",
            vec![Sort::bv64(), Sort::bool(), mem_sort.clone()],
        ));
        vc.add_relation(RelationDecl::new(
            "bb18",
            vec![Sort::bv64(), Sort::bool(), mem_sort.clone()],
        ));

        let state = Expr::var("state", Sort::bv64());
        let flag = Expr::var("flag", Sort::bool());
        let extra_ptr = Expr::var("extra_ptr", Sort::bv64());
        let extra_nonnull = Expr::var("extra_nonnull", Sort::bv64());
        let extra_valid = Expr::var("extra_valid", Sort::bool());
        let mem = Expr::var("mem", mem_sort.clone());

        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("bb17", vec![state.clone(), flag.clone(), mem.clone()])),
                vec![],
            ),
            RelationApp::new(
                "bb18",
                vec![state, flag, extra_ptr, extra_nonnull, extra_valid, mem.clone()],
            ),
        ));

        fixup_relation_app_arities(&mut vc);

        let head_args = &vc.rules[0].head.args;
        assert_eq!(head_args.len(), 3, "overlong head app should be trimmed to declaration arity");
        assert!(
            matches!(head_args[0].value(), ExprValue::Var { name } if name == "state"),
            "first arg should preserve the original state slot"
        );
        assert!(
            matches!(head_args[1].value(), ExprValue::Var { name } if name == "flag"),
            "second arg should preserve the original flag slot"
        );
        assert!(
            matches!(head_args[2].value(), ExprValue::Var { name } if name == "mem"),
            "final arg should preserve the original memory slot after trimming extras"
        );
    }
}
