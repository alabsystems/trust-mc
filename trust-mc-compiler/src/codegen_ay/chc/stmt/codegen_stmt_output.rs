// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Output arg building and MIR-to-CHC entry point.
//!
//! Helpers extracted from codegen_stmt.rs per #2246:
//! - `mark_modified_for_unsupported_rvalue`: nondet fallback for unsupported rvalues
//! - `build_block_output_args`: output arg construction from modified locals set
//! - `mir_to_chc`: public entry point for MIR -> CHC translation
//!
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::Expr;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, Place};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::sync::atomic::Ordering;
use tracing::{debug, warn};
use trust_mc_core::chc::ChcVc;

use crate::args::{ChcStepMode, ChcTrackLevel};
use crate::codegen_ay::loop_unroll::{Cfg, find_loop_headers};

use super::{CHC_DEBUG_FLAG, ChcCtx, ChcDebugMode};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Mark a local as modified when its rvalue translation fails.
    ///
    /// This implements the nondet fallback (#756, #767): when we can't translate an rvalue,
    /// the target local becomes unconstrained (nondet) rather than retaining stale constraints.
    ///
    /// For projected places (e.g., `*_1`, `_1.field`, `_1[i]`), we mark the root local as
    /// modified, making the entire aggregate nondet. This is an over-approximation but sound -
    /// we can't track partial modifications without full projection support.
    pub(in crate::codegen_ay::chc) fn mark_modified_for_unsupported_rvalue(
        lhs: &Place,
        modified: &mut HashSet<usize>,
    ) -> bool {
        // Always mark the root local, regardless of projections (#767)
        // For `_1 = ...`: marks _1 directly
        // For `*_1`, `_1.f`, `_1[i]`: marks _1 (whole aggregate becomes nondet)
        let local_idx: usize = lhs.local;
        modified.insert(local_idx);
        true
    }

    /// Emit a self-loop constraint (`output_var = input_var`) for a single
    /// (non-flattened) local. Part of #3038: constraint-or-unchanged invariant.
    ///
    /// When a local is marked modified but the codegen cannot produce a real
    /// constraint, this preserves the previous value instead of leaving the
    /// output variable unconstrained (which would let the solver pick any
    /// value, causing spurious CTREX).
    ///
    /// Returns `true` if the constraint was emitted.
    pub(in crate::codegen_ay::chc) fn emit_self_loop_constraint(
        &self,
        local_idx: usize,
        acc: &mut super::stmt_accumulator::StmtAccumulator<'_>,
    ) -> bool {
        let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
            return false;
        };
        let (Some((in_name, in_sort)), Some((out_name, out_sort))) = (
            self.state_var_mgr.state_vars.get(vec_idx).cloned(),
            self.state_var_mgr.output_state_vars.get(vec_idx).cloned(),
        ) else {
            return false;
        };
        let in_var = Expr::var(&*in_name, in_sort);
        let out_var = Expr::var(&*out_name, out_sort);
        acc.replace_constraint(local_idx, out_var.eq(in_var));
        true
    }

    /// Emit self-loop constraints for all N scalar state vars of a flattened
    /// local. Part of #3038: constraint-or-unchanged invariant for flattened
    /// locals (Option, Result, checked-op tuples, etc.).
    ///
    /// Each field state var at `vec_idx + i` gets `fldK_out = fldK_in`.
    /// Uses the same field-key scheme as `constrain_flattened_fields_core`:
    /// fld0 uses `local_idx`, fldN uses `local_idx + N * locals_len`.
    ///
    /// Returns the number of field constraints emitted.
    pub(in crate::codegen_ay::chc) fn emit_flattened_self_loop_constraints(
        &self,
        local_idx: usize,
        acc: &mut super::stmt_accumulator::StmtAccumulator<'_>,
    ) -> usize {
        let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
            return 0;
        };
        let field_count = self.flattened_field_count(local_idx);
        let locals_len = self.body.locals().len();
        let mut emitted = 0;

        for i in 0..field_count {
            let fld_key = if i == 0 { local_idx } else { local_idx + i * locals_len };
            let (Some((in_name, in_sort)), Some((out_name, out_sort))) = (
                self.state_var_mgr.state_vars.get(vec_idx + i).cloned(),
                self.state_var_mgr.output_state_vars.get(vec_idx + i).cloned(),
            ) else {
                continue;
            };
            let in_var = Expr::var(&*in_name, in_sort);
            let out_var = Expr::var(&*out_name, out_sort);
            acc.replace_constraint(fld_key, out_var.eq(in_var));
            emitted += 1;
        }
        emitted
    }

    /// Build output args from the set of modified locals.
    ///
    /// For modified locals, uses the OUTPUT state variable; for unmodified, uses INPUT.
    /// Non-local state (heap arrays, metadata, collection lengths) is propagated via
    /// the centralized `modified_state_indices` set.
    ///
    /// Part of #2214: Expands the modified set to include all state_var indices for
    /// flattened locals. `modified` stores MIR local indices, but flattened locals
    /// occupy N consecutive state_var slots (fld0..fldN-1).
    ///
    /// Part of #3348: When `last_constraint_for_local` is provided, uses per-field
    /// granularity for flattened locals — only fields with actual constraints get
    /// OUTPUT vars; unconstrained fields use INPUT vars (automatic carry-forward).
    /// This prevents nondeterministic output vars when a store handler partially
    /// constrains a struct-embedded Vec (e.g., store to `m.data` without
    /// constraining `m.indices` fields).
    pub(in crate::codegen_ay::chc) fn build_block_output_args(
        &self,
        modified: &HashSet<usize>,
        last_constraint_for_local: Option<&HashMap<usize, usize>>,
    ) -> Vec<Expr> {
        // Map modified MIR locals to state-vector indices. Flattened locals consume
        // multiple consecutive slots; non-flattened locals still need local->vec mapping.
        let mut modified_vec_indices: HashSet<usize> = HashSet::new();
        let locals_len = self.body.locals().len();
        for &local_idx in modified {
            let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
                continue;
            };
            modified_vec_indices.insert(vec_idx);

            if self.flatten.flattened_tuple_locals.contains(&local_idx) {
                let n = self.flattened_field_count(local_idx);
                if let Some(lcfl) = last_constraint_for_local {
                    // Per-field granularity: only add fields with actual constraints.
                    for i in 0..n {
                        let fld_key = if i == 0 { local_idx } else { local_idx + i * locals_len };
                        if lcfl.contains_key(&fld_key) {
                            modified_vec_indices.insert(vec_idx + i);
                        }
                    }
                } else {
                    // No per-field info: add all fields (legacy behavior).
                    for i in 0..n {
                        modified_vec_indices.insert(vec_idx + i);
                    }
                }
            }
        }
        self.state_var_mgr
            .state_vars
            .iter()
            .enumerate()
            .map(|(idx, (in_name, in_sort))| {
                // Check if this is a modified local variable.
                // Output slot missing (truncated by fallback path) → fall through.
                if modified_vec_indices.contains(&idx)
                    && let Some((out_name, out_sort)) =
                        self.state_var_mgr.output_state_vars.get(idx)
                {
                    return Expr::var(&**out_name, out_sort.clone());
                }

                // Part of #2552: Check centralized modified state index set.
                // This catches region arrays, type-indexed arrays, metadata arrays,
                // and any other state variable recorded via mark_state_var_modified.
                if self.encode.modified_state_indices.contains(&idx)
                    && let Some((out_name, out_sort)) =
                        self.state_var_mgr.output_state_vars.get(idx)
                {
                    return Expr::var(&**out_name, out_sort.clone());
                }

                Expr::var(&**in_name, in_sort.clone())
            })
            .collect()
    }
}

/// Translates a MIR body to a CHC verification condition.
///
/// This is the main entry point for external callers.
///
/// # Arguments
/// * `tcx` - The Rust compiler type context
/// * `body` - The MIR body to translate
/// * `fn_name` - The function name (for generating unique relation names)
///
/// # Returns
/// A `ChcVc` representing the verification condition in CHC form.
///
/// REQUIRES: `tcx` is the type context that produced `body`.
/// REQUIRES: `body` is a valid MIR body for a single function.
/// REQUIRES: `fn_name` uniquely identifies the function for relation naming.
/// ENSURES: Result declares one relation per basic block plus `error`.
/// ENSURES: Result query targets the `error` relation.
/// ENSURES: Result declares input/output state variables.
#[cfg_attr(not(test), allow(dead_code))]
pub(in crate::codegen_ay) fn mir_to_chc<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body,
    fn_name: impl Into<Arc<str>>,
    cfg: super::ChcConfig,
) -> ChcVc {
    mir_to_chc_internal(tcx, body, None, fn_name, cfg)
}

pub(in crate::codegen_ay) fn mir_to_chc_with_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body,
    instance: Instance,
    fn_name: impl Into<Arc<str>>,
    cfg: super::ChcConfig,
) -> ChcVc {
    mir_to_chc_internal(tcx, body, Some(instance), fn_name, cfg)
}

/// Accept a frame-narrowed VC only if it is well-formed; otherwise re-encode with
/// the full frame.
///
/// Frame narrowing (`ChcConfig::frame_narrowing`) drops backward-dead columns from
/// block relations, which is where the query-size win comes from. But it decides
/// deadness at DECL time from MIR source-operand liveness, and the encoder reads
/// state through channels MIR cannot see — `ref_targets` deref chains with
/// projections, `subslice_len`/`const_ref_values` sidecars replayed blocks later,
/// obj-id resolution via `known_alloc_ids`, `local_expr_env` cross-block
/// expression replay, and float congruent-table keys that embed operand columns.
/// When that happens the dropped column does not fail loudly: `declare-var` is
/// emitted for every state var, so it becomes a universally quantified FREE
/// variable and its constraints turn trivially satisfiable — a spurious
/// counterexample. Measured unguarded: 50 tests moved parity -> false_positive.
///
/// So the narrowing is treated as a speculative optimization, and the ORDER is
/// full frame first: the full-frame VC is the one that is always encoded, and the
/// narrowed one is attempted afterwards and kept only if it survives every guard
/// below. That ordering is what makes the fallback free — the full VC is already
/// in hand, so rejecting a narrowed encode costs no third translate — and it is
/// what lets GUARD 1 observe whether the full VC was straight-line discharged,
/// which is not predictable from MIR.
fn narrow_or_reencode<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body,
    current_instance: Option<Instance>,
    fn_name: &Arc<str>,
    cfg: super::ChcConfig,
    full_vc: ChcVc,
) -> ChcVc {
    if !cfg.frame_narrowing {
        return full_vc;
    }

    // GUARD 1 — never narrow a VC the straight-line discharge already proved.
    //
    // This is the whole of the recorded tail risk, and it is not the solver's
    // doing. Measured on `expected/loop-backedge/test.rs`: the full-frame VC is
    // discharged syntactically in 0.002 s; narrowing removes 772 of 9,499
    // columns (8%) and the discharge then bails, the VC goes to ay, and ay
    // returns `unknown` after 38 s — a SUCCESSFUL half-second harness turned
    // into a 44 s FAILED one for an 8% frame reduction. `prusti/Selection_sort.rs`
    // and `bounded-arbitrary/hash.rs` behave the same way.
    //
    // The reason is structural, not incidental. The discharge works by
    // enumerating CONCRETE relation frames, so it needs every column whose value
    // it must know; a narrowed column is exactly a column whose value the
    // enumeration no longer receives, and it turns the enumerated term symbolic.
    // Narrowing therefore cannot help this class — a discharged VC never reaches
    // the solver, so its frame width costs nothing — and can only take the proof
    // away. Deciding it AFTER the full translate is what makes the guard exact:
    // `trivially_safe_discharged` is an observation of the emitted VC, not a
    // prediction from MIR.
    if full_vc.trivially_safe_discharged {
        debug!(
            fn_name = %fn_name,
            "CHC: frame narrowing skipped — full-frame VC discharged syntactically"
        );
        return full_vc;
    }

    // GUARD 2 — width threshold.
    //
    // Narrowing pays for itself only through solver latency, and latency tracks
    // frame WIDTH: measured median relation arity is 16-19 on fast-parity
    // harnesses against 28/39/57 on the slow unknown ones. Below the threshold
    // the second translate below costs more than the columns it could remove.
    let max_arity = full_vc.relations.iter().map(|r| r.arg_sorts.len()).max().unwrap_or(0);
    if max_arity < MIN_ARITY_TO_NARROW {
        debug!(
            fn_name = %fn_name,
            max_arity,
            "CHC: frame narrowing skipped — frames already narrow"
        );
        return full_vc;
    }

    // Speculative narrowed encode. `reset` must sit immediately before it: the
    // validator compares against the columns THIS translate dropped.
    crate::codegen_ay::chc::reset_dropped_frame_columns();
    let ctx = if let Some(instance) = current_instance {
        ChcCtx::new_with_instance(tcx, body, instance, Arc::clone(fn_name), cfg)
    } else {
        ChcCtx::new(tcx, body, Arc::clone(fn_name), cfg)
    };
    let (narrow_vc, _) = ctx.translate();

    // GUARD 3 — free-variable validator on the EMITTED VC.
    let dropped = crate::codegen_ay::chc::take_dropped_frame_columns();
    let offenders =
        crate::codegen_ay::chc::constraint_vars_outside_relation_frames(&narrow_vc, &dropped);
    if !offenders.is_empty() {
        warn!(
            fn_name = %fn_name,
            offenders = offenders.len(),
            first = %offenders.first().map(String::as_str).unwrap_or(""),
            "CHC: frame narrowing dropped a column the encoding still reads; \
             keeping the full frame"
        );
        return full_vc;
    }

    // Accepted. Note what the guards leave: `full_vc` was NOT discharged (guard
    // 1), so this VC was always going to the solver, and a narrower frame there
    // is the only thing narrowing was ever for. If the narrowed VC now happens to
    // discharge, that is a strict improvement — the straight-line prover fails
    // closed on every symbolic shape a dropped column can produce, so it cannot
    // be talked into a proof by the narrowing.
    debug!(
        fn_name = %fn_name,
        dropped = dropped.len(),
        "CHC: frame narrowing accepted"
    );
    narrow_vc
}

/// Widest relation a VC must have before frame narrowing is attempted at all.
///
/// See GUARD 2 in [`narrow_or_reencode`].
const MIN_ARITY_TO_NARROW: usize = 24;

fn mir_to_chc_internal<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body,
    current_instance: Option<Instance>,
    fn_name: impl Into<Arc<str>>,
    cfg: super::ChcConfig,
) -> ChcVc {
    CHC_DEBUG_FLAG.store(cfg.chc_debug == ChcDebugMode::On, Ordering::Relaxed);
    let fn_name_str: Arc<str> = fn_name.into();

    // Part of #112: resolve Auto step mode per function.
    // Functions with loops benefit from large-step encoding (fewer predicates).
    // Acyclic functions use small-step (no benefit from fragment analysis).
    let effective_step_mode = match cfg.step_mode {
        ChcStepMode::Auto => {
            let body_cfg = Cfg::from_body(body);
            let has_loops = find_loop_headers(&body_cfg).map_or(false, |h| !h.is_empty());
            let resolved = if has_loops { ChcStepMode::Large } else { ChcStepMode::Small };
            debug!(
                fn_name = %fn_name_str,
                has_loops,
                ?resolved,
                "CHC: auto-detected step mode"
            );
            resolved
        }
        other => other,
    };

    crate::codegen_ay::chc::reset_dropped_frame_columns();
    let resolved_cfg = super::ChcConfig { step_mode: effective_step_mode, ..cfg };
    // The FIRST translate is always full-frame. Narrowing is attempted only
    // afterwards, by `narrow_or_reencode`, against this VC — see its GUARD 1.
    let full_cfg = super::ChcConfig {
        frame_narrowing: false,
        frame_narrowing_flattened: false,
        ..resolved_cfg
    };
    let ctx = if let Some(instance) = current_instance {
        ChcCtx::new_with_instance(tcx, body, instance, fn_name_str.clone(), full_cfg)
    } else {
        ChcCtx::new(tcx, body, fn_name_str.clone(), full_cfg)
    };
    let (vc, action) = ctx.translate();

    // Auto-promote to Mem level when Ref/AddressOf with projections was detected
    // at a lower track level (Part of #2084).
    // Part of #112 Direction 2: Suppress auto-promote when int-lift is active.
    // Int-lift intentionally downgrades to Reg for PDR invariant synthesis;
    // promoting back to Mem would reintroduce Array-sorted state vars that
    // prevent PDR from synthesizing invariants.
    if action == super::MemPromoteAction::Promote
        && cfg.track_level < ChcTrackLevel::Mem
        && !cfg.int_lift
    {
        warn!(
            fn_name = %fn_name_str,
            from = ?cfg.track_level,
            to = ?ChcTrackLevel::Mem,
            "CHC: auto-promoting track level due to projected Ref/AddressOf"
        );
        let promoted_cfg = super::ChcConfig {
            track_level: ChcTrackLevel::Mem,
            step_mode: effective_step_mode,
            ..cfg
        };
        let promoted_full_cfg = super::ChcConfig {
            frame_narrowing: false,
            frame_narrowing_flattened: false,
            ..promoted_cfg
        };
        let fn_name_str_retry: Arc<str> = Arc::clone(&fn_name_str);
        let ctx = if let Some(instance) = current_instance {
            ChcCtx::new_with_instance(tcx, body, instance, fn_name_str, promoted_full_cfg)
        } else {
            ChcCtx::new(tcx, body, fn_name_str, promoted_full_cfg)
        };
        let (vc, _) = ctx.translate();
        return narrow_or_reencode(
            tcx,
            body,
            current_instance,
            &fn_name_str_retry,
            promoted_cfg,
            vc,
        );
    }

    narrow_or_reencode(tcx, body, current_instance, &fn_name_str, resolved_cfg, vc)
}

/// Like `mir_to_chc`, but stops before Template-Directed Inductive Checking (TIC).
///
/// Tests verifying linearization artifacts need this because TIC detects the
/// same patterns and replaces the VC with a trivially safe system, clearing
/// all rules that linearization produced.
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay) fn mir_to_chc_skip_tic<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body,
    fn_name: impl Into<Arc<str>>,
    cfg: super::ChcConfig,
) -> ChcVc {
    CHC_DEBUG_FLAG.store(cfg.chc_debug == ChcDebugMode::On, Ordering::Relaxed);
    let fn_name_str: Arc<str> = fn_name.into();
    let effective_step_mode = match cfg.step_mode {
        ChcStepMode::Auto => {
            let body_cfg = Cfg::from_body(body);
            let has_loops = find_loop_headers(&body_cfg).map_or(false, |h| !h.is_empty());
            if has_loops { ChcStepMode::Large } else { ChcStepMode::Small }
        }
        other => other,
    };
    let resolved_cfg = super::ChcConfig { step_mode: effective_step_mode, ..cfg };
    let ctx = ChcCtx::new(tcx, body, fn_name_str, resolved_cfg);
    let (vc, _action) = ctx.translate_skip_tic();
    vc
}
