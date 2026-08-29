// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! #47: the REAL loop-contract proof rule (Kani/CBMC-style base + inductive
//! step + post), applied at the MIR layer.
//!
//! Before this module, `#[kani::loop_invariant]` emitted NO proof obligation:
//! the invariant value computed at the (transformed) latch fed the loop-guard
//! `SwitchInt`, so a false invariant silently EXITED the loop (an extra exit
//! condition — a latent fail-open), and the loop stayed a concrete cyclic CHC
//! system the solver had to crack unaided.
//!
//! This module rewrites every invariant-transformed loop (an entry of
//! `new_loop_latches`) into the standard inductive rule, making the loop
//! ACYCLIC:
//!
//! ```text
//! head:     loop_head_stmts (closure construction); _v = true
//!           _ = kani_register_loop_contract(&closure, 2)    // breadcrumb (body = `true`)
//!           _v = <closure Fn shim>(&closure, ())            // eval inv on entry state
//! base_sw:  switch(_v) [false -> base_fail, true -> havoc]  // 1. BASE
//! base_fail: safety_check(false, "base")                    //    (assert+assume false)
//! havoc:    l_i = any_modifies::<T_i>()  for every loop-modified l_i  // 2. HAVOC
//!           _v = <closure Fn shim>(&closure, ())            // eval inv on havocked state
//! asm_sw:   switch(_v) [false -> sink, true -> tail]        //    assume(inv)
//! tail:     _v = true; [old = <measure src>]; goto -> guard switch  // ONE iteration / post
//! ...
//! latch:    _v = kani_register_loop_contract(&closure, 1)   // breadcrumb (body = `true`)
//!           _v = <closure Fn shim>(&closure, ())            // eval inv after one body iter
//! step_sw:  switch(_v) [false -> step_fail, true -> sink]   // 3. STEP + CUT
//! step_fail: safety_check(false, "inductive step")
//! sink:     kani::assume(false) -> loop_termination         // dead forward edge (acyclic)
//! ```
//!
//! The register calls survive only as breadcrumbs: their body is literally
//! `{ true }` (and the CHC inline lane consumes the raw body), so the actual
//! invariant expression is evaluated by calling the closure's `Fn::call` shim
//! directly — the same well-tested closure-inline lane every closure call
//! takes. Every evaluation writes the ORIGINAL register destination `_v` and
//! is immediately consumed by a `SwitchInt(_v)`, keeping `_v` in the relation
//! signatures (fresh cross-block temporaries get liveness-pruned and their
//! constraints sanitized away — the decreases guard-7 "undeclared-mid" trap).
//!
//! The post-condition path needs no extra code: `switch` is now reached only
//! from the havocked head state with `inv` assumed, so the loop-exit edge
//! carries exactly `inv && !guard`.
//!
//! The invariant is evaluated as a REAL expression at all three sites by
//! cloning the existing latch register call (same closure operand); CHC
//! codegen already inlines that closure (`codegen_call_kani_model.rs`
//! `RunLoopContract` lane) and the BMC lane inlines the swapped register body.
//! The `_transformed` argument is set to 2/3 for the new sites so `transform_bb`
//! never re-transforms them (it only fires on 0); FC-29's loop-assigns
//! fallback (`loop_modifies_frame.rs`) uses the same 1/2/3 codes to recover
//! the loop region after the back edge is cut.
//!
//! SCOPE CONTROL: the rule is applied only when EVERY piece can be
//! constructed (register call located, loop region resolved, havoc set
//! register-resolvable with havocable types, guard block pure, all instances
//! resolvable) and the body is neither contract-instrumented nor carries an
//! explicit `kani_loop_modifies` assigns clause. Any failure leaves the loop
//! on the LEGACY encoding verbatim (cyclic + invariant-as-hint) — status quo
//! ante; the legacy silent-exit fail-open is pre-existing and tracked
//! (memory: contract-inline-check-loss). A loop is never PARTIALLY
//! instrumented (the plan phase is read-only).

use super::LoopContractPass;
use crate::kani_middle::KaniAttributes;
use crate::kani_middle::transform::body::{
    CheckType, InsertPosition, MutableBody, SourceInstruction,
};
use crate::rustc_public::CrateDef;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    BasicBlock, ConstOperand, Mutability, NonDivergingIntrinsic, Operand, Place, ProjectionElem,
    Rvalue, Statement, StatementKind, SwitchTargets, Terminator, TerminatorKind, UnwindAction,
};
use rustc_public::ty::{
    AdtKind, GenericArgKind, GenericArgs, MirConst, RigidTy, Ty, TyKind, UintTy,
};
use rustc_span::Symbol;
use std::collections::{BTreeSet, HashMap};

/// Message stem of the BASE-case obligation, and the marker that carries the
/// loop's index to the driver.
///
/// The obligation is registered through `hook_safety_check`, so its only
/// channel to the report is this message: the label is `kani_assert` for every
/// safety check, which is why the driver has to recognise loop-contract
/// obligations by TEXT (`ay_parse::vc_artifact::LOOP_CONTRACT_OBLIGATION_PREFIXES`,
/// which pins these same stems — keep the two in step).
///
/// The trailing `(loop N)` is the loop's index within its function, counted in
/// source order over the loops this pass instruments. The driver strips it and
/// renders `Check invariant before entry for loop <fn>.<N>` (CBMC/Kani's own
/// wording), splicing the function name from the check's source location so the
/// name in the description can never disagree with the check-id prefix.
///
/// LIMIT, deliberately not papered over: N counts CONTRACTED loops, while CBMC
/// numbers every loop in the function. A function that mixes an uncontracted
/// loop before a contracted one would therefore disagree with CBMC's id. No
/// corpus shape has that mix today, and inventing a number we cannot derive
/// would be worse than a documented divergence.
pub(crate) const LOOP_INVARIANT_BASE_MSG: &str =
    "loop invariant base case: invariant must hold on loop entry";

/// Message stem of the INDUCTIVE-STEP obligation. See `LOOP_INVARIANT_BASE_MSG`.
pub(crate) const LOOP_INVARIANT_STEP_MSG: &str =
    "loop invariant inductive step: invariant must be re-established by the loop body";

/// Opening of the loop-index suffix appended to both messages above.
pub(crate) const LOOP_ID_MARKER: &str = "(loop ";

/// `_transformed` code for the BASE breadcrumb at the rewritten loop head
/// (FC-29's loop-assigns fallback recovers the loop region from the 2/1 pair).
const TRANSFORMED_BASE: u128 = 2;

/// `_transformed` sentinel on the latch register call of a NESTED inner loop
/// deliberately left on the LEGACY encoding because its invariant reads
/// outer-havocked state (Wall-2 honesty gate). CHC codegen scans for this code
/// and records a fail-closed demotion for the body — the legacy-under-havoc
/// combination is over-approximate by construction, so its verdicts must
/// never classify as Genuine/clean.
pub(crate) const TRANSFORMED_NESTED_LEGACY: u128 = 4;

/// Everything needed to instrument one loop, gathered read-only up front so a
/// late failure can never leave a loop partially instrumented.
struct LoopRulePlan {
    /// The block carrying the single loop-ENTRY edge into the guard switch
    /// (usually the rewritten head; moved-call blocks can sit in between).
    anchor_bb: usize,
    /// Block whose terminator is the latch `kani_register_loop_contract` call.
    reg_bb: usize,
    /// The CHC-visible loop head: the `SwitchInt(_v)` block.
    switch_bb: usize,
    /// Forward target for the dead sink edge. Usually `termination_bb`, but
    /// for `loop{}` desugars the termination block is a fabricated
    /// `assert(false)` stub that cannot reach `Return` — the CHC retention
    /// policy then declares no relations for the sink/step tail and the
    /// #3436 error-only rewrite turns the `assume(false)` edge into a REAL
    /// error edge (`bb ∧ ¬inv → error`), fabricating a CEX (task #70's
    /// 19-step trace on simple_loop_loop). The sink edge is assume(false)-
    /// guarded, so its target is semantically irrelevant; retarget it to a
    /// return-reachable region exit so the tail keeps its relations and
    /// hook_assume encodes the dead edge exactly.
    sink_target: usize,
    /// Destination of the latch register call (`_v`, a plain bool local).
    reg_dest: Place,
    /// The closure-ref operand shared by all register call sites.
    closure_arg: Operand,
    /// Resolved instance of the register function (kept as a breadcrumb call:
    /// its body is literally `{ true }`, so it computes nothing — the actual
    /// invariant evaluation goes through `closure_shim`).
    reg_instance: Instance,
    /// Resolved `Fn::call` shim of the invariant closure — the REAL invariant
    /// evaluation vehicle (`_v = shim(&closure, ())`).
    closure_shim: Instance,
    /// Loop-modified locals to havoc, with the resolved `any_modifies::<T>`.
    havoc: Vec<(usize, Instance)>,
    /// Resolved `kani::assume` instance.
    assume_instance: Instance,
    /// Decreases interplay: re-snapshot `old = src` after the havoc so the
    /// ranking check compares within the symbolic iteration.
    resnapshot: Option<Vec<(usize, usize)>>,
}

impl LoopContractPass {
    /// Apply the loop-contract proof rule to every invariant-transformed loop.
    /// Runs after `instrument_loop_decreases` (which may relocate the latch
    /// register call into a successor block — the walk below re-locates it).
    pub(super) fn instrument_loop_invariant_rule(&mut self, tcx: TyCtxt, body: &mut MutableBody) {
        if self.new_loop_latches.is_empty() {
            return;
        }
        // Triage lever: fall back to the legacy (fail-open, cyclic) encoding.
        if std::env::var("TRUST_MC_NO_LOOP_RULE").map(|v| v == "1").unwrap_or(false) {
            tracing::warn!("loop-contract proof rule disabled by TRUST_MC_NO_LOOP_RULE");
            return;
        }
        // #47 scope gate 1 REMOVED (measured, 2026-08-28). It skipped every
        // contract-instrumented body because "the combined rule obligations
        // regress tests the legacy path proves (function_with_loop_no_assertion,
        // contract_proof_function_with_loop — both parity pre-rule)". Both
        // named tests were re-measured on the legacy path at this commit and
        // BOTH already FAIL there: function_with_loop_no_assertion reports
        // `contract_proof.unwind.1 "unwinding assertion loop 0": FAILURE`
        // (the uninstrumented loop simply unrolls past the bound) and
        // contract_proof_function_with_loop reports no loop obligation at all.
        // The gate is therefore protecting failures, not parity.
        //
        // What still protects the combination is the PLAN, which is
        // independent of this gate and unchanged: `scan_havoc_set` fails
        // closed on every contract artifact it cannot account for — a
        // kani-internal call that is not frame-pure, a `&mut`/raw-pointer
        // call argument whose provenance it cannot resolve, a shared-reference
        // argument carrying writable indirection (which is what a contract
        // closure capturing `&mut` state looks like), a store to a local
        // without a havocable type. Any of those leaves the loop on the
        // legacy encoding exactly as this gate did.
        // #47 scope gate 2: an explicit `kani_loop_modifies` assigns clause
        // defines its own frame; the legacy FC-29 loop-modifies machinery
        // proves those tests today (loop_assigns_for_{ref,ptr,fat_ptr} are
        // parity pre-rule). Havoc-set/assigns reconciliation is future work.
        let has_loop_modifies = body
            .var_debug_info()
            .iter()
            .any(|info| info.name.to_string().contains("kani_loop_modifies"));
        if has_loop_modifies {
            tracing::debug!("loop-contract rule: skipped (explicit loop assigns clause)");
            return;
        }
        let Some(check_type) = self.safety_check_no_assume_type.clone() else {
            // No harness in this unit: nothing is verified, keep MIR untouched.
            return;
        };

        let mut loops: Vec<(usize, usize)> =
            self.new_loop_latches.iter().map(|(head, latch)| (*head, *latch)).collect();
        loops.sort_unstable();
        let single_loop = loops.len() == 1;

        // Wall-2 honesty gate: a NESTED rule-instrumented loop whose invariant
        // reads a local that the OUTER loop's symbolic iteration havocs — with
        // no re-initialization between the havoc and the inner loop entry —
        // gets a structurally refutable base case (the havocked value flows
        // straight into `assert(inner_inv)`), even when the concrete program
        // maintains the invariant (multiple_loops' simple_while_loops: `y` is
        // only written inside the inner loop, so the outer havoc's
        // unconstrained `y` reaches the inner base check). Before Wall-2
        // resolved the closure-typed invariant evaluations, those bases were
        // havocked-and-demoted; with REAL evaluations the spurious base CTREX
        // would surface as a false Genuine. Leave such inner loops on the
        // LEGACY encoding (cyclic + invariant hint — status quo ante, same as
        // every other unsupported-shape skip below); the outer rule still
        // applies. Inner loops whose invariant locals are re-initialized on
        // the iteration path before their entry (nested_loop_local_var_
        // func_call's `j = sum_pair(..)`) keep the full rule.
        let skip_inner = self.nested_dependent_inner_skips(tcx, body, &loops);

        for (loop_idx, (head_bb, latch_hint)) in loops.into_iter().enumerate() {
            if skip_inner.contains(&head_bb) {
                tracing::debug!(
                    head_bb,
                    "loop-contract rule: skipped (nested inner loop with outer-havoc-dependent \
                     invariant, legacy encoding kept)"
                );
                // Honesty marker: rewrite the skipped loop's latch register
                // breadcrumb to `_transformed = TRANSFORMED_NESTED_LEGACY` so
                // CHC codegen records a fail-closed demotion for the body. The
                // legacy inner encoding under an outer havoc is over-
                // approximate BY CONSTRUCTION (outer-havocked state flows into
                // the legacy loop, whose invariant is only a hint with the
                // pre-existing silent-exit fail-open), so any CTREX from such
                // a body must classify OverApproximation — never Genuine —
                // and any PROOF must demote. The argument is otherwise unused
                // (`run_loop_contract_fn(_, _transformed)` ignores it; the
                // FC-29 breadcrumb recovery only matches codes 2/1).
                if let Ok(reg_bb) = self.walk_to_register_call(tcx, body, latch_hint) {
                    let span = body.blocks()[reg_bb].terminator.span;
                    let sentinel =
                        body.new_uint_operand(TRANSFORMED_NESTED_LEGACY, UintTy::Usize, span);
                    let mut term = body.blocks()[reg_bb].terminator.clone();
                    if let TerminatorKind::Call { args, .. } = &mut term.kind
                        && args.len() >= 2
                    {
                        args[1] = sentinel;
                        body.replace_terminator(
                            &SourceInstruction::Terminator { bb: reg_bb },
                            term,
                        );
                    }
                }
                continue;
            }
            match self.plan_loop_rule(tcx, body, head_bb, latch_hint, single_loop) {
                Ok(plan) => {
                    tracing::debug!(
                        head_bb,
                        reg_bb = plan.reg_bb,
                        switch_bb = plan.switch_bb,
                        havoc = ?plan.havoc.iter().map(|(l, _)| *l).collect::<Vec<_>>(),
                        "loop-contract rule: instrumenting base/step/post"
                    );
                    Self::apply_loop_rule(body, &plan, &check_type, loop_idx);
                }
                Err(reason) => {
                    // Unsupported shape: keep the LEGACY encoding verbatim
                    // (cyclic loop + invariant-as-hint). Status quo ante — the
                    // legacy path proves several of these (for_loop_for_array
                    // was parity pre-rule); fail-closing them here regressed
                    // parity tests. The legacy silent-exit fail-open is
                    // pre-existing and tracked (contract-inline-check-loss).
                    tracing::debug!(
                        head_bb,
                        reason,
                        "loop-contract rule: skipped (unsupported shape, legacy encoding kept)"
                    );
                }
            }
        }
    }

    /// Wall-2 honesty gate (see call site): heads of NESTED instrumented loops
    /// whose invariant captures a local havocked by an enclosing loop and for
    /// which at least one path from the enclosing post-havoc guard to the inner
    /// loop performs no whole-local re-initialization. Read-only over the
    /// pristine (still cyclic) body.
    ///
    /// A mere write somewhere outside the inner region is not authority for a
    /// re-initialization: it may be after the inner loop or on a sibling branch.
    /// Likewise, the source head executes before the enclosing rule's havoc and
    /// is bypassed by the post-havoc tail. We therefore start at the exact guard
    /// switch recovered from the latch, use the enclosing rule's exact havoc
    /// scan, and require every path that reaches the inner region to cross a
    /// whole-local assignment (or the normal return edge of a whole-local call
    /// destination). Missing or ambiguous evidence only SKIPS the inner rule.
    fn nested_dependent_inner_skips(
        &self,
        tcx: TyCtxt,
        body: &MutableBody,
        loops: &[(usize, usize)],
    ) -> BTreeSet<usize> {
        let mut skips = BTreeSet::new();
        if loops.len() < 2 {
            return skips;
        }
        struct LoopShape {
            source_head: usize,
            latch: usize,
            switch: usize,
            region: BTreeSet<usize>,
            havoc: BTreeSet<usize>,
        }

        // Admit only shapes for which the complete read-only plan succeeds.
        // A partial switch/region/havoc reconstruction is not enough: if any
        // later plan gate declines, the enclosing loop cannot gain a
        // rule-generated havoc and therefore cannot create this nested hazard.
        // `loops.len() >= 2`, so the caller will use `single_loop = false` too.
        let mut shapes = Vec::with_capacity(loops.len());
        for &(source_head, latch) in loops {
            let Ok(plan) = self.plan_loop_rule(tcx, body, source_head, latch, false) else {
                continue;
            };
            let region = loop_region(body, plan.switch_bb, plan.reg_bb);
            let havoc = plan.havoc.iter().map(|(local, _)| *local).collect();
            shapes.push(LoopShape { source_head, latch, switch: plan.switch_bb, region, havoc });
        }

        let successors: Vec<Vec<usize>> =
            body.blocks().iter().map(|block| block.terminator.successors()).collect();

        let defs = build_single_def_map(body);
        for (outer_idx, outer) in shapes.iter().enumerate() {
            for (inner_idx, inner) in shapes.iter().enumerate() {
                if inner_idx == outer_idx
                    || inner.source_head == outer.source_head
                    || !outer.region.contains(&inner.switch)
                {
                    continue;
                }
                let Some(captures) = self.invariant_capture_locals(tcx, body, &defs, inner.latch)
                else {
                    // Captures unrecoverable: fail toward SKIPPING the inner
                    // rule (legacy encoding) rather than risking a refutable
                    // base on a havocked capture.
                    skips.insert(inner.source_head);
                    continue;
                };
                if captures.iter().any(|local| {
                    outer.havoc.contains(local)
                        && capture_has_write_free_path_to_region(
                            body,
                            &successors,
                            outer.switch,
                            &outer.region,
                            &inner.region,
                            *local,
                        )
                }) {
                    skips.insert(inner.source_head);
                }
            }
        }
        skips
    }

    /// The invariant closure's captured LOCALS for the loop whose latch chain
    /// starts at `latch_hint`: register call → `&closure` operand → closure
    /// local → `Aggregate(Closure)` fields → `Ref`/`AddressOf`/copy sources.
    /// `None` when any link cannot be recovered.
    fn invariant_capture_locals(
        &self,
        tcx: TyCtxt,
        body: &MutableBody,
        defs: &HashMap<usize, Rvalue>,
        latch_hint: usize,
    ) -> Option<BTreeSet<usize>> {
        let reg_bb = self.walk_to_register_call(tcx, body, latch_hint).ok()?;
        let TerminatorKind::Call { args, .. } = &body.blocks()[reg_bb].terminator.kind else {
            return None;
        };
        let (Operand::Copy(p) | Operand::Move(p)) = args.first()? else {
            return None;
        };
        if !p.projection.is_empty() {
            return None;
        }
        // `&closure` temp → closure local (or the operand IS the closure local).
        let closure_local = match defs.get(&p.local) {
            Some(Rvalue::Ref(_, _, target) | Rvalue::AddressOf(_, target))
                if target.projection.is_empty() =>
            {
                target.local
            }
            _ => p.local,
        };
        // Find the closure construction (unique whole-local aggregate assign).
        let mut fields: Option<&Vec<Operand>> = None;
        for block in body.blocks() {
            for stmt in &block.statements {
                if let StatementKind::Assign(place, Rvalue::Aggregate(kind, ops)) = &stmt.kind
                    && place.local == closure_local
                    && place.projection.is_empty()
                    && matches!(kind, rustc_public::mir::AggregateKind::Closure(..))
                {
                    fields = Some(ops);
                }
            }
        }
        let fields = fields?;
        let mut captures = BTreeSet::new();
        for op in fields {
            let (Operand::Copy(fp) | Operand::Move(fp)) = op else {
                continue;
            };
            if !fp.projection.is_empty() {
                return None;
            }
            match defs.get(&fp.local) {
                Some(Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src)) => {
                    captures.insert(src.local);
                }
                Some(Rvalue::Use(Operand::Copy(src) | Operand::Move(src)))
                    if src.projection.is_empty() =>
                {
                    captures.insert(src.local);
                }
                _ => {
                    captures.insert(fp.local);
                }
            }
        }
        Some(captures)
    }

    /// Phase A (read-only): locate all the pieces and validate them.
    fn plan_loop_rule(
        &self,
        tcx: TyCtxt,
        body: &MutableBody,
        _head_bb: usize,
        latch_hint: usize,
        single_loop: bool,
    ) -> Result<LoopRulePlan, &'static str> {
        // ── Locate the latch register call (decreases may have moved it) ────
        let reg_bb = self.walk_to_register_call(tcx, body, latch_hint)?;
        let TerminatorKind::Call { func, args, destination, target, .. } =
            &body.blocks()[reg_bb].terminator.kind
        else {
            return Err("latch register terminator vanished");
        };
        let Some(switch_bb) = *target else { return Err("latch register call has no target") };
        if args.is_empty() {
            return Err("latch register call has no closure argument");
        }
        if !destination.projection.is_empty()
            || body.locals()[destination.local].ty != Ty::bool_ty()
        {
            return Err("latch register destination is not a plain bool local");
        }
        let Some(RigidTy::FnDef(fn_def, genargs)) =
            func.ty(body.locals()).ok().and_then(|t| t.kind().rigid().cloned())
        else {
            return Err("latch register callee is not a FnDef");
        };
        let Ok(reg_instance) = Instance::resolve(fn_def, &genargs) else {
            return Err("latch register instance unresolvable");
        };
        // The invariant closure is the LAST closure among the register fn's
        // generic args (an enclosing generic fn contributes earlier generics).
        let mut closure_shim = None;
        for arg in genargs.0.iter().rev() {
            if let GenericArgKind::Type(arg_ty) = arg
                && let TyKind::RigidTy(RigidTy::Closure(closure_def, closure_args)) = arg_ty.kind()
            {
                closure_shim = rustc_public::mir::mono::Instance::resolve_closure(
                    closure_def,
                    &closure_args,
                    rustc_public::ty::ClosureKind::Fn,
                )
                .ok();
                break;
            }
        }
        let Some(closure_shim) = closure_shim else {
            return Err("invariant closure shim unresolvable");
        };

        // ── Entry anchor / switch / termination sanity ──────────────────────
        if !matches!(body.blocks()[switch_bb].terminator.kind, TerminatorKind::SwitchInt { .. }) {
            return Err("guard block is not a SwitchInt");
        }
        let switch_successors = body.blocks()[switch_bb].terminator.successors();
        let Some(termination_bb) = switch_successors.first().copied() else {
            return Err("guard SwitchInt has no successors");
        };
        // The single loop-ENTRY edge into the guard switch: the unique
        // REACHABLE predecessor of `switch_bb` other than the latch register
        // block. (The head block may no longer target the switch directly —
        // move_storagelive_call_to_loophead can insert moved call blocks in
        // between — and block splitting leaves unreachable goto stubs that
        // must be ignored.)
        let reachable = reachable_blocks(body);
        let mut entry_anchors = Vec::new();
        for (bb, block) in body.blocks().iter().enumerate() {
            if bb == reg_bb || !reachable.contains(&bb) {
                continue;
            }
            if block.terminator.successors().contains(&switch_bb) {
                entry_anchors.push(bb);
            }
        }
        let [anchor_bb] = entry_anchors[..] else {
            return Err("loop guard has no unique entry edge");
        };

        // ── Loop region: {switch} + reverse-reach(reg_bb) stopping at switch ─
        let region = loop_region(body, switch_bb, reg_bb);

        // ── Havoc set (register-level store scan; fail-closed) ──────────────
        let havoc_locals = self.scan_havoc_set(tcx, body, &region, switch_bb, destination.local)?;

        // ── Resolve all instances up front ───────────────────────────────────
        let Some(assume_def) = self.assume_fn else { return Err("kani::assume FnDef missing") };
        let Ok(assume_instance) = Instance::resolve(assume_def, &GenericArgs(vec![])) else {
            return Err("kani::assume instance unresolvable");
        };
        let Some(any_modifies_def) = self.any_modifies_fn else {
            return Err("kani any_modifies FnDef missing");
        };
        let mut havoc = Vec::with_capacity(havoc_locals.len());
        for local in havoc_locals {
            let ty = body.locals()[local].ty;
            let Ok(inst) =
                Instance::resolve(any_modifies_def, &GenericArgs(vec![GenericArgKind::Type(ty)]))
            else {
                return Err("any_modifies instance unresolvable for a havocked local");
            };
            havoc.push((local, inst));
        }
        // ── Decreases interplay: re-snapshot after the havoc ────────────────
        // `instrument_loop_decreases` only fires on single-loop bodies, so the
        // snapshot (if any) belongs to this loop exactly when single_loop.
        let resnapshot = if single_loop { self.decreases_snapshot.clone() } else { None };

        // Sink-target selection (task #70; see the `sink_target` field doc).
        let return_reachable = return_reachable_blocks(body);
        let sink_target = if return_reachable.contains(&termination_bb) {
            termination_bb
        } else {
            // Alternate: any return-reachable successor of a region block
            // that lies outside the region (e.g. the break target).
            let mut alt = None;
            'outer: for &bb in &region {
                for succ in body.blocks()[bb].terminator.successors() {
                    if !region.contains(&succ) && return_reachable.contains(&succ) {
                        alt = Some(succ);
                        break 'outer;
                    }
                }
            }
            match alt {
                Some(bb) => bb,
                None => return Err("loop termination block cannot reach return"),
            }
        };

        Ok(LoopRulePlan {
            anchor_bb,
            reg_bb,
            switch_bb,
            sink_target,
            reg_dest: destination.clone(),
            closure_arg: args[0].clone(),
            reg_instance,
            closure_shim,
            havoc,
            assume_instance,
            resnapshot,
        })
    }

    /// Follow single-successor terminators from `start` until the block whose
    /// terminator is the `kani_register_loop_contract` call.
    fn walk_to_register_call(
        &self,
        tcx: TyCtxt,
        body: &MutableBody,
        start: usize,
    ) -> Result<usize, &'static str> {
        let mut cur = start;
        for _ in 0..body.blocks().len() {
            match &body.blocks()[cur].terminator.kind {
                TerminatorKind::Call { func, target, .. } => {
                    if let Some(RigidTy::FnDef(fn_def, _)) =
                        func.ty(body.locals()).ok().and_then(|t| t.kind().rigid().cloned())
                        && KaniAttributes::for_def_id(tcx, fn_def.def_id()).fn_marker()
                            == Some(Symbol::intern("kani_register_loop_contract"))
                    {
                        return Ok(cur);
                    }
                    let Some(t) = target else {
                        return Err("diverging call while walking to latch register");
                    };
                    cur = *t;
                }
                TerminatorKind::Goto { target } => cur = *target,
                _ => return Err("unexpected terminator while walking to latch register"),
            }
        }
        Err("latch register call not found")
    }

    /// Register-level scan of the loop region for modified locations.
    ///
    /// Returns the set of locals to havoc, or an error when a store cannot be
    /// resolved to a havocable local (the loop is then fail-closed).
    fn scan_havoc_set(
        &self,
        tcx: TyCtxt,
        body: &MutableBody,
        region: &BTreeSet<usize>,
        switch_bb: usize,
        exclude_local: usize,
    ) -> Result<BTreeSet<usize>, &'static str> {
        // Locals whose storage BEGINS inside the region are freshly scoped on
        // every iteration: their pre-iteration value is dead, so they need no
        // havoc (mirrors FC-29's loop-local exemption; storage markers are
        // kept alive via -Z mir-enable-passes=-RemoveStorageMarkers).
        let mut scoped: BTreeSet<usize> = BTreeSet::new();
        for &bb in region {
            for stmt in &body.blocks()[bb].statements {
                if let StatementKind::StorageLive(local) = stmt.kind {
                    scoped.insert(local);
                }
            }
        }
        let defs = build_single_def_map(body);
        let mut havoc: BTreeSet<usize> = BTreeSet::new();
        // Cache for the (more expensive) skip-havoc analysis of non-plain
        // stored locals: iteration-local temporaries (closure plumbing,
        // rewritten-iterator ref temps) that are written before every read on
        // all in-region paths and never observed outside the region.
        let mut skip_cache: HashMap<usize, bool> = HashMap::new();
        let mut add_store =
            |local: usize, havoc: &mut BTreeSet<usize>| -> Result<(), &'static str> {
                if local == exclude_local || scoped.contains(&local) {
                    return Ok(());
                }
                if !is_plain_value_ty(body.locals()[local].ty, 8) {
                    let safe = *skip_cache.entry(local).or_insert_with(|| {
                        local_is_iteration_scoped(body, region, switch_bb, local)
                    });
                    if safe {
                        return Ok(());
                    }
                    tracing::debug!(
                        local,
                        ty = ?body.locals()[local].ty,
                        "loop-contract rule: non-havocable store target"
                    );
                    return Err("loop stores to a local without a havocable (plain-value) type");
                }
                havoc.insert(local);
                Ok(())
            };

        for &bb in region {
            let block = &body.blocks()[bb];
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(place, _)
                    | StatementKind::SetDiscriminant { place, .. } => {
                        if place.projection.iter().any(|e| matches!(e, ProjectionElem::Deref)) {
                            let base = resolve_mut_pointer_base(body, &defs, place.local, 8)
                                .ok_or("deref store with unresolvable pointer provenance")?;
                            add_store(base, &mut havoc)?;
                        } else {
                            add_store(place.local, &mut havoc)?;
                        }
                    }
                    StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(..)) => {
                        return Err("copy_nonoverlapping inside contracted loop");
                    }
                    StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(..))
                    | StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::Retag(..)
                    | StatementKind::FakeRead(..)
                    | StatementKind::PlaceMention(..)
                    | StatementKind::AscribeUserType { .. }
                    | StatementKind::Coverage(..)
                    | StatementKind::ConstEvalCounter
                    | StatementKind::Nop => {}
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, target, .. } => {
                    // Diverging calls never return: their effects cannot flow
                    // into later iterations or the post-loop state.
                    if target.is_none() {
                        continue;
                    }
                    if destination.projection.iter().any(|e| matches!(e, ProjectionElem::Deref)) {
                        return Err("call destination behind a pointer");
                    }
                    add_store(destination.local, &mut havoc)?;

                    let Some(RigidTy::FnDef(fn_def, call_genargs)) =
                        func.ty(body.locals()).ok().and_then(|t| t.kind().rigid().cloned())
                    else {
                        return Err("indirect call inside contracted loop");
                    };
                    // Kani-internal instrumentation calls only write their
                    // destination (register/assume/checks/any*); trust them.
                    if let Some(marker) =
                        KaniAttributes::for_def_id(tcx, fn_def.def_id()).fn_marker()
                    {
                        if kani_marker_is_frame_pure(marker.as_str()) {
                            continue;
                        }
                        return Err("kani-internal call with side effects inside contracted loop");
                    }
                    // The loop-contract for-loop rewrite replaces the user's
                    // `IntoIterator` with this repo's own `KaniIter` adapters
                    // and steps them through a SHARED `&self` inside the loop
                    // region. Those arguments are rejected by the generic rule
                    // below because every adapter holds a `*const T`, and
                    // `no_writable_indirection` rejects a raw pointer whatever
                    // its mutability (a `*const` can be cast to `*mut`). That
                    // is the right default for a type whose code we have not
                    // read; it is wrong for these, whose bodies are in
                    // `library/kani_core/src/iter.rs`.
                    //
                    // The exemption is POSITIVE and per-(method, adapter) —
                    // see `readonly_kani_iter_shim` for why the trait as a
                    // whole is NOT read-only.
                    if readonly_kani_iter_shim(&fn_def.name(), &call_genargs) {
                        continue;
                    }

                    for arg in args {
                        let (Operand::Copy(_) | Operand::Move(_)) = arg else { continue };
                        let Ok(arg_ty) = arg.ty(body.locals()) else {
                            return Err("untypable call argument inside contracted loop");
                        };
                        match arg_ty.kind() {
                            TyKind::RigidTy(RigidTy::Ref(_, _, Mutability::Mut))
                            | TyKind::RigidTy(RigidTy::RawPtr(_, Mutability::Mut)) => {
                                let (Operand::Copy(p) | Operand::Move(p)) = arg else {
                                    unreachable!("guarded above")
                                };
                                if !p.projection.is_empty() {
                                    return Err("projected mutable-pointer call argument");
                                }
                                let base = resolve_mut_pointer_base(body, &defs, p.local, 8)
                                    .ok_or("mutable-pointer call argument with unresolvable provenance")?;
                                if !scoped.contains(&base) {
                                    add_store(base, &mut havoc)?;
                                }
                            }
                            TyKind::RigidTy(RigidTy::Ref(_, pointee, Mutability::Not))
                            | TyKind::RigidTy(RigidTy::RawPtr(pointee, Mutability::Not)) => {
                                if !no_writable_indirection(pointee, 8) {
                                    // Name the callee and the pointee: this
                                    // is the gate the for-loop family trips,
                                    // and the reason string alone does not
                                    // say WHICH call blocked the loop.
                                    tracing::debug!(
                                        callee = ?fn_def.name(),
                                        pointee = ?pointee,
                                        "loop-contract rule: shared-pointer call argument blocked \
                                         the havoc scan"
                                    );
                                    return Err(
                                        "shared-pointer call argument with interior mutability or writable indirection",
                                    );
                                }
                            }
                            _ => {
                                if !no_writable_indirection(arg_ty, 8) {
                                    return Err(
                                        "by-value call argument carrying writable indirection",
                                    );
                                }
                            }
                        }
                    }
                }
                TerminatorKind::Drop { place, .. } => {
                    if place.projection.iter().any(|e| matches!(e, ProjectionElem::Deref)) {
                        return Err("drop behind a pointer inside contracted loop");
                    }
                    if !is_plain_value_ty(body.locals()[place.local].ty, 8) {
                        return Err("drop of a non-trivial type inside contracted loop");
                    }
                    // Plain-value drops are no-ops; nothing to havoc beyond the
                    // local itself (deinit), which add_store covers.
                    add_store(place.local, &mut havoc)?;
                }
                TerminatorKind::InlineAsm { .. } => {
                    return Err("inline asm inside contracted loop");
                }
                TerminatorKind::Goto { .. }
                | TerminatorKind::SwitchInt { .. }
                | TerminatorKind::Assert { .. }
                | TerminatorKind::Return
                | TerminatorKind::Resume
                | TerminatorKind::Abort
                | TerminatorKind::Unreachable => {}
            }
        }
        Ok(havoc)
    }

    /// Phase B: mutate the body. Only called with a fully validated plan.
    ///
    /// ENCODING NOTE: every invariant evaluation writes the ORIGINAL register
    /// destination `_v` and is immediately consumed by a `SwitchInt(_v)` in the
    /// NEXT block — the exact shape of the pre-rule latch call, which the CHC
    /// pipeline is known to carry across the block boundary (`_v` is used by
    /// the switch, so it stays in the relation signature and the inline lane
    /// binds it on the call edge). Fresh cross-block temporaries must NOT be
    /// used here: locals without storage markers get pruned from relation
    /// signatures and their constraints are sanitized away (the decreases
    /// guard-7 "undeclared-mid" trap), silently erasing the obligation.
    /// Check conditions in branch blocks are same-block constants (the user
    /// `assert!` pattern), so reachability of the branch IS the property.
    fn apply_loop_rule(
        body: &mut MutableBody,
        plan: &LoopRulePlan,
        check_type: &CheckType,
        loop_idx: usize,
    ) {
        let span = body.blocks()[plan.anchor_bb].terminator.span;
        let (CheckType::SafetyCheck(check_instance)
        | CheckType::SafetyCheckNoAssume(check_instance)
        | CheckType::UnsupportedCheck(check_instance)) = check_type;

        let unit_ty = Ty::new_tuple(&[]);
        let bool_op = |value: bool| {
            Operand::Constant(ConstOperand {
                span,
                user_ty: None,
                const_: MirConst::from_bool(value),
            })
        };
        // Call-operand helper (same pattern as MutableBody::insert_call).
        let fn_op = |body: &mut MutableBody, instance: &Instance| {
            Operand::Copy(Place::from(body.new_local(instance.ty(), span, Mutability::Not)))
        };

        // An OBLIGATION block: `safety_check_no_assume(_v, msg)` where `_v`
        // holds the freshly-evaluated invariant.
        //
        // The condition is the invariant VALUE, not a constant `false` inside
        // a `¬inv`-guarded branch. That is the whole point: with the constant
        // form the obligation's own path condition IS `¬inv`, so the driver's
        // reachability classification demotes a DISCHARGED obligation to
        // UNREACHABLE — indistinguishable from a loop sitting in dead code.
        // Both printed UNREACHABLE before this change (controls `ctrl_true`
        // vs `ctrl_dead_loop`, which were byte-identical). Asserting `_v` at
        // the reachable loop head instead gives the three outcomes distinct
        // reports, and matches Kani/CBMC, which asserts the invariant itself:
        // provable => SUCCESS, refutable => FAILURE, loop head dead =>
        // UNREACHABLE.
        //
        // The check is assert-ONLY. Its `false` continuation is cut by the
        // switch that still follows it (base) or by the sink it targets
        // (step), so the assume half would only restate an edge the CFG
        // already removes.
        let make_check_block = |body: &mut MutableBody, msg: &str, target: usize| {
            let func = fn_op(body, check_instance);
            let msg_op = Operand::Constant(ConstOperand {
                span,
                user_ty: None,
                const_: MirConst::from_str(msg),
            });
            let dest = Place::from(body.new_local(unit_ty, span, Mutability::Mut));
            body.push_block(BasicBlock {
                statements: vec![],
                terminator: Terminator {
                    kind: TerminatorKind::Call {
                        func,
                        args: vec![Operand::Copy(plan.reg_dest.clone()), msg_op],
                        destination: dest,
                        target: Some(target),
                        unwind: UnwindAction::Terminate,
                    },
                    span,
                },
            })
        };

        // ── Shared sink: assume(false) — a dead forward edge to termination ─
        let sink_bb = {
            let func = fn_op(body, &plan.assume_instance);
            let dest = Place::from(body.new_local(unit_ty, span, Mutability::Mut));
            body.push_block(BasicBlock {
                statements: vec![],
                terminator: Terminator {
                    kind: TerminatorKind::Call {
                        func,
                        args: vec![bool_op(false)],
                        destination: dest,
                        target: Some(plan.sink_target),
                        unwind: UnwindAction::Terminate,
                    },
                    span,
                },
            })
        };

        let bool_switch = |discr: Place, false_bb: usize, true_bb: usize| Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(discr),
                targets: SwitchTargets::new(vec![(0, false_bb)], true_bb),
            },
            span,
        };

        // Build the head chain back-to-front so every block knows its target.
        // tail: [_v = true, (old = src)] goto -> original guard switch.
        let mut tail_stmts = vec![Statement {
            kind: StatementKind::Assign(plan.reg_dest.clone(), Rvalue::Use(bool_op(true))),
            span,
        }];
        // Decreases interplay: the ranking snapshot must be taken on the
        // havocked (symbolic-iteration) state, not the concrete entry state.
        // Refresh EVERY measure component after the havoc. A compound measure
        // (`hi - lo`) records one pair per component; the latch recomputes the
        // difference from these, so missing one would leave `old` free and the
        // ranking obligation would refute on a terminating loop.
        for &(old_local, measure_src) in plan.resnapshot.iter().flatten() {
            tail_stmts.push(Statement {
                kind: StatementKind::Assign(
                    Place::from(old_local),
                    Rvalue::Use(Operand::Copy(Place::from(measure_src))),
                ),
                span,
            });
        }
        let tail_bb = body.push_block(BasicBlock {
            statements: tail_stmts,
            terminator: Terminator { kind: TerminatorKind::Goto { target: plan.switch_bb }, span },
        });

        // The invariant closure's `Fn::call` shim self operand. Reuse the
        // register call's closure-ref by COPY (it stays initialized: the
        // original transform keeps the closure alive across the loop).
        let shim_self_op = match &plan.closure_arg {
            Operand::Copy(p) | Operand::Move(p) => Operand::Copy(p.clone()),
            c @ Operand::Constant(_) => c.clone(),
        };
        // An invariant-evaluation block: `_v = <closure shim>(&closure, ())`.
        // The REAL evaluation vehicle — the register fn's body is `{ true }`.
        let make_eval_block = |body: &mut MutableBody, target: usize| {
            let unit_local = body.new_local(unit_ty, span, Mutability::Mut);
            let func = fn_op(body, &plan.closure_shim);
            body.push_block(BasicBlock {
                statements: vec![Statement {
                    kind: StatementKind::Assign(
                        Place::from(unit_local),
                        Rvalue::Aggregate(rustc_public::mir::AggregateKind::Tuple, vec![]),
                    ),
                    span,
                }],
                terminator: Terminator {
                    kind: TerminatorKind::Call {
                        func,
                        args: vec![shim_self_op.clone(), Operand::Move(Place::from(unit_local))],
                        destination: plan.reg_dest.clone(),
                        target: Some(target),
                        unwind: UnwindAction::Terminate,
                    },
                    span,
                },
            })
        };

        // assume-switch: false (¬inv on havocked state) ⇒ sink; true ⇒ tail.
        let asm_sw_bb = body.push_block(BasicBlock {
            statements: vec![],
            terminator: bool_switch(plan.reg_dest.clone(), sink_bb, tail_bb),
        });

        // Evaluate the invariant on the havocked state.
        let havoc_eval_bb = make_eval_block(body, asm_sw_bb);

        // Havoc chain (front-to-back targets: last havoc -> havoc_eval).
        let mut next = havoc_eval_bb;
        for (local, any_instance) in plan.havoc.iter().rev() {
            let func = fn_op(body, any_instance);
            next = body.push_block(BasicBlock {
                statements: vec![],
                terminator: Terminator {
                    kind: TerminatorKind::Call {
                        func,
                        args: vec![],
                        destination: Place::from(*local),
                        target: Some(next),
                        unwind: UnwindAction::Terminate,
                    },
                    span,
                },
            });
        }
        let havoc_head_bb = next;

        // ── BASE: assert(inv) on the ENTRY state, then the ORIGINAL switch:
        // false ⇒ sink (the ¬inv continuation is cut structurally, exactly as
        // before this obligation moved into the check condition), true ⇒ the
        // havoc chain. Keeping the switch is what lets the check be
        // assert-ONLY: the assume half would duplicate an edge the CFG
        // already removes, and it measurably costs (see
        // `safety_check_no_assume_type`).
        let base_sw_bb = body.push_block(BasicBlock {
            statements: vec![],
            terminator: bool_switch(plan.reg_dest.clone(), sink_bb, havoc_head_bb),
        });
        let base_check_bb = make_check_block(
            body,
            &format!("{LOOP_INVARIANT_BASE_MSG} {LOOP_ID_MARKER}{loop_idx})"),
            base_sw_bb,
        );
        // Evaluate the invariant on the entry state.
        let base_eval_bb = make_eval_block(body, base_check_bb);

        // ── STEP: assert(inv) after the one symbolic body iteration, then the
        // CUT (sink; the back edge is gone, the system is acyclic). ──────────
        let step_check_bb = make_check_block(
            body,
            &format!("{LOOP_INVARIANT_STEP_MSG} {LOOP_ID_MARKER}{loop_idx})"),
            sink_bb,
        );
        // Evaluate the invariant after the one symbolic body iteration.
        let step_eval_bb = make_eval_block(body, step_check_bb);

        // ── Rewire: entry edge -> breadcrumb+eval; latch register -> step ───
        // The register calls are kept as BREADCRUMBS only (their body is
        // `{ true }`): `_transformed` = 2 marks the rewritten head for FC-29's
        // loop-assigns region recovery; the latch keeps its original call
        // (`_transformed` = 1). Both destinations are dead.
        let breadcrumb_dest = Place::from(body.new_local(Ty::bool_ty(), span, Mutability::Mut));
        let reg2_func = fn_op(body, &plan.reg_instance);
        let bc_bb = body.push_block(BasicBlock {
            statements: vec![],
            terminator: Terminator {
                kind: TerminatorKind::Call {
                    func: reg2_func,
                    args: vec![plan.closure_arg.clone(), transformed_const(TRANSFORMED_BASE, span)],
                    destination: breadcrumb_dest,
                    target: Some(base_eval_bb),
                    unwind: UnwindAction::Terminate,
                },
                span,
            },
        });
        let mut anchor_term = body.blocks()[plan.anchor_bb].terminator.clone();
        retarget_terminator(&mut anchor_term, plan.switch_bb, bc_bb);
        body.replace_terminator(&SourceInstruction::Terminator { bb: plan.anchor_bb }, anchor_term);

        let mut latch_term = body.blocks()[plan.reg_bb].terminator.clone();
        let TerminatorKind::Call { target, .. } = &mut latch_term.kind else {
            unreachable!("plan_loop_rule validated the latch register call terminator")
        };
        *target = Some(step_eval_bb);
        body.replace_terminator(&SourceInstruction::Terminator { bb: plan.reg_bb }, latch_term);
    }

    /// Fail-close a loop whose rule instrumentation cannot be constructed:
    /// an always-failing check at the loop head (assert false + assume false),
    /// so the harness reports FAILURE with the reason — never the fail-open
    /// silent-exit encoding.
    #[allow(dead_code)] // retained for a future strict mode
    fn fail_close_loop(
        body: &mut MutableBody,
        head_bb: usize,
        check_type: &CheckType,
        reason: &str,
    ) {
        let span = body.blocks()[head_bb].terminator.span;
        let mut src = SourceInstruction::Terminator { bb: head_bb };
        let ff = body.new_local(Ty::bool_ty(), span, Mutability::Mut);
        body.assign_to(
            Place::from(ff),
            Rvalue::Use(Operand::Constant(ConstOperand {
                span,
                user_ty: None,
                const_: MirConst::from_bool(false),
            })),
            &mut src,
            InsertPosition::Before,
        );
        let msg = format!("loop contract instrumentation unsupported ({reason}) — fail-closed");
        body.insert_check(check_type, &mut src, InsertPosition::Before, Some(ff), &msg);
    }
}

/// `_transformed` constant operand.
fn transformed_const(value: u128, span: rustc_public::ty::Span) -> Operand {
    Operand::Constant(ConstOperand {
        span,
        user_ty: None,
        const_: MirConst::try_from_uint(value, UintTy::Usize).expect("usize const"),
    })
}

/// Whether a stored-but-not-havocable local is ITERATION-SCOPED, making the
/// havoc skip sound:
///
/// 1. on every in-region path from the guard switch, every READ of the local
///    is preceded by a projection-free WRITE (forward dataflow; the switch
///    entry state is pinned to "unwritten" so a value flowing around the back
///    edge is never mistaken for a definition), and
/// 2. outside the region the local is only ever a projection-free write
///    target or a storage marker (its loop value is never observed).
///
/// Covers inner-loop invariant-closure plumbing and rewritten-iterator ref
/// temps, which are re-created inside every iteration.
fn local_is_iteration_scoped(
    body: &MutableBody,
    region: &BTreeSet<usize>,
    switch_bb: usize,
    local: usize,
) -> bool {
    // ── Guard 2: no observation outside the region ───────────────────────
    for (bb, block) in body.blocks().iter().enumerate() {
        if region.contains(&bb) {
            continue;
        }
        for stmt in &block.statements {
            let (reads, _defines) = statement_reads_defines(&stmt.kind, local);
            if reads {
                return false;
            }
        }
        let (reads, _defines) = terminator_reads_defines(&block.terminator.kind, local);
        if reads {
            return false;
        }
    }

    // ── Guard 1: write-before-read dataflow inside the region ────────────
    // in-state: true = "maybe unwritten since the switch" (join = OR; the
    // switch entry is pinned to unwritten so back-edge flow never counts a
    // previous-iteration write as a definition).
    let mut in_unwritten: HashMap<usize, bool> = HashMap::new();
    in_unwritten.insert(switch_bb, true);
    let mut worklist: Vec<usize> = vec![switch_bb];
    let mut fuel = region.len() * region.len() + 64;
    while let Some(bb) = worklist.pop() {
        if fuel == 0 {
            return false; // fail closed on analysis budget
        }
        fuel -= 1;
        let mut unwritten = *in_unwritten.get(&bb).unwrap_or(&true);
        let block = &body.blocks()[bb];
        for stmt in &block.statements {
            // Reads are checked before the write takes effect, so a
            // self-referential `L = f(L)` counts as a read of the old value.
            let (reads, defines) = statement_reads_defines(&stmt.kind, local);
            if reads && unwritten {
                return false;
            }
            if defines {
                unwritten = false;
            }
        }
        let (term_reads, term_defines) = terminator_reads_defines(&block.terminator.kind, local);
        if term_reads && unwritten {
            return false;
        }
        if term_defines {
            unwritten = false;
        }
        for succ in block.terminator.successors() {
            if succ == switch_bb || !region.contains(&succ) {
                continue; // switch entry is pinned; exits are guarded above.
            }
            match in_unwritten.get_mut(&succ) {
                Some(existing) => {
                    if unwritten && !*existing {
                        *existing = true;
                        worklist.push(succ);
                    }
                }
                None => {
                    in_unwritten.insert(succ, unwritten);
                    worklist.push(succ);
                }
            }
        }
    }
    true
}

/// (reads, defines) of `local` by one statement. A projected write
/// (`L.f = ...` / `L[i] = ...`) reads AND does not define (the rest of the
/// local keeps its old value).
fn statement_reads_defines(kind: &StatementKind, local: usize) -> (bool, bool) {
    match kind {
        StatementKind::Assign(place, rv) => {
            let mut reads =
                rvalue_reads_local(rv, local) || place_reads_local_via_projection(place, local);
            let mut defines = false;
            if place.local == local {
                if place.projection.is_empty() {
                    defines = true;
                } else {
                    reads = true;
                }
            }
            (reads, defines)
        }
        StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => (false, false),
        other => {
            let mut mentioned = BTreeSet::new();
            collect_stmt_kind_locals(other, &mut mentioned);
            (mentioned.contains(&local), false)
        }
    }
}

/// Whether a place expression READS `local` (base of a projected place used
/// as an rvalue source, or an `Index(local)` projection).
fn place_reads_local_via_projection(place: &Place, local: usize) -> bool {
    place.projection.iter().any(|elem| matches!(elem, ProjectionElem::Index(l) if *l == local))
}

/// Whether an rvalue reads `local` through any operand or place.
fn rvalue_reads_local(rv: &Rvalue, local: usize) -> bool {
    fn place_reads(place: &Place, local: usize) -> bool {
        place.local == local || place_reads_local_via_projection(place, local)
    }
    fn op_reads(op: &Operand, local: usize) -> bool {
        matches!(op, Operand::Copy(p) | Operand::Move(p) if place_reads(p, local))
    }
    match rv {
        Rvalue::Use(op)
        | Rvalue::Repeat(op, _)
        | Rvalue::Cast(_, op, _)
        | Rvalue::UnaryOp(_, op)
        | Rvalue::ShallowInitBox(op, _) => op_reads(op, local),
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            op_reads(a, local) || op_reads(b, local)
        }
        Rvalue::Ref(_, _, p)
        | Rvalue::AddressOf(_, p)
        | Rvalue::Len(p)
        | Rvalue::CopyForDeref(p)
        | Rvalue::Discriminant(p) => place_reads(p, local),
        Rvalue::Aggregate(_, ops) => ops.iter().any(|op| op_reads(op, local)),
        Rvalue::NullaryOp(..) | Rvalue::ThreadLocalRef(..) => false,
    }
}

/// Locals mentioned by a non-Assign, non-storage statement kind.
fn collect_stmt_kind_locals(kind: &StatementKind, out: &mut BTreeSet<usize>) {
    fn place_locals(place: &Place, out: &mut BTreeSet<usize>) {
        out.insert(place.local);
        for elem in &place.projection {
            if let ProjectionElem::Index(l) = elem {
                out.insert(*l);
            }
        }
    }
    fn op_locals(op: &Operand, out: &mut BTreeSet<usize>) {
        if let Operand::Copy(p) | Operand::Move(p) = op {
            place_locals(p, out);
        }
    }
    match kind {
        // Assign is handled by `statement_reads_defines` directly; if this
        // collector is ever handed one, be conservative: mention everything.
        StatementKind::Assign(place, rv) => {
            place_locals(place, out);
            match rv {
                Rvalue::Use(op)
                | Rvalue::Repeat(op, _)
                | Rvalue::Cast(_, op, _)
                | Rvalue::UnaryOp(_, op)
                | Rvalue::ShallowInitBox(op, _) => op_locals(op, out),
                Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                    op_locals(a, out);
                    op_locals(b, out);
                }
                Rvalue::Ref(_, _, p)
                | Rvalue::AddressOf(_, p)
                | Rvalue::Len(p)
                | Rvalue::CopyForDeref(p)
                | Rvalue::Discriminant(p) => place_locals(p, out),
                Rvalue::Aggregate(_, ops) => {
                    for op in ops {
                        op_locals(op, out);
                    }
                }
                Rvalue::NullaryOp(..) | Rvalue::ThreadLocalRef(..) => {}
            }
        }
        StatementKind::SetDiscriminant { place, .. }
        | StatementKind::PlaceMention(place)
        | StatementKind::FakeRead(_, place)
        | StatementKind::Retag(_, place) => place_locals(place, out),
        StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op)) => op_locals(op, out),
        StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(c)) => {
            op_locals(&c.src, out);
            op_locals(&c.dst, out);
            op_locals(&c.count, out);
        }
        StatementKind::StorageLive(_)
        | StatementKind::StorageDead(_)
        | StatementKind::AscribeUserType { .. }
        | StatementKind::Coverage(..)
        | StatementKind::ConstEvalCounter
        | StatementKind::Nop => {}
    }
}

/// (reads, defines) of `local` by a terminator. Call destinations define on
/// the success edge; everything else only reads.
fn terminator_reads_defines(kind: &TerminatorKind, local: usize) -> (bool, bool) {
    fn place_reads(place: &Place, local: usize) -> bool {
        place.local == local || place_reads_local_via_projection(place, local)
    }
    fn op_reads(op: &Operand, local: usize) -> bool {
        matches!(op, Operand::Copy(p) | Operand::Move(p) if place_reads(p, local))
    }
    match kind {
        TerminatorKind::Call { func, args, destination, .. } => {
            let mut reads = op_reads(func, local) || args.iter().any(|a| op_reads(a, local));
            let mut defines = false;
            if destination.local == local {
                if destination.projection.is_empty() {
                    defines = true;
                } else {
                    reads = true;
                }
            } else if place_reads_local_via_projection(destination, local) {
                reads = true;
            }
            (reads, defines)
        }
        TerminatorKind::SwitchInt { discr, .. } => (op_reads(discr, local), false),
        TerminatorKind::Assert { cond, .. } => (op_reads(cond, local), false),
        TerminatorKind::Drop { place, .. } => (place_reads(place, local), false),
        TerminatorKind::Return => (local == 0, false),
        _ => (false, false),
    }
}

/// Blocks reachable from the function entry (bb0).
/// Blocks from which a `Return` terminator is reachable (reverse BFS),
/// mirroring the CHC encoder's relation-retention criterion
/// (`compute_return_reachable_blocks`). Task #70.
fn return_reachable_blocks(body: &MutableBody) -> BTreeSet<usize> {
    let n = body.blocks().len();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut work: Vec<usize> = Vec::new();
    for (bb, block) in body.blocks().iter().enumerate() {
        for succ in block.terminator.successors() {
            if succ < n {
                preds[succ].push(bb);
            }
        }
        if matches!(block.terminator.kind, TerminatorKind::Return) {
            work.push(bb);
        }
    }
    let mut reach = BTreeSet::new();
    while let Some(bb) = work.pop() {
        if reach.insert(bb) {
            work.extend(preds[bb].iter().copied());
        }
    }
    reach
}

fn reachable_blocks(body: &MutableBody) -> BTreeSet<usize> {
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut stack = vec![0usize];
    while let Some(bb) = stack.pop() {
        if !seen.insert(bb) {
            continue;
        }
        stack.extend(body.blocks()[bb].terminator.successors());
    }
    seen
}

/// Rewrite every `old` target of `term` to `new` (Goto/Call/Assert/Drop/
/// SwitchInt edges). Used to redirect the loop-entry edge into the rule chain.
fn retarget_terminator(term: &mut Terminator, old: usize, new: usize) {
    match &mut term.kind {
        TerminatorKind::Goto { target } => {
            if *target == old {
                *target = new;
            }
        }
        TerminatorKind::Call { target, .. } => {
            if *target == Some(old) {
                *target = Some(new);
            }
        }
        TerminatorKind::Assert { target, .. } | TerminatorKind::Drop { target, .. } => {
            if *target == old {
                *target = new;
            }
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            let new_branches: Vec<_> =
                targets.branches().map(|(v, t)| (v, if t == old { new } else { t })).collect();
            let new_otherwise = if targets.otherwise() == old { new } else { targets.otherwise() };
            term.kind = TerminatorKind::SwitchInt {
                discr: discr.clone(),
                targets: SwitchTargets::new(new_branches, new_otherwise),
            };
        }
        _ => {}
    }
}

/// Natural-loop-style region of the (already transformed) contracted loop:
/// `{switch}` plus every block that reaches the latch register block without
/// passing through `switch` (reverse BFS from `reg_bb`, not expanding
/// `switch`'s predecessors).
fn loop_region(body: &MutableBody, switch_bb: usize, reg_bb: usize) -> BTreeSet<usize> {
    let mut preds: HashMap<usize, Vec<usize>> = HashMap::new();
    for (bb, block) in body.blocks().iter().enumerate() {
        for succ in block.terminator.successors() {
            preds.entry(succ).or_default().push(bb);
        }
    }
    let mut region: BTreeSet<usize> = BTreeSet::new();
    region.insert(switch_bb);
    let mut stack = vec![reg_bb];
    while let Some(bb) = stack.pop() {
        if !region.insert(bb) {
            continue;
        }
        if let Some(ps) = preds.get(&bb) {
            stack.extend(ps.iter().copied());
        }
    }
    region
}

/// Whether an enclosing loop's post-havoc execution can enter `target_region`
/// while `local` still carries its arbitrary havoc value.
///
/// Whole-local statement assignments re-initialize before every outgoing edge.
/// A call destination is initialized only on its normal return edge, never on
/// an unwind edge. Writes in the target region itself are deliberately too
/// late: the inner rule's entry boundary is already being crossed.
fn capture_has_write_free_path_to_region(
    body: &MutableBody,
    successors: &[Vec<usize>],
    start: usize,
    enclosing_region: &BTreeSet<usize>,
    target_region: &BTreeSet<usize>,
    local: usize,
) -> bool {
    let mut reinitialized_blocks = BTreeSet::new();
    let mut reinitialized_edges = BTreeSet::new();
    for &bb in enclosing_region {
        let block = &body.blocks()[bb];
        if block.statements.iter().any(|statement| {
            matches!(
                &statement.kind,
                StatementKind::Assign(place, _) if place.local == local && place.projection.is_empty()
            )
        }) {
            reinitialized_blocks.insert(bb);
        }
        if let TerminatorKind::Call { destination, target: Some(target), unwind, .. } =
            &block.terminator.kind
            && destination.local == local
            && destination.projection.is_empty()
            // The graph key cannot distinguish two edges with the same target.
            // If an unusual MIR call shares its normal and cleanup target, the
            // cleanup edge has no initialized destination and must win.
            && call_normal_return_definitely_initializes(unwind, *target)
        {
            reinitialized_edges.insert((bb, *target));
        }
    }
    write_free_path_reaches_region(
        successors,
        start,
        enclosing_region,
        target_region,
        &reinitialized_blocks,
        &reinitialized_edges,
    )
}

fn call_normal_return_definitely_initializes(unwind: &UnwindAction, target: usize) -> bool {
    !matches!(unwind, UnwindAction::Cleanup(cleanup) if *cleanup == target)
}

/// Pure graph core for the nested-loop re-initialization gate. `true` means a
/// path reaches the target before crossing a proven re-initialization and the
/// inner rule must therefore be skipped.
fn write_free_path_reaches_region(
    successors: &[Vec<usize>],
    start: usize,
    enclosing_region: &BTreeSet<usize>,
    target_region: &BTreeSet<usize>,
    reinitialized_blocks: &BTreeSet<usize>,
    reinitialized_edges: &BTreeSet<(usize, usize)>,
) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![start];
    while let Some(bb) = stack.pop() {
        if !seen.insert(bb) {
            continue;
        }
        if target_region.contains(&bb) {
            return true;
        }
        if !enclosing_region.contains(&bb) || reinitialized_blocks.contains(&bb) {
            continue;
        }
        let Some(block_successors) = successors.get(bb) else {
            // Malformed indices are not evidence of mandatory initialization.
            return true;
        };
        for &successor in block_successors {
            if reinitialized_edges.contains(&(bb, successor)) {
                continue;
            }
            if target_region.contains(&successor) {
                return true;
            }
            if enclosing_region.contains(&successor) {
                stack.push(successor);
            }
        }
    }
    false
}

/// Map from local to its unique whole-place `Rvalue` assignment. Locals that
/// are assigned more than once, through projections, or by calls resolve to
/// nothing (chains through them bail out).
fn build_single_def_map(body: &MutableBody) -> HashMap<usize, Rvalue> {
    let mut defs: HashMap<usize, Rvalue> = HashMap::new();
    let mut multi: BTreeSet<usize> = BTreeSet::new();
    for block in body.blocks() {
        for stmt in &block.statements {
            if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                if place.projection.is_empty() {
                    if multi.contains(&place.local) {
                        continue;
                    }
                    if defs.insert(place.local, rvalue.clone()).is_some() {
                        defs.remove(&place.local);
                        multi.insert(place.local);
                    }
                } else {
                    defs.remove(&place.local);
                    multi.insert(place.local);
                }
            }
        }
        if let TerminatorKind::Call { destination, .. } = &block.terminator.kind {
            defs.remove(&destination.local);
            multi.insert(destination.local);
        }
    }
    defs
}

/// Resolve a pointer-typed local back to the base LOCAL it points into
/// (`&x`, `&mut x`, `&raw mut x`, `&mut x.field`, reborrows, casts, copies).
/// Returns `None` when the chain leaves locals (heap, statics, arguments of
/// pointer type, multi-assigned pointers).
fn resolve_mut_pointer_base(
    body: &MutableBody,
    defs: &HashMap<usize, Rvalue>,
    pointer_local: usize,
    fuel: usize,
) -> Option<usize> {
    if fuel == 0 {
        return None;
    }
    match defs.get(&pointer_local)? {
        Rvalue::Ref(_, _, target) | Rvalue::AddressOf(_, target) => {
            match target.projection.first() {
                // Reborrow `&mut *p` / `&raw mut *p`: continue through `p`.
                Some(ProjectionElem::Deref) => {
                    if target.projection.len() == 1 {
                        resolve_mut_pointer_base(body, defs, target.local, fuel - 1)
                    } else {
                        None
                    }
                }
                // `&mut x` or `&mut x.field` / `&mut x[i]`: base local x.
                _ => Some(target.local),
            }
        }
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projection.is_empty() => {
            resolve_mut_pointer_base(body, defs, p.local, fuel - 1)
        }
        Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) if p.projection.is_empty() => {
            resolve_mut_pointer_base(body, defs, p.local, fuel - 1)
        }
        _ => None,
    }
}

/// A type is havocable as a plain VALUE: nondet of the local's sort covers all
/// runtime behaviors (no indirection, no interior mutability, no drop glue).
fn is_plain_value_ty(ty: Ty, fuel: usize) -> bool {
    if fuel == 0 {
        return false;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Bool)
        | TyKind::RigidTy(RigidTy::Char)
        | TyKind::RigidTy(RigidTy::Int(_))
        | TyKind::RigidTy(RigidTy::Uint(_))
        | TyKind::RigidTy(RigidTy::Float(_)) => true,
        TyKind::RigidTy(RigidTy::Tuple(tys)) => tys.iter().all(|t| is_plain_value_ty(*t, fuel - 1)),
        TyKind::RigidTy(RigidTy::Array(elem, _)) => is_plain_value_ty(elem, fuel - 1),
        TyKind::RigidTy(RigidTy::Adt(def, args)) => match def.kind() {
            AdtKind::Union => false,
            AdtKind::Struct | AdtKind::Enum => {
                if def.name().contains("UnsafeCell") || def.num_variants() == 0 {
                    return false;
                }
                def.variants_iter().all(|variant| {
                    variant
                        .fields()
                        .iter()
                        .all(|field| is_plain_value_ty(field.ty_with_args(&args), fuel - 1))
                })
            }
        },
        _ => false,
    }
}

/// No writable indirection reachable through OWNED structure or shared refs:
/// rejects `&mut`, any raw pointer, `UnsafeCell`, unions, closures, trait
/// objects and anything unrecognized. Used for shared-ref pointees and
/// by-value call arguments (the callee must not be able to write into
/// caller-visible state through them).
fn no_writable_indirection(ty: Ty, fuel: usize) -> bool {
    if fuel == 0 {
        return false;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Bool)
        | TyKind::RigidTy(RigidTy::Char)
        | TyKind::RigidTy(RigidTy::Int(_))
        | TyKind::RigidTy(RigidTy::Uint(_))
        | TyKind::RigidTy(RigidTy::Float(_))
        | TyKind::RigidTy(RigidTy::Str)
        | TyKind::RigidTy(RigidTy::Never)
        | TyKind::RigidTy(RigidTy::FnDef(..)) => true,
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            tys.iter().all(|t| no_writable_indirection(*t, fuel - 1))
        }
        TyKind::RigidTy(RigidTy::Array(elem, _)) | TyKind::RigidTy(RigidTy::Slice(elem)) => {
            no_writable_indirection(elem, fuel - 1)
        }
        // Shared refs are read-only; nested `&mut` behind `&` is unwritable.
        // Still reject interior mutability in the pointee (transitively).
        TyKind::RigidTy(RigidTy::Ref(_, pointee, Mutability::Not)) => {
            no_writable_indirection(pointee, fuel - 1)
        }
        TyKind::RigidTy(RigidTy::Ref(_, _, Mutability::Mut))
        | TyKind::RigidTy(RigidTy::RawPtr(..)) => false,
        TyKind::RigidTy(RigidTy::Adt(def, args)) => match def.kind() {
            AdtKind::Union => false,
            AdtKind::Struct | AdtKind::Enum => {
                if def.name().contains("UnsafeCell") {
                    return false;
                }
                def.variants_iter().all(|variant| {
                    variant
                        .fields()
                        .iter()
                        .all(|field| no_writable_indirection(field.ty_with_args(&args), fuel - 1))
                })
            }
        },
        _ => false,
    }
}

/// A call to one of the loop-contract library's `KaniIter` adapters that
/// provably only READS through its `&self` argument, so it cannot widen the
/// loop's frame beyond its (already havocked) destination.
///
/// This is deliberately NOT "the `KaniIter` trait is pure". `KaniMapIter`
/// breaks that: its `nth`/`first` do
///
/// ```text
/// let map_ptr = &self.map as *const F as *mut F;
/// unsafe { (*map_ptr)(item) }
/// ```
///
/// — they call an `FnMut` through a `*const -> *mut` cast on a shared `&self`,
/// so stepping a mapped iterator can mutate the closure's captured state.
/// The exemption is therefore split:
///
/// * `assumption` / `len` — read-only for EVERY adapter in the library. Each
///   impl either returns a field or recurses into the inner adapter's
///   `assumption`/`len`; none touches a mapped closure. Self is unrestricted.
/// * `nth` / `first` — read-only only for the adapters listed below, and only
///   when every adapter they are built from is also on the list.
///
/// Everything else — `KaniMapIter`, a user impl of the public `KaniIter`
/// trait, an adapter added later — is not matched, and the loop keeps the
/// legacy encoding exactly as before. Adding an adapter to the list without
/// reading its body would be an unsoundness: an unhavocked loop-modified
/// location makes the invariant obligations prove too much.
fn readonly_kani_iter_shim(callee: &str, genargs: &GenericArgs) -> bool {
    let Some(method) = callee.strip_prefix("kani::KaniIter::") else {
        return false;
    };
    match method {
        "assumption" | "len" => true,
        "nth" | "first" => genargs
            .0
            .iter()
            .filter_map(|a| match a {
                GenericArgKind::Type(t) => Some(*t),
                _ => None,
            })
            .all(|t| kani_iter_adapter_is_readonly(t, 8)),
        _ => false,
    }
}

/// Recursive membership test for `readonly_kani_iter_shim`'s `nth`/`first`
/// arm: an adapter whose element step only reads, built only from such
/// adapters. Type arguments that are not adapters must themselves carry no
/// writable indirection (the element type).
fn kani_iter_adapter_is_readonly(ty: Ty, fuel: usize) -> bool {
    if fuel == 0 {
        return false;
    }
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
        return no_writable_indirection(ty, fuel - 1);
    };
    let name = def.name();
    let admitted = matches!(
        name.as_str(),
        "kani::KaniPtrIter"
            | "kani::KaniRefIter"
            | "kani::KaniStepBy"
            | "kani::KaniChainIter"
            | "kani::KaniZipIter"
            | "kani::KaniEnumerateIter"
            | "kani::KaniTakeIter"
            | "kani::KaniRevIter"
            | "core::ops::Range"
            | "std::ops::Range"
    );
    if !admitted {
        // Not an adapter we have read: fall back to the generic rule, which
        // accepts a plain element type and rejects anything with writable
        // indirection (including `kani::KaniMapIter`).
        return no_writable_indirection(ty, fuel - 1);
    }
    args.0.iter().all(|a| match a {
        GenericArgKind::Type(t) => kani_iter_adapter_is_readonly(*t, fuel - 1),
        _ => true,
    })
}

/// Kani-internal fn markers whose calls only write their destination — safe
/// to treat as frame-pure during the loop store scan. Anything not on this
/// list fail-closes the loop (e.g. `write_any*`, which mutates a pointee).
fn kani_marker_is_frame_pure(marker: &str) -> bool {
    matches!(
        marker,
        "kani_register_loop_contract"
            | "AssumeHook"
            | "AssertHook"
            | "CheckHook"
            | "CoverHook"
            | "SafetyCheckHook"
            | "SafetyCheckNoAssumeHook"
            | "UnsupportedCheckHook"
            | "PanicHook"
            | "PanicStub"
            | "AnyModifiesIntrinsic"
            | "AnyModel"
            | "AnyRawHook"
            | "InitContractsHook"
            | "ModifiesFrameEnterHook"
            | "ModifiesFrameExitHook"
    )
}

#[cfg(test)]
mod nested_reinitialization_tests {
    use super::{call_normal_return_definitely_initializes, write_free_path_reaches_region};
    use rustc_public::mir::UnwindAction;
    use std::collections::BTreeSet;

    fn nodes(values: &[usize]) -> BTreeSet<usize> {
        values.iter().copied().collect()
    }

    fn edges(values: &[(usize, usize)]) -> BTreeSet<(usize, usize)> {
        values.iter().copied().collect()
    }

    #[test]
    fn unrelated_or_non_dominating_writes_do_not_authenticate_reinitialization() {
        // The write in block 2 is after entry into target block 1.
        let after_target = vec![vec![1], vec![2], vec![]];
        assert!(write_free_path_reaches_region(
            &after_target,
            0,
            &nodes(&[0, 1, 2]),
            &nodes(&[1]),
            &nodes(&[2]),
            &BTreeSet::new(),
        ));

        // A sibling branch writes, but the other path reaches the target with
        // the havoc value untouched.
        let sibling = vec![vec![1, 2], vec![3], vec![3], vec![]];
        assert!(write_free_path_reaches_region(
            &sibling,
            0,
            &nodes(&[0, 1, 2, 3]),
            &nodes(&[3]),
            &nodes(&[1]),
            &BTreeSet::new(),
        ));
    }

    #[test]
    fn every_reaching_path_must_cross_a_reinitialization() {
        let branches = vec![vec![1, 2], vec![3], vec![3], vec![]];
        assert!(!write_free_path_reaches_region(
            &branches,
            0,
            &nodes(&[0, 1, 2, 3]),
            &nodes(&[3]),
            &nodes(&[1, 2]),
            &BTreeSet::new(),
        ));

        // A call destination is initialized on the normal return edge.
        let call = vec![vec![1], vec![]];
        assert!(!write_free_path_reaches_region(
            &call,
            0,
            &nodes(&[0, 1]),
            &nodes(&[1]),
            &BTreeSet::new(),
            &edges(&[(0, 1)]),
        ));
    }

    #[test]
    fn call_destination_requires_a_distinct_normal_return_edge() {
        assert!(call_normal_return_definitely_initializes(&UnwindAction::Terminate, 1));
        assert!(call_normal_return_definitely_initializes(&UnwindAction::Cleanup(2), 1));
        assert!(!call_normal_return_definitely_initializes(&UnwindAction::Cleanup(1), 1));
    }

    #[test]
    fn pre_havoc_source_head_write_is_not_reused_after_havoc() {
        // Block 0 models the source head that ran before havoc. The post-havoc
        // tail starts at block 1, so block 0's assignment cannot authenticate
        // the path to the inner boundary.
        let cfg = vec![vec![1], vec![2], vec![]];
        assert!(write_free_path_reaches_region(
            &cfg,
            1,
            &nodes(&[0, 1, 2]),
            &nodes(&[2]),
            &nodes(&[0]),
            &BTreeSet::new(),
        ));
    }
}
