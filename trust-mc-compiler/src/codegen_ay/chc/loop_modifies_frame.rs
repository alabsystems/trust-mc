// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FC-29: loop `assigns` clause enforcement (`#[kani::loop_modifies(...)]`).
//!
//! The `loop_modifies` macro lowers the clause to a debug-named local:
//! `let kani_loop_modifies = (e0, e1, ...);` placed immediately before the
//! loop (mirroring upstream Kani, which recognizes the same local by debug
//! name and hands the tuple to CBMC's DFCC assigns checking). trust-mc has
//! no CBMC, so this module enforces the clause on the CHC path:
//!
//! 1. `prescan_loop_modifies_frames` (runs before rule generation, both
//!    small-step and large-step fragment modes):
//!    * finds each `kani_loop_modifies` local via `var_debug_info`,
//!    * resolves every tuple element back to a *declared coverage* — a base
//!      local plus a covered byte prefix — by walking single-assignment def
//!      chains (`&x`, `&raw const *r`, unsize casts, `as_ptr` calls,
//!      `slice_from_raw_parts` / raw-pointer aggregates with constant length),
//!    * associates the clause with the loop that follows it (first natural
//!      loop header reachable forward from the tuple assignment) and records
//!      the loop's block region (natural loop of its back edges).
//! 2. `loop_modifies_store_check` (hooked from the `Assign` statement path in
//!    `encode_block_statements`): every register-level store in a loop-region
//!    block whose base is a user-visible local declared *outside* the loop
//!    must be covered by the clause. Violations push a fail-if-false pending
//!    check (same mechanism as FC-06 / memory-safety checks), which both rule
//!    generation modes lower to an `error`-reachability rule — the CBMC
//!    "Check that <place> is assignable" equivalent.
//!
//! Precision notes (documented FC-29 limits):
//! * Fail-open by design: if ANY tuple element cannot be resolved, the whole
//!   frame is dropped (no checks) — never a false positive.
//! * Only direct local writes (`x = ...`) and single-index array writes
//!   (`a[i] = ...`, `a[k of n] = ...`) are checked. Deref stores (`*p = ...`)
//!   take the heap/ref-target store paths and are not yet checked against
//!   loop frames (deferred; FC-06 covers them for function contracts).
//! * Compiler temporaries (no debug name), `kani_*` internals, and locals
//!   whose storage begins inside the loop (loop-local `let`s) are exempt,
//!   matching DFCC loop-local semantics.

use std::collections::{HashMap, HashSet};

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{
    AggregateKind, Body, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
    VarDebugInfoContents,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use super::ChcCtx;
use crate::codegen_ay::loop_unroll::{Cfg, find_loop_headers};

/// One enforced loop-assigns frame: a loop region plus declared coverage.
pub(in crate::codegen_ay::chc) struct LoopModifiesFrame {
    /// Blocks inside the loop region (natural loop of the header's back edges).
    pub blocks: HashSet<usize>,
    /// Declared coverage: base local -> covered byte prefix `[0, bytes)`.
    pub coverage: HashMap<usize, u64>,
    /// User-visible locals subject to checking (declared outside the loop,
    /// not `kani_*` internals).
    pub checked_locals: HashSet<usize>,
}

/// Where a single-assignment local gets its value.
enum DefSite<'a> {
    /// `local = <rvalue>` statement.
    Rv(&'a Rvalue),
    /// `local = call(args...)` terminator (callee name, args).
    Call(String, &'a [Operand]),
}

/// Build a map from local -> unique definition site. Locals assigned more
/// than once (or via projections) are excluded — chains through them bail out.
fn build_def_map(body: &Body) -> HashMap<usize, DefSite<'_>> {
    let mut defs: HashMap<usize, DefSite<'_>> = HashMap::new();
    let mut multi: HashSet<usize> = HashSet::new();
    fn record<'a>(
        local: usize,
        site: DefSite<'a>,
        defs: &mut HashMap<usize, DefSite<'a>>,
        multi: &mut HashSet<usize>,
    ) {
        if multi.contains(&local) {
            return;
        }
        if defs.insert(local, site).is_some() {
            defs.remove(&local);
            multi.insert(local);
        }
    }
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                if place.projection.is_empty() {
                    record(place.local, DefSite::Rv(rvalue), &mut defs, &mut multi);
                } else {
                    // A projected write makes the local multi-defined for our purposes.
                    defs.remove(&place.local);
                    multi.insert(place.local);
                }
            }
        }
        if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind {
            if destination.projection.is_empty() {
                let callee = func
                    .ty(body.locals())
                    .ok()
                    .and_then(|t| t.kind().fn_def().map(|(def, _)| def.name()))
                    .unwrap_or_default();
                record(destination.local, DefSite::Call(callee, args), &mut defs, &mut multi);
            }
        }
    }
    defs
}

/// Result of walking a declared-element pointer chain.
struct PtrOrigin {
    /// Base local the pointer points into (at offset 0).
    base_local: usize,
    /// Element count for fat pointers, when statically known.
    len_elems: Option<u64>,
}

/// Resolve a `usize` operand to a constant by chasing `Use` chains.
fn resolve_const_usize(
    defs: &HashMap<usize, DefSite<'_>>,
    op: &Operand,
    fuel: usize,
) -> Option<u64> {
    if fuel == 0 {
        return None;
    }
    match op {
        Operand::Constant(c) => c.const_.eval_target_usize().ok(),
        Operand::Copy(p) | Operand::Move(p) => {
            if !p.projection.is_empty() {
                return None;
            }
            match defs.get(&p.local)? {
                DefSite::Rv(Rvalue::Use(inner)) => resolve_const_usize(defs, inner, fuel - 1),
                _ => None,
            }
        }
    }
}

/// Walk the def chain of a pointer-typed operand back to its base local.
///
/// Supported links (grounded in the corpus MIR shapes):
/// * `&place` / `&raw const place` with empty projection -> base local
///   (records the array element count when the place is an array, so a later
///   unsize cast covers the whole array);
/// * `&raw const (*r)` -> continue through `r`'s chain;
/// * `Use` / `Cast` passthrough;
/// * `*const [T] from (data, len)` raw-pointer aggregate -> data chain with
///   constant `len`;
/// * `as_ptr` / `as_mut_ptr` / `slice_from_raw_parts` calls.
fn resolve_ptr_chain(
    body: &Body,
    defs: &HashMap<usize, DefSite<'_>>,
    op: &Operand,
    fuel: usize,
) -> Option<PtrOrigin> {
    if fuel == 0 {
        return None;
    }
    let place = match op {
        Operand::Copy(p) | Operand::Move(p) => p,
        Operand::Constant(_) => return None,
    };
    if !place.projection.is_empty() {
        return None;
    }
    match defs.get(&place.local)? {
        DefSite::Rv(rvalue) => match rvalue {
            Rvalue::Ref(_, _, target) | Rvalue::AddressOf(_, target) => {
                match target.projection.as_slice() {
                    [] => {
                        // Direct `&x`: element count from x's type when it's an array.
                        let len_elems = match body.locals()[target.local].ty.kind() {
                            TyKind::RigidTy(RigidTy::Array(_, len)) => len.eval_target_usize().ok(),
                            _ => None,
                        };
                        Some(PtrOrigin { base_local: target.local, len_elems })
                    }
                    // `&raw const (*r)`: reborrow — continue through r.
                    [ProjectionElem::Deref] => resolve_ptr_chain(
                        body,
                        defs,
                        &Operand::Copy(Place { local: target.local, projection: vec![] }),
                        fuel - 1,
                    ),
                    _ => None,
                }
            }
            Rvalue::Use(inner) => resolve_ptr_chain(body, defs, inner, fuel - 1),
            Rvalue::Cast(_, inner, _) => resolve_ptr_chain(body, defs, inner, fuel - 1),
            Rvalue::Aggregate(AggregateKind::RawPtr(_, _), ops) if ops.len() == 2 => {
                let data = resolve_ptr_chain(body, defs, &ops[0], fuel - 1)?;
                let len = resolve_const_usize(defs, &ops[1], fuel)?;
                Some(PtrOrigin { base_local: data.base_local, len_elems: Some(len) })
            }
            _ => None,
        },
        DefSite::Call(callee, args) => {
            if callee.ends_with("::as_ptr") || callee.ends_with("::as_mut_ptr") {
                // Thin pointer to the first element; base identity carries over.
                let inner = resolve_ptr_chain(body, defs, args.first()?, fuel - 1)?;
                Some(PtrOrigin { base_local: inner.base_local, len_elems: inner.len_elems })
            } else if callee.contains("slice_from_raw_parts") {
                let data = resolve_ptr_chain(body, defs, args.first()?, fuel - 1)?;
                let len = resolve_const_usize(defs, args.get(1)?, fuel)?;
                Some(PtrOrigin { base_local: data.base_local, len_elems: Some(len) })
            } else {
                None
            }
        }
    }
}

/// Natural loop region of `header`: `{header}` plus all blocks that reach a
/// latch without passing through the header (reverse DFS from each latch).
fn natural_loop_region(cfg: &Cfg, header: usize, latches: &[usize]) -> HashSet<usize> {
    let mut region: HashSet<usize> = HashSet::new();
    region.insert(header);
    let mut stack: Vec<usize> = latches.to_vec();
    while let Some(bb) = stack.pop() {
        if bb == header || !region.insert(bb) {
            continue;
        }
        stack.extend(cfg.predecessors[bb].iter().copied());
    }
    region
}

/// A loop rewritten by the #47 loop-contract proof rule: the back edge is CUT
/// (the CHC system is acyclic), so `find_loop_headers` no longer sees it. The
/// rule leaves register-call breadcrumbs — `kani_register_loop_contract` calls
/// whose `_transformed` argument encodes the site (2 = base/entry, 1 = latch)
/// and whose closure-ref argument is the same local at both sites of one
/// loop — from which the one-iteration region is recovered so loop-assigns
/// enforcement keeps working.
struct RuleLoopFrame {
    /// Block ending with the base-site register call (the rewritten loop head).
    base_bb: usize,
    /// Blocks of the one symbolic iteration (reverse-reach of the latch
    /// register block, stopping at — and excluding — `base_bb`).
    region: HashSet<usize>,
}

/// Collect rule-instrumented loops from register-call breadcrumbs.
fn collect_rule_loop_frames(body: &Body, cfg: &Cfg) -> Vec<RuleLoopFrame> {
    // closure-ref local -> (base_bb, latch_bb)
    let mut groups: HashMap<usize, (Option<usize>, Option<usize>)> = HashMap::new();
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else { continue };
        if args.len() < 2 {
            continue;
        }
        let is_register = func
            .ty(body.locals())
            .ok()
            .and_then(|t| t.kind().fn_def().map(|(def, _)| def.name()))
            .is_some_and(|name| name.contains("kani_register_loop_contract"));
        if !is_register {
            continue;
        }
        let (Operand::Copy(closure_place) | Operand::Move(closure_place)) = &args[0] else {
            continue;
        };
        if !closure_place.projection.is_empty() {
            continue;
        }
        let Some(role) = (match &args[1] {
            Operand::Constant(c) => c.const_.eval_target_usize().ok(),
            _ => None,
        }) else {
            continue;
        };
        let entry = groups.entry(closure_place.local).or_default();
        match role {
            2 => entry.0 = Some(bb_idx),
            1 => entry.1 = Some(bb_idx),
            _ => {}
        }
    }

    let mut frames = Vec::new();
    for (base_bb, latch_bb) in groups.into_values() {
        let (Some(base_bb), Some(latch_bb)) = (base_bb, latch_bb) else { continue };
        // One-iteration region: reverse-reach of the latch register block,
        // stopping at (and excluding) the rewritten head. The included pieces
        // of the head chain (havoc/assume blocks) only store compiler temps,
        // which the checked-locals filter already exempts.
        let mut region: HashSet<usize> = HashSet::new();
        let mut stack = vec![latch_bb];
        while let Some(bb) = stack.pop() {
            if bb == base_bb || !region.insert(bb) {
                continue;
            }
            stack.extend(cfg.predecessors[bb].iter().copied());
        }
        frames.push(RuleLoopFrame { base_bb, region });
    }
    frames
}

/// Wall-2 honesty prescan: a `kani_register_loop_contract` breadcrumb whose
/// `_transformed` argument carries the NESTED-LEGACY sentinel marks a nested
/// inner loop deliberately left on the legacy encoding because its invariant
/// reads outer-havocked state (`rule.rs::TRANSFORMED_NESTED_LEGACY`). That
/// combination is over-approximate by construction, so record a fail-closed
/// demotion: any CTREX from this body classifies OverApproximation (never
/// Genuine) and any PROOF demotes — restoring the pre-Wall-2 honest
/// attribution the resolved invariant evaluations no longer provide.
pub(in crate::codegen_ay::chc) fn prescan_loop_rule_nested_legacy_demotion(
    ctx: &mut ChcCtx<'_, '_>,
) {
    let sentinel = crate::kani_middle::transform::loop_contracts::TRANSFORMED_NESTED_LEGACY as u64;
    let mut hits = 0usize;
    for block in &ctx.body.blocks {
        let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else { continue };
        if args.len() < 2 {
            continue;
        }
        let is_register = func
            .ty(ctx.body.locals())
            .ok()
            .and_then(|t| t.kind().fn_def().map(|(def, _)| def.name()))
            .is_some_and(|name| name.contains("kani_register_loop_contract"));
        if !is_register {
            continue;
        }
        let role = match &args[1] {
            Operand::Constant(c) => c.const_.eval_target_usize().ok(),
            _ => None,
        };
        if role == Some(sentinel) {
            hits += 1;
        }
    }
    for _ in 0..hits {
        ctx.record_sound_fallback_reason("loop_rule_nested_inner_legacy");
    }
    if hits > 0 {
        debug!(hits, "Wall-2: nested-legacy loop sentinel found — demoting (fail-closed)");
    }
}

/// Pre-scan the body for `kani_loop_modifies` clauses and build enforcement
/// frames. Runs from `generate_transition_rules` (both step modes) before any
/// block is encoded.
pub(in crate::codegen_ay::chc) fn prescan_loop_modifies_frames(ctx: &mut ChcCtx<'_, '_>) {
    let body = ctx.body;

    // Fast path: no loop_modifies locals in this body.
    let modifies_locals: Vec<usize> = body
        .var_debug_info
        .iter()
        .filter_map(|vdi| {
            if !vdi.name.as_str().contains("kani_loop_modifies") {
                return None;
            }
            match &vdi.value {
                VarDebugInfoContents::Place(p) if p.projection.is_empty() => Some(p.local),
                _ => None,
            }
        })
        .collect();
    if modifies_locals.is_empty() {
        return;
    }

    let cfg = Cfg::from_body(body);
    let Ok(headers) = find_loop_headers(&cfg) else {
        debug!("FC-29: loop header analysis failed; loop assigns not enforced (fail-open)");
        return;
    };
    // #47: loops rewritten by the loop-contract proof rule are acyclic (no
    // natural headers); recover their regions from register-call breadcrumbs.
    let rule_frames = collect_rule_loop_frames(body, &cfg);
    if headers.is_empty() && rule_frames.is_empty() {
        return;
    }
    let defs = build_def_map(body);

    // User-visible locals (debug-named places, excluding kani internals).
    let user_locals: HashSet<usize> = body
        .var_debug_info
        .iter()
        .filter_map(|vdi| {
            if vdi.name.as_str().starts_with("kani") {
                return None;
            }
            match &vdi.value {
                VarDebugInfoContents::Place(p) if p.projection.is_empty() => Some(p.local),
                _ => None,
            }
        })
        .collect();

    let mut frames: Vec<LoopModifiesFrame> = Vec::new();
    for tuple_local in modifies_locals {
        // Locate the tuple assignment `_t = (e0, e1, ...)` (or single element).
        let mut assign: Option<(usize, &Rvalue)> = None;
        'outer: for (bb_idx, block) in body.blocks.iter().enumerate() {
            for stmt in &block.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind
                    && place.local == tuple_local
                    && place.projection.is_empty()
                {
                    assign = Some((bb_idx, rvalue));
                    break 'outer;
                }
            }
        }
        let Some((assign_bb, rvalue)) = assign else {
            debug!(tuple_local, "FC-29: loop_modifies tuple assignment not found (fail-open)");
            continue;
        };

        // Element operands + their declared types.
        let tuple_ty = body.locals()[tuple_local].ty;
        let elements: Vec<(Operand, Ty)> = match (rvalue, tuple_ty.kind()) {
            (
                Rvalue::Aggregate(AggregateKind::Tuple, ops),
                TyKind::RigidTy(RigidTy::Tuple(tys)),
            ) if ops.len() == tys.len() => ops.iter().cloned().zip(tys.iter().copied()).collect(),
            // Single-element clause: `let kani_loop_modifies = (&x);` is not a tuple.
            (Rvalue::Use(op), _) => vec![(op.clone(), tuple_ty)],
            (Rvalue::Ref(..) | Rvalue::AddressOf(..) | Rvalue::Cast(..), _) => {
                // The rvalue itself is the single pointer element; resolve via a
                // synthetic operand over the tuple local's def (handled below by
                // treating the tuple local as the element).
                vec![(Operand::Copy(Place { local: tuple_local, projection: vec![] }), tuple_ty)]
            }
            _ => {
                debug!(tuple_local, "FC-29: unsupported loop_modifies rvalue shape (fail-open)");
                continue;
            }
        };

        // Associate with the loop that follows: forward BFS to the first
        // natural header or #47 rule-instrumented loop head.
        enum FoundLoop {
            Natural(usize),
            Rule(usize),
        }
        let mut found: Option<FoundLoop> = None;
        {
            let mut seen: HashSet<usize> = HashSet::new();
            let mut queue: std::collections::VecDeque<usize> = [assign_bb].into();
            while let Some(bb) = queue.pop_front() {
                if !seen.insert(bb) {
                    continue;
                }
                if headers.contains_key(&bb) {
                    found = Some(FoundLoop::Natural(bb));
                    break;
                }
                if let Some(idx) = rule_frames.iter().position(|f| f.base_bb == bb) {
                    found = Some(FoundLoop::Rule(idx));
                    break;
                }
                queue.extend(cfg.successors[bb].iter().copied());
            }
        }
        let Some(found_loop) = found else {
            debug!(tuple_local, "FC-29: no loop found after loop_modifies clause (fail-open)");
            continue;
        };

        // Resolve every element; drop the whole frame if any fails (fail-open).
        let mut coverage: HashMap<usize, u64> = HashMap::new();
        let mut all_resolved = true;
        for (op, field_ty) in &elements {
            let pointee = match field_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, t, _)) | TyKind::RigidTy(RigidTy::RawPtr(t, _)) => {
                    t
                }
                _ => {
                    all_resolved = false;
                    break;
                }
            };
            let Some(origin) = resolve_ptr_chain(body, &defs, op, 16) else {
                all_resolved = false;
                break;
            };
            let bytes = match pointee.kind() {
                TyKind::RigidTy(RigidTy::Slice(elem)) => {
                    let Some(len) = origin.len_elems else {
                        all_resolved = false;
                        break;
                    };
                    let Some(es) = ctx.get_type_size(elem) else {
                        all_resolved = false;
                        break;
                    };
                    len.saturating_mul(es as u64)
                }
                TyKind::RigidTy(RigidTy::Str) => {
                    let Some(len) = origin.len_elems else {
                        all_resolved = false;
                        break;
                    };
                    len
                }
                _ => {
                    let Some(sz) = ctx.get_type_size(pointee) else {
                        all_resolved = false;
                        break;
                    };
                    sz as u64
                }
            };
            let entry = coverage.entry(origin.base_local).or_insert(0);
            *entry = (*entry).max(bytes);
        }
        if !all_resolved {
            debug!(
                tuple_local,
                "FC-29: loop_modifies element unresolved; frame dropped (fail-open)"
            );
            continue;
        }

        let (anchor_bb, blocks) = match found_loop {
            FoundLoop::Natural(header_bb) => {
                let latches = headers.get(&header_bb).cloned().unwrap_or_default();
                (header_bb, natural_loop_region(&cfg, header_bb, &latches))
            }
            FoundLoop::Rule(idx) => (rule_frames[idx].base_bb, rule_frames[idx].region.clone()),
        };

        // Exempt locals whose storage begins inside the loop (loop-locals).
        let mut exempt: HashSet<usize> = HashSet::new();
        for &bb in &blocks {
            for stmt in &body.blocks[bb].statements {
                if let StatementKind::StorageLive(local) = &stmt.kind {
                    exempt.insert(*local);
                }
            }
        }
        let checked_locals: HashSet<usize> =
            user_locals.iter().copied().filter(|l| !exempt.contains(l)).collect();

        debug!(
            tuple_local,
            anchor_bb,
            region_blocks = blocks.len(),
            coverage_entries = coverage.len(),
            checked = checked_locals.len(),
            "FC-29: enforcing loop assigns frame"
        );
        frames.push(LoopModifiesFrame { blocks, coverage, checked_locals });
    }

    if frames.is_empty() {
        return;
    }
    // Innermost frame wins per block: insert larger regions first.
    let mut order: Vec<usize> = (0..frames.len()).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(frames[i].blocks.len()));
    let mut by_bb: HashMap<usize, usize> = HashMap::new();
    for idx in order {
        for &bb in &frames[idx].blocks {
            by_bb.insert(bb, idx);
        }
    }
    ctx.loop_modifies_frames = frames;
    ctx.loop_modifies_frame_by_bb = by_bb;
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Check a register-level store `lhs = ...` against the enclosing loop's
    /// assigns clause, if any. Pushes a fail-if-false pending check (drained
    /// into `error`-reachability rules by both rule generation modes).
    pub(in crate::codegen_ay::chc) fn loop_modifies_store_check(
        &mut self,
        lhs: &Place,
        modified_locals: &HashSet<usize>,
    ) {
        if self.loop_modifies_frames.is_empty() {
            return;
        }
        let Some(&frame_idx) = self.loop_modifies_frame_by_bb.get(&self.current_encode_bb) else {
            return;
        };
        let frame = &self.loop_modifies_frames[frame_idx];
        if !frame.checked_locals.contains(&lhs.local) {
            return;
        }
        // Deref stores take the heap/ref-target paths — not checked here (fail-open).
        if matches!(lhs.projection.first(), Some(ProjectionElem::Deref)) {
            return;
        }
        let base_ty = self.body.locals()[lhs.local].ty;
        let Some(base_size) = self.get_type_size(base_ty) else {
            return;
        };
        let covered = frame.coverage.get(&lhs.local).copied();
        let Some(covered) = covered else {
            // Base local not declared at all: unconditional violation when the
            // store executes ("Check that <local> is assignable" — FAILURE).
            debug!(
                bb = self.current_encode_bb,
                local = lhs.local,
                "FC-29: store to undeclared local in loop assigns frame"
            );
            self.heap_state.pending_checks.push(Expr::bool_const(false));
            return;
        };
        if covered >= base_size as u64 {
            return; // Whole local assignable.
        }
        match lhs.projection.as_slice() {
            [] => {
                // Partial coverage cannot admit a whole-local write.
                self.heap_state.pending_checks.push(Expr::bool_const(false));
            }
            [ProjectionElem::Index(idx_local)] => {
                let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = base_ty.kind() else {
                    return; // Unsupported base shape — fail-open.
                };
                let Some(es) = self.get_type_size(elem_ty) else {
                    return;
                };
                let es = (es as u64).max(1);
                let idx_place = Place { local: *idx_local, projection: vec![] };
                let Some(idx) = self.translate_place_with_modified(&idx_place, modified_locals)
                else {
                    debug!(
                        bb = self.current_encode_bb,
                        "FC-29: index untranslatable — store not checked (fail-open)"
                    );
                    return;
                };
                let sort = idx.sort();
                let cond = if sort.is_int() {
                    idx.int_mul(Expr::int_const(es as i128))
                        .int_add(Expr::int_const(es as i128))
                        .int_le(Expr::int_const(covered as i128))
                } else if let Some(width) = sort.bitvec_width() {
                    idx.bvmul(Expr::bitvec_const(es as u128, width))
                        .bvadd(Expr::bitvec_const(es as u128, width))
                        .bvule(Expr::bitvec_const(covered as u128, width))
                } else {
                    return; // Unexpected index sort — fail-open.
                };
                debug!(
                    bb = self.current_encode_bb,
                    local = lhs.local,
                    covered,
                    "FC-29: emitted loop assigns range check for indexed store"
                );
                self.heap_state.pending_checks.push(cond);
            }
            [ProjectionElem::ConstantIndex { offset, from_end: false, .. }] => {
                let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = base_ty.kind() else {
                    return;
                };
                let Some(es) = self.get_type_size(elem_ty) else {
                    return;
                };
                let es = (es as u64).max(1);
                if offset.saturating_add(1).saturating_mul(es) > covered {
                    self.heap_state.pending_checks.push(Expr::bool_const(false));
                }
            }
            _ => {
                // Field/other projections: not yet checked (fail-open).
                debug!(
                    bb = self.current_encode_bb,
                    local = lhs.local,
                    "FC-29: unsupported store projection — not checked (fail-open)"
                );
            }
        }
    }
}
