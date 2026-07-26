// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Core MIR transformation for loop contract pass.
//!
//! This module implements the main body transformation that converts loops with
//! `kani_register_loop_contract` annotations into the split loop-head / new-latch form.
//!
//! Helper functions for pattern replacement, storage movement, and block manipulation
//! are in the sibling `rewrite` module.

use super::{ExtractedLoopInvariant, LoopContractPass};
use crate::kani_middle::KaniAttributes;
use crate::kani_middle::transform::body::{InsertPosition, MutableBody, SourceInstruction};
use crate::rustc_public::CrateDef;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::{
    AggregateKind, BasicBlock, BasicBlockIdx, Body, ConstOperand, Operand, Rvalue, Statement,
    StatementKind, SwitchTargets, Terminator, TerminatorKind, VarDebugInfoContents,
};
use rustc_public::ty::{GenericArgKind, MirConst, RigidTy, TyKind, UintTy};
use rustc_public_bridge::IndexedVal;
use rustc_span::Symbol;
use std::collections::{HashSet, VecDeque};

impl LoopContractPass {
    pub(super) fn get_loop_head_block(&self, block: &BasicBlock) -> BasicBlock {
        let new_stmts: Vec<Statement> = block
            .statements
            .iter()
            .filter(|stmt| {
                matches!(stmt.kind, StatementKind::StorageLive(_) | StatementKind::StorageDead(_))
            })
            .cloned()
            .collect();
        BasicBlock { statements: new_stmts, terminator: block.terminator.clone() }
    }

    /// Remove `StorageDead closure_var` to avoid invariant closure becoming dead.
    ///
    /// Returns `false` if the expected statement shape is not present.
    pub(super) fn make_invariant_closure_alive(
        &self,
        body: &mut MutableBody,
        bb_idx: usize,
    ) -> bool {
        let mut stmts = body.blocks()[bb_idx].statements.clone();
        let Some(first_stmt) = stmts.first() else { return false };
        if !matches!(first_stmt.kind, StatementKind::StorageDead(_)) {
            return false;
        }
        stmts.remove(0);
        body.replace_statements(&SourceInstruction::Terminator { bb: bb_idx }, stmts);
        true
    }

    //Move all storagedead inside the loop body to the loop termination block
    pub(super) fn move_storagedead(
        &self,
        body: &mut MutableBody,
        src_block_idx: usize,
        dst_block_idx: usize,
    ) {
        let localvars = self.get_user_defined_variables(body);
        let storagedead_stmts: Vec<_> = body.blocks()[src_block_idx]
            .clone()
            .statements
            .iter()
            .filter(
                |stmt| matches!(stmt.kind, StatementKind::StorageDead(x) if localvars.contains(&x)),
            )
            .cloned()
            .collect();
        let other_stmts: Vec<_> = body.blocks()[src_block_idx]
            .clone()
            .statements
            .iter()
            .filter(|stmt| !matches!(stmt.kind, StatementKind::StorageDead(x) if localvars.contains(&x)))
            .cloned()
            .collect();
        body.replace_statements(&SourceInstruction::Terminator { bb: src_block_idx }, other_stmts);
        let mut new_stmts = body.blocks()[dst_block_idx].statements.clone();
        let dst_block_stmt_kind: Vec<_> = new_stmts.iter().map(|st| st.kind.clone()).collect();
        for stmt in &storagedead_stmts {
            if !dst_block_stmt_kind.contains(&stmt.kind) {
                new_stmts.push(stmt.clone());
            }
        }
        body.replace_statements(&SourceInstruction::Terminator { bb: dst_block_idx }, new_stmts);
    }

    /// This function transform the function body as described in fn transform.
    /// It is the core of fn transform, and is separated just to avoid code repetition.
    pub(super) fn transform_body_with_loop(&mut self, tcx: TyCtxt, body: Body) -> (bool, Body) {
        let mut new_body = MutableBody::from(body);
        self.replace_first_pat_by_nth_pat(&mut new_body);
        let loop_head_map = self.get_associated_loop_head_hashmap(&new_body, tcx);
        let found_local_list =
            self.move_storagelive_assign_to_loophead(&mut new_body, &loop_head_map);
        let mut contain_loop_contracts: bool = false;

        // Visit basic blocks in control flow order (BFS).
        let mut visited: HashSet<BasicBlockIdx> = HashSet::new();
        let mut queue: VecDeque<BasicBlockIdx> = VecDeque::new();
        // Visit blocks in loops only when there is no blocks in queue.
        let mut loop_queue: VecDeque<BasicBlockIdx> = VecDeque::new();
        queue.push_back(0);

        while let Some(bb_idx) = queue.pop_front().or_else(|| loop_queue.pop_front()) {
            visited.insert(bb_idx);

            let terminator = new_body.blocks()[bb_idx].terminator.clone();

            let is_loop_head = self.transform_bb(tcx, &mut new_body, bb_idx);
            contain_loop_contracts |= is_loop_head;

            // Add successors of the current basic blocks to
            // the visiting queue.
            for to_visit in terminator.successors() {
                if !visited.contains(&to_visit) {
                    if is_loop_head {
                        loop_queue.push_back(to_visit);
                    } else {
                        queue.push_back(to_visit);
                    }
                }
            }
        }
        self.move_storagelive_call_to_loophead(&mut new_body, &loop_head_map, found_local_list);
        if contain_loop_contracts {
            self.instrument_loop_decreases(tcx, &mut new_body);
            // #47: the REAL loop-contract proof rule (base + inductive step +
            // post). Runs after decreases (whose latch inserts relocate the
            // register call; the rule re-locates it and re-snapshots the
            // ranking measure after the havoc).
            self.instrument_loop_invariant_rule(tcx, &mut new_body);
        }
        (contain_loop_contracts, new_body.into())
    }

    /// Encode the `#[kani::loop_decreases(<measure>)]` ranking obligation for the
    /// supported shape (CBMC-style back-edge check):
    ///
    /// ```text
    /// register_bb:  old = <measure closure>();            // was: _v = kani_register_loop_decreases(&closure, 0)
    ///               _v = true; goto <register target>;
    /// ...
    /// new_latch:    new = <measure closure>();
    ///               safety_check(new < old, "decreases");  // assert + assume
    ///               old = new;
    ///               _v = kani_register_loop_contract(...);  // unchanged invariant latch
    /// ```
    ///
    /// GUARDS (all violations leave the register call in place, which CHC codegen
    /// fail-closes into a FAILED verdict — never a silent drop):
    /// 1. exactly ONE decreases register call in the body (nested contracted
    ///    loops are a Kani `fixme_*` limitation reported FAILURE by the oracle);
    /// 2. exactly ONE invariant-transformed loop (`new_loop_latches`);
    /// 3. no `kani_loop_modifies` binding (decreases+loop_modifies is a Kani
    ///    `fixme_*` limitation);
    /// 4. the measure type is an unsigned integer (well-founded under `<`
    ///    without a separate lower-bound obligation);
    /// 5. every closure capture is a direct scalar-int local (or reference to
    ///    one) with no place projection — struct-field measures are a Kani
    ///    `fixme_*` limitation.
    ///
    /// Soundness: the check is assert+assume through the normal per-property
    /// CHC pipeline; a wrong/stale measure makes the latch obligation
    /// refutable, so ay reports FAILURE. Guards only ever widen to the
    /// fail-closed path.
    fn instrument_loop_decreases(&mut self, tcx: TyCtxt, new_body: &mut MutableBody) {
        use rustc_public::mir::mono::Instance;
        use rustc_public::mir::{BorrowKind, Local, Mutability, Place};
        use rustc_public::ty::{ClosureKind, GenericArgs, Region, Ty};

        let Some(check_type) = self.safety_check_type.clone() else { return };

        // ── Locate decreases register calls (guard 1) ───────────────────────
        struct RegisterSite {
            bb: usize,
            target: usize,
            destination: Place,
            /// `T` from `register<T, F: Fn() -> T>(_f: &F, _transformed: usize)`.
            measure_ty: Ty,
        }
        let mut sites: Vec<RegisterSite> = Vec::new();
        for (bb_idx, block) in new_body.blocks().iter().enumerate() {
            let TerminatorKind::Call { func, target, destination, .. } = &block.terminator.kind
            else {
                continue;
            };
            let Some(RigidTy::FnDef(fn_def, genarg)) =
                func.ty(new_body.locals()).ok().and_then(|t| t.kind().rigid().cloned())
            else {
                continue;
            };
            if KaniAttributes::for_def_id(tcx, fn_def.def_id()).fn_marker()
                != Some(Symbol::intern("kani_register_loop_decreases"))
            {
                continue;
            }
            let Some(target) = target else { continue };
            // The register fn's generics are <outer fn generics..., T, F>; the
            // measure type T immediately precedes the register's own closure
            // generic F, which is the LAST closure in the list (an enclosing
            // contract closure can contribute earlier closure generics).
            let mut measure_ty: Option<Ty> = None;
            for (i, arg) in genarg.0.iter().enumerate().rev() {
                if let GenericArgKind::Type(arg_ty) = arg
                    && matches!(arg_ty.kind(), TyKind::RigidTy(RigidTy::Closure(..)))
                {
                    if i > 0
                        && let GenericArgKind::Type(prev_ty) = &genarg.0[i - 1]
                    {
                        measure_ty = Some(*prev_ty);
                    }
                    break;
                }
            }
            let Some(measure_ty) = measure_ty else { continue };
            sites.push(RegisterSite {
                bb: bb_idx,
                target: *target,
                destination: destination.clone(),
                measure_ty,
            });
        }
        if sites.len() != 1 {
            return; // guard 1 (0 = nothing to do; >1 = nested fixme shape)
        }
        // guard 2
        if self.new_loop_latches.len() != 1 {
            return;
        }
        let latch_bb = *self.new_loop_latches.values().next().expect("checked len == 1");
        // guard 3
        let has_loop_modifies = new_body.var_debug_info().iter().any(|info| {
            let name = info.name.to_string();
            name.contains("kani_loop_modifies")
        });
        if has_loop_modifies {
            return;
        }

        let site = sites.remove(0);
        if site.bb == latch_bb {
            return; // malformed shape; keep fail-closed
        }

        // ── Extract the measure closure from the register block ────────────
        // Shape (from the macro): `_c = Closure{captures}; _r = &_c;
        //                          _v = register(move _r, 0) -> target`.
        let mut closure_local: Option<Local> = None;
        let mut closure_def = None;
        let mut closure_args: Option<GenericArgs> = None;
        let mut capture_operands: Vec<rustc_public::mir::Operand> = Vec::new();
        let mut ref_region: Option<Region> = None;
        for stmt in &new_body.blocks()[site.bb].statements {
            if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                match rvalue {
                    Rvalue::Aggregate(AggregateKind::Closure(def, gargs), ops) => {
                        if closure_local.is_some() {
                            return; // more than one closure in the block: unexpected shape
                        }
                        closure_local = Some(place.local);
                        closure_def = Some(*def);
                        closure_args = Some(gargs.clone());
                        capture_operands = ops.clone();
                    }
                    Rvalue::Ref(region, _, ref_place) => {
                        if Some(ref_place.local) == closure_local && ref_place.projection.is_empty()
                        {
                            ref_region = Some(region.clone());
                        }
                    }
                    _ => {}
                }
            }
        }
        let (Some(closure_local), Some(closure_def), Some(closure_args), Some(ref_region)) =
            (closure_local, closure_def, closure_args, ref_region)
        else {
            return;
        };

        // guard 4: the measure type must be an unsigned integer (well-founded
        // under `<` with no separate lower-bound obligation).
        let measure_ty = site.measure_ty;
        if !matches!(measure_ty.kind(), TyKind::RigidTy(RigidTy::Uint(_))) {
            return;
        }
        let Ok(shim) = Instance::resolve_closure(closure_def, &closure_args, ClosureKind::Fn)
        else {
            return;
        };

        // guard 5: captures must be direct scalar-int locals (possibly by ref),
        // no projections anywhere (excludes struct-field measures).
        for op in &capture_operands {
            let (Operand::Copy(place) | Operand::Move(place)) = op else { return };
            if !place.projection.is_empty() {
                return;
            }
            let Ok(op_ty) = op.ty(new_body.locals()) else { return };
            let scalar_ok =
                |ty: &Ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Uint(_) | RigidTy::Int(_)));
            match op_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => {
                    if !scalar_ok(&inner) {
                        return;
                    }
                    // The ref temp must borrow a projection-free local
                    // (a `&c.field` capture borrows through a projection).
                    let mut borrow_ok = false;
                    for stmt in &new_body.blocks()[site.bb].statements {
                        if let StatementKind::Assign(p, Rvalue::Ref(_, _, src)) = &stmt.kind
                            && p.local == place.local
                        {
                            borrow_ok = src.projection.is_empty();
                        }
                    }
                    if !borrow_ok {
                        return;
                    }
                }
                _ => {
                    if !scalar_ok(&op_ty) {
                        return;
                    }
                }
            }
        }

        // ── Identity-measure fast path ──────────────────────────────────────
        // Most measures are a single loop variable (`x`, `i`, `remaining`).
        // Detect the identity closure body (`_0 = *((*_1).0)`) and read the
        // capture's SOURCE local directly instead of calling the closure —
        // this keeps the loop state free of the closure aggregate and its
        // reference captures (which otherwise drag memory arrays into the
        // per-BB relations and stall PDR).
        let identity_source: Option<Local> = (|| {
            if capture_operands.len() != 1 {
                return None;
            }
            let (Operand::Copy(cap_place) | Operand::Move(cap_place)) = &capture_operands[0] else {
                return None;
            };
            // The capture temp must be `&src` on a projection-free local
            // (validated in guard 5); recover src.
            let mut src: Option<Local> = None;
            for stmt in &new_body.blocks()[site.bb].statements {
                if let StatementKind::Assign(p, Rvalue::Ref(_, _, rsrc)) = &stmt.kind
                    && p.local == cap_place.local
                    && rsrc.projection.is_empty()
                {
                    src = Some(rsrc.local);
                }
            }
            // By-value scalar capture: the capture temp IS the value, but the
            // temp is consumed by the aggregate; read the temp's own source if
            // it is a plain copy of a local, else give up.
            if src.is_none() {
                let Ok(cap_ty) = capture_operands[0].ty(new_body.locals()) else { return None };
                if matches!(cap_ty.kind(), TyKind::RigidTy(RigidTy::Uint(_) | RigidTy::Int(_))) {
                    for stmt in &new_body.blocks()[site.bb].statements {
                        if let StatementKind::Assign(p, Rvalue::Use(Operand::Copy(usrc))) =
                            &stmt.kind
                            && p.local == cap_place.local
                            && usrc.projection.is_empty()
                        {
                            src = Some(usrc.local);
                        }
                    }
                }
            }
            let src = src.or_else(|| {
                tracing::debug!("loop_decreases identity: no src recovered for capture temp");
                None
            })?;
            // Closure body must be the identity read of capture 0:
            // single block, Return terminator, and the return local assigned
            // from a place rooted at the self arg (local 1) with projections
            // only (Deref/Field) — no arithmetic statements.
            // Use the ClosureKind::Fn instance — FnOnce resolves to the
            // MIR-less call_once adapter shim (body() is None).
            let cbody = shim.body().or_else(|| {
                tracing::debug!("loop_decreases identity: shim.body() is None");
                None
            })?;
            if cbody.blocks.len() != 1
                || !matches!(cbody.blocks[0].terminator.kind, TerminatorKind::Return)
            {
                tracing::debug!(
                    blocks = cbody.blocks.len(),
                    "loop_decreases identity: closure body not single-block/Return"
                );
                return None;
            }
            // Accept the direct form (`_0 = copy <place rooted at _1>`) and
            // the split form rustc emits for by-ref captures:
            //   _t = copy ((*_1).0)   // load the capture reference
            //   _0 = copy (*_t)       // deref it
            // Both are pure reads of capture 0 — the measure IS the captured
            // local's current value.
            use rustc_public::mir::ProjectionElem;
            let mut ret_assigned_identity = false;
            let mut ref_temp: Option<usize> = None;
            for stmt in &cbody.blocks[0].statements {
                match &stmt.kind {
                    StatementKind::Assign(p, rv) => {
                        if p.local == 0 {
                            match rv {
                                Rvalue::Use(Operand::Copy(rp) | Operand::Move(rp)) => {
                                    let deref_of_ref_temp = Some(rp.local) == ref_temp
                                        && rp.projection.len() == 1
                                        && matches!(rp.projection[0], ProjectionElem::Deref);
                                    // Must read through the self arg (directly
                                    // or via the single capture-ref temp).
                                    if rp.local == 1 || deref_of_ref_temp {
                                        ret_assigned_identity = true;
                                    } else {
                                        tracing::debug!(
                                            local = rp.local,
                                            "loop_decreases identity: _0 read not rooted at self"
                                        );
                                        return None;
                                    }
                                }
                                _ => {
                                    tracing::debug!(
                                        ?rv,
                                        "loop_decreases identity: _0 assigned non-Use rvalue"
                                    );
                                    return None;
                                }
                            }
                        } else if ref_temp.is_none()
                            && !ret_assigned_identity
                            && matches!(
                                rv,
                                Rvalue::Use(Operand::Copy(rp) | Operand::Move(rp))
                                    if rp.local == 1
                            )
                            && p.projection.is_empty()
                        {
                            // The capture-ref load of the split form.
                            ref_temp = Some(p.local);
                        } else {
                            // Any other computation disqualifies the fast path.
                            tracing::debug!(
                                local = p.local,
                                ?rv,
                                "loop_decreases identity: extra statement in closure body"
                            );
                            return None;
                        }
                    }
                    StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
                    _ => {
                        tracing::debug!(?stmt.kind, "loop_decreases identity: non-assign statement");
                        return None;
                    }
                }
            }
            ret_assigned_identity.then_some(src)
        })();

        // guard 6: the measure closure body must be a single straight-line
        // block (`return <expr>`, no control flow). Overflow-checked compound
        // measures (`hi - lo` under -C overflow-checks) lower to multi-block
        // closures whose inlined form currently produces a VC ay rejects with
        // an instant SolverError (inconclusive-FAILED) — no better than the
        // blanket fail-closed path. Single-block measures (`x`, `i`,
        // `remaining`) are the supported shape; they flow through the
        // closure-call lane (inlined by FunctionInlinePass) or, when the body
        // is a plain capture read, the identity fast path above.
        {
            // NOTE: must inspect the ClosureKind::Fn instance (`shim`) — the
            // FnOnce resolution yields the `call_once` adapter shim, whose MIR
            // is unavailable (`body()` is None), which would spuriously bail.
            let Some(cbody) = shim.body() else { return };
            if cbody.blocks.len() != 1
                || !matches!(cbody.blocks[0].terminator.kind, TerminatorKind::Return)
            {
                return;
            }
        }

        tracing::debug!(
            register_bb = site.bb,
            latch_bb,
            identity = identity_source.is_some(),
            "loop_decreases: instrumenting back-edge ranking check"
        );

        // guard 7 (#44): ONLY the identity fast path is supported. The
        // closure-CALL lane inlines the measure closure into fresh blocks
        // whose composed-fragment constraints are stripped downstream
        // (undeclared-mid sanitization drops the `old = measure()` snapshot,
        // leaving `old` free at the loop head — the ranking obligation then
        // refutes on SAFE programs: validated-spurious Genuine ctrex).
        // Until that pipeline is fixed, non-identity measures keep the
        // pre-existing blanket fail-closed path (conservative FAILED verdict).
        if identity_source.is_none() {
            tracing::debug!(
                register_bb = site.bb,
                "loop_decreases: non-identity measure — keeping blanket fail-closed (#44)"
            );
            return;
        }

        // ── Keep the measure closure alive through the loop (call path only) ─
        if identity_source.is_none() {
            for bb in 0..new_body.blocks().len() {
                let stmts: Vec<_> = new_body.blocks()[bb]
                    .statements
                    .iter()
                    .filter(|stmt| {
                        !matches!(stmt.kind, StatementKind::StorageDead(l) if l == closure_local)
                    })
                    .cloned()
                    .collect();
                if stmts.len() != new_body.blocks()[bb].statements.len() {
                    new_body.replace_statements(&SourceInstruction::Terminator { bb }, stmts);
                }
            }
        }

        let span = new_body.blocks()[site.bb].terminator.span;
        let old_local = new_body.new_local(measure_ty, span, Mutability::Mut);

        // ── Register block: `old = measure()`; neutralize the register call ─
        let mut source = SourceInstruction::Terminator { bb: site.bb };
        if let Some(src) = identity_source {
            new_body.assign_to(
                Place::from(old_local),
                Rvalue::Use(Operand::Copy(Place::from(src))),
                &mut source,
                InsertPosition::Before,
            );
        } else {
            let ref1 = new_body.insert_assignment(
                Rvalue::Ref(ref_region.clone(), BorrowKind::Shared, Place::from(closure_local)),
                &mut source,
                InsertPosition::Before,
            );
            let unit1 = new_body.insert_assignment(
                Rvalue::Aggregate(AggregateKind::Tuple, vec![]),
                &mut source,
                InsertPosition::Before,
            );
            new_body.insert_call(
                &shim,
                &mut source,
                InsertPosition::Before,
                vec![Operand::Move(Place::from(ref1)), Operand::Move(Place::from(unit1))],
                Place::from(old_local),
            );
        }
        // `source` now points at the register-call terminator: replace it with
        // `_v = true; goto target` exactly like the invariant register call.
        new_body.assign_to(
            site.destination.clone(),
            Rvalue::Use(Operand::Constant(ConstOperand {
                span,
                user_ty: None,
                const_: MirConst::from_bool(true),
            })),
            &mut source,
            InsertPosition::Before,
        );
        let SourceInstruction::Terminator { bb: register_tail_bb } = source else {
            unreachable!("instrumentation keeps a terminator cursor")
        };
        new_body.replace_terminator(
            &SourceInstruction::Terminator { bb: register_tail_bb },
            Terminator { kind: TerminatorKind::Goto { target: site.target }, span },
        );

        // ── Latch: `new = measure(); safety_check(new < old); old = new` ────
        let mut latch_source = SourceInstruction::Terminator { bb: latch_bb };
        let new_measure = new_body.new_local(measure_ty, span, Mutability::Not);
        if let Some(src) = identity_source {
            new_body.assign_to(
                Place::from(new_measure),
                Rvalue::Use(Operand::Copy(Place::from(src))),
                &mut latch_source,
                InsertPosition::Before,
            );
        } else {
            let ref2 = new_body.insert_assignment(
                Rvalue::Ref(ref_region, BorrowKind::Shared, Place::from(closure_local)),
                &mut latch_source,
                InsertPosition::Before,
            );
            let unit2 = new_body.insert_assignment(
                Rvalue::Aggregate(AggregateKind::Tuple, vec![]),
                &mut latch_source,
                InsertPosition::Before,
            );
            new_body.insert_call(
                &shim,
                &mut latch_source,
                InsertPosition::Before,
                vec![Operand::Move(Place::from(ref2)), Operand::Move(Place::from(unit2))],
                Place::from(new_measure),
            );
        }
        let cmp = new_body.insert_assignment(
            Rvalue::BinaryOp(
                rustc_public::mir::BinOp::Lt,
                Operand::Copy(Place::from(new_measure)),
                Operand::Copy(Place::from(old_local)),
            ),
            &mut latch_source,
            InsertPosition::Before,
        );
        new_body.insert_check(
            &check_type,
            &mut latch_source,
            InsertPosition::Before,
            Some(cmp),
            "loop decreases clause: measure must strictly decrease on every iteration",
        );
        new_body.assign_to(
            Place::from(old_local),
            Rvalue::Use(Operand::Copy(Place::from(new_measure))),
            &mut latch_source,
            InsertPosition::Before,
        );

        // #47: let the loop-contract proof rule re-snapshot `old = src` after
        // its havoc, so the ranking check compares within the symbolic
        // iteration (guard 7 guarantees identity_source is Some here).
        if let Some(src) = identity_source {
            self.decreases_snapshot = Some((old_local, src));
        }
    }

    /// Transform loops with contracts from
    ///    ```text
    ///    bb_idx: {
    ///         loop_head_stmts
    ///         _v = kani_register_loop_contract(move args) -> [return: terminator_target];
    ///    }
    ///
    ///    ...
    ///    loop_body_blocks
    ///    ...
    ///
    ///    loop_latch_block: {
    ///         loop_latch_stmts
    ///         goto -> bb_idx;
    ///    }
    ///    ```
    ///    to blocks
    ///    ```text
    ///    bb_idx: {
    ///         loop_head_stmts
    ///         _v = true
    ///         goto -> terminator_target
    ///    }
    ///
    ///    ...
    ///    loop_body_blocks
    ///    ...
    ///
    ///    loop_latch_block: {
    ///         loop_latch_stmts
    ///         goto -> bb_new_loop_latch;
    ///    }
    ///
    ///    bb_new_loop_latch: {
    ///         loop_head_body
    ///         _v = kani_register_loop_contract(move args) -> [return: terminator_target];
    ///    }
    ///    ```
    pub(super) fn transform_bb(
        &mut self,
        tcx: TyCtxt,
        new_body: &mut MutableBody,
        bb_idx: usize,
    ) -> bool {
        let terminator = new_body.blocks()[bb_idx].terminator.clone();
        let mut contain_loop_contracts = false;

        // Redirect loop latches to the new latches.
        if let TerminatorKind::Goto { target: terminator_target } = &terminator.kind
            && self.new_loop_latches.contains_key(terminator_target)
        {
            new_body.replace_terminator(
                &SourceInstruction::Terminator { bb: bb_idx },
                Terminator {
                    kind: TerminatorKind::Goto { target: self.new_loop_latches[terminator_target] },
                    span: terminator.span,
                },
            );
        }

        if let TerminatorKind::SwitchInt { discr, targets } = &terminator.kind {
            let new_branches: Vec<_> = targets
                .branches()
                .map(|(a, b)| {
                    if self.new_loop_latches.contains_key(&b) {
                        (a, self.new_loop_latches[&b])
                    } else {
                        (a, b)
                    }
                })
                .collect();

            let new_otherwise = if self.new_loop_latches.contains_key(&targets.otherwise()) {
                self.new_loop_latches[&targets.otherwise()]
            } else {
                targets.otherwise()
            };

            let new_targets = SwitchTargets::new(new_branches, new_otherwise);
            new_body.replace_terminator(
                &SourceInstruction::Terminator { bb: bb_idx },
                Terminator {
                    kind: TerminatorKind::SwitchInt { discr: discr.clone(), targets: new_targets },
                    span: terminator.span,
                },
            );
        }

        // Transform loop heads with loop contracts.
        if let TerminatorKind::Call {
            func: terminator_func,
            args: terminator_args,
            destination: terminator_destination,
            target: terminator_target,
            unwind: terminator_unwind,
        } = &terminator.kind
        {
            // Get the function signature of the terminator call.
            let Some(RigidTy::FnDef(fn_def, genarg)) = terminator_func
                .ty(new_body.locals())
                .ok()
                .and_then(|fn_ty| fn_ty.kind().rigid().cloned())
            else {
                return false;
            };

            let fn_marker = KaniAttributes::for_def_id(tcx, fn_def.def_id()).fn_marker();

            // NOTE: a `#[kani::loop_decreases(...)]` clause lowers to a
            // `kani_register_loop_decreases<id>(&|| <measure>, 0)` call
            // (fn_marker `kani_register_loop_decreases`) that `transform_bb`
            // leaves untouched; supported shapes are instrumented AFTER the
            // main BFS by `instrument_loop_decreases` (which needs the
            // invariant-transformed latch from `new_loop_latches`). Unsupported
            // shapes keep the register call: because the register fn is
            // `#[inline(never)]` it survives inlining, so CHC codegen
            // (`codegen_function::codegen_chc_path`) detects it and emits a
            // conservative FAILED verdict rather than silently ignoring the measure.

            // The basic blocks end with register functions are loop head blocks.
            if fn_marker == Some(Symbol::intern("kani_register_loop_contract"))
                && matches!(
                    &terminator_args[1],
                    Operand::Constant(op)
                        if op.const_.eval_target_usize().map(|value| value == 0).unwrap_or(false)
                )
            {
                let terminator_target_bb =
                    terminator_target.expect("terminator target should exist");
                let target_successors =
                    new_body.blocks()[terminator_target_bb].terminator.clone().successors();
                let Some(loop_termination_block_id) = target_successors.first().copied() else {
                    return false;
                };
                let loop_latch_ids = self.get_all_loop_latch_ids(new_body, bb_idx);
                for loop_latch_id in loop_latch_ids {
                    self.move_storagedead(new_body, loop_latch_id, loop_termination_block_id);
                }

                // Check if the MIR satisfy the assumptions of this transformation.
                if !new_body.blocks()[terminator_target_bb].statements.is_empty()
                    || !matches!(
                        new_body.blocks()[terminator_target_bb].terminator.kind,
                        TerminatorKind::SwitchInt { .. }
                    )
                {
                    unreachable!(
                        "The assumptions for loop-contracts transformation are violated by some other transformation. \
                    Please report github.com/model-checking/kani/issues/new?template=bug_report.md"
                    );
                }
                let GenericArgKind::Type(arg_ty) = genarg.0[0] else { return false };
                let TyKind::RigidTy(RigidTy::Closure(closure_def, genarg)) = arg_ty.kind() else {
                    return false;
                };
                // Capture the closure DefId index for CHC solver hints.
                let closure_def_index = Some(closure_def.def_id().to_index() as u32);
                // We look for the args' types of the kani_register_loop_contract function
                // They are always stored in a tuple, which is next to the FnPtr generic args of kani_registered_loop_contract fn
                // All the generic args before the FnPtr are from the outer function
                let mut fnptrpos = None;
                for (i, arg) in genarg.0.iter().enumerate() {
                    if let GenericArgKind::Type(arg_ty) = arg
                        && let TyKind::RigidTy(RigidTy::FnPtr(_)) = arg_ty.kind()
                    {
                        fnptrpos = Some(i);
                        break;
                    }
                }
                let fnptrpos = match fnptrpos {
                    Some(pos) if pos + 1 < genarg.0.len() => pos,
                    _ => return false, // non-enum: Option (fnptrpos: None or failed guard)
                };
                let GenericArgKind::Type(arg_ty) = genarg.0[fnptrpos + 1] else { return false };
                let TyKind::RigidTy(RigidTy::Tuple(args)) = arg_ty.kind() else { return false };
                // Check if the invariant involves any local variable
                if !args.is_empty() {
                    let Some(ori_condition_bb_idx) = target_successors.get(1).copied() else {
                        return false;
                    };
                    if !self.make_invariant_closure_alive(new_body, ori_condition_bb_idx) {
                        return false;
                    }
                }

                contain_loop_contracts = true;

                // Collect supported vars assigned in the block.
                // And check if all arguments of the closure is supported.
                let mut supported_vars: Vec<usize> = Vec::new();
                // All user variables are support
                supported_vars.extend(new_body.var_debug_info().iter().filter_map(|info| {
                    match &info.value {
                        VarDebugInfoContents::Place(debug_place) => Some(debug_place.local),
                        _ => None, // external enum: VarDebugInfoContents
                    }
                }));

                // For each assignment in the loop head block,
                // if it assigns to the closure place, we check if all arguments are supported;
                // if it assigns to other places, we cache if the assigned places are supported.
                // Also capture the actual closure arguments for CHC solver hints.
                //
                // NOTE: If multiple Closure aggregates exist in the block (unusual), we accumulate
                // all their captured variables. The order is preserved for CHC hint consumption.
                let mut actual_captured_vars: Vec<usize> = Vec::new();
                for stmt in &new_body.blocks()[bb_idx].statements {
                    if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                        match rvalue {
                            Rvalue::Ref(_, _, rplace)
                            | Rvalue::CopyForDeref(rplace)
                            | Rvalue::Use(Operand::Copy(rplace)) => {
                                if supported_vars.contains(&rplace.local) {
                                    supported_vars.push(place.local);
                                }
                            }
                            Rvalue::Aggregate(AggregateKind::Closure(..), closure_args) => {
                                if closure_args.iter().any(|arg| !matches!(arg, Operand::Copy(arg_place) | Operand::Move(arg_place) if supported_vars.contains(&arg_place.local))) {
                                    tracing::debug!(
                                        bb_idx,
                                        "loop invariant captures an unsupported dereference; \
                                         retaining the register-call breadcrumb for fail-closed codegen"
                                    );
                                    return false;
                                }
                                // Capture the actual locals passed to the closure for CHC hints.
                                // Deduplicate to handle cases where same local appears multiple times.
                                for arg in closure_args {
                                    if let Operand::Copy(arg_place) | Operand::Move(arg_place) = arg
                                        && !actual_captured_vars.contains(&arg_place.local)
                                    {
                                        actual_captured_vars.push(arg_place.local);
                                    }
                                }
                            }
                            _ => {
                                // external enum: Rvalue
                                if self.is_supported_argument_of_closure(rvalue, new_body) {
                                    supported_vars.push(place.local);
                                }
                            }
                        }
                    }
                }

                // Replace the original loop head block
                // ```text
                // bb_idx: {
                //          loop_head_stmts
                //          _v = kani_register_loop_contract(move args) -> [return: terminator_target];
                // }
                // ```
                // with
                // ```text
                // bb_idx: {
                //          loop_head_stmts
                //          _v = true;
                //          goto -> terminator_target
                // }
                // ```
                new_body.assign_to(
                    terminator_destination.clone(),
                    Rvalue::Use(Operand::Constant(ConstOperand {
                        span: terminator.span,
                        user_ty: None,
                        const_: MirConst::from_bool(true),
                    })),
                    &mut SourceInstruction::Terminator { bb: bb_idx },
                    InsertPosition::Before,
                );
                let new_latch_block = self.get_loop_head_block(&new_body.blocks()[bb_idx]);

                // Insert a new basic block as the loop latch block, and later redirect
                // all latches to the new loop latch block.
                // -----
                // bb_new_loop_latch: {
                //    _v = kani_register_loop_contract(move args) -> [return: terminator_target];
                // }
                new_body.insert_bb(
                    new_latch_block,
                    &mut SourceInstruction::Terminator { bb: bb_idx },
                    InsertPosition::After,
                );
                // Update the argument `transformed` to 1 to avoid double transformation.
                let new_args = vec![
                    terminator_args[0].clone(),
                    Operand::Constant(ConstOperand {
                        span: terminator.span,
                        user_ty: None,
                        const_: MirConst::try_from_uint(1, UintTy::Usize)
                            .expect("usize(1) should be valid"),
                    }),
                ];
                new_body.replace_terminator(
                    &SourceInstruction::Terminator { bb: new_body.blocks().len() - 1 },
                    Terminator {
                        kind: TerminatorKind::Call {
                            func: terminator_func.clone(),
                            args: new_args,
                            destination: terminator_destination.clone(),
                            target: *terminator_target,
                            unwind: *terminator_unwind,
                        },
                        span: terminator.span,
                    },
                );
                new_body.replace_terminator(
                    &SourceInstruction::Terminator { bb: bb_idx },
                    Terminator {
                        kind: TerminatorKind::Goto { target: terminator_target_bb },
                        span: terminator.span,
                    },
                );
                // Cache the new loop latch.
                let new_latch_bb_idx = new_body.blocks().len() - 1;
                self.new_loop_latches.insert(bb_idx, new_latch_bb_idx);

                // Part of #1562: Extract formula from closure body.
                // This attempts to resolve the closure and extract a simple boolean formula.
                // Complex closures (multi-statement, control flow) fall back to None.
                let formula_smt2 =
                    Self::extract_closure_formula(closure_def, &genarg, &actual_captured_vars);

                // Extract loop invariant information for CHC solver hints.
                self.extracted_invariants.push(ExtractedLoopInvariant {
                    loop_head_bb: bb_idx,
                    loop_latch_bb: Some(new_latch_bb_idx),
                    // Part of #40: the CHC relation the invariant belongs to is
                    // the register call's terminator target (the block the
                    // rewritten loop head `goto`s to), not the register block.
                    chc_loop_head_bb: Some(terminator_target_bb),
                    captured_vars: actual_captured_vars,
                    closure_def_index,
                    formula_smt2,
                    captured_rel_arg_positions: None,
                });
            }
        }
        contain_loop_contracts
    }
}
