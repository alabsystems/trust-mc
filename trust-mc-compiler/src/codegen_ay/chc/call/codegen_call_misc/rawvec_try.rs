// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! RawVec, Try/Residual, and unconstrained stub handlers.
//! Part of #2408 S1: codegen_call_misc decomposition.

use ay_bindings::Expr;
use tracing::{debug, warn};

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::super::ChcCtx;
use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_call_coerce::emit_sound_fallback_goto;
use super::super::codegen_call_vec::ChcVecFields;
use super::super::codegen_ctx::types::CollectionProjectionKind;
use super::super::codegen_rules::CodegenRules;

struct ProjectedVecUpdate {
    ptr: Expr,
    len: Expr,
    cap: Expr,
    data: Expr,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle RawVec internal stubs (Part of #2196, #2877).
    ///
    /// RawVec is Vec's internal allocation buffer. In CHC:
    /// - `RawVecGrowOne` → model capacity growth on parent Vec (Part of #2877)
    /// - `RawVecShrinkToFit` → model capacity shrink on parent Vec (Part of #2877)
    /// - `RawVecDrop` → no-op
    /// - `RawVecNewIn`, `RawVecCapacity`, `RawVecPtr`, `RawVecFromNonNullIn` → leave
    ///   destination unconstrained (these produce values that subsequent code
    ///   will use, but over-approximation is sound)
    pub(in crate::codegen_ay::chc) fn codegen_call_rawvec_impl(&mut self, cx: &ChcCallContext<'_>) {
        debug!("rawvec_stub stub={:?} dest={}", cx.stub, cx.destination.local);
        match cx.stub {
            StubKind::RawVecGrowOne => {
                // Model capacity growth on parent Vec. RawVecGrowOne is used for
                // grow_one (1 arg), reserve_exact (3 args: self, len, additional),
                // and grow_amortized (3 args: self, len, additional). Part of #2877.
                let mut extra_constraints: Vec<Expr> = Vec::new();
                let mut extra_dests: Vec<usize> = Vec::new();
                self.rawvec_grow_capacity(cx, &mut extra_constraints, &mut extra_dests);
                let new_output_args = self.build_output_args(cx.modified_locals, &extra_dests);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    extra_constraints,
                );
            }
            StubKind::RawVecShrinkToFit => {
                // Model capacity shrink: cap = len on parent Vec. Part of #2877.
                let mut extra_constraints: Vec<Expr> = Vec::new();
                let mut extra_dests: Vec<usize> = Vec::new();
                self.rawvec_shrink_capacity(cx, &mut extra_constraints, &mut extra_dests);
                let new_output_args = self.build_output_args(cx.modified_locals, &extra_dests);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    extra_constraints,
                );
            }
            StubKind::RawVecDrop => {
                // Drop is a no-op in the CHC abstraction.
                let new_output_args =
                    self.build_output_args(cx.modified_locals, &[cx.destination.local]);
                self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
            }
            StubKind::RawVecNewIn => {
                if self.extra_pointer_checks && self.emit_rawvec_new_in_extra_checks(cx) {
                    return;
                }
                let dest_local: usize = cx.destination.local;
                let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
            }
            StubKind::RawVecCapacity | StubKind::RawVecPtr | StubKind::RawVecFromNonNullIn => {
                // Sound over-approximation: destination left nondet. record_fallback()
                // NOT called: nondeterministic RawVec internals cannot produce false
                // proofs (#2753, Part of #3123 Tier 3 review).
                let dest_local: usize = cx.destination.local;
                let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
            }
            _other => {
                // Unexpected stub — translation failure (Part of #3123).
                warn!(?_other, "codegen_call_rawvec: unexpected stub — update routing");
                emit_sound_fallback_goto(
                    self,
                    cx.from_app,
                    cx.target,
                    cx.modified_locals,
                    &[cx.destination.local],
                    cx.stmt_constraints,
                );
            }
        }
    }

    /// Model capacity growth for RawVecGrowOne on the parent Vec (Part of #2877).
    ///
    /// Resolves `args[0]` through ref_targets to find the parent Vec state var.
    /// If found and it has `fld_cap`, updates capacity:
    /// - 3 args (reserve_exact/grow_amortized): `new_cap = ite(cap < len + additional, len + additional, cap)`
    /// - 1 arg (grow_one): `new_cap = cap + 1`
    ///
    /// Falls back to no-op (sound over-approximation) when the parent Vec
    /// cannot be resolved.
    fn rawvec_grow_capacity(
        &mut self,
        cx: &ChcCallContext<'_>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        let collection_local = self.resolve_collection_local(cx.args);
        let Some(coll_local) = collection_local else {
            debug!("rawvec_grow: no collection local resolved — no-op fallback");
            extra_dests.push(cx.destination.local);
            return;
        };

        // Part of #1037 V1: skip if Vec-level stub already modeled capacity
        // for this local (prevents dual-path constraint conflicts).
        if self.collections.vec_cap_stubs_fired.contains(&coll_local) {
            debug!(
                coll_local,
                "rawvec_grow: skipped — Vec-level stub already modeled capacity (#1037 V1)"
            );
            extra_dests.push(cx.destination.local);
            return;
        }

        if self.collections.projection_locals.get(&coll_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            // Projected Vec path (#2877): update flattened fields directly.
            let ptr = self.flattened_local_field_expr(coll_local, 0, cx.modified_locals);
            let len = self.flattened_local_field_expr(coll_local, 1, cx.modified_locals);
            let cap = self.flattened_local_field_expr(coll_local, 2, cx.modified_locals);
            let data = self.flattened_local_field_expr(coll_local, 3, cx.modified_locals);
            if let (Some(ptr), Some(len), Some(cap), Some(data)) = (ptr, len, cap, data) {
                let new_cap = if cx.args.len() >= 3 {
                    let additional = self
                        .translate_operand_with_modified(&cx.args[2], cx.modified_locals)
                        .unwrap_or_else(|| Expr::bitvec_const(1u64, POINTER_WIDTH));
                    let required_cap = len.clone().bvadd(additional);
                    let grow_needed = cap.clone().bvult(required_cap.clone());
                    Expr::ite(grow_needed, required_cap, cap)
                } else {
                    cap.bvadd(Expr::bitvec_const(1u64, POINTER_WIDTH))
                };
                let projected_update = ProjectedVecUpdate { ptr, len, cap: new_cap, data };
                if self.constrain_projected_vec_fields_for_rawvec_call(
                    coll_local,
                    projected_update,
                    extra_constraints,
                    extra_dests,
                ) {
                    debug!(
                        coll_local,
                        "rawvec_grow: modeled projected Vec capacity growth (#2877)"
                    );
                    return;
                }
            }
            debug!(coll_local, "rawvec_grow: projected Vec field update failed — no-op fallback");
            extra_dests.push(cx.destination.local);
            return;
        }

        let Some(vec_idx) = self.state_var_mgr.local_to_state_idx.get(&coll_local).copied() else {
            debug!(coll_local, "rawvec_grow: local not tracked as state var — no-op fallback");
            extra_dests.push(cx.destination.local);
            return;
        };
        let (name, sort) = if let Some(pair) = if cx.modified_locals.contains(&coll_local) {
            self.state_var_mgr.output_state_vars.get(vec_idx)
        } else {
            self.state_var_mgr.state_vars.get(vec_idx)
        } {
            (pair.0.clone(), pair.1.clone())
        } else {
            extra_dests.push(cx.destination.local);
            return;
        };
        // Verify the state var is a Vec datatype with fld_cap
        if sort.datatype_name().is_none()
            || Self::get_dt_field_sort(&Expr::var(&*name, sort.clone()), "fld_cap").is_none()
        {
            debug!(coll_local, "rawvec_grow: state var is not a Vec datatype — no-op fallback");
            extra_dests.push(cx.destination.local);
            return;
        }
        let vec_in = Expr::var(&*name, sort);
        let Some(fields) = ChcVecFields::extract(vec_in) else {
            extra_dests.push(cx.destination.local);
            return;
        };
        let ChcVecFields { vec_sort, ptr, len, cap, data } = fields;

        // Compute new capacity based on argument count.
        // reserve_exact/grow_amortized: 3 args (self, len, additional)
        // grow_one: 1 arg (self)
        let new_cap = if cx.args.len() >= 3 {
            // reserve_exact(self, len, additional): new_cap = max(cap, len + additional)
            let additional = self
                .translate_operand_with_modified(&cx.args[2], cx.modified_locals)
                .unwrap_or_else(|| Expr::bitvec_const(1u64, POINTER_WIDTH));
            let required_cap = len.clone().bvadd(additional);
            let grow_needed = cap.clone().bvult(required_cap.clone());
            Expr::ite(grow_needed, required_cap, cap)
        } else {
            // grow_one: new_cap = cap + 1
            cap.bvadd(Expr::bitvec_const(1u64, POINTER_WIDTH))
        };

        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
        {
            let dt_name = vec_sort
                .datatype_name()
                .expect("invariant: ChcVecFields::extract ensures datatype Vec sort");
            extra_constraints.push(Self::build_vec_datatype_eq(
                dt_name,
                vec![ptr, len, new_cap, data],
                &out_name,
                &out_sort,
            ));
            extra_dests.push(coll_local);
            debug!(coll_local, "rawvec_grow: modeled capacity growth on parent Vec (#2877)");
        } else {
            extra_dests.push(cx.destination.local);
        }
    }

    /// Model capacity shrink for RawVecShrinkToFit on the parent Vec (Part of #2877).
    ///
    /// Sets `fld_cap = fld_len` (conservative: shrink to current length).
    /// Falls back to no-op when the parent Vec cannot be resolved.
    fn rawvec_shrink_capacity(
        &mut self,
        cx: &ChcCallContext<'_>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        let collection_local = self.resolve_collection_local(cx.args);
        let Some(coll_local) = collection_local else {
            extra_dests.push(cx.destination.local);
            return;
        };

        // Part of #1037 V1: skip if Vec-level stub already modeled capacity
        // for this local (prevents dual-path constraint conflicts).
        if self.collections.vec_cap_stubs_fired.contains(&coll_local) {
            debug!(
                coll_local,
                "rawvec_shrink: skipped — Vec-level stub already modeled capacity (#1037 V1)"
            );
            extra_dests.push(cx.destination.local);
            return;
        }

        if self.collections.projection_locals.get(&coll_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let ptr = self.flattened_local_field_expr(coll_local, 0, cx.modified_locals);
            let len = self.flattened_local_field_expr(coll_local, 1, cx.modified_locals);
            let data = self.flattened_local_field_expr(coll_local, 3, cx.modified_locals);
            if let (Some(ptr), Some(len), Some(data)) = (ptr, len, data) {
                let projected_update = ProjectedVecUpdate { ptr, len: len.clone(), cap: len, data };
                if self.constrain_projected_vec_fields_for_rawvec_call(
                    coll_local,
                    projected_update,
                    extra_constraints,
                    extra_dests,
                ) {
                    debug!(
                        coll_local,
                        "rawvec_shrink: modeled projected Vec capacity shrink (#2877)"
                    );
                    return;
                }
            }
            extra_dests.push(cx.destination.local);
            return;
        }

        let Some(vec_idx) = self.state_var_mgr.local_to_state_idx.get(&coll_local).copied() else {
            extra_dests.push(cx.destination.local);
            return;
        };
        let (name, sort) = if let Some(pair) = if cx.modified_locals.contains(&coll_local) {
            self.state_var_mgr.output_state_vars.get(vec_idx)
        } else {
            self.state_var_mgr.state_vars.get(vec_idx)
        } {
            (pair.0.clone(), pair.1.clone())
        } else {
            extra_dests.push(cx.destination.local);
            return;
        };
        if sort.datatype_name().is_none()
            || Self::get_dt_field_sort(&Expr::var(&*name, sort.clone()), "fld_cap").is_none()
        {
            extra_dests.push(cx.destination.local);
            return;
        }
        let vec_in = Expr::var(&*name, sort);
        let Some(fields) = ChcVecFields::extract(vec_in) else {
            extra_dests.push(cx.destination.local);
            return;
        };
        let ChcVecFields { vec_sort, ptr, len, cap: _, data } = fields;

        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
        {
            let dt_name = vec_sort
                .datatype_name()
                .expect("invariant: ChcVecFields::extract ensures datatype Vec sort");
            // Shrink: cap = len
            extra_constraints.push(Self::build_vec_datatype_eq(
                dt_name,
                vec![ptr, len.clone(), len, data],
                &out_name,
                &out_sort,
            ));
            extra_dests.push(coll_local);
            debug!(coll_local, "rawvec_shrink: modeled capacity shrink on parent Vec (#2877)");
        } else {
            extra_dests.push(cx.destination.local);
        }
    }

    /// Write projected Vec flattened fields (ptr, len, cap, data) for call handlers.
    fn constrain_projected_vec_fields_for_rawvec_call(
        &mut self,
        coll_local: usize,
        fields: ProjectedVecUpdate,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) -> bool {
        let emitted = self.constrain_flattened_fields_for_call(
            coll_local,
            &[Some(fields.ptr), Some(fields.len), Some(fields.cap), Some(fields.data)],
            extra_constraints,
        );
        if emitted {
            extra_dests.push(coll_local);
        }
        emitted
    }

    /// Handle Try/Residual stubs (Part of #2196).
    ///
    /// The `?` operator lowers to:
    /// - `Try::branch(self)` → `ControlFlow::Continue(output)` (allocation always succeeds)
    /// - `FromResidual::from_residual(residual)` → unreachable (no-op)
    ///
    /// In CHC, both are no-ops: just emit goto with unconstrained destination.
    pub(in crate::codegen_ay::chc) fn codegen_call_try_residual_impl(
        &mut self,
        cx: &ChcCallContext<'_>,
    ) {
        debug!("try_residual_stub stub={:?}", cx.stub);
        // Both TryBranch and FromResidualFromResidual: just emit goto.
        // Try::branch would ideally constrain the ControlFlow discriminant
        // to Continue, but over-approximation is sound here. record_fallback()
        // NOT called: nondeterministic ControlFlow cannot produce false proofs
        // (#2753, Part of #3123 Tier 3 review).
        let new_output_args = self.build_output_args(cx.modified_locals, &[cx.destination.local]);
        self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
    }

    /// Handle stub calls with unconstrained destination (Part of #2196).
    ///
    /// Shared handler for stub families where all variants produce sound
    /// over-approximation by leaving the destination unconstrained:
    /// - Layout non-semantic: LayoutDangling, LayoutCalculateLayoutFor
    ///   (LayoutNew/LayoutArray/LayoutFromSizeAlign{,Unchecked}/LayoutForValueRaw route
    ///   to `codegen_call_layout_semantic` instead; Part of #3641)
    /// - NonNull extras (New, SliceFromRawParts, AsNonNullPtr, Dangling, AsMutPtr)
    /// - BTreeMap internals (Entry API, node operations, SetValZstDefault)
    pub(in crate::codegen_ay::chc) fn codegen_call_unconstrained_stub_impl(
        &mut self,
        cx: &ChcCallContext<'_>,
    ) {
        if cx.stub == StubKind::LayoutDangling
            && self.extra_pointer_checks
            && self.emit_layout_dangling_extra_checks(cx)
        {
            return;
        }
        // Sound over-approximation: destination left unconstrained (nondet).
        // This is intentional for NonNull, BTreeMap internals, Layout stubs.
        // warn! provides log visibility; record_fallback() is NOT called because
        // this is sound over-approximation (cannot produce false proofs), not a
        // translation failure. Verdict demotion would falsely reject valid proofs
        // for any harness touching these common types (#2753).
        warn!(
            fn_name = %self.fn_name,
            stub = ?cx.stub,
            dest = cx.destination.local,
            "CHC: unconstrained stub — destination left nondet (sound over-approximation)"
        );
        let dest_local: usize = cx.destination.local;
        let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
        self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
    }
}
