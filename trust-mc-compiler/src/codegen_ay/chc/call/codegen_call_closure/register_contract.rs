// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Helpers for lowering `kani_register_contract(closure)` as direct inline
//! closure execution.

use rustc_public::CrateDef;
use rustc_public::mir::LocalDecl;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::{ClosureKind, RigidTy, TyKind};
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::inline_body::translate_closure_inline_result;
use crate::kani_middle::attributes::fn_marker;

pub(in crate::codegen_ay::chc) fn resolve_closure_body_for_operand(
    tcx: rustc_middle::ty::TyCtxt,
    operand: &rustc_public::mir::Operand,
    locals: &[LocalDecl],
) -> Option<rustc_public::mir::Body> {
    resolve_closure_body_for_ty(tcx, operand.ty(locals).ok()?)
}

/// Wall-2 strategy (b) for the `run_contract_fn`/`run_loop_contract_fn`
/// closure-unresolved class: the operand's DECLARED type did not name a
/// closure (type-computation error, or a coerced/opaque sort), but the operand
/// local may still be uniquely DEFINED by a closure construction in the host
/// body. Walk the body for the operand local's unique whole-local
/// `Aggregate(Closure)` assign and resolve the (transformed, scope-gated) body
/// from the closure def recovered there.
///
/// FAIL-CLOSED by construction: a projected operand, any projected write to
/// the local, more than one whole-local assign, the local being a call
/// destination, a non-closure-aggregate unique def, or a failed instance/body
/// resolve all return `None` — the caller keeps its existing demotion
/// fallback.
pub(in crate::codegen_ay::chc) fn resolve_closure_body_via_unique_aggregate_def(
    tcx: rustc_middle::ty::TyCtxt,
    operand: &rustc_public::mir::Operand,
    body: &rustc_public::mir::Body,
) -> Option<rustc_public::mir::Body> {
    use rustc_public::mir::{AggregateKind, Operand, Rvalue, StatementKind, TerminatorKind};
    let place = match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p,
        _ => return None,
    };
    let mut unique_def: Option<(rustc_public::ty::ClosureDef, rustc_public::ty::GenericArgs)> =
        None;
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(p, rv) = &stmt.kind else {
                continue;
            };
            if p.local != place.local {
                continue;
            }
            if !p.projection.is_empty() || unique_def.is_some() {
                return None;
            }
            match rv {
                Rvalue::Aggregate(AggregateKind::Closure(def, genargs), _fields) => {
                    unique_def = Some((*def, genargs.clone()));
                }
                _ => return None,
            }
        }
        if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
            && destination.local == place.local
        {
            return None;
        }
    }
    let (closure_def, closure_args) = unique_def?;
    debug!(
        local = place.local,
        closure = %closure_def.name(),
        "closure operand recovered via unique Aggregate(Closure) def walk (Wall-2 strategy b)"
    );
    [ClosureKind::FnOnce, ClosureKind::FnMut, ClosureKind::Fn].into_iter().find_map(|kind| {
        Instance::resolve_closure(closure_def, &closure_args, kind).ok().and_then(|instance| {
            // Transformed, scope-gated fetch — identical policy to
            // `resolve_closure_body_for_ty` (contract closures need the
            // mode-dispatched body; everything else gets the raw body).
            crate::kani_middle::transform::walker_transformed_body(tcx, instance)
        })
    })
}

/// Is this operand's type a closure (or `&closure`) at all? Discriminates the
/// benign "not a closure" `None` from "closure whose body fetch failed" so the
/// register-contract dispatchers can demote the latter (fail-closed) instead of
/// silently falling through to generic havoc dispatch.
pub(in crate::codegen_ay::chc) fn operand_is_closure_shaped(
    operand: &rustc_public::mir::Operand,
    locals: &[LocalDecl],
) -> bool {
    let Ok(ty) = operand.ty(locals) else {
        return false;
    };
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Closure(..)) => true,
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => {
            matches!(inner.kind(), TyKind::RigidTy(RigidTy::Closure(..)))
        }
        _ => false,
    }
}

pub(super) fn resolve_closure_body_for_ty(
    tcx: rustc_middle::ty::TyCtxt,
    closure_ty: rustc_public::ty::Ty,
) -> Option<rustc_public::mir::Body> {
    let (closure_def, closure_args, kinds) = match closure_ty.kind() {
        TyKind::RigidTy(RigidTy::Closure(def, args)) => {
            (def, args, [ClosureKind::FnOnce, ClosureKind::FnMut, ClosureKind::Fn])
        }
        TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Closure(..))) =>
        {
            let TyKind::RigidTy(RigidTy::Closure(def, args)) = inner.kind() else {
                unreachable!("guard ensures inner closure type");
            };
            (def, args, [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce])
        }
        _ => return None,
    };

    kinds.into_iter().find_map(|kind| {
        Instance::resolve_closure(closure_def, &closure_args, kind).ok().and_then(|instance| {
            // TRANSFORMED fetch (scope-gated): contract check/replace closures
            // carry the kani_contract_mode dispatch + FC-06 frame markers ONLY
            // in their transformed bodies; raw bodies leave walked contract
            // checks vacuous. Non-contract closures get the raw body verbatim
            // (walker_wants_transformed is false), so this is byte-identical
            // outside contract machinery.
            crate::kani_middle::transform::walker_transformed_body(tcx, instance)
        })
    })
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(super) fn is_register_contract_fn<T: CrateDef>(&self, fn_def: T) -> bool {
        fn_marker(fn_def).as_deref() == Some("kani_register_contract")
    }

    pub(in crate::codegen_ay::chc) fn try_dispatch_call_register_contract(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: rustc_public::mir::BasicBlockIdx,
    ) -> bool {
        let Some(closure_arg) = dcx.args.first() else {
            return false;
        };
        let Some(closure_body) =
            resolve_closure_body_for_operand(self.tcx, closure_arg, self.body.locals())
                // Wall-2 strategy (b): opaque operand type — recover the
                // closure from its unique Aggregate(Closure) defining assign
                // (fail-closed walk). Demotion below stays the fallback.
                .or_else(|| {
                    resolve_closure_body_via_unique_aggregate_def(self.tcx, closure_arg, self.body)
                })
        else {
            // A register_contract arg that IS closure-shaped but yields no body
            // (transform-panic fail-close in walker_transformed_body, or an
            // unresolvable instance) means the contract closure's checks are
            // LOST on the fall-through havoc path — demote (fail-closed)
            // instead of silently continuing.
            if operand_is_closure_shaped(closure_arg, self.body.locals()) {
                debug!(
                    bb_idx = dcx.bb_idx,
                    "closure: register_contract closure body unavailable — demoting (fail-closed)"
                );
                self.record_fallback();
            }
            return false;
        };
        let captures = self.extract_closure_env_captures(closure_arg, dcx.modified_locals);
        // P2 S3 Stage A: scope-guard the contract-closure walk so untracked
        // writebacks inside it fail closed (terminator_exec.rs) instead of
        // silently fabricating contract-visible state.
        self.register_contract_walk_depth += 1;
        let inline_result =
            translate_closure_inline_result(self, &closure_body, &[], &captures, dcx.bb_idx, 0);
        self.register_contract_walk_depth -= 1;
        let Some(inline_result) = inline_result else {
            // Contract closure resolved but the inline walk failed: its checks
            // are lost on the fall-through path — demote (fail-closed).
            debug!(
                bb_idx = dcx.bb_idx,
                "closure: register_contract closure inline failed — demoting (fail-closed)"
            );
            self.record_fallback();
            return false;
        };
        debug!(
            bb_idx = dcx.bb_idx,
            callee = dcx.callee_path.as_deref().unwrap_or("<kani_register_contract>"),
            capture_count = captures.len(),
            "closure: lowered kani_register_contract as direct closure inline"
        );
        self.emit_closure_inline_result(dcx, target, Some(closure_arg), inline_result);
        true
    }
}
