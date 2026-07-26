// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CHC-only inline-budget relaxations.
//!
//! Shared inline policy stays limited to defaults that are intentionally common
//! across encodings. CHC-specific helper-body exceptions live here so BMC does
//! not inherit them implicitly.

use rustc_public::mir::TerminatorKind;
use rustc_public::ty::{RigidTy, TyKind};

use crate::codegen_ay::shared::{count_effective_blocks, inline_effective_block_limit};

/// Relaxed limit for small `&self`/`&mut self` helper orchestrators in CHC.
/// Part of #3830: raised from 32 to 40 to cover medium-complexity methods
/// like TableauRow::add_coeff (37 effective blocks) that contain while-loops
/// with nested calls to small helper functions.
const MAX_INLINE_REF_HELPER_BLOCKS: usize = 40;
/// Relaxed limit for raw-pointer assertion helpers used by ptr-comparison proofs.
///
/// The shared 16-block cap rejects helper packets like `compare_diff` /
/// `compare_equal`, which are branchy only because they expand many pointer
/// assertions. Keeping these on the precise CHC path avoids `P_inf_*` summaries
/// in `tests/trust_mc/PointerComparison/ptr_comparison.rs`.
const MAX_INLINE_RAW_PTR_HELPER_BLOCKS: usize = 48;
/// Limit helper-orchestrator fanout so the relaxed class stays narrow.
const MAX_INLINE_REF_HELPER_CALLS: usize = 4;

fn success_path_reachable_blocks(body: &rustc_public::mir::Body) -> Vec<bool> {
    let mut reachable = vec![false; body.blocks.len()];
    let mut work = vec![0usize];
    while let Some(bb) = work.pop() {
        if bb >= body.blocks.len() || reachable[bb] {
            continue;
        }
        reachable[bb] = true;
        match &body.blocks[bb].terminator.kind {
            TerminatorKind::Return => {}
            TerminatorKind::Goto { target } => work.push(*target),
            TerminatorKind::Assert { target, .. } => work.push(*target),
            TerminatorKind::Call { target: Some(target), .. } => work.push(*target),
            // Part of #4050: follow Drop normal-path successor (same fix as
            // count_effective_blocks in inline_limits.rs).
            TerminatorKind::Drop { target, .. } => work.push(*target),
            TerminatorKind::SwitchInt { targets, .. } => {
                for (_, target) in targets.branches() {
                    work.push(target);
                }
                work.push(targets.otherwise());
            }
            _ => {}
        }
    }
    reachable
}

fn ty_is_inline_scalar(ty: rustc_public::ty::Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_))
    )
}

fn ty_is_unit_or_inline_scalar(ty: rustc_public::ty::Ty) -> bool {
    ty_is_inline_scalar(ty)
        || matches!(ty.kind(), TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.is_empty())
}

fn ty_is_small_inline_aggregate(ty: rustc_public::ty::Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Tuple(fields)) => {
            !fields.is_empty()
                && fields.len() <= 2
                && fields.iter().all(|field_ty| ty_is_inline_scalar(*field_ty))
        }
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if def.kind() == rustc_public::ty::AdtKind::Struct =>
        {
            let variants = def.variants();
            let Some(variant) = variants.first() else {
                return false;
            };
            let fields = variant.fields();
            !fields.is_empty()
                && fields.len() <= 2
                && fields.iter().all(|field| ty_is_inline_scalar(field.ty_with_args(&args)))
        }
        _ => false,
    }
}

fn ty_is_small_inline_helper_arg(ty: rustc_public::ty::Ty) -> bool {
    ty_is_inline_scalar(ty)
        || ty_is_small_inline_aggregate(ty)
        || matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, inner, _)) if ty_is_inline_scalar(inner) || ty_is_small_inline_aggregate(inner))
}

fn ty_is_raw_pointer_helper_arg(ty: rustc_public::ty::Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(..)) => true,
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty_is_raw_pointer_helper_arg(inner),
        _ => false,
    }
}

fn body_is_small_raw_pointer_helper(body: &rustc_public::mir::Body) -> bool {
    let args = body.arg_locals();
    if args.len() < 2 || args.len() > 3 {
        return false;
    }
    if !args.iter().all(|local| ty_is_raw_pointer_helper_arg(local.ty)) {
        return false;
    }

    let Some(ret_local) = body.locals().first() else {
        return false;
    };
    matches!(ret_local.ty.kind(), TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.is_empty())
}

fn body_is_small_ref_receiver_helper(body: &rustc_public::mir::Body) -> bool {
    let [receiver, rest @ ..] = body.arg_locals() else {
        return false;
    };
    if !matches!(receiver.ty.kind(), TyKind::RigidTy(RigidTy::Ref(..))) {
        return false;
    }
    if !rest.iter().all(|local| ty_is_small_inline_helper_arg(local.ty)) {
        return false;
    }
    let Some(ret_local) = body.locals().first() else {
        return false;
    };
    if !ty_is_unit_or_inline_scalar(ret_local.ty) {
        return false;
    }

    let mut direct_call_count = 0usize;
    let reachable = success_path_reachable_blocks(body);
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        if !reachable[bb_idx] {
            continue;
        }
        match &block.terminator.kind {
            TerminatorKind::Return
            | TerminatorKind::Goto { .. }
            | TerminatorKind::Assert { .. }
            | TerminatorKind::SwitchInt { .. } => {}
            TerminatorKind::Call { func, .. } => {
                direct_call_count += 1;
                if direct_call_count > MAX_INLINE_REF_HELPER_CALLS {
                    return false;
                }
                let Ok(func_ty) = func.ty(body.locals()) else {
                    return false;
                };
                let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() else {
                    return false;
                };
                let Ok(instance) = rustc_public::mir::mono::Instance::resolve(def, &args) else {
                    return false;
                };
                let Some(callee_body) = instance.body() else {
                    return false;
                };
                let callee_effective = count_effective_blocks(&callee_body);
                if callee_effective > inline_effective_block_limit(&callee_body, callee_effective) {
                    return false;
                }
            }
            _ => return false,
        }
    }

    // Part of #3830: Allow zero-call bodies too. The receiver/arg/return type
    // filters are sufficient. remove_coeff (21 blocks, 0 calls) is a pure
    // while-loop body that should qualify for the relaxed limit.
    true
}

pub(in crate::codegen_ay::chc) fn chc_inline_effective_block_limit(
    body: &rustc_public::mir::Body,
    effective_blocks: usize,
) -> usize {
    let shared_limit = inline_effective_block_limit(body, effective_blocks);
    if effective_blocks > shared_limit
        && effective_blocks <= MAX_INLINE_RAW_PTR_HELPER_BLOCKS
        && body_is_small_raw_pointer_helper(body)
    {
        MAX_INLINE_RAW_PTR_HELPER_BLOCKS
    } else if effective_blocks > shared_limit
        && effective_blocks <= MAX_INLINE_REF_HELPER_BLOCKS
        && body_is_small_ref_receiver_helper(body)
    {
        MAX_INLINE_REF_HELPER_BLOCKS
    } else {
        shared_limit
    }
}
