// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared inline-body size heuristics used by CHC and BMC call inlining.

use rustc_public::mir::TerminatorKind;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::{RigidTy, TyKind};

use crate::kani_middle::attributes;

/// Maximum number of effective blocks in a body eligible for inline translation.
pub(in crate::codegen_ay) const MAX_INLINE_EFFECTIVE_BLOCKS: usize = 16;

/// Relaxed limit for tiny helper bodies that only grow because of `kani::*` marker expansion.
const MAX_INLINE_KANI_HELPER_BLOCKS: usize = 40;

/// Count reachable success-path blocks, excluding unwind-only edges.
pub(in crate::codegen_ay) fn count_effective_blocks(body: &rustc_public::mir::Body) -> usize {
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
            // Part of #4050: Drop terminators have a normal-path successor
            // that must be counted. Without this, drop shim bodies (e.g.,
            // drop_in_place::<ArraySolver> with 6 Vec fields) report
            // effective_blocks ≈ 1, causing the walker visit_limit to be
            // too small and the inline walk to bail prematurely.
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
    reachable.iter().filter(|&&is_reachable| is_reachable).count()
}

fn body_contains_kani_markers(body: &rustc_public::mir::Body) -> bool {
    for block in &body.blocks {
        if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
            let Ok(func_ty) = func.ty(body.locals()) else {
                continue;
            };
            if let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() {
                if let Ok(instance) = Instance::resolve(def, &args)
                    && attributes::fn_marker(instance.def).is_some()
                {
                    return true;
                }
                if attributes::fn_marker(def).is_some() {
                    return true;
                }
            }
        }
    }
    false
}

/// Return the inline block limit for `body`, applying the relaxed Kani-helper budget when needed.
pub(in crate::codegen_ay) fn inline_effective_block_limit(
    body: &rustc_public::mir::Body,
    effective_blocks: usize,
) -> usize {
    if effective_blocks > MAX_INLINE_EFFECTIVE_BLOCKS && body_contains_kani_markers(body) {
        MAX_INLINE_KANI_HELPER_BLOCKS
    } else {
        MAX_INLINE_EFFECTIVE_BLOCKS
    }
}
