// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pre-scan pass for constant-foldable math intrinsic calls.
//!
//! Scans all MIR blocks for Call terminators with constant-foldable math
//! intrinsic arguments and stores folded results in `const_folded_call_results`
//! before any block encoding begins. This handles block-order dependencies:
//! a subtraction block may be encoded before the exp() call block, so the
//! constant must be available upfront. Part of #3839.
//!
//! Split from `math_const.rs` per file size limit.
//!
//! Host-target assumption (#3885): the constant folders below call the host
//! Rust `f32`/`f64` intrinsics during verification-time prescan. That is only
//! sound while trust_mc verifies for the same floating-point target semantics as
//! the host running the compiler. Cross-target FP verification must disable or
//! replace this prescan with target-aware folding instead of reusing host
//! rounded results.

use std::collections::{HashMap, HashSet};

use ay_bindings::Expr;
use rustc_public::mir::{
    Body, BorrowKind, Mutability, Operand, RawPtrKind, Rvalue, StatementKind, TerminatorKind,
};

use super::super::ChcCtx;
use super::math_const::{try_extract_const_f32, try_extract_const_f64};

/// Pre-scan MIR to identify locals with exactly one assignment site.
///
/// Single-assignment locals have a unique value regardless of execution path,
/// making cross-block BV constant propagation sound for them. Multi-assignment
/// locals (e.g., `y` assigned in both branches of an `if`) are path-dependent
/// and must not be propagated cross-block (false PROOF at merge points, #3905).
pub(in crate::codegen_ay::chc) fn compute_single_assign_locals(ctx: &mut ChcCtx<'_, '_>) {
    let mut assign_counts: HashMap<usize, usize> = HashMap::new();
    for block in &ctx.body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, _) = &stmt.kind {
                if lhs.projection.is_empty() {
                    *assign_counts.entry(lhs.local).or_insert(0) += 1;
                }
            }
        }
        // Call terminators also assign to the destination local.
        if let TerminatorKind::Call { destination, .. } = &block.terminator.kind {
            *assign_counts.entry(destination.local).or_insert(0) += 1;
        }
    }
    // Part of #3937: Exclude locals that are ref_target referents.
    // These locals can be indirectly written through pointers (e.g.,
    // atomic_store(ptr, val) writes *ptr which resolves to the referent local).
    // The MIR assign count misses these indirect writes, so the local appears
    // single-assign when it actually has multiple values across blocks.
    let ref_target_referents: HashSet<usize> =
        ctx.ref_resolution.ref_targets.values().map(|rt| rt.local).collect();
    let shared_const_referents = shared_borrowed_const_referents(ctx.body);
    // Raw "written exactly once" set, WITHOUT the ref-target exclusion below.
    // Consumed only by the field-0 Box/pointer-wrapper provenance forward,
    // which pairs it with `deref_store_target_locals` for soundness.
    ctx.encode.raw_single_assign_locals =
        assign_counts.iter().filter(|&(_, &count)| count == 1).map(|(&local, _)| local).collect();
    ctx.encode.deref_store_target_locals = compute_deref_store_targets(ctx);
    // Field-0 provenance map is per-function; drop any prior harness's entries
    // before this body is (re)encoded.
    ctx.known_pointer_to_alloc.clear();
    ctx.encode.single_assign_locals = assign_counts
        .into_iter()
        .filter(|&(local, count)| {
            count == 1
                && (!ref_target_referents.contains(&local)
                    || shared_const_referents.contains(&local))
        })
        .map(|(local, _)| local)
        .collect();
}

/// Locals whose storage may be overwritten through a pointer: the referent of
/// any pointer that appears as the base of a Deref STORE (`(*p)… = v`).
///
/// A Deref store's base local is resolved to its referent via `ref_targets`.
/// Deref stores whose base does NOT resolve to a stack referent (e.g. writes
/// through a raw heap pointer) target heap storage, not a stack container, so
/// they cannot alias a Box/wrapper container local and are safely ignored here
/// — the field-0 forward only ever resolves containers to stack-slot obj_ids.
fn compute_deref_store_targets(ctx: &ChcCtx<'_, '_>) -> HashSet<usize> {
    use rustc_public::mir::{ProjectionElem, StatementKind};

    let mut targets = HashSet::new();
    for block in &ctx.body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, _) = &stmt.kind else {
                continue;
            };
            if !matches!(lhs.projection.first(), Some(ProjectionElem::Deref)) {
                continue;
            }
            // The base local is written through: mark its referent (if any).
            if let Some(rt) = ctx.ref_resolution.ref_targets.get(&lhs.local) {
                targets.insert(rt.local);
            }
            // Also mark the base local itself: a later copy may deref it too.
            targets.insert(lhs.local);
        }
    }
    targets
}

fn shared_borrowed_const_referents(body: &Body) -> HashSet<usize> {
    let mut direct_const_assigns = HashSet::new();
    let mut disqualified = HashSet::new();

    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                continue;
            };

            if lhs.projection.is_empty()
                && matches!(rvalue, Rvalue::Use(Operand::Constant(_)))
                && body
                    .locals()
                    .get(lhs.local)
                    .is_some_and(|decl| decl.mutability == Mutability::Not)
            {
                direct_const_assigns.insert(lhs.local);
            }

            match rvalue {
                Rvalue::Ref(_, borrow_kind, place) => {
                    if !matches!(borrow_kind, BorrowKind::Shared | BorrowKind::Fake(_)) {
                        disqualified.insert(place.local);
                    }
                }
                Rvalue::AddressOf(raw_ptr_kind, place) => {
                    if matches!(raw_ptr_kind, RawPtrKind::Mut) {
                        disqualified.insert(place.local);
                    }
                }
                _ => {}
            }
        }
    }

    direct_const_assigns.difference(&disqualified).copied().collect()
}

/// Pre-scan all blocks for constant-foldable math intrinsic calls and store
/// results in `const_folded_call_results`. This runs BEFORE block encoding
/// to handle block-order dependencies. Part of #3839.
pub(in crate::codegen_ay::chc) fn prescan_const_foldable_math_calls(ctx: &mut ChcCtx<'_, '_>) {
    use super::math::{detect_math_intrinsic, normalize_to_intrinsic_suffix};

    for block in &ctx.body.blocks {
        let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind else {
            continue;
        };
        let Some(callee_path) = ctx.resolve_callee_path(func) else {
            continue;
        };
        let Some(is_f32) = detect_math_intrinsic(&callee_path) else {
            continue;
        };
        let normalized = normalize_to_intrinsic_suffix(&callee_path);
        let callee = normalized.as_deref().unwrap_or(&callee_path);
        let dest_local: usize = destination.local;

        let folded = if is_f32 {
            try_fold_f32_intrinsic_body(callee, args, ctx.body)
                .map(|bits| Expr::bitvec_const(bits as u128, 32))
        } else {
            try_fold_f64_intrinsic_body(callee, args, ctx.body)
                .map(|bits| Expr::bitvec_const(bits as u128, 64))
        };
        if let Some(expr) = folded {
            ctx.encode.const_folded_call_results.insert(dest_local, expr);
        }
    }
}

/// Body-only f32 math intrinsic constant fold (no ChcCtx needed).
fn try_fold_f32_intrinsic_body(intrinsic_name: &str, args: &[Operand], body: &Body) -> Option<u32> {
    let arg0 = args.first()?;
    let bits0 = try_extract_const_f32(arg0, body)?;
    let val0 = f32::from_bits(bits0);
    let result = fold_f32_unary(intrinsic_name, val0)?;
    if result.is_nan() && !val0.is_nan() {
        return None;
    }
    Some(result.to_bits())
}

/// Body-only f64 math intrinsic constant fold (no ChcCtx needed).
fn try_fold_f64_intrinsic_body(intrinsic_name: &str, args: &[Operand], body: &Body) -> Option<u64> {
    let arg0 = args.first()?;
    let bits0 = try_extract_const_f64(arg0, body)?;
    let val0 = f64::from_bits(bits0);
    let result = fold_f64_unary(intrinsic_name, val0)?;
    if result.is_nan() && !val0.is_nan() {
        return None;
    }
    Some(result.to_bits())
}

fn fold_f32_unary(name: &str, val: f32) -> Option<f32> {
    // Binary/math intrinsics not listed here fall through to the normal sound
    // over-approximation path instead of being host-folded during prescan.
    if name.ends_with("sqrtf32") {
        Some(val.sqrt())
    } else if name.ends_with("sinf32") {
        Some(val.sin())
    } else if name.ends_with("cosf32") {
        Some(val.cos())
    } else if name.ends_with("expf32") {
        Some(val.exp())
    } else if name.ends_with("exp2f32") {
        Some(val.exp2())
    } else if name.ends_with("logf32") {
        Some(val.ln())
    } else if name.ends_with("log2f32") {
        Some(val.log2())
    } else if name.ends_with("log10f32") {
        Some(val.log10())
    } else if name.ends_with("fabsf32") {
        Some(val.abs())
    } else if name.ends_with("floorf32") {
        Some(val.floor())
    } else if name.ends_with("ceilf32") {
        Some(val.ceil())
    } else if name.ends_with("truncf32") {
        Some(val.trunc())
    } else if name.ends_with("roundf32") {
        Some(val.round())
    } else if name.ends_with("round_ties_even_f32") {
        Some(val.round_ties_even())
    } else {
        None
    }
}

fn fold_f64_unary(name: &str, val: f64) -> Option<f64> {
    // Keep the f64 prescan set aligned with the explicit f32 cases above.
    if name.ends_with("sqrtf64") {
        Some(val.sqrt())
    } else if name.ends_with("sinf64") {
        Some(val.sin())
    } else if name.ends_with("cosf64") {
        Some(val.cos())
    } else if name.ends_with("expf64") {
        Some(val.exp())
    } else if name.ends_with("exp2f64") {
        Some(val.exp2())
    } else if name.ends_with("logf64") {
        Some(val.ln())
    } else if name.ends_with("log2f64") {
        Some(val.log2())
    } else if name.ends_with("log10f64") {
        Some(val.log10())
    } else if name.ends_with("fabsf64") {
        Some(val.abs())
    } else if name.ends_with("floorf64") {
        Some(val.floor())
    } else if name.ends_with("ceilf64") {
        Some(val.ceil())
    } else if name.ends_with("truncf64") {
        Some(val.trunc())
    } else if name.ends_with("roundf64") {
        Some(val.round())
    } else if name.ends_with("round_ties_even_f64") {
        Some(val.round_ties_even())
    } else {
        None
    }
}
