// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Nested `kani_register_contract(closure)` helpers.

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{AggregateKind, Operand, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{HashMap, HashSet};
use tracing::debug;

use super::super::ChcCtx;
use super::super::codegen_call_closure::resolve_closure_body_for_operand;
use super::super::codegen_types::CodegenTypes;
use super::super::inline_body::InlineReturn;
use super::super::inline_shared::{PlaceResolver, inline_operand_to_expr};
use crate::codegen_ay::provenance::is_value_widened_into_address;
use crate::codegen_ay::ptr_repr::PtrSlot;

fn extract_nested_closure_captures<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    closure_arg: &Operand,
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Vec<Expr> {
    let closure_local = match closure_arg {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => place.local,
        _ => return Vec::new(),
    };

    for block in &outer_body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(
                place,
                Rvalue::Aggregate(AggregateKind::Closure(_, _), fields),
            ) = &stmt.kind
                && place.local == closure_local
            {
                return fields
                    .iter()
                    .filter_map(|op| {
                        resolve_nested_closure_capture_expr(
                            ctx,
                            op,
                            outer_body,
                            local_exprs,
                            resolver,
                        )
                    })
                    .collect();
            }
        }
    }

    // Part of #4003: Fallback — extract captures from the receiver's AY expression.
    // When a closure is passed through a function boundary (e.g., `takes_dyn_fun(fun: &dyn Fn)`),
    // the outer_body is the intermediate function's body, which has no Aggregate(Closure).
    // The receiver's local_exprs value IS the closure aggregate (due to deref-as-identity),
    // so extract cap_N fields directly from the AY expression.
    extract_captures_from_ay_expr(local_exprs, closure_local)
}

/// Extract closure captures from a AY expression that represents a closure aggregate.
///
/// Part of #4003: When closures cross function boundaries via `&dyn Fn`, the MIR body
/// scan cannot find the Aggregate(Closure) statement. The AY expression in local_exprs
/// already holds the closure value — either as a DatatypeConstructor (direct) or as a
/// datatype-sorted variable whose fields can be extracted via field_select.
fn extract_captures_from_ay_expr(
    local_exprs: &HashMap<usize, Expr>,
    closure_local: usize,
) -> Vec<Expr> {
    let Some(receiver_expr) = local_exprs.get(&closure_local) else {
        return Vec::new();
    };

    // Case 1: DatatypeConstructor — extract args directly (preserves constants).
    if let ExprValue::DatatypeConstructor { args, .. } = receiver_expr.value() {
        if !args.is_empty() {
            debug!(
                closure_local,
                capture_count = args.len(),
                "extract_captures_from_ay_expr: extracted from DatatypeConstructor (#4003)"
            );
            return args.clone();
        }
    }

    // Case 2: Datatype-sorted expression — extract via field_select on first constructor.
    if let ay_bindings::SortInner::Datatype(dt) = receiver_expr.sort().inner() {
        if let Some(cons) = dt.constructors.first() {
            if !cons.fields.is_empty() {
                let fields: Vec<Expr> = cons
                    .fields
                    .iter()
                    .map(|field| {
                        receiver_expr.clone().field_select(
                            &dt.name,
                            &field.name,
                            field.sort.clone(),
                        )
                    })
                    .collect();
                debug!(
                    closure_local,
                    capture_count = fields.len(),
                    "extract_captures_from_ay_expr: extracted via field_select (#4003)"
                );
                return fields;
            }
        }
    }

    Vec::new()
}

/// Is the term resolved for a `&T`-typed capture local the ADDRESS of the
/// referent (peel on to the referent) rather than the referent's own value?
///
/// # What the retired guard got wrong
///
/// The test used to be "the local is `Ref`-typed AND the term is pointer-width",
/// read as "what I am holding is the address, so keep peeling". That reading is
/// unavailable from a width: the inline walker models references transparently,
/// so a `&T` local's term is very often the referent's VALUE already — and when
/// `T` is itself pointer-width (`&usize`, `&u64`, `&fn()`) that value is a
/// `bv(POINTER_WIDTH)` indistinguishable from an address. The peel then ran on
/// past the correct answer, up to the loop's six hops, and returned some
/// unrelated ancestor local's term.
///
/// # What decides it now
///
/// The MIR pointee type, which the walker's own transparent-reference model
/// makes decisive: if the referent's sort is the sort we are holding, then what
/// we are holding *is* (or is indistinguishable from) the referent's value, and
/// there is nothing left to peel. Only a term that cannot be the referent's
/// value is treated as its address.
///
/// Both remaining refusals are honest about their limits rather than papering
/// over them: an unresolvable pointee sort answers `false` (stop, we cannot
/// tell), and so does a `&&T` / `&Box<T>` capture whose pointee is itself
/// pointer-width — genuinely ambiguous, and stopping keeps a real term instead
/// of gambling on another hop. The width comparison that survives is a
/// representation precondition (`PtrSlot::Thin`), and the widened-value refusal
/// keeps a zero-extended narrow datum from re-entering through it.
fn should_peel_capture_reference(
    ctx: &ChcCtx<'_, '_>,
    outer_body: &rustc_public::mir::Body,
    local: usize,
    expr: &Expr,
) -> bool {
    let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) =
        ctx.resolve_body_ty(outer_body.locals()[local].ty).kind()
    else {
        return false;
    };
    if PtrSlot::of_sort(expr.sort()) != Some(PtrSlot::Thin) || is_value_widened_into_address(expr) {
        return false;
    }
    let Some(pointee_sort) = ChcCtx::translate_ty(ctx.resolve_body_ty(pointee)) else {
        return false;
    };
    pointee_sort != *expr.sort()
}

fn resolve_nested_closure_capture_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    operand: &Operand,
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<Expr> {
    let mut current = operand.clone();
    let mut visited = HashSet::new();

    for _ in 0..6 {
        let maybe_local = match &current {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        };

        if let Some(expr) =
            inline_operand_to_expr(ctx, &current, local_exprs, resolver, outer_body.locals())
        {
            let keep_peeling = maybe_local
                .is_some_and(|local| should_peel_capture_reference(ctx, outer_body, local, &expr));
            if !keep_peeling {
                return Some(expr);
            }
        }

        let Some(local) = maybe_local else {
            return inline_operand_to_expr(
                ctx,
                &current,
                local_exprs,
                resolver,
                outer_body.locals(),
            );
        };
        if !visited.insert(local) {
            break;
        }
        let Some(next_local) = find_nested_closure_capture_source_local(outer_body, local) else {
            break;
        };
        current =
            Operand::Copy(rustc_public::mir::Place { local: next_local, projection: Vec::new() });
    }

    inline_operand_to_expr(ctx, &current, local_exprs, resolver, outer_body.locals())
}

fn find_nested_closure_capture_source_local(
    outer_body: &rustc_public::mir::Body,
    local: usize,
) -> Option<usize> {
    for block in &outer_body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                continue;
            };
            if place.local != local || !place.projection.is_empty() {
                continue;
            }
            match rvalue {
                Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src) if src.projection.is_empty() => {
                    return Some(src.local);
                }
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                    if src.projection.is_empty() =>
                {
                    return Some(src.local);
                }
                _ => {}
            }
        }
    }
    None
}

pub(super) fn nested_fn_trait_closure_captures<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    args: &[Operand],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Vec<Expr> {
    args.first().map_or_else(Vec::new, |receiver| {
        extract_nested_closure_captures(ctx, receiver, outer_body, local_exprs, resolver)
    })
}

pub(super) fn try_inline_register_contract<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    args: &[Operand],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    let closure_arg = args.first()?;
    let closure_body =
        match resolve_closure_body_for_operand(ctx.tcx, closure_arg, outer_body.locals())
            // Wall-2 strategy (b): opaque operand type — recover the closure from
            // its unique Aggregate(Closure) defining assign in the WALKED body
            // (fail-closed walk). Demotion below stays the fallback.
            .or_else(|| {
                super::super::codegen_call_closure::resolve_closure_body_via_unique_aggregate_def(
                    ctx.tcx,
                    closure_arg,
                    outer_body,
                )
            }) {
            Some(b) => b,
            None => {
                // Closure-shaped register_contract arg with no resolvable body:
                // the contract closure's checks are lost on the havoc fallback —
                // demote (fail-closed) before bailing.
                if super::super::codegen_call_closure::operand_is_closure_shaped(
                    closure_arg,
                    outer_body.locals(),
                ) {
                    ctx.record_fallback();
                }
                return None;
            }
        };
    let captures =
        extract_nested_closure_captures(ctx, closure_arg, outer_body, local_exprs, resolver);
    // Thread caller depth + 1 so `#[kani::recursion]` contract closures that
    // re-enter `kani_register_contract` cannot inline unboundedly (previously
    // the last arg was a hardcoded `0` bb_idx and the depth reset to 0 inside,
    // defeating MAX_INLINE_DEPTH → stack overflow / SIGABRT). On exhaustion the
    // walker returns None and the nested-call fallback havocs the result.
    //
    // P2 S3 Stage A: scope-guard the contract-closure walk so untracked
    // writebacks inside it fail closed (terminator_exec.rs) instead of
    // silently fabricating contract-visible state.
    ctx.register_contract_walk_depth += 1;
    let result = super::super::inline_body::translate_closure_inline_result(
        ctx,
        &closure_body,
        &[],
        &captures,
        0,
        inline_depth + 1,
    );
    ctx.register_contract_walk_depth -= 1;
    result
}
