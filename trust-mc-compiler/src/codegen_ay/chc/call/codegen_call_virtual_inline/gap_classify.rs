// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Rvalue gap classification for inline walker diagnostics.
//!
//! Extracted from `statement_exec.rs` to keep it under the 500-line limit.
//! Part of #4050: enriched gap diagnostics for pop_restores_assignments.

use ay_bindings::Expr;
use rustc_public::mir::LocalDecl;
use std::collections::HashMap;

/// Classify a rvalue gap as root-cause or cascading, with the rvalue variant.
///
/// Part of #4050: enriched gap reason enables the exact-file diagnostic to
/// distinguish root-cause inline walker limitations from cascading failures
/// where a prior local was already missing.
pub(super) fn classify_rvalue_gap(
    rvalue: &rustc_public::mir::Rvalue,
    local_exprs: &HashMap<usize, Expr>,
    locals: &[LocalDecl],
) -> String {
    use rustc_public::mir::{AggregateKind, Rvalue};

    // Check if any operand references an unpopulated local (cascading).
    let has_missing_operand = match rvalue {
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_refs_missing(lhs, local_exprs) || operand_refs_missing(rhs, local_exprs)
        }
        Rvalue::UnaryOp(_, operand) | Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
            operand_refs_missing(operand, local_exprs)
        }
        Rvalue::Aggregate(_, operands) => {
            operands.iter().any(|op| operand_refs_missing(op, local_exprs))
        }
        Rvalue::Repeat(operand, _) => operand_refs_missing(operand, local_exprs),
        Rvalue::Ref(_, _, place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place) => !local_exprs.contains_key(&place.local),
        _ => false,
    };

    let cause = if has_missing_operand { "cascade" } else { "root" };

    match rvalue {
        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) if !place.projection.is_empty() => {
            format!("rvalue_gap_Ref_projected_{cause}")
        }
        Rvalue::Aggregate(kind, operands) if !has_missing_operand => {
            // Root Aggregate failure — classify by aggregate kind and operand count.
            let kind_tag = match kind {
                AggregateKind::Adt(def, variant, _, _, _) => {
                    use crate::rustc_public_bridge::IndexedVal;
                    let adt_name = format!("{:?}", def);
                    let short_name = adt_name.rsplit("::").next().unwrap_or(&adt_name);
                    format!("Adt_{short_name}_v{}", variant.to_index())
                }
                AggregateKind::Tuple => "Tuple".to_string(),
                AggregateKind::Array(_) => "Array".to_string(),
                AggregateKind::Closure(..) => "Closure".to_string(),
                AggregateKind::Coroutine(..) => "Coroutine".to_string(),
                _ => "Other".to_string(),
            };
            format!("rvalue_gap_Aggregate_root_{kind_tag}_ops{}", operands.len())
        }
        Rvalue::BinaryOp(op, lhs, _) if !has_missing_operand => {
            // Root BinaryOp failure — include the op and LHS type.
            let lhs_ty_tag = lhs
                .ty(locals)
                .ok()
                .map(|ty| format!("{:?}", ty.kind()))
                .unwrap_or_else(|| "unknown".to_string());
            let short_ty = lhs_ty_tag.split('(').next().unwrap_or(&lhs_ty_tag);
            format!("rvalue_gap_BinaryOp_root_{op:?}_{short_ty}")
        }
        Rvalue::Use(operand) if !has_missing_operand => {
            // Root Use failure — the operand is a projected place.
            let detail = match operand {
                rustc_public::mir::Operand::Copy(place)
                | rustc_public::mir::Operand::Move(place) => {
                    if place.projection.is_empty() {
                        "flat"
                    } else {
                        "projected"
                    }
                }
                rustc_public::mir::Operand::Constant(_) => "const",
            };
            format!("rvalue_gap_Use_root_{detail}")
        }
        _ => {
            let variant_name = match rvalue {
                Rvalue::BinaryOp(..) => "BinaryOp",
                Rvalue::CheckedBinaryOp(..) => "CheckedBinaryOp",
                Rvalue::UnaryOp(..) => "UnaryOp",
                Rvalue::Use(..) => "Use",
                Rvalue::Aggregate(..) => "Aggregate",
                Rvalue::Cast(..) => "Cast",
                Rvalue::Ref(..) | Rvalue::AddressOf(..) => "Ref",
                Rvalue::CopyForDeref(..) => "CopyForDeref",
                Rvalue::Discriminant(..) => "Discriminant",
                Rvalue::Len(..) => "Len",
                Rvalue::Repeat(..) => "Repeat",
                Rvalue::NullaryOp(..) => "NullaryOp",
                _ => "Other",
            };
            format!("rvalue_gap_{variant_name}_{cause}")
        }
    }
}

/// Check if an operand references a local that is not in `local_exprs`.
fn operand_refs_missing(
    operand: &rustc_public::mir::Operand,
    local_exprs: &HashMap<usize, Expr>,
) -> bool {
    match operand {
        rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place) => {
            place.projection.is_empty() && !local_exprs.contains_key(&place.local)
        }
        rustc_public::mir::Operand::Constant(_) => false,
    }
}
