// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared Vec-builder pattern helpers for CHC codegen.
//!
//! Part of #3348: detects `Bits::from_u64`-style push loops and synthesizes
//! concrete `Vec<bool>` backing arrays from the source bitvector.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{BinOp, Body, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};

pub(in crate::codegen_ay::chc) fn make_vec_builder_data_expr(
    dest_local: usize,
    data_sort: &ay_bindings::Sort,
    vec_data_expr: Option<&Expr>,
) -> Expr {
    vec_data_expr
        .filter(|expr| expr.sort() == data_sort)
        .cloned()
        .or_else(|| build_from_u64_bool_data_expr(data_sort, vec_data_expr))
        .unwrap_or_else(|| {
            super::declare_pending_var(format!("vec_builder_data_{dest_local}"), data_sort.clone())
        })
}

fn build_from_u64_bool_data_expr(
    data_sort: &ay_bindings::Sort,
    value_expr: Option<&Expr>,
) -> Option<Expr> {
    let value_expr = value_expr?;
    let array_sort = data_sort.array_sort()?;
    if !array_sort.element_sort.is_bool() || value_expr.sort().bitvec_width() != Some(64) {
        return None;
    }

    let index_width = array_sort.index_sort.bitvec_width()?;
    let mut data = Expr::const_array(array_sort.index_sort.clone(), Expr::bool_const(false));
    for bit in 0..64u64 {
        let idx = Expr::bitvec_const(bit, index_width);
        let bit_is_one =
            value_expr.clone().extract(bit as u32, bit as u32).eq(Expr::bitvec_const(1u64, 1));
        data = data.store(idx, bit_is_one);
    }
    Some(data)
}

pub(in crate::codegen_ay::chc) fn detect_from_u64_value_param_idx(body: &Body) -> Option<usize> {
    for push_value_local in push_value_locals_in_loops(body) {
        if !local_has_bool_const_assignment(body, push_value_local, false) {
            continue;
        }
        let Some(bitand_local) = find_eq_const_assignment_local(body, push_value_local, 1) else {
            continue;
        };
        let Some((shift_value_local, shift_index_local)) =
            find_shift_assignment(body, bitand_local)
        else {
            continue;
        };
        if !has_lt_const_check(body, shift_index_local, 64) {
            continue;
        }
        if let Some(param_idx) = trace_local_to_param(body, shift_value_local) {
            return Some(param_idx);
        }
    }
    None
}

fn push_value_locals_in_loops(body: &Body) -> Vec<usize> {
    let mut locals = Vec::new();
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        let TerminatorKind::Call { func, args, target, .. } = &block.terminator.kind else {
            continue;
        };
        let Some(callee_name) = resolve_callee_name(func, body) else {
            continue;
        };
        if !callee_name.ends_with("::push") || !is_vec_method(&callee_name) {
            continue;
        }
        let Some(target_bb) = target else { continue };
        if !has_back_edge(body, *target_bb, bb_idx) {
            continue;
        }
        let Some(push_value_local) = args.get(1).and_then(extract_operand_local) else {
            continue;
        };
        locals.push(push_value_local);
    }
    locals
}

fn local_has_bool_const_assignment(body: &Body, dest_local: usize, expected: bool) -> bool {
    body.blocks.iter().flat_map(|block| &block.statements).any(|stmt| {
        let StatementKind::Assign(place, Rvalue::Use(op)) = &stmt.kind else {
            return false;
        };
        place.local == dest_local
            && place.projection.is_empty()
            && extract_operand_const_bool(op) == Some(expected)
    })
}

fn find_eq_const_assignment_local(
    body: &Body,
    dest_local: usize,
    expected_const: u128,
) -> Option<usize> {
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                continue;
            };
            if place.local != dest_local || !place.projection.is_empty() {
                continue;
            }
            let Rvalue::BinaryOp(BinOp::Eq, lhs, rhs) = rvalue else {
                continue;
            };
            if extract_operand_const_uint(lhs) == Some(expected_const) {
                if let Some(local) = extract_operand_local(rhs) {
                    return Some(local);
                }
            }
            if extract_operand_const_uint(rhs) == Some(expected_const) {
                if let Some(local) = extract_operand_local(lhs) {
                    return Some(local);
                }
            }
        }
    }
    None
}

fn find_shift_assignment(body: &Body, dest_local: usize) -> Option<(usize, usize)> {
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                continue;
            };
            if place.local != dest_local || !place.projection.is_empty() {
                continue;
            }
            let Rvalue::BinaryOp(BinOp::BitAnd, lhs, rhs) = rvalue else {
                continue;
            };
            let shift_local = if extract_operand_const_uint(lhs) == Some(1) {
                extract_operand_local(rhs)
            } else if extract_operand_const_uint(rhs) == Some(1) {
                extract_operand_local(lhs)
            } else {
                None
            }?;
            for block in &body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                        continue;
                    };
                    if place.local != shift_local || !place.projection.is_empty() {
                        continue;
                    }
                    let Rvalue::BinaryOp(BinOp::Shr | BinOp::ShrUnchecked, value, index) = rvalue
                    else {
                        continue;
                    };
                    let Some(value_local) = extract_operand_local(value) else {
                        continue;
                    };
                    let Some(index_local) = extract_operand_local(index) else {
                        continue;
                    };
                    return Some((value_local, index_local));
                }
            }
        }
    }
    None
}

fn has_lt_const_check(body: &Body, local: usize, upper_bound: u128) -> bool {
    body.blocks.iter().flat_map(|block| &block.statements).any(|stmt| {
        let StatementKind::Assign(_, Rvalue::BinaryOp(BinOp::Lt, lhs, rhs)) = &stmt.kind else {
            return false;
        };
        extract_operand_local(lhs) == Some(local)
            && extract_operand_const_uint(rhs) == Some(upper_bound)
    })
}

pub(in crate::codegen_ay::chc) fn extract_operand_const_uint(operand: &Operand) -> Option<u128> {
    use rustc_public::ty::{ConstantKind, TyConstKind};

    let Operand::Constant(const_op) = operand else { return None };
    match const_op.const_.kind() {
        ConstantKind::Allocated(alloc) => alloc.read_uint().ok(),
        ConstantKind::Ty(ty_const) => match ty_const.kind() {
            TyConstKind::Value(_value_ty, alloc) => alloc.read_uint().ok(),
            _ => None,
        },
        _ => None,
    }
}

fn extract_operand_const_bool(operand: &Operand) -> Option<bool> {
    use rustc_public::ty::{ConstantKind, TyConstKind};

    let Operand::Constant(const_op) = operand else { return None };
    match const_op.const_.kind() {
        ConstantKind::Allocated(alloc) => alloc.read_bool().ok(),
        ConstantKind::Ty(ty_const) => match ty_const.kind() {
            TyConstKind::Value(_value_ty, alloc) => alloc.read_bool().ok(),
            _ => None,
        },
        _ => None,
    }
}

/// Check whether a local is provably zero by following copy/cast/deref chains.
///
/// Accepts a direct constant `0` or a local that reaches `0` through
/// `Rvalue::Use`, `Rvalue::Cast`, and `Rvalue::CopyForDeref` within a small
/// step budget.  Returns `false` for params, arithmetic, or anything
/// non-trivial.  Part of #3610.
pub(in crate::codegen_ay::chc) fn local_is_known_zero(body: &Body, mut local: usize) -> bool {
    use std::collections::HashSet;
    let mut visited = HashSet::new();
    for _ in 0..10 {
        if !visited.insert(local) {
            return false;
        }
        let mut found_zero = false;
        let mut found_source = None;
        let mut assign_count = 0u32;
        for block in &body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if place.local != local || !place.projection.is_empty() {
                    continue;
                }
                assign_count += 1;
                match rvalue {
                    Rvalue::Use(op) => {
                        if extract_operand_const_uint(op) == Some(0) {
                            found_zero = true;
                        } else if let Some(src) = extract_operand_local(op) {
                            found_source = Some(src);
                        }
                    }
                    Rvalue::Cast(_, op, _) => {
                        if extract_operand_const_uint(op) == Some(0) {
                            found_zero = true;
                        } else if let Some(src) = extract_operand_local(op) {
                            found_source = Some(src);
                        }
                    }
                    Rvalue::CopyForDeref(place_src) if place_src.projection.is_empty() => {
                        found_source = Some(place_src.local);
                    }
                    _ => {}
                }
            }
        }
        // Only accept zero if there is exactly one assignment (no reassignment).
        if found_zero && assign_count == 1 {
            return true;
        }
        // Follow copy chain if exactly one non-zero source found.
        match found_source {
            Some(src) if assign_count == 1 => local = src,
            _ => return false,
        }
    }
    false
}

/// Trace a local variable back to a function parameter through copy chains.
pub(in crate::codegen_ay::chc) fn trace_local_to_param(
    body: &Body,
    mut local: usize,
) -> Option<usize> {
    let param_count = body.arg_locals().len();
    if local >= 1 && local <= param_count {
        return Some(local - 1);
    }
    for _ in 0..10 {
        let mut found_source = None;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                    if place.local == local && place.projection.is_empty() {
                        if let Rvalue::Use(op) = rvalue {
                            if let Some(src) = extract_operand_local(op) {
                                found_source = Some(src);
                            }
                        }
                    }
                }
            }
        }
        match found_source {
            Some(src) if src >= 1 && src <= param_count => return Some(src - 1),
            Some(src) => local = src,
            None => return None,
        }
    }
    None
}

pub(in crate::codegen_ay::chc) fn extract_operand_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
        _ => None,
    }
}

pub(in crate::codegen_ay::chc) fn resolve_callee_name(
    func: &Operand,
    body: &Body,
) -> Option<String> {
    let func_ty = func.ty(body.locals()).ok()?;
    match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, _)) => Some(def.trimmed_name()),
        _ => None,
    }
}

pub(in crate::codegen_ay::chc) fn is_vec_method(name: &str) -> bool {
    name.contains("Vec")
        || name.contains("vec")
        || name.contains("alloc::vec")
        || name.contains("RawVec")
}

pub(in crate::codegen_ay::chc) fn has_back_edge(
    body: &Body,
    from_bb: usize,
    threshold_bb: usize,
) -> bool {
    if from_bb <= threshold_bb {
        return true;
    }
    if from_bb < body.blocks.len() {
        match &body.blocks[from_bb].terminator.kind {
            TerminatorKind::Goto { target } => *target <= threshold_bb,
            TerminatorKind::SwitchInt { targets, .. } => {
                targets.branches().any(|(_, t)| t <= threshold_bb)
                    || targets.otherwise() <= threshold_bb
            }
            _ => false,
        }
    } else {
        false
    }
}
