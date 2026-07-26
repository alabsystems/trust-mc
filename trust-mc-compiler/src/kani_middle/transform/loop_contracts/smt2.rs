// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! SMT-LIB2 formula extraction from loop invariant closures.
//!
//! Part of #1562: Converts closure MIR to SMT-LIB2 format for CHC solver hints.

use super::LoopContractPass;
use rustc_public::mir::{Operand, Rvalue, Statement, StatementKind, TerminatorKind};
use rustc_public::ty::MirConst;
use std::collections::HashMap;

impl LoopContractPass {
    pub(super) fn extract_closure_formula(
        closure_def: rustc_public::ty::ClosureDef,
        generic_args: &rustc_public::ty::GenericArgs,
        captured_vars: &[usize],
    ) -> Option<String> {
        use rustc_public::mir::mono::Instance;
        use rustc_public::ty::ClosureKind;

        // Part of #40 (same bug class as the inliner fix in 114e35e86): the
        // closure's callable MIR lives on the `Fn`/`FnMut` instance; the
        // `FnOnce` `call_once` adapter shim has no MIR body. Resolving
        // `FnOnce` first silently yielded `None` for every invariant closure,
        // so no formula ever reached the driver's PDR hint pipeline. Try the
        // kinds with real bodies first.
        let body = [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce]
            .into_iter()
            .find_map(|kind| {
                Instance::resolve_closure(closure_def, generic_args, kind)
                    .ok()
                    .and_then(|instance| instance.body())
            })?;

        if body.blocks.len() != 1 {
            tracing::debug!(
                "extract_closure_formula: closure has {} blocks, expected 1",
                body.blocks.len()
            );
            return None;
        }

        let bb0 = &body.blocks[0];

        if !matches!(bb0.terminator.kind, TerminatorKind::Return) {
            tracing::debug!(
                "extract_closure_formula: unexpected terminator {:?}",
                bb0.terminator.kind
            );
            return None;
        }

        let return_expr = Self::find_return_value_formula(&bb0.statements, captured_vars);

        if return_expr.is_some() {
            tracing::debug!("extract_closure_formula: extracted formula: {:?}", return_expr);
        }

        return_expr
    }

    pub(super) fn find_return_value_formula(
        statements: &[Statement],
        captured_vars: &[usize],
    ) -> Option<String> {
        let mut local_exprs: HashMap<usize, String> = HashMap::new();

        for (idx, &var) in captured_vars.iter().enumerate() {
            local_exprs.insert(var, ["captured_", &idx.to_string()].concat());
        }

        for stmt in statements {
            if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                let local = place.local;
                if let Some(expr) = Self::rvalue_to_smt2(rvalue, &local_exprs) {
                    local_exprs.insert(local, expr);
                }
            }
        }

        local_exprs.get(&0).cloned()
    }

    pub(super) fn rvalue_to_smt2(
        rvalue: &Rvalue,
        local_exprs: &HashMap<usize, String>,
    ) -> Option<String> {
        match rvalue {
            Rvalue::BinaryOp(op, lhs, rhs) => {
                let lhs_expr = Self::operand_to_smt2(lhs, local_exprs)?;
                let rhs_expr = Self::operand_to_smt2(rhs, local_exprs)?;
                let op_str = Self::binop_to_smt2(*op)?;
                Some(format!("({} {} {})", op_str, lhs_expr, rhs_expr))
            }
            Rvalue::UnaryOp(rustc_public::mir::UnOp::Not, operand) => {
                let inner = Self::operand_to_smt2(operand, local_exprs)?;
                Some(format!("(not {})", inner))
            }
            Rvalue::Use(operand) => Self::operand_to_smt2(operand, local_exprs),
            Rvalue::Ref(_, _, place) | Rvalue::CopyForDeref(place) => {
                local_exprs.get(&place.local).cloned()
            }
            _ => {
                // external enum: Rvalue
                tracing::debug!("rvalue_to_smt2: unsupported rvalue {:?}", rvalue);
                None
            }
        }
    }

    pub(super) fn operand_to_smt2(
        operand: &Operand,
        local_exprs: &HashMap<usize, String>,
    ) -> Option<String> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if !place.projection.is_empty()
                    && let Some(last_proj) = place.projection.last()
                    && let rustc_public::mir::ProjectionElem::Field(idx, _) = last_proj
                {
                    return Some(["captured_", &idx.to_string()].concat());
                }
                local_exprs.get(&place.local).cloned()
            }
            Operand::Constant(const_op) => Self::const_to_smt2(&const_op.const_),
        }
    }

    pub(super) fn const_to_smt2(constant: &MirConst) -> Option<String> {
        use rustc_public::ty::{Allocation, ConstantKind, RigidTy, Ty, TyConstKind, TyKind};

        // `eval_target_usize` ICEs on non-usize integer constants ("expected
        // int of size 8, but got size 1") — e.g. the `2` in a `u8` invariant
        // `|x| *x >= 2`. Read the allocation bytes by the const's own type
        // instead (same pattern as `try_eval_const_operand`).
        let extract = |alloc: &Allocation, ty: Ty| -> Option<String> {
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Uint(_)) => alloc.read_uint().ok().map(|v| v.to_string()),
                TyKind::RigidTy(RigidTy::Int(_)) => {
                    let v = alloc.read_int().ok()?;
                    Some(if v < 0 { format!("(- {})", -v) } else { v.to_string() })
                }
                _ => None, // external enum: TyKind
            }
        };
        let result = match constant.kind() {
            ConstantKind::Allocated(alloc) => extract(alloc, constant.ty()),
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(value_ty, alloc) => extract(alloc, *value_ty),
                _ => None, // external enum: TyConstKind
            },
            _ => None, // external enum: ConstantKind
        };
        if result.is_none() {
            tracing::debug!("const_to_smt2: cannot evaluate constant {:?}", constant);
        }
        result
    }

    pub(super) fn binop_to_smt2(op: rustc_public::mir::BinOp) -> Option<&'static str> {
        use rustc_public::mir::BinOp;
        match op {
            BinOp::Ge => Some(">="),
            BinOp::Gt => Some(">"),
            BinOp::Le => Some("<="),
            BinOp::Lt => Some("<"),
            BinOp::Eq => Some("="),
            BinOp::Ne => Some("distinct"),
            BinOp::Add | BinOp::AddUnchecked => Some("+"),
            BinOp::Sub | BinOp::SubUnchecked => Some("-"),
            BinOp::Mul | BinOp::MulUnchecked => Some("*"),
            BinOp::BitAnd => Some("and"),
            BinOp::BitOr => Some("or"),
            BinOp::BitXor => Some("xor"),
            BinOp::Div => Some("div"),
            BinOp::Rem => Some("mod"),
            _ => {
                // external enum: BinOp
                tracing::debug!("binop_to_smt2: unsupported binop {:?}", op);
                None
            }
        }
    }
}
