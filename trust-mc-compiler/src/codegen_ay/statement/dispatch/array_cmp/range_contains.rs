// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Direct Range::contains lowering for BMC array comparison dispatch.

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{BasicBlockIdx, LocalDecl, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::statement::{IntoOption, StatementCodegen};
use crate::rustc_public::CrateDef;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Handle `Range::contains` and `RangeInclusive::contains` directly.
    ///
    /// The stdlib implementation goes through `RangeBounds::{start,end}_bound`
    /// and `Bound<&T>`. In BMC that path compares generated reference addresses
    /// instead of the pointee values after inlining. This keeps the call in value
    /// semantics: `start <= item && item < end`, or `item <= end` for inclusive
    /// ranges, with `!exhausted` for `RangeInclusive`.
    pub(super) fn try_codegen_range_contains(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let range_expr = self.get_value_through_ref(&args[0])?;
        let item_expr = self.get_value_through_ref(&args[1])?;
        let (start_expr, end_expr, exhausted_expr) = self.extract_range_fields(range_expr)?;

        let is_signed = self.operand_signedness(&args[1]).unwrap_or(false);
        let lower = build_range_le(start_expr, item_expr.clone(), is_signed)?;
        let upper = if range_contains_arg_is_inclusive(&args[0], self.body.locals()) {
            build_range_le(item_expr, end_expr, is_signed)?
        } else {
            build_range_lt(item_expr, end_expr, is_signed)?
        };

        let mut result = lower.and(upper);
        if let Some(exhausted) = exhausted_expr
            && exhausted.sort().is_bool()
        {
            result = result.and(exhausted.not());
        }

        debug!("array_cmp: lowering Range::contains to direct bound comparison (#3470)");
        self.bind_ssa_result(destination, result);
        target
    }

    fn extract_range_fields(&self, range_expr: Expr) -> Option<(Expr, Expr, Option<Expr>)> {
        let range_expr = self.resolve_range_concrete_expr(&range_expr);
        if let ExprValue::Ite { cond, then_expr, else_expr } = range_expr.value() {
            if self.current_path_contains_conjunct(&cond) {
                return self.extract_range_fields(then_expr.clone());
            }
            if self.current_path_contains_negated_conjunct(&cond) {
                return self.extract_range_fields(else_expr.clone());
            }
        }

        if let ExprValue::DatatypeConstructor { args, .. } = range_expr.value()
            && args.len() >= 2
        {
            return Some((args[0].clone(), args[1].clone(), args.get(2).cloned()));
        }

        let dt = range_expr.sort().datatype_sort()?;
        let cons = dt.constructors.first()?;
        let start_field = cons.fields.iter().find(|field| field.name == "fld_start")?;
        let end_field = cons.fields.iter().find(|field| field.name == "fld_end")?;
        let exhausted_field = cons.fields.iter().find(|field| field.name == "fld_exhausted");

        let start =
            range_expr.clone().field_select(&dt.name, &start_field.name, start_field.sort.clone());
        let end =
            range_expr.clone().field_select(&dt.name, &end_field.name, end_field.sort.clone());
        let exhausted = exhausted_field.map(|field| {
            range_expr.clone().field_select(&dt.name, &field.name, field.sort.clone())
        });

        Some((start, end, exhausted))
    }

    fn resolve_range_concrete_expr(&self, expr: &Expr) -> Expr {
        if let ExprValue::Var { name } = expr.value()
            && let Some(concrete) = self.ssa_concrete_values.get(name)
        {
            return concrete.clone();
        }
        expr.clone()
    }

    fn current_path_contains_conjunct(&self, needle: &Expr) -> bool {
        self.current_path_condition
            .as_ref()
            .is_some_and(|path| expr_contains_conjunct(path, needle))
    }

    fn current_path_contains_negated_conjunct(&self, needle: &Expr) -> bool {
        self.current_path_condition
            .as_ref()
            .is_some_and(|path| expr_contains_negated_conjunct(path, needle))
    }
}

pub(super) fn is_range_contains_call(callee_path: &str) -> bool {
    let is_contains = callee_path.ends_with("::contains") || callee_path.contains("::contains");
    if !is_contains {
        return false;
    }

    callee_path.contains("RangeBounds")
        || callee_path.contains("RangeInclusive")
        || callee_path.contains("ops::range::Range")
}

fn range_contains_arg_is_inclusive(arg: &Operand, locals: &[LocalDecl]) -> bool {
    if let Some(ty) = arg.ty(locals).into_option() {
        let mut current = ty;
        for _ in 0..3 {
            match current.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => current = inner,
                TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                    return def.trimmed_name().contains("RangeInclusive");
                }
                _ => return false,
            }
        }
    }
    false
}

fn expr_contains_conjunct(expr: &Expr, needle: &Expr) -> bool {
    if expr == needle {
        return true;
    }
    match expr.value() {
        ExprValue::And(args) => args.iter().any(|arg| expr_contains_conjunct(arg, needle)),
        _ => false,
    }
}

fn expr_contains_negated_conjunct(expr: &Expr, needle: &Expr) -> bool {
    match expr.value() {
        ExprValue::Not(inner) if inner == needle => true,
        ExprValue::And(args) => args.iter().any(|arg| expr_contains_negated_conjunct(arg, needle)),
        _ => false,
    }
}

fn build_range_le(lhs: Expr, rhs: Expr, is_signed: bool) -> Option<Expr> {
    if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
        let (lhs, rhs) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, is_signed);
        return Some(if is_signed { lhs.bvsle(rhs) } else { lhs.bvule(rhs) });
    }
    if lhs.sort().is_int() && rhs.sort().is_int() {
        return Some(lhs.int_le(rhs));
    }
    None
}

fn build_range_lt(lhs: Expr, rhs: Expr, is_signed: bool) -> Option<Expr> {
    if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
        let (lhs, rhs) = StatementCodegen::coerce_to_match_widths_typed(lhs, rhs, is_signed);
        return Some(if is_signed { lhs.bvslt(rhs) } else { lhs.bvult(rhs) });
    }
    if lhs.sort().is_int() && rhs.sort().is_int() {
        return Some(lhs.int_lt(rhs));
    }
    None
}
