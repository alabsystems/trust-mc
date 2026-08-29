// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Quantifier encoding for CHC codegen.
//!
//! Translates `kani::forall!`/`kani::exists!` into unrolled AY expressions.
//! Handles closure MIR parsing, capture resolution, and closure body translation.
//!
//! Extracted from codegen_call_kani.rs via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//! Decomposed into submodules — Part of #2408.

mod closure_body;
mod closure_captures;
mod helpers;

use ay_bindings::{Expr, ExprValue, SortInner};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{LocalDecl, Operand, StatementKind};
use rustc_public::ty::{ClosureKind, RigidTy, TyKind};
use std::collections::{HashMap, HashSet};
use tracing::{debug, warn};

use super::ChcCtx;
use super::call::inline_shared::{PlaceResolver, inline_operand_to_expr};

pub(in crate::codegen_ay) use closure_body::{
    ClosureBodyResult, translate_closure_body_as_expr, translate_closure_body_with_params,
};
pub(in crate::codegen_ay::chc) use closure_captures::{
    extract_closure_captures, extract_inline_closure_captures,
};
pub(in crate::codegen_ay::chc) use helpers::resolve_debug_const_quantifier_bound;
use helpers::{
    linear_predecessor_chain, replay_quantifier_local_assignments,
    resolve_debug_const_quantifier_local,
};

/// Extension trait for quantifier encoding on `ChcCtx`.
///
/// These methods handle the translation of `kani::forall!`/`kani::exists!`
/// closures into AY quantified expressions (unrolled for PDR compatibility).
pub(super) trait QuantifierEncoding {
    /// Build a quantified AY expression from kani::forall!/exists! MIR args.
    ///
    /// Translates `kani_forall(lower, upper, closure)` into
    /// `P(lo) && P(lo+1) && ... && P(hi-1)` (forall) or the disjunction (exists).
    ///
    /// Returns None if quantifier translation fails (closure body too complex,
    /// bounds untranslatable, etc.) — caller falls back to nondet.
    fn build_quantifier_expr(
        &mut self,
        func: &Operand,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        bb_idx: usize,
        is_forall: bool,
    ) -> Option<Expr>;

    fn build_inline_quantifier_expr(
        &mut self,
        func: &Operand,
        args: &[Operand],
        locals: &[LocalDecl],
        local_exprs: &HashMap<usize, Expr>,
        resolver: &PlaceResolver<'_>,
        bb_idx: usize,
        is_forall: bool,
    ) -> Option<Expr>;

    /// Convert a MIR BinOp to a AY binary expression.
    ///
    /// `signed`: `Some(true)` = signed, `Some(false)` = unsigned, `None` = default signed.
    /// `int_bv_width`: BV width for Int-to-BV round-trip on Int-lifted locals (Part of #3043).
    #[must_use]
    fn binop_to_expr(
        &self,
        op: rustc_public::mir::BinOp,
        lhs: Expr,
        rhs: Expr,
        signed: Option<bool>,
        int_bv_width: u32,
    ) -> Option<Expr>;
}

/// Maximum range size for finite quantifier unrolling.
/// PDR rejects quantifiers inside recursive CHC rules, so we unroll
/// `forall(x in lo..hi, P(x))` into `P(lo) && P(lo+1) && ... && P(hi-1)`.
/// Raised from 256 to 2048: the Kani test suite includes harnesses with
/// ranges up to 1000 (e.g., `Quantifiers/even.rs` uses `(0, 1000)`).
/// Z3 handles the resulting conjunction/disjunction efficiently since each
/// instance is a small closed-form BV expression with no internal branching.
pub(in crate::codegen_ay) const QUANTIFIER_UNROLL_LIMIT: u64 = 2048;

impl<'tcx, 'body> QuantifierEncoding for ChcCtx<'tcx, 'body> {
    fn build_quantifier_expr(
        &mut self,
        func: &Operand,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        bb_idx: usize,
        is_forall: bool,
    ) -> Option<Expr> {
        if args.len() < 3 {
            warn!(?bb_idx, "quantifier call with < 3 args");
            return None;
        }

        debug!(
            "build_quantifier_expr bb{} is_forall={} args.len={}",
            bb_idx,
            is_forall,
            args.len()
        );

        // Translate bounds
        let lower = resolve_quantifier_bound_operand(self, &args[0], modified_locals, bb_idx)?;
        let upper = resolve_quantifier_bound_operand(self, &args[1], modified_locals, bb_idx)?;

        // Extract constant bound values for finite unrolling.
        // PDR explicitly rejects quantifiers inside recursive CHC rules, so we
        // must unroll to a finite conjunction/disjunction for constant bounds.
        let (lower_val, upper_val, bv_width) = extract_constant_bounds(&lower, &upper)?;
        let range_size = upper_val.saturating_sub(lower_val);
        if range_size > QUANTIFIER_UNROLL_LIMIT {
            warn!(
                ?bb_idx,
                lower_val, upper_val, range_size, "quantifier range too large for unrolling"
            );
            return None;
        }

        // Extract closure from func's generic args
        let func_ty = func.ty(self.body.locals()).ok()?;
        let (_fn_def, fn_args) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return None, // external enum: TyKind
        };

        // Extract captured variable expressions from the closure aggregate.
        let captured_exprs = extract_closure_captures(self, &args[2], modified_locals, bb_idx);

        debug!("quantifier captures={} range={}..{}", captured_exprs.len(), lower_val, upper_val);

        // Find the Closure type arg and resolve its MIR body.
        // Try all closure kinds: Fn, FnMut, FnOnce — FnMut/FnOnce closures fail
        // to resolve as Fn, causing the quantifier to silently become nondeterministic.
        // (Part of #2440)
        let mut closure_body: Option<rustc_public::mir::Body> = None;
        for arg in &fn_args.0 {
            let Some(arg_ty) = arg.ty() else { continue };
            if let TyKind::RigidTy(RigidTy::Closure(def, closure_args)) = arg_ty.kind() {
                for kind in [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce] {
                    if let Ok(instance) =
                        Instance::resolve_closure(def, &closure_args, kind.clone())
                        && let Some(body) = instance.body()
                    {
                        debug!(
                            "quantifier closure found (kind={kind:?}), blocks={} locals={}",
                            body.blocks.len(),
                            body.locals().len()
                        );
                        closure_body = Some(body);
                        break;
                    }
                }
                if closure_body.is_some() {
                    break;
                }
            }
        }
        let closure_body = closure_body?;

        // Unroll: evaluate the closure body for each value in [lower_val, upper_val).
        // Part of #2440: collect both predicates and no-panic guards per instance.
        let mut predicates: Vec<Expr> = Vec::with_capacity(range_size as usize);
        let mut safety_guards: Vec<Expr> = Vec::new();
        for i in lower_val..upper_val {
            let qvar_concrete = if let Some(width) = bv_width {
                Expr::bitvec_const(i, width)
            } else {
                Expr::int_const(i)
            };
            let ClosureBodyResult { pred, no_panic_guard } = translate_closure_body_as_expr(
                self,
                &closure_body,
                &qvar_concrete,
                &captured_exprs,
                bb_idx,
            )?;
            predicates.push(pred);
            if let Some(guard) = no_panic_guard {
                safety_guards.push(guard);
            }
        }

        if predicates.is_empty() {
            let bounds_are_literal = quantifier_bounds_are_literal_consts(args);
            if !bounds_are_literal {
                warn!(
                    ?bb_idx,
                    lower_val,
                    upper_val,
                    "empty quantifier range from non-literal bounds; failing closed (nondet fallback)"
                );
            }
            return empty_quantifier_range_expr(is_forall, bounds_are_literal);
        }

        // Combine predicates: conjunction for forall, disjunction for exists.
        let quantifier_result = predicates
            .into_iter()
            .reduce(|a, b| if is_forall { a.and(b) } else { a.or(b) })
            .unwrap_or_else(|| Expr::bool_const(is_forall));

        // Part of #2440: Conjoin all no-panic guards. The quantifier result is
        // only meaningful when ALL iterations are panic-free. For `exists`, this
        // prevents a witness on iteration N from masking a panic on iteration M.
        let result = if safety_guards.is_empty() {
            quantifier_result
        } else {
            let all_safe = safety_guards
                .into_iter()
                .reduce(|a, b| a.and(b))
                .expect("invariant: safety_guards is non-empty");
            debug!("quantifier: conjoining no-panic guards with quantifier result (#2440)");
            all_safe.and(quantifier_result)
        };

        debug!("quantifier unrolled {} instances for {}..{}", range_size, lower_val, upper_val);

        Some(result)
    }

    fn build_inline_quantifier_expr(
        &mut self,
        func: &Operand,
        args: &[Operand],
        locals: &[LocalDecl],
        local_exprs: &HashMap<usize, Expr>,
        resolver: &PlaceResolver<'_>,
        bb_idx: usize,
        is_forall: bool,
    ) -> Option<Expr> {
        if args.len() < 3 {
            warn!(?bb_idx, "inline quantifier call with < 3 args");
            return None;
        }

        let lower = inline_operand_to_expr(self, &args[0], local_exprs, resolver, locals)?;
        let upper = inline_operand_to_expr(self, &args[1], local_exprs, resolver, locals)?;
        let (lower_val, upper_val, bv_width) = extract_constant_bounds(&lower, &upper)?;
        let range_size = upper_val.saturating_sub(lower_val);
        if range_size > QUANTIFIER_UNROLL_LIMIT {
            warn!(
                ?bb_idx,
                lower_val, upper_val, range_size, "inline quantifier range too large for unrolling"
            );
            return None;
        }

        let closure_body = resolve_quantifier_closure_body(func, locals)?;
        let captured_exprs =
            extract_inline_closure_captures(self, &args[2], local_exprs, resolver, locals);

        let mut predicates = Vec::with_capacity(range_size as usize);
        let mut safety_guards = Vec::new();
        for i in lower_val..upper_val {
            let qvar_concrete = if let Some(width) = bv_width {
                Expr::bitvec_const(i, width)
            } else {
                Expr::int_const(i)
            };
            let ClosureBodyResult { pred, no_panic_guard } = translate_closure_body_as_expr(
                self,
                &closure_body,
                &qvar_concrete,
                &captured_exprs,
                bb_idx,
            )?;
            predicates.push(pred);
            if let Some(guard) = no_panic_guard {
                safety_guards.push(guard);
            }
        }

        if predicates.is_empty() {
            let bounds_are_literal = quantifier_bounds_are_literal_consts(args);
            if !bounds_are_literal {
                warn!(
                    ?bb_idx,
                    lower_val,
                    upper_val,
                    "empty inline quantifier range from non-literal bounds; failing closed"
                );
            }
            return empty_quantifier_range_expr(is_forall, bounds_are_literal);
        }

        let quantifier_result = predicates
            .into_iter()
            .reduce(|a, b| if is_forall { a.and(b) } else { a.or(b) })
            .unwrap_or_else(|| Expr::bool_const(is_forall));

        if safety_guards.is_empty() {
            Some(quantifier_result)
        } else {
            let all_safe = safety_guards
                .into_iter()
                .reduce(|a, b| a.and(b))
                .expect("invariant: safety_guards is non-empty");
            Some(all_safe.and(quantifier_result))
        }
    }

    fn binop_to_expr(
        &self,
        op: rustc_public::mir::BinOp,
        lhs: Expr,
        rhs: Expr,
        signed: Option<bool>,
        int_bv_width: u32,
    ) -> Option<Expr> {
        // Part of #2440: Delegate to the canonical translate_binop which handles
        // width coercion (mixed-width BV operands), Shl/Shr/Cmp operators,
        // Eq/Ne sort-mismatch guards, Real sort support, and bitwise coercion.
        //
        // Previously this was a separate 100+ line implementation that lacked all
        // coercion, causing AY sort errors on mixed-width bitvec operands in closures
        // and missing Shl/Shr/Cmp entirely.
        let is_signed = signed.unwrap_or_else(|| {
            crate::codegen_ay::shared::signedness_fallback_for_binop(
                op,
                "quantifier_encoding::binop_to_expr",
            )
        });
        self.translate_binop(op, lhs, rhs, is_signed, int_bv_width, false)
    }
}

pub(in crate::codegen_ay) fn resolve_quantifier_closure_body(
    func: &Operand,
    locals: &[LocalDecl],
) -> Option<rustc_public::mir::Body> {
    let func_ty = func.ty(locals).ok()?;
    let (_fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => return None,
    };

    for arg in &fn_args.0 {
        let Some(arg_ty) = arg.ty() else { continue };
        if let TyKind::RigidTy(RigidTy::Closure(def, closure_args)) = arg_ty.kind() {
            for kind in [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce] {
                if let Ok(instance) = Instance::resolve_closure(def, &closure_args, kind)
                    && let Some(body) = instance.body()
                {
                    return Some(body);
                }
            }
        }
    }
    None
}

// --- Internal helper functions (not part of the trait) ---

/// True when both quantifier bound operands (`args[0]` = lower, `args[1]` =
/// upper) are literal constants at the MIR callsite (`Operand::Constant`),
/// i.e. the resolved range did not pass through any local-resolution
/// heuristic (assignment replay / debug-const recovery).
fn quantifier_bounds_are_literal_consts(args: &[Operand]) -> bool {
    matches!(args.first(), Some(Operand::Constant(_)))
        && matches!(args.get(1), Some(Operand::Constant(_)))
}

/// Encode a quantifier whose unrolled range is empty.
///
/// `forall` over an empty set is vacuously `true` and `exists` is `false` —
/// but emitting that constant is only sound when the emptiness is CERTAIN,
/// i.e. both bounds were literal constants at the callsite. When a bound was
/// resolved through locals, a mis-resolved bound can collapse a real range to
/// empty, and a vacuously-true `forall` then silently discharges the property
/// (proof-side soundness hole — Quantifiers B1). In that case fail closed
/// with `None`, which routes every caller to its sound nondet fallback
/// (assert(nondet) always fails, assume(nondet) over-approximates).
fn empty_quantifier_range_expr(is_forall: bool, bounds_are_literal: bool) -> Option<Expr> {
    if bounds_are_literal { Some(Expr::bool_const(is_forall)) } else { None }
}

/// Extract constant u64 values and BV width from bound expressions.
///
/// Returns `(lower_val, upper_val, bv_width)` where `bv_width` is `Some(w)`
/// for bitvector bounds or `None` for integer bounds.
pub(in crate::codegen_ay) fn extract_constant_bounds(
    lower: &Expr,
    upper: &Expr,
) -> Option<(u64, u64, Option<u32>)> {
    let folded_lower = fold_quantifier_constant_expr(lower)?;
    let folded_upper = fold_quantifier_constant_expr(upper)?;
    match (folded_lower.value(), folded_upper.value()) {
        (
            ExprValue::BitVecConst { value: lo, width: w1 },
            ExprValue::BitVecConst { value: hi, width: w2 },
        ) if w1 == w2 => {
            let lo_u64 = u64::try_from(lo).ok()?;
            let hi_u64 = u64::try_from(hi).ok()?;
            Some((lo_u64, hi_u64, Some(*w1)))
        }
        (ExprValue::IntConst(lo), ExprValue::IntConst(hi)) => {
            let lo_u64 = u64::try_from(lo).ok()?;
            let hi_u64 = u64::try_from(hi).ok()?;
            Some((lo_u64, hi_u64, None))
        }
        _ => {
            // external enum: ExprValue
            debug!("extract_constant_bounds: non-constant bounds");
            None
        }
    }
}

fn fold_quantifier_constant_expr(expr: &Expr) -> Option<Expr> {
    match expr.value() {
        ExprValue::BitVecConst { .. } | ExprValue::IntConst(_) | ExprValue::BoolConst(_) => {
            Some(expr.clone())
        }
        ExprValue::BvAdd(lhs, rhs) => fold_quantifier_bv_binop(lhs, rhs, QuantifierConstBinOp::Add),
        ExprValue::BvSub(lhs, rhs) => fold_quantifier_bv_binop(lhs, rhs, QuantifierConstBinOp::Sub),
        ExprValue::BvMul(lhs, rhs) => fold_quantifier_bv_binop(lhs, rhs, QuantifierConstBinOp::Mul),
        ExprValue::IntAdd(lhs, rhs) => {
            fold_quantifier_int_binop(lhs, rhs, QuantifierConstBinOp::Add)
        }
        ExprValue::IntSub(lhs, rhs) => {
            fold_quantifier_int_binop(lhs, rhs, QuantifierConstBinOp::Sub)
        }
        ExprValue::IntMul(lhs, rhs) => {
            fold_quantifier_int_binop(lhs, rhs, QuantifierConstBinOp::Mul)
        }
        ExprValue::DatatypeSelector { selector_name, expr, .. } => {
            fold_quantifier_datatype_selector(selector_name, expr)
        }
        _ => None,
    }
}

enum QuantifierConstBinOp {
    Add,
    Sub,
    Mul,
}

fn fold_quantifier_bv_binop(lhs: &Expr, rhs: &Expr, op: QuantifierConstBinOp) -> Option<Expr> {
    let lhs = fold_quantifier_constant_expr(lhs)?;
    let rhs = fold_quantifier_constant_expr(rhs)?;
    let (
        ExprValue::BitVecConst { value: lhs_value, width: lhs_width },
        ExprValue::BitVecConst { value: rhs_value, width: rhs_width },
    ) = (lhs.value(), rhs.value())
    else {
        return None;
    };
    if lhs_width != rhs_width {
        return None;
    }
    let value = match op {
        QuantifierConstBinOp::Add => lhs_value.clone() + rhs_value.clone(),
        QuantifierConstBinOp::Sub => lhs_value.clone() - rhs_value.clone(),
        QuantifierConstBinOp::Mul => lhs_value.clone() * rhs_value.clone(),
    };
    Some(Expr::bitvec_const(value, *lhs_width))
}

fn fold_quantifier_int_binop(lhs: &Expr, rhs: &Expr, op: QuantifierConstBinOp) -> Option<Expr> {
    let lhs = fold_quantifier_constant_expr(lhs)?;
    let rhs = fold_quantifier_constant_expr(rhs)?;
    let (ExprValue::IntConst(lhs_value), ExprValue::IntConst(rhs_value)) =
        (lhs.value(), rhs.value())
    else {
        return None;
    };
    let value = match op {
        QuantifierConstBinOp::Add => lhs_value.clone() + rhs_value.clone(),
        QuantifierConstBinOp::Sub => lhs_value.clone() - rhs_value.clone(),
        QuantifierConstBinOp::Mul => lhs_value.clone() * rhs_value.clone(),
    };
    Some(Expr::int_const(value))
}

fn fold_quantifier_datatype_selector(selector_name: &str, expr: &Expr) -> Option<Expr> {
    let folded_expr = fold_quantifier_constant_expr(expr)?;
    let ExprValue::DatatypeConstructor { constructor_name, args, .. } = folded_expr.value() else {
        return None;
    };
    let SortInner::Datatype(datatype) = folded_expr.sort().inner() else {
        return None;
    };
    let constructor =
        datatype.constructors.iter().find(|constructor| constructor.name == *constructor_name)?;
    let field_idx = constructor.fields.iter().position(|field| field.name == selector_name)?;
    fold_quantifier_constant_expr(args.get(field_idx)?)
}

/// Resolve a quantifier bound operand using callsite-local constant propagation
/// before falling back to the normal CHC state translation.
///
/// Quantifier macros often lower constant bounds through one or two locals
/// (`let upper = 20; kani::forall(1, upper, ...)`). The CHC state translation
/// sees those locals as symbolic state vars, which makes `extract_constant_bounds`
/// reject them and forces the hook down the nondeterministic fallback path.
/// Replaying unique plain-local assignments from the prefix of the current body
/// (up to the call block) recovers the concrete bound expression for these
/// callsite-local constants even when earlier `kani::assume` calls have split
/// the control flow into multiple MIR basic blocks.
fn resolve_quantifier_bound_operand<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    operand: &Operand,
    modified_locals: &HashSet<usize>,
    bb_idx: usize,
) -> Option<Expr> {
    let locals = ctx.body.locals();
    if ctx.body.blocks.get(bb_idx).is_none() {
        return ctx.translate_operand_with_modified(operand, modified_locals);
    }
    let resolver = PlaceResolver::Captures(&[]);
    let replay_blocks = linear_predecessor_chain(ctx, bb_idx);
    let mut assign_counts: HashMap<usize, usize> = HashMap::new();
    for &block_idx in &replay_blocks {
        let Some(block) = ctx.body.blocks.get(block_idx) else { continue };
        for stmt in &block.statements {
            if let StatementKind::Assign(place, _) = &stmt.kind
                && place.projection.is_empty()
            {
                *assign_counts.entry(place.local).or_insert(0) += 1;
            }
        }
    }

    // Seed with name-gated debug-const recoveries (locals whose assignment was
    // const-propagated away and survives only in var_debug_info). These are
    // heuristic GUESSES: the replay below overwrites them with the actual
    // single-assignment semantics wherever an assignment still exists in MIR
    // (Quantifiers B1 — replayed values take priority over debug-const guesses).
    let mut local_exprs: HashMap<usize, Expr> = ctx
        .body
        .local_decls()
        .filter_map(|(local, _)| {
            resolve_debug_const_quantifier_local(ctx, local).map(|expr| (local, expr))
        })
        .collect();
    for &block_idx in &replay_blocks {
        let Some(block) = ctx.body.blocks.get(block_idx) else { continue };
        replay_quantifier_local_assignments(
            ctx,
            &block.statements,
            &assign_counts,
            &resolver,
            &locals,
            &mut local_exprs,
        );
    }

    if let Operand::Copy(place) | Operand::Move(place) = operand
        && place.projection.is_empty()
        && assign_counts.get(&place.local).copied().unwrap_or(0) == 1
        && let Some(expr) = local_exprs.get(&place.local).cloned()
    {
        return Some(expr);
    }

    inline_operand_to_expr(ctx, operand, &local_exprs, &resolver, &locals)
        .or_else(|| resolve_debug_const_quantifier_bound(ctx, operand))
        .or_else(|| ctx.translate_operand_with_modified(operand, modified_locals))
}

// linear_predecessor_chain, replay_quantifier_local_assignments,
// inline_quantifier_rvalue_expr, resolve_debug_const_quantifier_bound,
// resolve_debug_const_quantifier_local, identifier_source_snippet
// moved to helpers.rs per #4206.

#[cfg(test)]
mod tests {
    use super::*;
    use ay_bindings::Expr;

    /// Small bitvec bounds extract correctly.
    #[test]
    fn test_extract_constant_bounds_bv_small() {
        let lo = Expr::bitvec_const(3u64, 32);
        let hi = Expr::bitvec_const(10u64, 32);
        let result = extract_constant_bounds(&lo, &hi);
        assert_eq!(result, Some((3, 10, Some(32))));
    }

    /// Int-const bounds extract correctly for small positive values.
    #[test]
    fn test_extract_constant_bounds_int_const_small() {
        let lo = Expr::int_const(0u64);
        let hi = Expr::int_const(5u64);
        let result = extract_constant_bounds(&lo, &hi);
        assert_eq!(result, Some((0, 5, None)));
    }

    /// Int-const bounds near u64::MAX extract correctly (regression for #2544).
    /// Before the fix, `Expr::int_const(i as i64)` would wrap values > i64::MAX
    /// to negative BigInt, causing `u64::try_from` to fail and silently drop
    /// the quantifier.
    #[test]
    fn test_extract_constant_bounds_int_const_large_positive() {
        let large_val = u64::MAX - 5;
        let lo = Expr::int_const(large_val);
        let hi = Expr::int_const(u64::MAX);
        let result = extract_constant_bounds(&lo, &hi);
        assert_eq!(result, Some((large_val, u64::MAX, None)));
    }

    /// Empty range (lo == hi) extracts as a valid zero-width range.
    #[test]
    fn test_extract_constant_bounds_empty_range() {
        let val = Expr::bitvec_const(7u64, 16);
        let result = extract_constant_bounds(&val, &val);
        assert_eq!(result, Some((7, 7, Some(16))));
    }

    /// Empty range with literal-constant bounds keeps the vacuous truth value:
    /// forall over the empty set is `true`, exists is `false`.
    #[test]
    fn test_empty_quantifier_range_literal_bounds_vacuous_truth() {
        let forall = empty_quantifier_range_expr(true, true).expect("literal forall");
        assert!(matches!(forall.value(), ExprValue::BoolConst(true)));
        let exists = empty_quantifier_range_expr(false, true).expect("literal exists");
        assert!(matches!(exists.value(), ExprValue::BoolConst(false)));
    }

    /// Quantifiers B1: an empty range whose bounds did NOT come from two
    /// literal constants must fail closed (None -> caller's sound nondet
    /// fallback) instead of collapsing to vacuous truth. A mis-resolved bound
    /// that collapses the range would otherwise turn an asserted-false forall
    /// into `assert(true)` — a proof-side soundness hole.
    #[test]
    fn test_empty_quantifier_range_nonliteral_bounds_fails_closed() {
        assert!(empty_quantifier_range_expr(true, false).is_none());
        assert!(empty_quantifier_range_expr(false, false).is_none());
    }

    /// Mixed sorts (one BV, one Int) returns None.
    #[test]
    fn test_extract_constant_bounds_mixed_sorts_returns_none() {
        let bv = Expr::bitvec_const(0u64, 32);
        let int = Expr::int_const(10u64);
        assert!(extract_constant_bounds(&bv, &int).is_none());
        assert!(extract_constant_bounds(&int, &bv).is_none());
    }

    /// Width mismatch returns None.
    #[test]
    fn test_extract_constant_bounds_width_mismatch_returns_none() {
        let lo = Expr::bitvec_const(0u64, 32);
        let hi = Expr::bitvec_const(10u64, 64);
        assert!(extract_constant_bounds(&lo, &hi).is_none());
    }
}
