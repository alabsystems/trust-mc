// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC state-variable plumbing for the congruent float-binop tables.
//!
//! Symbolic f32/f64 Add/Sub/Mul/Div/Rem have no direct CHC encoding: PDR
//! cannot reason about FP theory terms in CHC bodies, and raw BV integer
//! arithmetic on float bit patterns produced false counterexamples (issue
//! 1739, family 2). `bv_float_binop_chc` therefore failed closed (`None`)
//! for symbolic operands, which havocked the destination AND recorded a
//! demoting `chc_fallback` — flipping sound AY PROOFs to FAILED
//! (Intrinsics/FastMath cluster).
//!
//! Symbolic float value binops now translate to a CONGRUENT APPLICATION over
//! an unconstrained, read-only table instead:
//!
//! ```text
//! result = select(float_binop_tbl_f<w>, op_tag(8) ++ lhs(w) ++ rhs(w))
//! ```
//!
//! One table per float width (f32: `Array(BV72 → BV32)`, f64:
//! `Array(BV136 → BV64)`), threaded through every Horn relation like the
//! `obj_valid`/`obj_size` heap-metadata arrays but NEVER modified: the table
//! is not marked modified anywhere, so `build_output_args` always passes the
//! input variable through to successor relation heads. ay-bindings has no
//! first-class UF application, so array-select provides congruence: the same
//! `(op, lhs, rhs)` yields the same result term at every translation site
//! (regular BinOp statements AND `f*_fast` intrinsic calls route through
//! `float_binop_chc_term`, so congruence holds by construction).
//!
//! SOUNDNESS (for proofs): the table is never constrained — not in the entry
//! rule, not anywhere — so the real IEEE 754 operation is one interpretation
//! of it. Any property proven over ALL interpretations of the table therefore
//! holds under real float semantics. No algebraic axioms (commutativity etc.)
//! are added. Bug-finding is restored by the companion NaN-generation
//! obligation (Kani `--nan-check` parity, `codegen_stmt_safety_checks.rs`):
//! it fails closed on any symbolic float binop whose operands are not
//! provably non-NaN sources, keeping a live error edge over the table term.
//!
//! The tables are declared ONLY when a pre-scan of the MIR body finds a float
//! value binop (or fast-math intrinsic) with potentially-symbolic operands,
//! so ordinary harnesses keep their relation arity unchanged.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BinOp, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{FloatTy, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::float_arithmetic::{bv_float_binop_chc, is_float_arithmetic_op};

use super::ChcCtx;
use super::call::codegen_call_cmp_string::fast_math::detect_fast_math_intrinsic;

pub(in crate::codegen_ay::chc) const FLOAT_BINOP_TBL_F32: &str = "float_binop_tbl_f32";
pub(in crate::codegen_ay::chc) const FLOAT_BINOP_TBL_F64: &str = "float_binop_tbl_f64";

/// Width of the op tag prepended to the concatenated operands in the key.
const FLOAT_BINOP_TAG_WIDTH: u32 = 8;

/// `(in_name, out_name)` for the congruent table of a float width.
/// Only f32/f64 have tables (f16/f128 keep the fail-closed fallback, matching
/// `bv_float_binop_chc`'s width support).
pub(in crate::codegen_ay::chc) fn float_binop_table_names(
    width: u32,
) -> Option<(&'static str, &'static str)> {
    match width {
        32 => Some((FLOAT_BINOP_TBL_F32, "float_binop_tbl_f32__out")),
        64 => Some((FLOAT_BINOP_TBL_F64, "float_binop_tbl_f64__out")),
        _ => None,
    }
}

/// Sort of the congruent table: `Array(BV(8 + 2·w) → BV(w))`.
pub(in crate::codegen_ay::chc) fn float_binop_table_sort(width: u32) -> Option<Sort> {
    float_binop_table_names(width)?;
    Some(Sort::array(Sort::bitvec(FLOAT_BINOP_TAG_WIDTH + 2 * width), Sort::bitvec(width)))
}

/// Op tag distinguishing the five float value ops in the table key.
/// Unchecked variants share the checked op's tag (identical value semantics),
/// and fast-math intrinsics map to the same tags via `BinOp` — deliberate:
/// `fadd_fast(x, y) == x + y` exactly on non-UB (finite-operand) paths, and
/// the operand-finiteness error rules covering the UB paths are unchanged.
fn float_binop_op_tag(op: BinOp) -> Option<u64> {
    Some(match op {
        BinOp::Add | BinOp::AddUnchecked => 0,
        BinOp::Sub | BinOp::SubUnchecked => 1,
        BinOp::Mul | BinOp::MulUnchecked => 2,
        BinOp::Div => 3,
        BinOp::Rem => 4,
        _ => return None,
    })
}

/// Build the table key `op_tag(8) ++ lhs(w) ++ rhs(w)` for a float binop.
///
/// Fails closed (`None`) on width mismatches so a mis-sorted `select` can
/// never be constructed.
pub(in crate::codegen_ay::chc) fn float_binop_congruent_key(
    op: BinOp,
    lhs: Expr,
    rhs: Expr,
    width: u32,
) -> Option<Expr> {
    let tag = float_binop_op_tag(op)?;
    if lhs.sort().bitvec_width() != Some(width) || rhs.sort().bitvec_width() != Some(width) {
        return None;
    }
    Some(Expr::bitvec_const(tag, FLOAT_BINOP_TAG_WIDTH).concat(lhs).concat(rhs))
}

/// P4-4: exact reflexive-subtraction boundary refinement.
///
/// When the operands are BITWISE equal and FINITE, IEEE 754 subtraction
/// (round-to-nearest, Rust's rounding mode) yields exactly +0.0 — this lets
/// `fp_equals` (`(a - b).abs() <= EPSILON`) discharge at exact boundaries
/// like `sine == 1.0` instead of leaving the difference a free table value.
///
/// GUARDS (mandatory — an unguarded x-x=0 axiom is UNSOUND):
/// - finiteness excludes NaN (NaN bit patterns compare bitwise-equal, but
///   NaN - NaN = NaN) and infinities (Inf - Inf = NaN);
/// - bitwise equality never conflates 0.0 with -0.0 (distinct bits), and
///   (-0.0) - (-0.0) = +0.0 under RNE, matching the refinement.
///
/// This is a term REFINEMENT (an ite selecting the exact value on the
/// guarded branch, the free table value otherwise), so congruence by
/// construction is preserved and no rule-level axiom plumbing is needed.
/// Non-Sub ops pass through unchanged: they have no comparable exact
/// boundary.
fn refine_sub_reflexive_boundary(
    op: BinOp,
    lhs: &Expr,
    rhs: &Expr,
    width: u32,
    tbl_term: Expr,
) -> Expr {
    if !matches!(op, BinOp::Sub | BinOp::SubUnchecked) {
        return tbl_term;
    }
    use super::call::codegen_call_cmp_string::float_predicates::{
        FloatPredicateKind, build_float_predicate_expr,
    };
    let Some(finite) = build_float_predicate_expr(lhs, FloatPredicateKind::Finite) else {
        return tbl_term;
    };
    let pos_zero = Expr::bitvec_const(0u128, width);
    let cond = lhs.clone().eq(rhs.clone()).and(finite);
    Expr::ite(cond, pos_zero, tbl_term)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// CHC float value binop: exact constant fold when both operands are
    /// concrete, congruent table application when symbolic.
    ///
    /// This is THE single entry point for float Add/Sub/Mul/Div/Rem in the
    /// CHC lane — both the regular BinOp site (`translate_binop`) and the
    /// fast-math intrinsic site (`compute_fp_arith`) route through it, so the
    /// same `(op, lhs, rhs)` always yields the same term (congruence by
    /// construction). Returns `None` when neither lane applies (unsupported
    /// width, non-arithmetic op, or table not declared), which preserves the
    /// pre-existing fail-closed fallback.
    pub(in crate::codegen_ay::chc) fn float_binop_chc_term(
        &self,
        op: BinOp,
        lhs: Expr,
        rhs: Expr,
        width: u32,
    ) -> Option<Expr> {
        // Concrete operands: exact constant fold (existing lane, kept first).
        if let Some(folded) = bv_float_binop_chc(op, lhs.clone(), rhs.clone(), width) {
            return Some(folded);
        }
        // Symbolic operands: unconstrained-table select. Sound for proofs —
        // the IEEE 754 op is one interpretation of the table (see module doc).
        let tbl = self.float_binop_table_var(width)?;
        let key = float_binop_congruent_key(op, lhs.clone(), rhs.clone(), width)?;
        let tbl_term = tbl.select(key);

        Some(refine_sub_reflexive_boundary(op, &lhs, &rhs, width, tbl_term))
    }

    /// Input-side table variable, iff declared for this harness (pre-scan).
    ///
    /// Never returns an undeclared variable: emitting a table select over a
    /// var missing from the relation signature would leave a per-rule free
    /// variable — sound (degenerates to havoc) but silently non-congruent.
    fn float_binop_table_var(&self, width: u32) -> Option<Expr> {
        let (in_name, _) = float_binop_table_names(width)?;
        let idx = self.state_var_mgr.state_var_index_by_name(in_name)?;
        let (name, sort) = &self.state_var_mgr.state_vars[idx];
        Some(Expr::var(&**name, sort.clone()))
    }

    /// Declare the congruent float-binop tables needed by this body.
    ///
    /// Called from `collect_state_vars` (never under int-lift: Array sorts
    /// block PDR there, and the float lane then fails closed exactly as
    /// before). Read-only: the table is never marked modified, so successor
    /// heads always receive the input variable (identity threading), and the
    /// entry rule leaves it unconstrained.
    pub(in crate::codegen_ay::chc) fn collect_float_binop_table_state_vars(&mut self) {
        let needed = self.float_binop_table_widths_needed();
        for (width, need) in [(32u32, needed[0]), (64u32, needed[1])] {
            if !need {
                continue;
            }
            let (in_name, out_name) =
                float_binop_table_names(width).expect("f32/f64 table names exist");
            let sort = float_binop_table_sort(width).expect("f32/f64 table sorts exist");
            self.push_state_var_pair(in_name, out_name, sort);
            debug!(width, "CHC: added congruent float-binop table (read-only, unconstrained)");
        }
    }

    /// Pre-scan the MIR body for float value binops with potentially-symbolic
    /// operands. Returns `[f32_needed, f64_needed]`.
    ///
    /// Conservative on the symbolic side: an operand that is a MIR local may
    /// still constant-fold at translation time (cached constants), in which
    /// case the declared table is simply unused — harmless. An operand that
    /// is a MIR constant always translates to a concrete bit pattern, so
    /// both-constant binops never need the table.
    fn float_binop_table_widths_needed(&self) -> [bool; 2] {
        let mut needed = [false; 2];
        let mark = |needed: &mut [bool; 2], width: u32| match width {
            32 => needed[0] = true,
            64 => needed[1] = true,
            _ => {}
        };
        let both_const = |lhs: &Operand, rhs: &Operand| {
            matches!(lhs, Operand::Constant(_)) && matches!(rhs, Operand::Constant(_))
        };
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                    continue;
                };
                let (Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs)) =
                    rvalue
                else {
                    continue;
                };
                if !is_float_arithmetic_op(*op) || both_const(lhs, rhs) {
                    continue;
                }
                if let Some(width) = self.float_operand_width(lhs) {
                    mark(&mut needed, width);
                }
            }
            // Fast-math intrinsics route through the same congruent helper
            // (compute_fp_arith), so they need the table too. Cheap checks
            // first — resolve_callee_path (Instance::resolve) is last.
            if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind
                && args.len() >= 2
                && !both_const(&args[0], &args[1])
                && let Some(width) = self.float_operand_width(&args[0])
                && self.resolve_callee_path(func).is_some_and(|p| detect_fast_math_intrinsic(&p))
            {
                mark(&mut needed, width);
            }
            // SIMD elementwise float binops now route through the same congruent
            // table (apply_simd_binop -> float_binop_chc_term): declare the table
            // for the element width so simd-only harnesses get the term instead
            // of falling back to havoc. Conservative: a width the extractor
            // can't resolve (generic Simd<T, N>) just keeps the old fallback.
            if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind
                && args.len() >= 2
                && let Some(width) = self.simd_float_elem_width(&args[0])
                && self.resolve_callee_path(func).is_some_and(|p| {
                    matches!(
                        p.rsplit("::").next(),
                        Some("simd_add" | "simd_sub" | "simd_mul" | "simd_div" | "simd_rem")
                    )
                })
            {
                mark(&mut needed, width);
            }
        }
        needed
    }

    /// Element width if `operand` is a `#[repr(simd)]` wrapper over f32/f64
    /// lanes (single-variant ADT whose first field is `[fN; K]` or a repeated
    /// float scalar). `None` for generic/unresolvable shapes — the caller then
    /// simply doesn't declare the table (old fail-closed fallback).
    fn simd_float_elem_width(&self, operand: &Operand) -> Option<u32> {
        let ty = operand.ty(self.body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
            return None;
        };
        let variants = def.variants();
        if variants.len() != 1 {
            return None;
        }
        let f0 = variants[0].fields().first()?.ty();
        let elem = match f0.kind() {
            TyKind::RigidTy(RigidTy::Array(elem, _)) => elem,
            _ => f0,
        };
        match elem.kind() {
            TyKind::RigidTy(RigidTy::Float(FloatTy::F32)) => Some(32),
            TyKind::RigidTy(RigidTy::Float(FloatTy::F64)) => Some(64),
            _ => None,
        }
    }

    /// f32 → 32, f64 → 64; `None` for anything else (incl. f16/f128).
    fn float_operand_width(&self, operand: &Operand) -> Option<u32> {
        match operand.ty(self.body.locals()).ok()?.kind() {
            TyKind::RigidTy(RigidTy::Float(FloatTy::F32)) => Some(32),
            TyKind::RigidTy(RigidTy::Float(FloatTy::F64)) => Some(64),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(name: &str, width: u32) -> Expr {
        Expr::var(name, Sort::bitvec(width))
    }

    #[test]
    fn test_congruent_key_same_inputs_same_term() {
        // Congruence by construction: identical (op, lhs, rhs) → identical key.
        let a = float_binop_congruent_key(BinOp::Add, sym("x", 32), sym("y", 32), 32).unwrap();
        let b = float_binop_congruent_key(BinOp::Add, sym("x", 32), sym("y", 32), 32).unwrap();
        assert_eq!(a, b);
        assert_eq!(a.sort().bitvec_width(), Some(72)); // 8 + 32 + 32
    }

    #[test]
    fn test_congruent_key_distinguishes_ops_and_operand_order() {
        let add = float_binop_congruent_key(BinOp::Add, sym("x", 32), sym("y", 32), 32).unwrap();
        let sub = float_binop_congruent_key(BinOp::Sub, sym("x", 32), sym("y", 32), 32).unwrap();
        let add_swapped =
            float_binop_congruent_key(BinOp::Add, sym("y", 32), sym("x", 32), 32).unwrap();
        assert_ne!(add, sub); // distinct op tags
        assert_ne!(add, add_swapped); // no commutativity axiom smuggled in
    }

    #[test]
    fn test_congruent_key_unchecked_variants_share_tag() {
        // AddUnchecked has identical value semantics to Add — same key.
        let a = float_binop_congruent_key(BinOp::Add, sym("x", 64), sym("y", 64), 64).unwrap();
        let b =
            float_binop_congruent_key(BinOp::AddUnchecked, sym("x", 64), sym("y", 64), 64).unwrap();
        assert_eq!(a, b);
        assert_eq!(a.sort().bitvec_width(), Some(136)); // 8 + 64 + 64
    }

    #[test]
    fn test_congruent_key_fails_closed_on_width_mismatch() {
        // Never build a mis-sorted select.
        assert!(float_binop_congruent_key(BinOp::Add, sym("x", 32), sym("y", 64), 32).is_none());
        assert!(float_binop_congruent_key(BinOp::Add, sym("x", 64), sym("y", 64), 32).is_none());
        // Non-arithmetic ops have no tag.
        assert!(float_binop_congruent_key(BinOp::BitAnd, sym("x", 32), sym("y", 32), 32).is_none());
    }

    #[test]
    fn test_sub_boundary_refinement_is_guarded_ite() {
        // P4-4: Sub gets ite((lhs == rhs) && finite(lhs), +0.0, tbl_term).
        let tbl_term = sym("tbl_val", 32);
        let refined =
            refine_sub_reflexive_boundary(BinOp::Sub, &sym("x", 32), &sym("y", 32), 32, tbl_term);
        let ay_bindings::ExprValue::Ite { cond, then_expr, else_expr } = refined.value() else {
            panic!("Sub refinement must be an ite, got {refined:?}");
        };
        // Exact branch: +0.0 (all-zero bits).
        assert!(
            matches!(then_expr.value(), ay_bindings::ExprValue::BitVecConst { value, .. }
                if *value == num_bigint::BigInt::from(0)),
            "guarded branch must be +0.0"
        );
        // Fallback branch: the untouched table term.
        assert!(
            matches!(else_expr.value(), ay_bindings::ExprValue::Var { name } if name == "tbl_val"),
            "unguarded branch must keep the free table value"
        );
        // The guard must include BOTH bitwise equality and a finiteness
        // predicate over lhs — an equality-only guard is the unsound
        // NaN/Inf-admitting shape the duals refute.
        let cond_str = format!("{cond:?}");
        assert!(cond_str.contains("Eq"), "guard must test bitwise equality: {cond_str}");
        assert!(
            cond_str.contains("x") && cond_str.contains("y"),
            "guard must compare the operands: {cond_str}"
        );
        // Finiteness for BV floats is expressed via exponent-bits comparison —
        // the guard must be an AND of equality with more than the bare Eq.
        assert!(
            matches!(cond.value(), ay_bindings::ExprValue::And(parts) if parts.len() >= 2),
            "guard must conjoin equality with the finiteness predicate: {cond_str}"
        );
    }

    #[test]
    fn test_non_sub_ops_not_refined() {
        for op in [BinOp::Add, BinOp::Mul, BinOp::Div, BinOp::Rem] {
            let tbl_term = sym("tbl_val", 64);
            let refined =
                refine_sub_reflexive_boundary(op, &sym("x", 64), &sym("x", 64), 64, tbl_term);
            assert!(
                matches!(refined.value(), ay_bindings::ExprValue::Var { name } if name == "tbl_val"),
                "{op:?} must pass the table term through unchanged"
            );
        }
    }

    #[test]
    fn test_table_sort_shapes() {
        let f32_sort = float_binop_table_sort(32).unwrap();
        let arr = f32_sort.array_sort().unwrap();
        assert_eq!(arr.index_sort.bitvec_width(), Some(72));
        assert_eq!(arr.element_sort.bitvec_width(), Some(32));

        let f64_sort = float_binop_table_sort(64).unwrap();
        let arr = f64_sort.array_sort().unwrap();
        assert_eq!(arr.index_sort.bitvec_width(), Some(136));
        assert_eq!(arr.element_sort.bitvec_width(), Some(64));

        // f16/f128: no table — fail-closed fallback preserved.
        assert!(float_binop_table_sort(16).is_none());
        assert!(float_binop_table_sort(128).is_none());
    }
}
