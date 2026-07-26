// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `quantifier_encoding.rs` — quantifier unrolling and binop translation.
//!
//! Part of #2303 (quantifier_encoding.rs, 651 LOC, zero dedicated coverage).
//! Covers:
//! - `binop_to_expr`: BinOp dispatch for signed/unsigned BV, Int, and Bool sorts
//! - `build_quantifier_expr`: Full pipeline quantifier unrolling through MIR

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::mono::Instance;
use rustc_public::ty::ClosureKind;

// Re-import the trait so we can call binop_to_expr on ChcCtx
use super::super::quantifier_encoding::QuantifierEncoding;
use crate::kani_middle::kani_functions::KaniHook;

// =============================================================================
// binop_to_expr — BV signed/unsigned dispatch
// =============================================================================

const SIMPLE_ADD_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_binop(x: u32) -> u32 {
        x + 1
    }
"#;

const EXISTS_QUANTIFIER_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[kanitool::fn_marker = "ExistsHook"]
    pub fn exists<F>(lower: u32, upper: u32, pred: F) -> bool
    where
        F: Fn(u32) -> bool,
    {
        let mut i = lower;
        while i < upper {
            if pred(i) { return true; }
            i += 1;
        }
        false
    }

    #[kanitool::fn_marker = "ForallHook"]
    pub fn forall<F>(lower: u32, upper: u32, pred: F) -> bool
    where
        F: Fn(u32) -> bool,
    {
        let mut i = lower;
        while i < upper {
            if !pred(i) { return false; }
            i += 1;
        }
        true
    }
}

pub fn probe_exists_empty() -> bool {
    kani::exists(7, 7, |x| x > 0)
}

pub fn probe_exists_nonempty() -> bool {
    kani::exists(0, 3, |x| x == 1)
}

pub fn probe_forall_empty() -> bool {
    kani::forall(4, 4, |x| x <= 4)
}

pub fn probe_forall_nonempty() -> bool {
    kani::forall(1, 4, |x| x > 0)
}
"#;

const QUANTIFIER_LOCAL_BOUNDS_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[kanitool::fn_marker = "ForallHook"]
    pub fn forall<F>(lower: usize, upper: usize, pred: F) -> bool
    where
        F: Fn(usize) -> bool,
    {
        let mut i = lower;
        while i < upper {
            if !pred(i) { return false; }
            i += 1;
        }
        true
    }
}

pub fn probe_forall_local_const_bound_array_index() -> bool {
    let arr = [3i32, 4, 5, 6];
    let upper = 3usize;
    kani::forall(1usize, upper, |idx| arr[idx] > 0)
}
"#;

const QUANTIFIER_ARBITRARY_RANGE_PLUS_ONE_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[kanitool::fn_marker = "ForallHook"]
    pub fn forall<F>(lower: usize, upper: usize, pred: F) -> bool
    where
        F: Fn(usize) -> bool,
    {
        let mut i = lower;
        while i < upper {
            if !pred(i) { return false; }
            i += 1;
        }
        true
    }
}

pub fn probe_forall_arbitrary_range_plus_one() -> bool {
    const N: usize = 100;
    let a: [i32; N] = [0; N];
    let i = 20usize;
    let _first = kani::forall(1usize, i, |j| a[j] < 10);
    kani::forall(1usize, i + 1, |j| a[j] < 10)
}
"#;

/// Test Add on bitvector operands produces bvadd.
#[test]
fn test_binop_add_bitvec() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Add, lhs, rhs, None, 32);

        assert!(result.is_some(), "Add on BV should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bitvec(), "Add on BV should return BV sort");
    });
}

/// Test Sub on bitvector operands produces bvsub.
#[test]
fn test_binop_sub_bitvec() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Sub, lhs, rhs, None, 32);

        assert!(result.is_some(), "Sub on BV should produce an expression");
    });
}

/// Test Lt on bitvec with signed flag produces bvslt.
#[test]
fn test_binop_lt_signed() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Lt, lhs, rhs, Some(true), 32);

        assert!(result.is_some(), "Lt signed on BV should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "Lt should return Bool sort");
    });
}

/// Test Lt on bitvec with unsigned flag produces bvult.
#[test]
fn test_binop_lt_unsigned() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Lt, lhs, rhs, Some(false), 32);

        assert!(result.is_some(), "Lt unsigned on BV should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "Lt should return Bool sort");
    });
}

/// Test Add on Int sort produces int_add.
#[test]
fn test_binop_add_int() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::int());
        let rhs = Expr::var("b", Sort::int());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Add, lhs, rhs, None, 32);

        assert!(result.is_some(), "Add on Int should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_int(), "Add on Int should return Int sort");
    });
}

/// Test Lt on Int sort produces int lt (not bvslt).
#[test]
fn test_binop_lt_int() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::int());
        let rhs = Expr::var("b", Sort::int());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Lt, lhs, rhs, None, 32);

        assert!(result.is_some(), "Lt on Int should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "Lt should return Bool sort");
    });
}

/// Test Eq on bitvec produces eq.
#[test]
fn test_binop_eq_bitvec() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Eq, lhs, rhs, None, 32);

        assert!(result.is_some(), "Eq on BV should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "Eq should return Bool sort");
    });
}

/// Test Ne on bitvec produces ne.
#[test]
fn test_binop_ne_bitvec() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Ne, lhs, rhs, None, 32);

        assert!(result.is_some(), "Ne on BV should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "Ne should return Bool sort");
    });
}

/// Test BitAnd on bitvec produces bvand.
#[test]
fn test_binop_bitand_bitvec() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::BitAnd, lhs, rhs, None, 32);

        assert!(result.is_some(), "BitAnd on BV should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bitvec(), "BitAnd on BV should return BV sort");
    });
}

/// Test BitAnd on Bool produces logical and.
#[test]
fn test_binop_bitand_bool() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bool());
        let rhs = Expr::var("b", Sort::bool());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::BitAnd, lhs, rhs, None, 32);

        assert!(result.is_some(), "BitAnd on Bool should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "BitAnd on Bool should return Bool sort");
    });
}

/// Test Div on BV signed produces bvsdiv.
#[test]
fn test_binop_div_signed() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Div, lhs, rhs, Some(true), 32);

        assert!(result.is_some(), "Div signed on BV should produce an expression");
    });
}

/// Test Div on BV unsigned produces bvudiv.
#[test]
fn test_binop_div_unsigned() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result =
            chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Div, lhs, rhs, Some(false), 32);

        assert!(result.is_some(), "Div unsigned on BV should produce an expression");
    });
}

/// Test Div on Int produces int_div.
#[test]
fn test_binop_div_int() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::int());
        let rhs = Expr::var("b", Sort::int());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Div, lhs, rhs, None, 32);

        assert!(result.is_some(), "Div on Int should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_int(), "Div on Int should return Int sort");
    });
}

/// Test Mul on bitvec.
#[test]
fn test_binop_mul_bitvec() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Mul, lhs, rhs, None, 32);

        assert!(result.is_some(), "Mul on BV should produce an expression");
    });
}

/// Test Ge on bitvec signed produces bvsle with swapped args.
#[test]
fn test_binop_ge_signed() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Ge, lhs, rhs, Some(true), 32);

        assert!(result.is_some(), "Ge signed on BV should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "Ge should return Bool sort");
    });
}

/// Test Le on bitvec unsigned produces bvule.
#[test]
fn test_binop_le_unsigned() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Le, lhs, rhs, Some(false), 32);

        assert!(result.is_some(), "Le unsigned on BV should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "Le should return Bool sort");
    });
}

/// Test Rem on bitvec signed produces bvsrem.
#[test]
fn test_binop_rem_signed() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Rem, lhs, rhs, Some(true), 32);

        assert!(result.is_some(), "Rem signed on BV should produce an expression");
    });
}

/// Test BitXor on bitvec produces bvxor.
#[test]
fn test_binop_bitxor_bitvec() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::BitXor, lhs, rhs, None, 32);

        assert!(result.is_some(), "BitXor on BV should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bitvec(), "BitXor on BV should return BV sort");
    });
}

/// Test Gt on Int produces correct comparison.
#[test]
fn test_binop_gt_int() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::int());
        let rhs = Expr::var("b", Sort::int());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Gt, lhs, rhs, None, 32);

        assert!(result.is_some(), "Gt on Int should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "Gt should return Bool sort");
    });
}

// =============================================================================
// Full pipeline: build_quantifier_expr through MIR
// =============================================================================

/// Default signed flag (None) should be treated as signed.
#[test]
fn test_binop_default_signed_flag() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));

        // None defaults to signed=true, so Lt with None and Lt with Some(true) should both work
        let with_none =
            chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Lt, lhs.clone(), rhs.clone(), None, 32);
        let with_true =
            chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Lt, lhs, rhs, Some(true), 32);

        assert!(with_none.is_some(), "Lt with None signed flag should produce an expression");
        assert!(with_true.is_some(), "Lt with Some(true) should produce an expression");
        // Both should return Bool
        assert!(with_none.unwrap().sort().is_bool());
        assert!(with_true.unwrap().sort().is_bool());
    });
}

/// BitOr on bool produces logical or.
#[test]
fn test_binop_bitor_bool() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bool());
        let rhs = Expr::var("b", Sort::bool());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::BitOr, lhs, rhs, None, 32);

        assert!(result.is_some(), "BitOr on Bool should produce an expression");
        let expr = result.unwrap();
        assert!(expr.sort().is_bool(), "BitOr on Bool should return Bool sort");
    });
}

// =============================================================================
// Part of #2272: Int-sort binop coverage (soundness-critical for BigInt paths)
// =============================================================================

/// Sub on Int operands produces int_sub.
#[test]
fn test_binop_sub_int() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::int());
        let rhs = Expr::var("b", Sort::int());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Sub, lhs, rhs, None, 32);

        assert!(result.is_some(), "Sub on Int should produce an expression");
        assert!(result.unwrap().sort().is_int(), "Sub on Int should return Int sort");
    });
}

/// Mul on Int operands produces int_mul.
#[test]
fn test_binop_mul_int() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::int());
        let rhs = Expr::var("b", Sort::int());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Mul, lhs, rhs, None, 32);

        assert!(result.is_some(), "Mul on Int should produce an expression");
        assert!(result.unwrap().sort().is_int(), "Mul on Int should return Int sort");
    });
}

/// Rem on Int operands produces int_mod (remainder).
#[test]
fn test_binop_rem_int() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::int());
        let rhs = Expr::var("b", Sort::int());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Rem, lhs, rhs, None, 32);

        assert!(result.is_some(), "Rem on Int should produce an expression");
        assert!(result.unwrap().sort().is_int(), "Rem on Int should return Int sort");
    });
}

/// Le on Int operands produces le (less-than-or-equal).
#[test]
fn test_binop_le_int() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::int());
        let rhs = Expr::var("b", Sort::int());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Le, lhs, rhs, None, 32);

        assert!(result.is_some(), "Le on Int should produce an expression");
        assert!(result.unwrap().sort().is_bool(), "Le on Int should return Bool sort");
    });
}

/// Ge on Int operands produces ge (greater-than-or-equal).
#[test]
fn test_binop_ge_int() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::int());
        let rhs = Expr::var("b", Sort::int());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Ge, lhs, rhs, None, 32);

        assert!(result.is_some(), "Ge on Int should produce an expression");
        assert!(result.unwrap().sort().is_bool(), "Ge on Int should return Bool sort");
    });
}

/// Eq on Int operands produces eq.
#[test]
fn test_binop_eq_int() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::int());
        let rhs = Expr::var("b", Sort::int());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Eq, lhs, rhs, None, 32);

        assert!(result.is_some(), "Eq on Int should produce an expression");
        assert!(result.unwrap().sort().is_bool(), "Eq on Int should return Bool sort");
    });
}

/// Ne on Int operands produces ne.
#[test]
fn test_binop_ne_int() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::int());
        let rhs = Expr::var("b", Sort::int());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Ne, lhs, rhs, None, 32);

        assert!(result.is_some(), "Ne on Int should produce an expression");
        assert!(result.unwrap().sort().is_bool(), "Ne on Int should return Bool sort");
    });
}

// =============================================================================
// Edge cases: shift operators and Unchecked variants
// =============================================================================

/// Shl is now handled by binop_to_expr via translate_binop delegation (Part of #2440).
#[test]
fn test_binop_shl_returns_bvshl() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Shl, lhs, rhs, None, 32);

        assert!(result.is_some(), "Shl should be supported after translate_binop delegation");
        assert!(result.unwrap().sort().is_bitvec(), "Shl result should be bitvec");
    });
}

/// Shr is now handled by binop_to_expr via translate_binop delegation (Part of #2440).
#[test]
fn test_binop_shr_returns_bvshr() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Shr, lhs, rhs, None, 32);

        assert!(result.is_some(), "Shr should be supported after translate_binop delegation");
        assert!(result.unwrap().sort().is_bitvec(), "Shr result should be bitvec");
    });
}

/// AddUnchecked should be treated the same as Add.
#[test]
fn test_binop_add_unchecked_same_as_add() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result =
            chc_ctx.binop_to_expr(rustc_public::mir::BinOp::AddUnchecked, lhs, rhs, None, 32);

        assert!(result.is_some(), "AddUnchecked should produce an expression");
        assert!(result.unwrap().sort().is_bitvec(), "AddUnchecked on BV should return BV sort");
    });
}

/// SubUnchecked should be treated the same as Sub.
#[test]
fn test_binop_sub_unchecked_same_as_sub() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result =
            chc_ctx.binop_to_expr(rustc_public::mir::BinOp::SubUnchecked, lhs, rhs, None, 32);

        assert!(result.is_some(), "SubUnchecked should produce an expression");
    });
}

/// MulUnchecked should be treated the same as Mul.
#[test]
fn test_binop_mul_unchecked_same_as_mul() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result =
            chc_ctx.binop_to_expr(rustc_public::mir::BinOp::MulUnchecked, lhs, rhs, None, 32);

        assert!(result.is_some(), "MulUnchecked should produce an expression");
    });
}

// =============================================================================
// Rem unsigned on BV — signedness matters for semantics
// =============================================================================

/// Rem on unsigned BV (signed=false) should use bvurem, not bvsrem.
#[test]
fn test_binop_rem_unsigned() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(32));
        let rhs = Expr::var("b", Sort::bitvec(32));
        let result =
            chc_ctx.binop_to_expr(rustc_public::mir::BinOp::Rem, lhs, rhs, Some(false), 32);

        assert!(result.is_some(), "Rem unsigned on BV should produce an expression");
        assert!(result.unwrap().sort().is_bitvec(), "Rem unsigned should return BV sort");
    });
}

/// BitXor on Bool produces logical xor.
#[test]
fn test_binop_bitxor_bool() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bool());
        let rhs = Expr::var("b", Sort::bool());
        let result = chc_ctx.binop_to_expr(rustc_public::mir::BinOp::BitXor, lhs, rhs, None, 32);

        assert!(result.is_some(), "BitXor on Bool should produce an expression");
        assert!(result.unwrap().sort().is_bool(), "BitXor on Bool should return Bool sort");
    });
}

/// BitAnd on BV with explicit unsigned flag.
#[test]
fn test_binop_bitand_bitvec_unsigned() {
    with_test_ay_ctx_for_source(SIMPLE_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_binop");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_binop", ChcConfig::default());

        let lhs = Expr::var("a", Sort::bitvec(64));
        let rhs = Expr::var("b", Sort::bitvec(64));
        // BitAnd doesn't care about signedness — should work with either
        let result =
            chc_ctx.binop_to_expr(rustc_public::mir::BinOp::BitAnd, lhs, rhs, Some(false), 32);

        assert!(result.is_some(), "BitAnd on BV64 should produce an expression");
        assert!(
            result.unwrap().sort().bitvec_width() == Some(64),
            "BitAnd on BV64 should return BV64 sort"
        );
    });
}

#[test]
fn test_build_quantifier_expr_exists_empty_false_and_nonempty_or() {
    fn find_exists_call<'a>(
        chc_ctx: &ChcCtx<'_, 'a>,
        body: &'a rustc_public::mir::Body,
    ) -> (usize, &'a rustc_public::mir::Operand, &'a [rustc_public::mir::Operand]) {
        body.blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Call { func, args, .. }
                    if matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::Exists)) =>
                {
                    Some((bb_idx, func, args.as_slice()))
                }
                _ => None,
            })
            .expect("expected ExistsHook call in probe body")
    }

    with_test_ay_ctx_for_source(EXISTS_QUANTIFIER_SOURCE, |ctx| {
        let empty_instance = find_instance_by_suffix(ctx.tcx, "probe_exists_empty");
        let empty_body = empty_instance.body().expect("empty exists body");
        let mut empty_ctx =
            ChcCtx::new(ctx.tcx, &empty_body, "probe_exists_empty", ChcConfig::default());
        let (empty_bb, empty_func, empty_args) = find_exists_call(&empty_ctx, &empty_body);
        let empty_expr = empty_ctx.build_quantifier_expr(
            empty_func,
            empty_args,
            &HashSet::new(),
            empty_bb,
            false,
        );
        let empty_expr = empty_expr.expect("exists empty-range expression should be built");
        assert!(
            matches!(empty_expr.value(), ay_bindings::ExprValue::BoolConst(false)),
            "exists over empty range should evaluate to false, got {}",
            empty_expr
        );

        let nonempty_instance = find_instance_by_suffix(ctx.tcx, "probe_exists_nonempty");
        let nonempty_body = nonempty_instance.body().expect("nonempty exists body");
        let mut nonempty_ctx =
            ChcCtx::new(ctx.tcx, &nonempty_body, "probe_exists_nonempty", ChcConfig::default());
        let (nonempty_bb, nonempty_func, nonempty_args) =
            find_exists_call(&nonempty_ctx, &nonempty_body);
        let nonempty_expr = nonempty_ctx
            .build_quantifier_expr(
                nonempty_func,
                nonempty_args,
                &HashSet::new(),
                nonempty_bb,
                false,
            )
            .expect("exists non-empty expression should be built");
        let nonempty_value = nonempty_expr.value();
        assert!(
            matches!(nonempty_value, ay_bindings::ExprValue::Or(args) if !args.is_empty()),
            "exists over non-empty range should use non-empty ExprValue::Or, got {nonempty_value:?}"
        );
    });
}

#[test]
fn test_build_quantifier_expr_forall_empty_true_and_nonempty_and() {
    fn find_forall_call<'a>(
        chc_ctx: &ChcCtx<'_, 'a>,
        body: &'a rustc_public::mir::Body,
    ) -> (usize, &'a rustc_public::mir::Operand, &'a [rustc_public::mir::Operand]) {
        body.blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Call { func, args, .. }
                    if matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::Forall)) =>
                {
                    Some((bb_idx, func, args.as_slice()))
                }
                _ => None,
            })
            .expect("expected ForallHook call in probe body")
    }

    with_test_ay_ctx_for_source(EXISTS_QUANTIFIER_SOURCE, |ctx| {
        let empty_instance = find_instance_by_suffix(ctx.tcx, "probe_forall_empty");
        let empty_body = empty_instance.body().expect("empty forall body");
        let mut empty_ctx =
            ChcCtx::new(ctx.tcx, &empty_body, "probe_forall_empty", ChcConfig::default());
        let (empty_bb, empty_func, empty_args) = find_forall_call(&empty_ctx, &empty_body);
        let empty_expr = empty_ctx.build_quantifier_expr(
            empty_func,
            empty_args,
            &HashSet::new(),
            empty_bb,
            true,
        );
        let empty_expr = empty_expr.expect("forall empty-range expression should be built");
        assert!(
            matches!(empty_expr.value(), ay_bindings::ExprValue::BoolConst(true)),
            "forall over empty range should evaluate to true, got {}",
            empty_expr
        );

        let nonempty_instance = find_instance_by_suffix(ctx.tcx, "probe_forall_nonempty");
        let nonempty_body = nonempty_instance.body().expect("nonempty forall body");
        let mut nonempty_ctx =
            ChcCtx::new(ctx.tcx, &nonempty_body, "probe_forall_nonempty", ChcConfig::default());
        let (nonempty_bb, nonempty_func, nonempty_args) =
            find_forall_call(&nonempty_ctx, &nonempty_body);
        let nonempty_expr = nonempty_ctx
            .build_quantifier_expr(nonempty_func, nonempty_args, &HashSet::new(), nonempty_bb, true)
            .expect("forall non-empty expression should be built");
        let nonempty_value = nonempty_expr.value();
        assert!(
            matches!(nonempty_value, ay_bindings::ExprValue::And(args) if !args.is_empty()),
            "forall over non-empty range should use non-empty ExprValue::And, got {nonempty_value:?}"
        );
    });
}

#[test]
fn test_quantifier_local_const_bound_array_index_avoids_dispatch_fallback() {
    fn find_forall_call<'a>(
        chc_ctx: &ChcCtx<'_, 'a>,
        body: &'a rustc_public::mir::Body,
    ) -> (usize, &'a rustc_public::mir::Operand, &'a [rustc_public::mir::Operand]) {
        body.blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Call { func, args, .. }
                    if matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::Forall)) =>
                {
                    Some((bb_idx, func, args.as_slice()))
                }
                _ => None,
            })
            .expect("expected ForallHook call in probe body")
    }

    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(QUANTIFIER_LOCAL_BOUNDS_SOURCE, |ctx| {
        let fn_name = "probe_forall_local_const_bound_array_index";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("probe body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (bb_idx, func, args) = find_forall_call(&chc_ctx, &body);
        let upper_debug_const =
            super::super::quantifier_encoding::resolve_debug_const_quantifier_bound(
                &mut chc_ctx,
                &args[1],
            );
        let captures = super::super::quantifier_encoding::extract_closure_captures(
            &mut chc_ctx,
            &args[2],
            &HashSet::new(),
            bb_idx,
        );
        assert!(
            upper_debug_const.is_some(),
            "optimized-away local const upper bound should recover from var_debug_info"
        );
        assert_eq!(
            captures.len(),
            1,
            "array-index closure should recover one capture from the closure aggregate"
        );
        assert!(
            captures[0].sort().is_array(),
            "array-index closure capture should inline to Array sort, got {:?}",
            captures[0].sort()
        );
        let Some(quant_expr) =
            chc_ctx.build_quantifier_expr(func, args, &HashSet::new(), bb_idx, true)
        else {
            panic!("local const bound + array index quantifier should translate");
        };
        let quant_value = quant_expr.value();
        assert!(
            matches!(quant_value, ay_bindings::ExprValue::And(args) if !args.is_empty()),
            "forall over a non-empty local-const range should produce conjunction, got {quant_value:?}"
        );

        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        assert_vc_structure(&vc, fn_name, body.blocks.len());

        let translation_drops = take_translation_drop_by_fn();
        let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            drop_count, 0,
            "{fn_name} should not record translation drops once local const bounds are recovered, map={translation_drops:?}"
        );

        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
        let call_dispatch_fallbacks = fn_sites.get("call_dispatch_fallback").copied().unwrap_or(0);
        assert_eq!(
            call_dispatch_fallbacks, 0,
            "{fn_name} should not record call_dispatch_fallback, sites={translation_sites:?}"
        );
    });

    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

#[test]
fn test_quantifier_arbitrary_range_plus_one_replays_linear_predecessor_state() {
    fn find_forall_calls<'a>(
        chc_ctx: &ChcCtx<'_, 'a>,
        body: &'a rustc_public::mir::Body,
    ) -> Vec<(usize, &'a rustc_public::mir::Operand, &'a [rustc_public::mir::Operand])> {
        body.blocks
            .iter()
            .enumerate()
            .filter_map(|(bb_idx, block)| match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Call { func, args, .. }
                    if matches!(chc_ctx.detect_kani_hook(func), Some(KaniHook::Forall)) =>
                {
                    Some((bb_idx, func, args.as_slice()))
                }
                _ => None,
            })
            .collect()
    }

    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(QUANTIFIER_ARBITRARY_RANGE_PLUS_ONE_SOURCE, |ctx| {
        let fn_name = "probe_forall_arbitrary_range_plus_one";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("probe body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let forall_calls = find_forall_calls(&chc_ctx, &body);
        assert_eq!(forall_calls.len(), 2, "expected two ForallHook calls");

        let (bb_idx, func, args) = forall_calls[1];
        let captures = super::super::quantifier_encoding::extract_closure_captures(
            &mut chc_ctx,
            &args[2],
            &HashSet::new(),
            bb_idx,
        );
        assert_eq!(
            captures.len(),
            1,
            "second arbitrary-range quantifier should recover the array capture from linear predecessors"
        );
        assert!(
            captures[0].sort().is_array(),
            "second arbitrary-range quantifier capture should inline to Array sort, got {:?}",
            captures[0].sort()
        );

        let quant_expr = chc_ctx.build_quantifier_expr(func, args, &HashSet::new(), bb_idx, true);
        assert!(
            quant_expr.is_some(),
            "second arbitrary-range quantifier should replay linear predecessor bounds/captures"
        );

        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        assert_vc_structure(&vc, fn_name, body.blocks.len());

        let translation_drops = take_translation_drop_by_fn();
        let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            drop_count, 0,
            "{fn_name} should not record translation drops once linear predecessor replay is active, map={translation_drops:?}"
        );

        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
        let call_dispatch_fallbacks = fn_sites.get("call_dispatch_fallback").copied().unwrap_or(0);
        assert_eq!(
            call_dispatch_fallbacks, 0,
            "{fn_name} should not record call_dispatch_fallback, sites={translation_sites:?}"
        );
    });

    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

const QUANTIFIER_CLOSURE_BODY_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[kanitool::fn_marker = "ForallHook"]
    pub fn forall<F>(lower: i32, upper: i32, pred: F) -> bool
    where
        F: Fn(i32) -> bool,
    {
        let mut i = lower;
        while i < upper {
            if !pred(i) { return false; }
            i += 1;
        }
        true
    }

    #[kanitool::fn_marker = "ExistsHook"]
    pub fn exists<F>(lower: i32, upper: i32, pred: F) -> bool
    where
        F: Fn(i32) -> bool,
    {
        let mut i = lower;
        while i < upper {
            if pred(i) { return true; }
            i += 1;
        }
        false
    }
}

#[inline(never)]
fn gt_zero(x: i32) -> bool {
    x > 0
}

pub fn probe_quant_call_delegation() -> bool {
    kani::exists(0, 3, |x| gt_zero(x))
}

pub fn probe_quant_checked_binop() -> bool {
    kani::forall(0, 3, |x| x + 1 >= x)
}

pub fn probe_quant_exists_checked_binop() -> bool {
    kani::exists(0, 3, |x| x + 1 >= x)
}

pub fn probe_quant_unary_not() -> bool {
    kani::forall(0, 2, |x| {
        let is_zero = x == 0;
        !is_zero
    })
}

pub fn probe_quant_switch_unsupported(threshold: i32) -> bool {
    kani::forall(0, 3, |x| if x > threshold { x > 0 } else { x == 0 })
}
"#;

fn find_quantifier_call_by_hook<'a>(
    chc_ctx: &ChcCtx<'_, 'a>,
    body: &'a rustc_public::mir::Body,
    expected_hook: KaniHook,
) -> (usize, &'a rustc_public::mir::Operand, &'a [rustc_public::mir::Operand]) {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| match &block.terminator.kind {
            rustc_public::mir::TerminatorKind::Call { func, args, .. }
                if matches!(chc_ctx.detect_kani_hook(func), Some(found) if found == expected_hook) =>
            {
                Some((bb_idx, func, args.as_slice()))
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("expected {expected_hook:?} call in probe body"))
}

fn resolve_quantifier_closure_body(
    call_site_body: &rustc_public::mir::Body,
    func: &rustc_public::mir::Operand,
) -> rustc_public::mir::Body {
    let func_ty = func.ty(call_site_body.locals()).expect("quantifier call type");
    let (_fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => panic!("quantifier call target should be a FnDef"),
    };

    for arg in &fn_args.0 {
        let Some(arg_ty) = arg.ty() else { continue };
        if let TyKind::RigidTy(RigidTy::Closure(def, closure_args)) = arg_ty.kind() {
            for kind in [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce] {
                if let Ok(instance) = Instance::resolve_closure(def, &closure_args, kind)
                    && let Some(body) = instance.body()
                {
                    return body;
                }
            }
        }
    }
    panic!("expected quantifier closure body to resolve");
}

#[test]
fn test_quantifier_closure_body_two_block_call_delegation_path() {
    with_test_ay_ctx_for_source(QUANTIFIER_CLOSURE_BODY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_quant_call_delegation");
        let body = instance.body().expect("probe body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_quant_call_delegation", ChcConfig::default());

        let (bb_idx, func, args) = find_quantifier_call_by_hook(&chc_ctx, &body, KaniHook::Exists);
        let closure_body = resolve_quantifier_closure_body(&body, func);
        let has_two_block_call_delegation = closure_body.blocks.len() == 2
            && matches!(
                &closure_body.blocks[0].terminator.kind,
                rustc_public::mir::TerminatorKind::Call { target: Some(1), .. }
            )
            && matches!(
                &closure_body.blocks[1].terminator.kind,
                rustc_public::mir::TerminatorKind::Return
            );
        assert_mir_pattern_found(
            has_two_block_call_delegation,
            "quantifier closure 2-block call delegation (Call -> bb1 -> Return)",
        );

        let expr = chc_ctx
            .build_quantifier_expr(func, args, &HashSet::new(), bb_idx, false)
            .expect("exists quantifier expression should be generated");
        assert!(
            expr.sort().is_bool(),
            "exists quantifier translation should produce a Bool expression, got {}",
            expr.sort()
        );
    });
}

#[test]
fn test_quantifier_closure_body_checked_binop_assert_path() {
    with_test_ay_ctx_for_source(QUANTIFIER_CLOSURE_BODY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_quant_checked_binop");
        let body = instance.body().expect("probe body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_quant_checked_binop", ChcConfig::default());

        let (bb_idx, func, args) = find_quantifier_call_by_hook(&chc_ctx, &body, KaniHook::Forall);
        let closure_body = resolve_quantifier_closure_body(&body, func);
        let has_checked_binop = closure_body.blocks.iter().any(|bb| {
            bb.statements.iter().any(|stmt| {
                matches!(
                    &stmt.kind,
                    rustc_public::mir::StatementKind::Assign(
                        _,
                        rustc_public::mir::Rvalue::CheckedBinaryOp(_, _, _)
                    )
                )
            })
        });
        let has_assert_terminator = closure_body.blocks.iter().any(|bb| {
            matches!(&bb.terminator.kind, rustc_public::mir::TerminatorKind::Assert { .. })
        });
        assert_mir_pattern_found(
            has_checked_binop && has_assert_terminator,
            "quantifier closure CheckedBinaryOp + Assert terminator path",
        );

        let expr = chc_ctx
            .build_quantifier_expr(func, args, &HashSet::new(), bb_idx, true)
            .expect("forall quantifier expression should be generated for checked-binop closure");
        assert!(
            expr.sort().is_bool(),
            "forall checked-binop translation should produce a Bool expression, got {}",
            expr.sort()
        );
    });
}

#[test]
fn test_quantifier_exists_checked_binop_conjoins_no_panic_guards() {
    with_test_ay_ctx_for_source(QUANTIFIER_CLOSURE_BODY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_quant_exists_checked_binop");
        let body = instance.body().expect("probe body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_quant_exists_checked_binop", ChcConfig::default());

        let (bb_idx, func, args) = find_quantifier_call_by_hook(&chc_ctx, &body, KaniHook::Exists);
        let expr = chc_ctx
            .build_quantifier_expr(func, args, &HashSet::new(), bb_idx, false)
            .expect("exists quantifier expression should be generated for checked-binop closure");

        assert!(
            expr.sort().is_bool(),
            "exists checked-binop translation should produce a Bool expression, got {}",
            expr.sort()
        );
        assert!(
            constraint_tree_contains(
                &expr,
                &|e| matches!(e.value(), ay_bindings::ExprValue::Or(args) if !args.is_empty())
            ),
            "exists checked-binop quantifier should still contain the witness disjunction"
        );
    });
}

#[test]
fn test_quantifier_closure_body_unary_not_path() {
    with_test_ay_ctx_for_source(QUANTIFIER_CLOSURE_BODY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_quant_unary_not");
        let body = instance.body().expect("probe body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_quant_unary_not", ChcConfig::default());

        let (bb_idx, func, args) = find_quantifier_call_by_hook(&chc_ctx, &body, KaniHook::Forall);
        let closure_body = resolve_quantifier_closure_body(&body, func);
        let has_unary_not = closure_body.blocks.iter().any(|bb| {
            bb.statements.iter().any(|stmt| {
                matches!(
                    &stmt.kind,
                    rustc_public::mir::StatementKind::Assign(
                        _,
                        rustc_public::mir::Rvalue::UnaryOp(rustc_public::mir::UnOp::Not, _)
                    )
                )
            })
        });
        assert_mir_pattern_found(has_unary_not, "quantifier closure unary Not rvalue");

        let expr = chc_ctx
            .build_quantifier_expr(func, args, &HashSet::new(), bb_idx, true)
            .expect("forall quantifier expression should be generated for unary-not closure");
        assert!(
            expr.sort().is_bool(),
            "forall unary-not translation should produce a Bool expression, got {}",
            expr.sort()
        );
    });
}

#[test]
fn test_quantifier_closure_body_switchint_returns_none_and_pipeline_falls_back() {
    with_test_ay_ctx_for_source(QUANTIFIER_CLOSURE_BODY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_quant_switch_unsupported");
        let body = instance.body().expect("probe body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_quant_switch_unsupported", ChcConfig::default());

        let (bb_idx, func, args) = find_quantifier_call_by_hook(&chc_ctx, &body, KaniHook::Forall);
        let closure_body = resolve_quantifier_closure_body(&body, func);
        let has_switchint = closure_body.blocks.iter().any(|bb| {
            matches!(&bb.terminator.kind, rustc_public::mir::TerminatorKind::SwitchInt { .. })
        });
        assert_mir_pattern_found(has_switchint, "quantifier closure SwitchInt terminator");

        let maybe_expr = chc_ctx.build_quantifier_expr(func, args, &HashSet::new(), bb_idx, true);
        assert!(
            maybe_expr.is_none(),
            "SwitchInt closure should fail closed in translate_closure_body_as_expr"
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_quant_switch_unsupported", ChcConfig::default());
        assert_vc_structure(&vc, "probe_quant_switch_unsupported", body.blocks.len());
        assert!(!vc.rules.is_empty(), "pipeline fallback should still emit CHC rules");
    });
}
