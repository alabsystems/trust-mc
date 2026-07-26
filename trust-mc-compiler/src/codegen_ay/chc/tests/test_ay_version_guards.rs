// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AY SMT-level backend regression guard tests.
//!
//! Part of #3410: These tests construct minimal CHC/SMT formulas that exercise
//! version-sensitive AY solver behaviors. Unlike end-to-end compiletest canaries
//! (which take minutes), these run in `cargo test` (seconds) and pinpoint the
//! exact SMT theory/pattern that changed behavior.
//!
//! Each test documents:
//! - What AY theory/feature it exercises
//! - The expected solver result at the current pinned AY version
//! - What a result change would indicate (improvement vs regression)
//!
//! Pattern adapted from trust_wp's solver-level regression guards
//! (crates/trust_wp-ay/src/tests/loops/tests.rs).
//!
//! Run this lane with the repository's pinned nightly toolchain and the corpus
//! feature that admits this module:
//! `cargo test -p trust-mc-compiler --features compiler-corpus-tests ay_guard_`.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use ay_bindings::{Expr, Sort};
use trust_mc_core::decl::Decl;
use trust_mc_core::{ChcQuery, ChcVc, RelationApp, RelationDecl, Rule, RuleBody, VarDecl};

/// Helper: register a datatype sort declaration in a ChcVc.
///
/// For CHC programs that use datatype sorts (struct/enum encoding),
/// the `declare-datatypes` command must be emitted before any use.
/// This extracts the `DatatypeSort` from a `Sort` and adds it as a `Decl`.
fn register_datatype_decl(vc: &mut ChcVc, sort: &Sort) {
    if let Some(dt) = sort.datatype_sort() {
        vc.add_decl(Decl::datatype(dt.clone()));
    }
}

// =============================================================================
// Guard 1: Integer arithmetic CHC — baseline adaptive-portfolio sanity
// =============================================================================

/// Baseline integer arithmetic CHC: verifies the adaptive portfolio can solve
/// a trivial integer-domain Horn clause system.
///
/// Encodes:
///   entry → bb0(x) with x = 0
///   bb0(x) ∧ x < 10 → bb0(x + 1)   [loop]
///   bb0(x) ∧ x >= 10 → bb1(x)       [exit]
///   bb1(x) ∧ x != 10 → error()
///
/// The loop invariant is 0 <= x <= 10. After the loop, x == 10.
/// Error is UNSAT. If this fails, the CHC engine is fundamentally broken.
///
/// Exercises: CHC integer invariant synthesis (most basic pattern).
/// AY version sensitivity: LOW — this is a sanity check, not a boundary test.
#[test]
fn ay_guard_int_loop_invariant_baseline() {
    let mut vc = ChcVc::new();

    vc.add_var(VarDecl::new("x", Sort::int()));
    vc.add_var(VarDecl::new("x_next", Sort::int()));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::int()]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::int()]));

    let x = Expr::var("x", Sort::int());
    let x_next = Expr::var("x_next", Sort::int());
    let zero = Expr::int_const(0);
    let one = Expr::int_const(1);
    let ten = Expr::int_const(10);

    // Entry: x = 0 → bb0(x)
    vc.add_rule(Rule::init(x.clone().eq(zero), RelationApp::new("bb0", vec![x.clone()])));

    // Loop back-edge: bb0(x) ∧ x < 10 ∧ x_next = x + 1 → bb0(x_next)
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone()])),
            vec![x.clone().int_lt(ten.clone()), x_next.clone().eq(x.clone().int_add(one))],
        ),
        RelationApp::new("bb0", vec![x_next]),
    ));

    // Loop exit: bb0(x) ∧ x >= 10 → bb1(x)
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone()])),
            vec![x.clone().int_ge(ten.clone())],
        ),
        RelationApp::new("bb1", vec![x.clone()]),
    ));

    // Error: bb1(x) ∧ x != 10 → error()
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![x.clone()])), vec![x.eq(ten).not()]),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Expected: unsat (error is unreachable — x is exactly 10 after loop)
    // If this becomes sat or unknown: CHC integer-domain reasoning is broken.
    assert_z3_result(&smt, "unsat");
}

// =============================================================================
// Guard 2: BV arithmetic with loop invariant — tests portfolio BV reasoning
// =============================================================================

/// BV arithmetic loop invariant: exercises the portfolio's ability to
/// synthesize invariants over bitvector domains.
///
/// Encodes a simple countdown loop:
///   entry → bb0(n) with n = 5 (bv32)
///   bb0(n) ∧ n >u 0 → bb0(n - 1)
///   bb0(n) ∧ n == 0 → bb1(n)
///   bb1(n) ∧ n != 0 → error()
///
/// Exercises: CHC BV invariant synthesis. BV loops are harder than integer
/// loops because the portfolio must reason about fixed-width arithmetic.
///
/// AY version sensitivity: MEDIUM — BV scalarization and portfolio interaction
/// can change across AY versions. The countdown pattern was chosen because
/// it exercises the same BV+CHC path as the DT+BV canary harnesses.
///
/// Expected at the manifest-pinned AY authority: unsat
/// If unknown: AY BV scalarization or CHC BV reasoning regressed.
/// If sat: Fundamental encoding error (should not happen).
#[test]
fn ay_guard_bv_countdown_loop_invariant() {
    let mut vc = ChcVc::new();

    vc.add_var(VarDecl::new("n", Sort::bitvec(32)));
    vc.add_var(VarDecl::new("n_next", Sort::bitvec(32)));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(32)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(32)]));

    let n = Expr::var("n", Sort::bitvec(32));
    let n_next = Expr::var("n_next", Sort::bitvec(32));
    let five = Expr::bitvec_const(5u64, 32);
    let zero = Expr::bitvec_const(0u64, 32);
    let one = Expr::bitvec_const(1u64, 32);

    // Entry: n = 5 → bb0(n)
    vc.add_rule(Rule::init(n.clone().eq(five), RelationApp::new("bb0", vec![n.clone()])));

    // Loop back-edge: bb0(n) ∧ n >u 0 ∧ n_next = n - 1 → bb0(n_next)
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![n.clone()])),
            vec![n.clone().bvugt(zero.clone()), n_next.clone().eq(n.clone().bvsub(one))],
        ),
        RelationApp::new("bb0", vec![n_next]),
    ));

    // Loop exit: bb0(n) ∧ n == 0 → bb1(n)
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![n.clone()])),
            vec![n.clone().eq(zero.clone())],
        ),
        RelationApp::new("bb1", vec![n.clone()]),
    ));

    // Error: bb1(n) ∧ n != 0 → error()
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![n.clone()])), vec![n.eq(zero).not()]),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Expected: unsat (countdown from 5 always reaches 0)
    // If unknown: CHC BV invariant synthesis regressed.
    assert_z3_result(&smt, "unsat");
}

// =============================================================================
// Guard 3: Array select/store with BV indices — tests BV array scalarization
// =============================================================================

/// Array select/store with BV indices: exercises the BV-indexed array theory
/// path that is sensitive to AY's adaptive scalarization.
///
/// Encodes:
///   entry → bb0(arr, i) with arr = store(const_array(0), i, 42)
///   bb0(arr, i) → bb1(arr, i)
///   bb1(arr, i) ∧ select(arr, i) != 42 → error()
///
/// The select-after-store axiom (select(store(a,i,v),i) = v) must hold.
/// This is a standard array theory test that becomes version-sensitive when
/// AY's BV scalarization rewrites the array operations.
///
/// Exercises: BV-indexed array select/store, scalarization path.
/// AY version sensitivity: HIGH — ay#5148 (store/select) and ay#5826 (DPE)
/// are both array-theory fixes that changed behavior across AY versions.
///
/// Expected at the manifest-pinned AY authority: unsat
/// If unknown: AY array theory or BV scalarization regressed.
/// If sat: Array select/store axiom broken (critical regression).
#[test]
fn ay_guard_bv_array_select_store() {
    let mut vc = ChcVc::new();

    let arr_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));

    vc.add_var(VarDecl::new("arr", arr_sort.clone()));
    vc.add_var(VarDecl::new("i", Sort::bitvec(32)));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![arr_sort.clone(), Sort::bitvec(32)]));
    vc.add_relation(RelationDecl::new("bb1", vec![arr_sort.clone(), Sort::bitvec(32)]));

    let arr = Expr::var("arr", arr_sort.clone());
    let i = Expr::var("i", Sort::bitvec(32));
    let zero_bv = Expr::bitvec_const(0u64, 32);
    let forty_two = Expr::bitvec_const(42u64, 32);

    // Build: arr = store(const_array(bv32, 0), i, 42)
    let base_arr = Expr::const_array(Sort::bitvec(32), zero_bv);
    let stored_arr = base_arr.store(i.clone(), forty_two.clone());

    // Entry: arr = store(const(0), i, 42) → bb0(arr, i)
    vc.add_rule(Rule::init(
        arr.clone().eq(stored_arr),
        RelationApp::new("bb0", vec![arr.clone(), i.clone()]),
    ));

    // Passthrough: bb0(arr, i) → bb1(arr, i)
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![arr.clone(), i.clone()])),
            vec![Expr::bool_const(true)],
        ),
        RelationApp::new("bb1", vec![arr.clone(), i.clone()]),
    ));

    // Error: bb1(arr, i) ∧ select(arr, i) != 42 → error()
    let read_back = arr.clone().select(i);
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb1", vec![arr, Expr::var("i", Sort::bitvec(32))])),
            vec![read_back.eq(forty_two).not()],
        ),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Expected: unsat (select(store(a, i, 42), i) == 42 is an axiom)
    // If unknown: AY array theory weakened.
    // If sat: Array select/store axiom violated — critical regression.
    assert_z3_result(&smt, "unsat");
}

// =============================================================================
// Guard 4: Datatype constructor/accessor — tests DT theory
// =============================================================================

/// Datatype constructor and field access: exercises the datatype theory
/// path used by trust_mc's struct/enum encoding.
///
/// Encodes a struct-like datatype "Pair" with fields (fst: bv32, snd: bv32):
///   entry → bb0(p) with p = Pair(10, 20)
///   bb0(p) → bb1(p)
///   bb1(p) ∧ fst(p) != 10 → error()
///
/// The DT accessor axiom (fst(Pair(a, b)) = a) must hold.
///
/// Exercises: AY datatype constructor, selector (accessor), SMT-LIB2
/// declare-datatypes emission.
/// AY version sensitivity: HIGH — ay#7930 (DT+BV canary regression) showed
/// that DT theory interacting with BV can regress across AY versions.
///
/// Expected at the manifest-pinned AY authority: unsat
/// If unknown: DT theory or adaptive CHC handling regressed.
/// If sat: DT accessor axiom broken (critical regression).
#[test]
fn ay_guard_datatype_constructor_accessor() {
    // Construct a struct datatype sort "Pair" with two bv32 fields.
    let pair_sort = Sort::struct_type(
        "Pair",
        vec![("fld_fst".to_string(), Sort::bitvec(32)), ("fld_snd".to_string(), Sort::bitvec(32))],
    );

    let mut vc = ChcVc::new();
    register_datatype_decl(&mut vc, &pair_sort);

    vc.add_var(VarDecl::new("p", pair_sort.clone()));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![pair_sort.clone()]));
    vc.add_relation(RelationDecl::new("bb1", vec![pair_sort.clone()]));

    let p = Expr::var("p", pair_sort.clone());
    let ten = Expr::bitvec_const(10u64, 32);
    let twenty = Expr::bitvec_const(20u64, 32);

    // Build: p = Pair(10, 20)
    // Constructor name is prefixed: "Pair_mk" (ay-bindings #948 convention)
    let pair_val =
        Expr::datatype_constructor("Pair", "Pair_mk", vec![ten.clone(), twenty], pair_sort.clone());

    // Entry: p = Pair(10, 20) → bb0(p)
    vc.add_rule(Rule::init(p.clone().eq(pair_val), RelationApp::new("bb0", vec![p.clone()])));

    // Passthrough: bb0(p) → bb1(p)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![p.clone()])), vec![Expr::bool_const(true)]),
        RelationApp::new("bb1", vec![p.clone()]),
    ));

    // Error: bb1(p) ∧ fld_fst(p) != 10 → error()
    let fst = p.clone().field_select("Pair", "fld_fst", Sort::bitvec(32));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![p])), vec![fst.eq(ten).not()]),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Expected: unsat (fld_fst(Pair(10, 20)) == 10 by DT axiom)
    // If unknown: AY DT theory handling in adaptive CHC regressed.
    // If sat: DT accessor axiom broken (critical regression).
    assert_z3_result(&smt, "unsat");
}

// =============================================================================
// Guard 5: Boolean combination of BV predicates
// =============================================================================

/// Boolean combination of BV predicates: exercises the interaction between
/// Boolean logic and BV comparisons in CHC rules.
///
/// Encodes:
///   entry → bb0(x, y) with unconstrained bv32 x, y
///   bb0(x, y) ∧ (x >u 0) ∧ (y >u 0) → bb1(x, y)
///   bb1(x, y) ∧ NOT((x >u 0) AND (y >u 0)) → error()
///
/// In bb1, both x > 0 and y > 0 hold, so the conjunction is always true.
/// Error is UNSAT.
///
/// Exercises: Boolean AND/NOT with BV unsigned comparisons in CHC.
/// This pattern appears in trust_mc's encoding of Rust `if cond1 && cond2` guards.
///
/// AY version sensitivity: MEDIUM — Bool-to-BV coercion and BV comparison
/// handling changed in ay#4765 (TRL/Kind fix). This pattern tests whether
/// the Boolean combination is correctly preserved through CHC emission.
///
/// Expected at the manifest-pinned AY authority: unsat
/// If unknown: BV comparison or Boolean combination handling regressed.
#[test]
fn ay_guard_bool_bv_predicate_combination() {
    let mut vc = ChcVc::new();

    let state_sorts = vec![Sort::bitvec(32), Sort::bitvec(32)];
    vc.add_var(VarDecl::new("x", Sort::bitvec(32)));
    vc.add_var(VarDecl::new("y", Sort::bitvec(32)));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", state_sorts.clone()));
    vc.add_relation(RelationDecl::new("bb1", state_sorts));

    let x = Expr::var("x", Sort::bitvec(32));
    let y = Expr::var("y", Sort::bitvec(32));
    let zero = Expr::bitvec_const(0u64, 32);

    let x_pos = x.clone().bvugt(zero.clone());
    let y_pos = y.clone().bvugt(zero);

    // Entry: unconstrained → bb0(x, y)
    vc.add_rule(Rule::init(
        Expr::bool_const(true),
        RelationApp::new("bb0", vec![x.clone(), y.clone()]),
    ));

    // Guard: bb0(x, y) ∧ x >u 0 ∧ y >u 0 → bb1(x, y)
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![x.clone(), y.clone()])),
            vec![x_pos.clone(), y_pos.clone()],
        ),
        RelationApp::new("bb1", vec![x.clone(), y.clone()]),
    ));

    // Error: bb1(x, y) ∧ NOT(x >u 0 AND y >u 0) → error()
    let both_pos = x_pos.and(y_pos);
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![x, y])), vec![both_pos.not()]),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Expected: unsat (in bb1, both x > 0 and y > 0 hold by construction)
    // If unknown: Boolean/BV predicate combination handling regressed.
    assert_z3_result(&smt, "unsat");
}

// =============================================================================
// Guard 6: BV overflow detection — tests BV arithmetic safety
// =============================================================================

/// BV overflow detection: exercises BV addition overflow checking, which
/// is central to trust_mc's encoding of Rust's checked arithmetic.
///
/// Encodes:
///   entry → bb0(a, b) with a = 0xFFFFFFFF, b = 1 (bv32)
///   bb0(a, b) → bb1(a, b)
///   bb1(a, b) ∧ bvadd(a, b) != 0 → error()
///
/// 0xFFFFFFFF + 1 wraps to 0 in 32-bit BV arithmetic. Error is UNSAT.
///
/// Exercises: BV wrapping addition semantics in CHC.
/// This pattern appears when trust_mc encodes wrapping_add/overflowing_add.
///
/// AY version sensitivity: LOW-MEDIUM — BV arithmetic is well-specified,
/// but ay#4868 (BvConcat) showed that BV operation encoding can change.
///
/// Expected at the manifest-pinned AY authority: unsat
/// If sat: BV addition wrapping semantics broken.
#[test]
fn ay_guard_bv_wrapping_addition() {
    let mut vc = ChcVc::new();

    let state_sorts = vec![Sort::bitvec(32), Sort::bitvec(32)];
    vc.add_var(VarDecl::new("a", Sort::bitvec(32)));
    vc.add_var(VarDecl::new("b", Sort::bitvec(32)));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", state_sorts.clone()));
    vc.add_relation(RelationDecl::new("bb1", state_sorts));

    let a = Expr::var("a", Sort::bitvec(32));
    let b = Expr::var("b", Sort::bitvec(32));
    let max_u32 = Expr::bitvec_const(0xFFFF_FFFFu64, 32);
    let one = Expr::bitvec_const(1u64, 32);
    let zero = Expr::bitvec_const(0u64, 32);

    // Entry: a = 0xFFFFFFFF, b = 1 → bb0(a, b)
    vc.add_rule(Rule::init(
        a.clone().eq(max_u32).and(b.clone().eq(one)),
        RelationApp::new("bb0", vec![a.clone(), b.clone()]),
    ));

    // Passthrough: bb0(a, b) → bb1(a, b)
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![a.clone(), b.clone()])),
            vec![Expr::bool_const(true)],
        ),
        RelationApp::new("bb1", vec![a.clone(), b.clone()]),
    ));

    // Error: bb1(a, b) ∧ bvadd(a, b) != 0 → error()
    // 0xFFFFFFFF + 1 = 0 in bv32 (wrapping)
    let sum = a.clone().bvadd(b.clone());
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![a, b])), vec![sum.eq(zero).not()]),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Expected: unsat (0xFFFFFFFF + 1 == 0 in bv32)
    // If sat: BV wrapping semantics broken.
    assert_z3_result(&smt, "unsat");
}

// =============================================================================
// Guard 7: Reachable counterexample — negative test (SAT expected)
// =============================================================================

/// Reachable counterexample with BV arithmetic: verifies that the solver
/// correctly detects a genuine violation (SAT), not just provable safety.
///
/// Encodes:
///   entry → bb0(x) with unconstrained bv32 x
///   bb0(x) ∧ x <u 256 → bb1(x)
///   bb1(x) ∧ x == 42 → error()
///
/// Error IS reachable: x = 42 satisfies both x < 256 and x == 42.
/// Z3 should report SAT.
///
/// This negative test ensures the solver is not over-approximating (reporting
/// unsat when sat is correct). False PROOFs are a critical soundness issue.
///
/// Exercises: adaptive-portfolio counterexample generation with BV constraints.
/// AY version sensitivity: LOW — SAT results are stable across versions.
/// The test exists to catch accidental encoding errors in guards 1-6.
///
/// Expected at the manifest-pinned AY authority: sat
/// If unsat: Over-approximation bug — false PROOF (P0 soundness issue).
/// If unknown: Solver lost ability to find concrete counterexample.
#[test]
fn ay_guard_reachable_bv_counterexample() {
    let mut vc = ChcVc::new();

    vc.add_var(VarDecl::new("x", Sort::bitvec(32)));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(32)]));
    vc.add_relation(RelationDecl::new("bb1", vec![Sort::bitvec(32)]));

    let x = Expr::var("x", Sort::bitvec(32));
    let bound = Expr::bitvec_const(256u64, 32);
    let target = Expr::bitvec_const(42u64, 32);

    // Entry: unconstrained → bb0(x)
    vc.add_rule(Rule::init(Expr::bool_const(true), RelationApp::new("bb0", vec![x.clone()])));

    // Guard: bb0(x) ∧ x <u 256 → bb1(x)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb0", vec![x.clone()])), vec![x.clone().bvult(bound)]),
        RelationApp::new("bb1", vec![x.clone()]),
    ));

    // Error: bb1(x) ∧ x == 42 → error()
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![x.clone()])), vec![x.eq(target)]),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");

    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Expected: sat (x = 42 is a valid counterexample)
    // If unsat: FALSE PROOF — solver incorrectly claims safety (P0).
    // If unknown: Solver cannot find obvious counterexample.
    assert_z3_result(&smt, "sat");
}

// =============================================================================
// Guard 8: Sequence witness above the ground-reasoning cap
// =============================================================================

/// A symbolic sequence length above AY's 64-element ground-reasoning cap still
/// has a small, concrete model witness. The point-read reduction and ordinary
/// len/nth reconstruction paths must share the larger model-witness cap; a cap
/// mismatch causes the independently validatable SAT model to degrade to
/// `unknown`.
///
/// This is an integration guard for the private-main regression found at AY
/// `b36361f25ef1`, where point-read reconstruction retained the old cap while
/// ordinary witness reconstruction used 4096.
///
/// Expected: sat. If unknown, AY model completion or independent validation
/// lost the bounded sequence witness. If unsat, the solver rejected a concrete
/// satisfying assignment (critical soundness regression).
#[test]
fn ay_guard_seq_len_above_ground_cap_validated_sat_model() {
    let smt = r#"
(set-logic QF_SEQLIA)
(declare-const a (Seq Int))
(assert (> (seq.len a) 100))
(check-sat)
"#;

    assert_z3_result(smt, "sat");
}

// =============================================================================
// Guard 9: Multi-state BV transition with datatype — DT+BV interaction
// =============================================================================

/// Build a CHC verification condition for the Counter(val, active) struct
/// mutation pattern: Counter(0, true) → increment val → assert val == 1.
///
/// Extracted from `ay_guard_dt_bv_interaction_struct_mutation` to satisfy
/// the 80-line function limit.
fn build_counter_struct_mutation_vc() -> ChcVc {
    let counter_sort = Sort::struct_type(
        "Counter",
        vec![("fld_val".to_string(), Sort::bitvec(32)), ("fld_active".to_string(), Sort::bool())],
    );

    let mut vc = ChcVc::new();
    register_datatype_decl(&mut vc, &counter_sort);

    vc.add_var(VarDecl::new("c", counter_sort.clone()));
    vc.add_var(VarDecl::new("c_next", counter_sort.clone()));

    vc.add_relation(RelationDecl::nullary("error"));
    vc.add_relation(RelationDecl::new("bb0", vec![counter_sort.clone()]));
    vc.add_relation(RelationDecl::new("bb1", vec![counter_sort.clone()]));
    vc.add_relation(RelationDecl::new("bb2", vec![counter_sort.clone()]));

    let c = Expr::var("c", counter_sort.clone());
    let c_next = Expr::var("c_next", counter_sort.clone());
    let zero_bv = Expr::bitvec_const(0u64, 32);
    let one_bv = Expr::bitvec_const(1u64, 32);

    // Build initial value: Counter(0, true)
    let init_counter = Expr::datatype_constructor(
        "Counter",
        "Counter_mk",
        vec![zero_bv, Expr::bool_const(true)],
        counter_sort.clone(),
    );

    // Entry: c = Counter(0, true) → bb0(c)
    vc.add_rule(Rule::init(c.clone().eq(init_counter), RelationApp::new("bb0", vec![c.clone()])));

    // Transition: bb0(c) ∧ active(c) ∧ c_next = Counter(val(c) + 1, true) → bb1(c_next)
    let c_active = c.clone().field_select("Counter", "fld_active", Sort::bool());
    let c_val = c.clone().field_select("Counter", "fld_val", Sort::bitvec(32));
    let incremented = Expr::datatype_constructor(
        "Counter",
        "Counter_mk",
        vec![c_val.bvadd(one_bv.clone()), Expr::bool_const(true)],
        counter_sort.clone(),
    );
    vc.add_rule(Rule::new(
        RuleBody::new(
            Some(RelationApp::new("bb0", vec![c.clone()])),
            vec![c_active, c_next.clone().eq(incremented)],
        ),
        RelationApp::new("bb1", vec![c_next]),
    ));

    // Passthrough: bb1(c) → bb2(c)
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb1", vec![c.clone()])), vec![Expr::bool_const(true)]),
        RelationApp::new("bb2", vec![c.clone()]),
    ));

    // Error: bb2(c) ∧ val(c) != 1 → error()
    let c_val_final = c.clone().field_select("Counter", "fld_val", Sort::bitvec(32));
    vc.add_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("bb2", vec![c])), vec![c_val_final.eq(one_bv).not()]),
        RelationApp::nullary("error"),
    ));

    vc.query = ChcQuery::new().with_target("error");
    vc
}

/// DT+BV interaction: exercises the combination of datatype fields and
/// BV arithmetic in a multi-step transition system.
///
/// Encodes a struct "Counter" with fields (val: bv32, active: Bool):
///   entry → bb0(c) with c = Counter(0, true)
///   bb0(c) ∧ active(c) → bb1(c')  where c' = Counter(val(c) + 1, true)
///   bb1(c) → bb2(c)
///   bb2(c) ∧ val(c) != 1 → error()
///
/// After one increment, val should be 1. Error is UNSAT.
///
/// Exercises: DT constructor/selector combined with BV arithmetic in CHC
/// transition rules. This is the core encoding pattern for Rust struct
/// mutations in trust_mc's CHC backend.
///
/// AY version sensitivity: HIGH — ay#7930 (DT+BV canary regression) showed
/// that the DT+BV interaction is the most version-sensitive path. Three
/// canary harnesses (debug_array_option, memory_store_load, multi_struct_debug)
/// regressed PROOF→ERROR at ay rev 66aaedc due to DT+BV handling changes.
///
/// Expected at the manifest-pinned AY authority: unsat
/// If unknown/error: DT+BV interaction in adaptive CHC regressed (ay#7930 class).
#[test]
fn ay_guard_dt_bv_interaction_struct_mutation() {
    let vc = build_counter_struct_mutation_vc();
    let program = emit_chc(&vc);
    let smt = program.to_string();

    // Expected: unsat (Counter starts at 0, incremented once → val == 1)
    // If unknown: DT+BV interaction in adaptive CHC regressed.
    // If sat: DT constructor/accessor axiom with BV broken.
    assert_z3_result(&smt, "unsat");
}
