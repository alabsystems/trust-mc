// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::{SMT_QUERY_TIMEOUT, SolveOutcome, solve_constraints};
use super::*;
use ay_chc::SmtContext;

// ---- wide/nonlinear abstraction retry lane (`abstract_wide_nonlinear`) ----
//
// The retry may ONLY promote `Undecided -> Unsat`, and only via a DEFINITIVE
// abstract-UNSAT of a pure over-approximation. These tests pin the properties
// the over-approximation soundness argument depends on.

/// The base-1e9 Horner encoding of a `>i128`/`u128` constant, exactly as
/// `typed_chc_ay::encode_large_uint_base_1e9` emits it: `768211455 + 1e9 *
/// 340282366920938463463374607431`. The inner factor (~3.4e29) is a single
/// `i128` literal well beyond `i64::MAX` — the "wide" noise the abstraction
/// targets.
fn horner_wide_constant() -> ChcExpr {
    ChcExpr::add(
        ChcExpr::int(768_211_455_i128),
        ChcExpr::mul(
            ChcExpr::int(1_000_000_000_i128),
            ChcExpr::int(340_282_366_920_938_463_463_374_607_431_i128),
        ),
    )
}

/// Collect every integer LITERAL appearing anywhere in `e`.
fn collect_int_literals(e: &ChcExpr, out: &mut Vec<i128>) {
    match e {
        ChcExpr::Int(v) => out.push(*v),
        ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) | ChcExpr::PredicateApp(_, _, args) => {
            for a in args {
                collect_int_literals(a, out);
            }
        }
        ChcExpr::ConstArray(_, inner) => collect_int_literals(inner, out),
        _ => {}
    }
}

fn no_wide_literal_remains(e: &ChcExpr) -> bool {
    let mut lits = Vec::new();
    collect_int_literals(e, &mut lits);
    lits.iter().all(|v| v.unsigned_abs() <= i64::MAX as u128)
}

/// The abstraction preserves the boolean/comparison skeleton verbatim while
/// havocing the wide constant — so a purely LINEAR contradiction survives and
/// the LIA/NIA-choking noise disappears. This is the exact `range_usize`
/// postcondition shape (`_0 = lo ∧ lo ≤ hi ∧ ¬(lo ≤ _0 ≤ hi)` + wide noise).
#[test]
fn abstract_preserves_linear_skeleton_and_drops_wide_constant() {
    let v = |n: &str| ChcExpr::var(ChcVar::new(n, ChcSort::Int));
    let constraints = vec![
        ChcExpr::eq(v("_0"), v("lo")),
        ChcExpr::le(v("lo"), v("hi")),
        ChcExpr::not(ChcExpr::and_vec(vec![
            ChcExpr::le(v("_0"), v("hi")),
            ChcExpr::le(v("lo"), v("_0")),
        ])),
        ChcExpr::eq(v("width"), horner_wide_constant()),
    ];
    let out = abstract_wide_nonlinear(&constraints);
    assert_eq!(out.len(), constraints.len());
    // The three pure-linear constraints are returned structurally identical.
    assert_eq!(out[0], constraints[0], "linear equality perturbed");
    assert_eq!(out[1], constraints[1], "linear bound perturbed");
    assert_eq!(out[2], constraints[2], "negated-conjunction skeleton perturbed");
    // The wide constant is gone from every output constraint.
    for c in &out {
        assert!(no_wide_literal_remains(c), "a >i64::MAX literal survived abstraction: {c:?}");
    }
    // The wide fact became `width = <fresh Int var>`.
    match &out[3] {
        ChcExpr::Op(ChcOp::Eq, args) => match args[1].as_ref() {
            ChcExpr::Var(fresh) => assert!(
                fresh.name.starts_with("__abs_wide_"),
                "wide constant not replaced by a fresh abstraction var: {:?}",
                args[1]
            ),
            other => panic!("wide constant not replaced by a variable: {other:?}"),
        },
        other => panic!("width-equality shape changed: {other:?}"),
    }
}

/// A nonlinear product of two variables (`a * b`) is havoced to a fresh var —
/// the NIA-hard operand the concrete solver cannot reason about linearly.
#[test]
fn abstract_havocs_nonlinear_product() {
    let a = ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let constraints = vec![ChcExpr::le(ChcExpr::mul(a, b), ChcExpr::int(10))];
    let out = abstract_wide_nonlinear(&constraints);
    match &out[0] {
        ChcExpr::Op(ChcOp::Le, args) => {
            assert!(
                matches!(args[0].as_ref(), ChcExpr::Var(v) if v.name.starts_with("__abs_wide_")),
                "nonlinear product not replaced by a fresh var: {:?}",
                args[0]
            );
            assert_eq!(args[1].as_ref(), &ChcExpr::int(10), "bound literal perturbed");
        }
        other => panic!("comparison skeleton changed: {other:?}"),
    }
}

/// A purely linear formula (no wide literals, no nonlinear ops) is returned
/// structurally UNCHANGED. Guards against perturbing bodies the concrete
/// solver already decides — the abstraction is inert on the common case.
#[test]
fn abstract_is_identity_on_purely_linear_formula() {
    let v = |n: &str| ChcExpr::var(ChcVar::new(n, ChcSort::Int));
    let constraints = vec![
        ChcExpr::le(v("a"), v("b")),
        ChcExpr::eq(v("a"), ChcExpr::int(3)),
        ChcExpr::not(ChcExpr::le(v("b"), v("a"))),
        ChcExpr::eq(ChcExpr::add(v("a"), ChcExpr::int(1)), v("b")),
    ];
    let out = abstract_wide_nonlinear(&constraints);
    assert_eq!(out, constraints, "abstraction perturbed a purely linear body");
}

/// SOUNDNESS-CRITICAL: minted fresh variables are disjoint from EVERY program
/// variable. Reusing an already-constrained name would not be an
/// over-approximation and could manufacture a spurious UNSAT (a false proof).
/// Here a program variable is literally named `__abs_wide_0`; the abstraction
/// must skip it.
#[test]
fn abstract_fresh_vars_never_collide_with_program_vars() {
    let collide = ChcExpr::var(ChcVar::new("__abs_wide_0", ChcSort::Int));
    let constraints = vec![
        ChcExpr::eq(ChcExpr::var(ChcVar::new("x", ChcSort::Int)), horner_wide_constant()),
        ChcExpr::le(collide, ChcExpr::int(0)),
    ];
    let out = abstract_wide_nonlinear(&constraints);
    // Find the fresh var introduced for the wide constant in out[0].
    let fresh_name = match &out[0] {
        ChcExpr::Op(ChcOp::Eq, args) => match args[1].as_ref() {
            ChcExpr::Var(v) => v.name.clone(),
            other => panic!("expected fresh var, got {other:?}"),
        },
        other => panic!("unexpected shape {other:?}"),
    };
    assert_ne!(
        fresh_name, "__abs_wide_0",
        "fresh abstraction var collided with an existing program variable — UNSOUND"
    );
    assert!(fresh_name.starts_with("__abs_wide_"));
    // The pre-existing `__abs_wide_0` constraint is untouched (no wide term).
    assert_eq!(out[1], constraints[1]);
}

/// Equal wide subterms map to the SAME fresh variable, so any linear relation
/// running through the havoced term is preserved (keeps the over-approximation
/// tight enough to still refute).
#[test]
fn abstract_memoizes_equal_wide_subterms() {
    let a = ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let constraints =
        vec![ChcExpr::eq(a, horner_wide_constant()), ChcExpr::eq(b, horner_wide_constant())];
    let out = abstract_wide_nonlinear(&constraints);
    let name_of = |c: &ChcExpr| -> String {
        match c {
            ChcExpr::Op(ChcOp::Eq, args) => match args[1].as_ref() {
                ChcExpr::Var(v) => v.name.clone(),
                other => panic!("expected fresh var: {other:?}"),
            },
            other => panic!("unexpected shape: {other:?}"),
        }
    };
    assert_eq!(
        name_of(&out[0]),
        name_of(&out[1]),
        "equal wide subterms must map to the same fresh var"
    );
}

/// The optional max/min lemmas must remain true for every concrete valuation.
/// Pin the branch-sensitive shapes on a satisfiable instance: if either lemma
/// accidentally constrained the replacement more tightly than the concrete
/// `ite`, the abstract query could become UNSAT and authorize a false prune.
#[test]
fn max_min_replacement_lemmas_preserve_a_concrete_model() {
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let z_max = ChcExpr::var(ChcVar::new("z_max", ChcSort::Int));
    let z_min = ChcExpr::var(ChcVar::new("z_min", ChcSort::Int));
    let product = ChcExpr::mul(x.clone(), y.clone());
    let five = ChcExpr::int(5);
    let max =
        ChcExpr::ite(ChcExpr::ge(product.clone(), five.clone()), product.clone(), five.clone());
    let min = ChcExpr::ite(ChcExpr::le(product.clone(), five.clone()), product, five);
    // x*y = 6, hence max(6, 5) = 6 and min(6, 5) = 5.
    let constraints = vec![
        ChcExpr::eq(x, ChcExpr::int(2)),
        ChcExpr::eq(y, ChcExpr::int(3)),
        ChcExpr::eq(z_max.clone(), max),
        ChcExpr::eq(z_max, ChcExpr::int(6)),
        ChcExpr::eq(z_min.clone(), min),
        ChcExpr::eq(z_min, ChcExpr::int(5)),
    ];
    let abstracted = abstract_wide_nonlinear(&constraints);
    assert_eq!(
        abstracted.len(),
        constraints.len() + 4,
        "max and min replacements must each emit exactly two bound lemmas"
    );

    let mut smt = SmtContext::new();
    let formula = ChcExpr::and_all(abstracted.iter().cloned());
    let result = smt.check_sat_with_timeout(&formula, SMT_QUERY_TIMEOUT);
    assert!(result.is_sat(), "sound max/min lemmas removed a concrete model: {result:?}");
}

/// End-to-end SOUNDNESS backstop: a genuinely SATISFIABLE body carrying wide
/// noise is NEVER reported `Unsat` (which would prune a reachable edge — a
/// false proof). Whether the raw solve decides it or the retry runs on the
/// over-approximation, the verdict must not be `Unsat`.
#[test]
fn retry_never_prunes_a_satisfiable_wide_body() {
    let mut smt = SmtContext::new();
    let a = ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let w = ChcExpr::var(ChcVar::new("w", ChcSort::Int));
    // a=3 ∧ b=5 ∧ a<b (SAT) ∧ w = <wide constant> (pure noise, still SAT).
    let constraints = vec![
        ChcExpr::eq(a.clone(), ChcExpr::int(3)),
        ChcExpr::eq(b.clone(), ChcExpr::int(5)),
        ChcExpr::lt(a, b),
        ChcExpr::eq(w, horner_wide_constant()),
    ];
    assert!(
        !matches!(solve_constraints(&mut smt, &constraints), SolveOutcome::Unsat),
        "FALSE PROOF: a satisfiable body was pruned as Unsat by the abstraction retry"
    );
}

/// End-to-end mechanism check: the over-approximation of a `range_usize`-shaped
/// body (linear-UNSAT core + wide noise) is DEFINITIVELY UNSAT — the property
/// that licenses promoting the edge's verdict to `Unsat`.
#[test]
fn abstraction_of_linear_unsat_wide_body_is_definitively_unsat() {
    let mut smt = SmtContext::new();
    let v = |n: &str| ChcExpr::var(ChcVar::new(n, ChcSort::Int));
    // _0 = lo ∧ lo ≤ hi ∧ ¬(lo ≤ _0 ∧ _0 ≤ hi) is UNSAT (substituting _0=lo
    // makes the negated conjunction false); the wide fact is irrelevant noise.
    let constraints = vec![
        ChcExpr::eq(v("_0"), v("lo")),
        ChcExpr::le(v("lo"), v("hi")),
        ChcExpr::not(ChcExpr::and_vec(vec![
            ChcExpr::le(v("lo"), v("_0")),
            ChcExpr::le(v("_0"), v("hi")),
        ])),
        ChcExpr::eq(v("width"), horner_wide_constant()),
    ];
    let abstracted = abstract_wide_nonlinear(&constraints);
    let formula = ChcExpr::and_all(abstracted.iter().cloned());
    smt.reset();
    let result = smt.check_sat_with_timeout(&formula, SMT_QUERY_TIMEOUT);
    assert!(
        result.is_unsat(),
        "over-approximation of a linear-UNSAT body was not decided UNSAT: {result:?}"
    );
    // And the original body is not SAT either (soundness direction sanity).
    assert!(!result.is_sat());
}

/// SOUNDNESS REGRESSION (real-sort confusion): the arithmetic ops are
/// polymorphic over Int AND Real, so a REAL-valued subterm must NEVER be
/// replaced by an INTEGER fresh variable — that pins a real quantity to ℤ and,
/// via ay's `to_real` integrality reasoning, could turn a SATISFIABLE body into
/// a spurious UNSAT (a false proof: a reachable float obligation pruned to
/// SAFE). Body: `r1/r2 = r ∧ r + r = 1` — satisfiable (r=1/2, r1=1, r2=2). The
/// abstraction must leave the real division intact, so the query is never
/// promoted to UNSAT.
#[test]
fn abstraction_never_replaces_a_real_subterm_with_an_int_var() {
    let r1 = ChcExpr::var(ChcVar::new("r1", ChcSort::Real));
    let r2 = ChcExpr::var(ChcVar::new("r2", ChcSort::Real));
    let r = ChcExpr::var(ChcVar::new("r", ChcSort::Real));
    // Real division with a symbolic denominator (a nonlinear real term).
    let div = ChcExpr::Op(ChcOp::Div, vec![Arc::new(r1), Arc::new(r2)]);
    let constraints = vec![
        ChcExpr::eq(div, r.clone()),
        ChcExpr::eq(ChcExpr::add(r.clone(), r), ChcExpr::Real(1, 1)),
    ];
    // The real subterm is int-mis-sorted no longer: the body is returned
    // structurally UNCHANGED (nothing replaced).
    let out = abstract_wide_nonlinear(&constraints);
    assert_eq!(out, constraints, "a real-valued subterm was abstracted to an Int var — UNSOUND");
    // Solving the over-approximation (== the original here) must NOT be a
    // definitive UNSAT — the satisfiable real body must never be pruned.
    let mut smt = SmtContext::new();
    let formula = ChcExpr::and_all(out.iter().cloned());
    smt.reset();
    let result = smt.check_sat_with_timeout(&formula, SMT_QUERY_TIMEOUT);
    assert!(
        !result.is_unsat(),
        "FALSE PROOF: a satisfiable real body was decided UNSAT after abstraction: {result:?}"
    );
}

/// Direct unit pin on the sort classifier: `Real`-sorted arithmetic (and mixed
/// Int/Real terms) are NOT integer-sorted, while pure-integer terms are.
#[test]
fn is_int_sorted_rejects_real_and_mixed_arithmetic() {
    let iv = ChcExpr::var(ChcVar::new("i", ChcSort::Int));
    let rv = ChcExpr::var(ChcVar::new("r", ChcSort::Real));
    // Pure integer arithmetic — accepted.
    assert!(is_int_sorted(&ChcExpr::mul(iv.clone(), iv.clone())));
    assert!(is_int_sorted(&ChcExpr::add(iv.clone(), ChcExpr::int(5))));
    // Real product — rejected.
    assert!(!is_int_sorted(&ChcExpr::mul(rv.clone(), rv.clone())));
    // Mixed Int/Real (`sort()` would report Int from the first operand, but the
    // term coerces to Real) — must be rejected.
    assert!(!is_int_sorted(&ChcExpr::add(iv, rv)));
}
