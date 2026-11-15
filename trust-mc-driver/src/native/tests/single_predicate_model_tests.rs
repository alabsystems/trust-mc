// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PKG-C5d: on a problem whose only predicate is the nullary query target, the
//! strict proof run checks the one model that can satisfy the query clause
//! (`error := false`) instead of searching for it.
//!
//! The change is admissible only if nothing downstream can tell the two runs
//! apart, so these tests compare what the compiler's evidence is built from —
//! the result, the certificate's metadata and consumer evidence, and the exact
//! model and replay-transcript bytes — between ay's PDR search and the model
//! check, on the masked-add shape the compiler emits for `(x & 0xff) + k`.
//! They also pin that a problem whose fact body is satisfiable still gets the
//! search's verdict, and that every other shape keeps the search.

use std::sync::Arc;

use ay_chc::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

use super::*;

const TIMEOUT: Duration = Duration::from_secs(60);

fn config() -> ay_encode::invoke::EncodeConfig {
    ay_encode::invoke::EncodeConfig::new()
        .with_engine(ay_encode::invoke::Engine::Pdr)
        .with_proof_mode(ay_encode::invoke::ProofMode::Strict)
        .with_timeout(TIMEOUT)
}

fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

fn int_var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

/// `error :- 0 <= x <= 2^32-1, v = bv2nat(255 & int2bv32(x)), v + k > bound`
/// plus the query `error => false`: the one-predicate CHC of the overflow check
/// of `(x & 0xff) + k` on `u32` when `bound` is `u32::MAX`. A small `bound`
/// makes the fact body satisfiable.
fn masked_add(k: i128, bound: i128) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let error = problem.declare_predicate("error", Vec::new());
    let (x, v) = (int_var("x"), int_var("v"));
    let masked = op(
        ChcOp::Bv2Nat,
        vec![op(
            ChcOp::BvAnd,
            vec![
                op(ChcOp::Int2Bv(32), vec![ChcExpr::int(255)]),
                op(ChcOp::Int2Bv(32), vec![x.clone()]),
            ],
        )],
    );
    let constraint = [
        ChcExpr::le(ChcExpr::int(0), x.clone()),
        ChcExpr::le(x, ChcExpr::int(i128::from(u32::MAX))),
        ChcExpr::eq(masked, v.clone()),
        ChcExpr::gt(ChcExpr::add(v, ChcExpr::int(k)), ChcExpr::int(bound)),
    ]
    .into_iter()
    .reduce(ChcExpr::and)
    .expect("four conjuncts");
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), Some(constraint)),
        ClauseHead::Predicate(error, Vec::new()),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(error, Vec::new())])));
    problem
}

/// Everything the `PdrInvariant` transport and the compiler's evidence are
/// derived from, for two runs of the same problem.
fn assert_same_evidence(search: &ay_encode::proof::ProofRun, check: &ay_encode::proof::ProofRun) {
    assert_eq!(check.accepted_as_proof(), search.accepted_as_proof());
    assert_eq!(format!("{:?}", check.result()), format!("{:?}", search.result()));
    let (search, check) = (search.certificate(), check.certificate());
    assert_eq!(check.metadata(), search.metadata());
    assert_eq!(check.metadata_json(), search.metadata_json());
    assert_eq!(check.consumer_evidence(), search.consumer_evidence());
    assert_eq!(check.artifacts().model_bytes(), search.artifacts().model_bytes());
    assert_eq!(
        check.artifacts().quantifier_free_invariant_model_bytes(),
        search.artifacts().quantifier_free_invariant_model_bytes()
    );
    assert_eq!(
        check.artifacts().replay_transcript_bytes(),
        search.artifacts().replay_transcript_bytes()
    );
}

/// The model check accepts the only model and yields the run the search
/// yields, byte for byte, on a Safe masked add.
#[test]
fn single_predicate_model_check_matches_the_search() {
    let problem = masked_add(7, i128::from(u32::MAX));
    let search = ay_encode::invoke::solve_with_proof(problem.clone(), &config())
        .expect("control: the strict PDR search runs");
    assert!(search.accepted_as_proof() && search.result().is_safe(), "control: the search proves");

    let model = only_model_of_single_nullary_predicate(&problem).expect("one nullary predicate");
    let check = ay_encode::invoke::prove_with_external_model(problem.clone(), model, &config())
        .expect("the model check runs");
    assert!(check.accepted_as_proof() && check.result().is_safe(), "the only model is accepted");
    assert_same_evidence(&search, &check);

    let model = only_model_of_single_nullary_predicate(&problem).expect("one nullary predicate");
    let run = single_predicate_proof_run(problem, model, &config(), TIMEOUT)
        .expect("the proof run returns");
    assert_same_evidence(&search, &run);
}

/// A satisfiable fact body: ay's clause check refuses `error := false`, so the
/// proof run is the search's, and its verdict (a refutation) is the search's.
#[test]
fn a_satisfiable_fact_body_gets_the_search_verdict() {
    let problem = masked_add(7, 100);
    let model = only_model_of_single_nullary_predicate(&problem).expect("one nullary predicate");
    let check =
        ay_encode::invoke::prove_with_external_model(problem.clone(), model.clone(), &config())
            .expect("the model check runs");
    assert!(!check.accepted_as_proof(), "a model that admits the error state is refused");

    let search = ay_encode::invoke::solve_with_proof(problem.clone(), &config())
        .expect("control: the strict PDR search runs");
    assert!(!search.result().is_safe(), "control: the search does not prove a reachable error");
    let run = single_predicate_proof_run(problem, model, &config(), TIMEOUT)
        .expect("the proof run returns");
    assert_same_evidence(&search, &run);
}

/// The check and the search share one budget: a check that ends past it is not
/// used, and with nothing left no search is started, so the run fails closed
/// instead of handing ay a zero timeout, which parts of ay read as no limit.
/// It fails as a timeout, never as a caller's cancellation: the compiler
/// publishes a reason that says timeout as a clock stop and any other as an
/// unknown (trust's `is_timeout_reason`).
#[test]
fn a_spent_budget_fails_closed_as_a_timeout_without_a_search() {
    let problem = masked_add(7, i128::from(u32::MAX));
    let model = only_model_of_single_nullary_predicate(&problem).expect("one nullary predicate");
    let spent = Duration::from_nanos(1);
    let run = single_predicate_proof_run(problem, model, &config().with_timeout(spent), spent);
    let error = match run {
        Err(error) => error,
        Ok(run) => panic!("a spent budget must leave no proof run, got {:?}", run.result()),
    };
    assert!(
        matches!(error, ay_encode::EncodeError::Chc(ay_chc::ChcError::Timeout(0))),
        "a spent budget is a timeout after no search iteration, got {error:?}"
    );
    let said = error.to_string().to_ascii_lowercase();
    assert!(said.contains("timeout"), "the reason must read as a clock stop: {said}");
}

/// Only a nullary, acyclic, one-predicate problem has the one-model shape.
#[test]
fn other_shapes_keep_the_search() {
    // A second predicate.
    let mut two = masked_add(7, i128::from(u32::MAX));
    two.declare_predicate("block", vec![ChcSort::Int]);
    assert!(only_model_of_single_nullary_predicate(&two).is_none());

    // A cycle through the nullary predicate.
    let mut cyclic = masked_add(7, i128::from(u32::MAX));
    let error = cyclic.predicates()[0].id;
    cyclic.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(error, Vec::new())]),
        ClauseHead::Predicate(error, Vec::new()),
    ));
    assert!(only_model_of_single_nullary_predicate(&cyclic).is_none());

    // A predicate with an argument.
    let mut unary = ChcProblem::new();
    let p = unary.declare_predicate("p", vec![ChcSort::Int]);
    unary.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), Some(ChcExpr::eq(int_var("y"), ChcExpr::int(0)))),
        ClauseHead::Predicate(p, vec![int_var("y")]),
    ));
    unary.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![int_var("y")])],
        Some(ChcExpr::gt(int_var("y"), ChcExpr::int(0))),
    )));
    assert!(only_model_of_single_nullary_predicate(&unary).is_none());

    // The shape itself.
    assert!(only_model_of_single_nullary_predicate(&masked_add(7, 100)).is_some());
}

/// Observational only, never a threshold: what one strict proof run of the
/// masked add costs by search and by the model check. Run it in release:
/// `targo --unverified test -p trust-mc-driver --lib --release --
/// --ignored --nocapture single_predicate_model_timing_probe`.
#[test]
#[ignore = "manual single-predicate proof-run timing probe"]
fn single_predicate_model_timing_probe() {
    let problem = masked_add(7, i128::from(u32::MAX));
    let mut search_ms = Vec::new();
    let mut check_ms = Vec::new();
    for _ in 0..7 {
        let started = std::time::Instant::now();
        let search = ay_encode::invoke::solve_with_proof(problem.clone(), &config())
            .expect("the search runs");
        search_ms.push(started.elapsed().as_secs_f64() * 1000.0);
        assert!(search.result().is_safe());
        let model =
            only_model_of_single_nullary_predicate(&problem).expect("one nullary predicate");
        let started = std::time::Instant::now();
        let run = single_predicate_proof_run(problem.clone(), model, &config(), TIMEOUT)
            .expect("the proof run returns");
        check_ms.push(started.elapsed().as_secs_f64() * 1000.0);
        assert!(run.result().is_safe());
    }
    search_ms.sort_by(f64::total_cmp);
    check_ms.sort_by(f64::total_cmp);
    println!(
        "single-predicate proof run, masked add, 7 runs: search median {:.1} ms {search_ms:.1?}, \
         model check median {:.1} ms {check_ms:.1?}",
        search_ms[3], check_ms[3]
    );
}
