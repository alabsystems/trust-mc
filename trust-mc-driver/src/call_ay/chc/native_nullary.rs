// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Exact handling for degenerate zero-arity propositional CHC reachability.

use std::collections::{HashMap, HashSet};

use ay::chc::{ChcExpr, ChcProblem, ClauseHead, PredicateId, SmtResult, SmtValue};
use std::borrow::Cow;
use trust_mc_metadata::HarnessMetadata;

use crate::property_model::{CheckStatus, Property, PropertyId, RawSourceLocation};
use crate::session::KaniSession;
use crate::verification_result::{FailedProperties, ProofCrosscheck, VerificationStatus};

use super::ChcSolverResult;
use super::model_eval::constraints_are_constant_refuted;
use super::smt_analysis::smt_has_recursive_unwind_assertion;
use super::verdict_policy::{ChcOutcomeKind, apply_recursion_unwind_verdict};

macro_rules! solver_stdout {
    ($($arg:tt)*) => {{
        use std::io::Write;
        let stdout = std::io::stdout();
        let mut handle = stdout.lock();
        let _ = writeln!(handle, $($arg)*);
    }};
}

fn propositional_constraint_holds(constraint: Option<&ChcExpr>) -> bool {
    match constraint {
        None | Some(ChcExpr::Bool(true)) => true,
        Some(_) => false,
    }
}

/// Exact reachability for the propositional, zero-arity CHC subset.
///
/// This is deliberately narrow: any relation argument or non-`true` constraint
/// makes the clause unusable for this shortcut. Returning `true` therefore means
/// there is a concrete Horn derivation of the queried `false` head without asking
/// the portfolio solver to classify a degenerate zero-arity problem.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn has_constraint_free_nullary_error_derivation(problem: &ChcProblem) -> bool {
    constraint_free_nullary_error_derivation_relations(problem).is_some()
}

/// Like [`has_constraint_free_nullary_error_derivation`], but on a positive
/// result returns the names of the predicates on the winning derivation path
/// (the `false`-head clause's body predicates plus, transitively, every
/// predicate that supported them). Unlike the constraint-ignoring
/// [`forward_reachable_relation_names`] superset, this is the EXACT derivation
/// set for the propositional subset: every clause on the path is zero-arity
/// with a trivially-true constraint, so reachability is derivability.
pub(super) fn constraint_free_nullary_error_derivation_relations(
    problem: &ChcProblem,
) -> Option<HashSet<String>> {
    // Per-predicate origin sets: the predicate itself plus the origins of the
    // body predicates that first derived it (mirrors ReachFact::origins in the
    // acyclic witness search).
    let mut reachable = HashMap::<PredicateId, HashSet<PredicateId>>::new();

    loop {
        let mut changed = false;

        for clause in problem.clauses() {
            if !propositional_constraint_holds(clause.body.constraint.as_ref()) {
                continue;
            }

            let body_reachable = clause
                .body
                .predicates
                .iter()
                .all(|(pred, args)| args.is_empty() && reachable.contains_key(pred));
            if !body_reachable {
                continue;
            }

            match &clause.head {
                ClauseHead::Predicate(pred, args) if args.is_empty() => {
                    if !reachable.contains_key(pred) {
                        let mut origins: HashSet<PredicateId> = clause
                            .body
                            .predicates
                            .iter()
                            .flat_map(|(body_pred, _)| {
                                reachable.get(body_pred).into_iter().flatten().copied()
                            })
                            .collect();
                        origins.insert(*pred);
                        reachable.insert(*pred, origins);
                        changed = true;
                    }
                }
                ClauseHead::False => {
                    let derived: HashSet<PredicateId> = clause
                        .body
                        .predicates
                        .iter()
                        .flat_map(|(body_pred, _)| {
                            reachable.get(body_pred).into_iter().flatten().copied()
                        })
                        .collect();
                    return Some(
                        derived
                            .iter()
                            .filter_map(|pred| problem.get_predicate(*pred).map(|p| p.name.clone()))
                            .collect(),
                    );
                }
                _ => {}
            }
        }

        if !changed {
            return None;
        }
    }
}

#[derive(Clone)]
struct ReachFact {
    args: Vec<ChcExpr>,
    constraints: Vec<ChcExpr>,
    /// Predicates on the derivation path that produced this fact (the fact's
    /// own head predicate plus, transitively, every predicate of the facts it
    /// was composed from). Lets the `false`-head arm report WHICH per-check
    /// error relation the winning derivation went through.
    origins: HashSet<PredicateId>,
}

/// Conservative exact reachability for acyclic CHCs.
///
/// This shortcut is intentionally SAT-backed: it only reports unsafe after
/// composing a concrete derivation path to `false` and checking the accumulated
/// background-theory constraints. It may miss derivations, but a positive result
/// is a real counterexample path.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn has_satisfiable_acyclic_error_derivation(problem: &ChcProblem) -> bool {
    // Effectively-unbounded deadline: this wrapper is exactness-only (tests);
    // production callers pass the real per-harness deadline to the witness fn.
    let deadline = crate::deadline::Deadline::after(std::time::Duration::from_secs(3600));
    satisfiable_acyclic_error_derivation_witness(problem, deadline).is_some()
}

/// Witness of a satisfiable acyclic derivation to `error`: the raw SMT model
/// plus the names of every predicate on the winning derivation path, so the
/// caller can attribute the counterexample to its per-check error relation
/// instead of a generic aggregate property.
pub(super) struct AcyclicErrorWitness {
    /// JSON rendering of the satisfying assignment for the derivation path.
    pub(super) model_json: serde_json::Value,
    /// Names of the predicates the derivation to `false` went through
    /// (direct body predicates of the final clause plus, transitively, the
    /// predicates of every fact composed along the path).
    pub(super) derived_relations: HashSet<String>,
}

/// Like [`has_satisfiable_acyclic_error_derivation`], but on a positive result
/// returns the witness: the SMT model for the derivation to `error` (so the
/// caller can attach a concrete counterexample, e.g. the overflowing input
/// assignment) plus the derivation-path predicate names (so the caller can
/// attribute the failure to its per-check error relation). `None` means no
/// satisfiable acyclic derivation was found — i.e. no counterexample from this
/// exact shortcut.
///
/// `deadline`: the per-harness wall-clock deadline. The fact-combination
/// enumeration is SMT-backed and can blow up combinatorially on large
/// problems; on an exhausted deadline the search aborts with `None`.
/// Fail-closed: `None` only skips this CTREX shortcut (the caller falls
/// through to the deadline-clamped portfolio) — it never asserts safety.
pub(super) fn satisfiable_acyclic_error_derivation_witness(
    problem: &ChcProblem,
    deadline: crate::deadline::Deadline,
) -> Option<AcyclicErrorWitness> {
    const MAX_FACTS_PER_PREDICATE: usize = 128;
    const MAX_COMBINATIONS_PER_CLAUSE: usize = 1024;

    let mut smt = problem.make_smt_context();
    let mut facts: HashMap<PredicateId, Vec<ReachFact>> = HashMap::new();

    for _ in 0..=problem.predicates().len().saturating_add(problem.clauses().len()) {
        let mut changed = false;

        for clause in problem.clauses() {
            let Some(body_fact_options) = body_fact_options(clause, &facts) else {
                continue;
            };

            let mut checked = 0usize;
            for combo in FactCombinationIter::new(body_fact_options) {
                if deadline.remaining().is_zero() {
                    solver_stdout!(
                        "[AY-chc] acyclic-witness search aborted: per-harness deadline \
                         exhausted (no witness claimed)"
                    );
                    return None;
                }
                checked += 1;
                if checked > MAX_COMBINATIONS_PER_CLAUSE {
                    break;
                }

                let mut constraints = Vec::new();
                for (body_idx, fact) in combo.iter().enumerate() {
                    constraints.extend(fact.constraints.iter().cloned());
                    let (_, body_args) = &clause.body.predicates[body_idx];
                    constraints.extend(body_args.iter().zip(&fact.args).map(
                        |(body_arg, fact_arg)| ChcExpr::eq(body_arg.clone(), fact_arg.clone()),
                    ));
                }
                if let Some(constraint) = &clause.body.constraint {
                    constraints.push(constraint.clone());
                }

                if !constraints_are_sat(&mut smt, &constraints) {
                    continue;
                }

                match &clause.head {
                    ClauseHead::False => {
                        // The pre-check above confirmed satisfiability via the
                        // embedded `SmtContext::check_sat`. That solver has a known
                        // soundness gap on bitvector `concat`/`extract` reasoning
                        // (e.g. it reports
                        // `(not (= ((_ extract 31 0) (concat _ #x00000000)) #x0))`
                        // as SAT, which z3 and the ay CLI both refute as UNSAT).
                        // Trusting it blindly turned genuinely-UNSAT contract
                        // proofs into spurious `Genuine` counterexamples.
                        //
                        // Model-free guard: if the accumulated constraints are
                        // provably contradictory by constant propagation (the
                        // `concat`/`extract` folding the embedded solver gets
                        // wrong), the `Sat` verdict is spurious. Discard it and let
                        // the full CHC portfolio decide. A genuinely-satisfiable
                        // set is never refuted, so real counterexamples keep the
                        // fast exact-derivation path.
                        if constraints_are_constant_refuted(&constraints) {
                            continue;
                        }
                        let model =
                            constraints_sat_raw_model(&mut smt, &constraints).unwrap_or_default();
                        // Derivation-path predicates: the final clause's direct
                        // body predicates plus everything the composed facts
                        // already went through. Names feed per-check property
                        // attribution in `interpret_chc_trivial_unsafe`.
                        let mut derived: HashSet<PredicateId> =
                            clause.body.predicates.iter().map(|(pred, _)| *pred).collect();
                        for fact in &combo {
                            derived.extend(fact.origins.iter().copied());
                        }
                        let derived_relations = derived
                            .iter()
                            .filter_map(|pred| problem.get_predicate(*pred).map(|p| p.name.clone()))
                            .collect();
                        return Some(AcyclicErrorWitness {
                            model_json: render_model_json(&model),
                            derived_relations,
                        });
                    }
                    ClauseHead::Predicate(pred, args) => {
                        let entry = facts.entry(*pred).or_default();
                        if entry.len() >= MAX_FACTS_PER_PREDICATE {
                            continue;
                        }
                        let signature = fact_signature(args, &constraints);
                        if entry
                            .iter()
                            .any(|fact| fact_signature(&fact.args, &fact.constraints) == signature)
                        {
                            continue;
                        }
                        let mut origins: HashSet<PredicateId> =
                            combo.iter().flat_map(|fact| fact.origins.iter().copied()).collect();
                        origins.insert(*pred);
                        entry.push(ReachFact { args: args.clone(), constraints, origins });
                        changed = true;
                    }
                    _ => {}
                }
            }
        }

        if !changed {
            return None;
        }
    }

    None
}

fn body_fact_options(
    clause: &ay::chc::HornClause,
    facts: &HashMap<PredicateId, Vec<ReachFact>>,
) -> Option<Vec<Vec<ReachFact>>> {
    let mut options = Vec::with_capacity(clause.body.predicates.len());
    for (pred, _) in &clause.body.predicates {
        let pred_facts = facts.get(pred)?;
        if pred_facts.is_empty() {
            return None;
        }
        options.push(pred_facts.clone());
    }
    Some(options)
}

fn constraints_are_sat(smt: &mut ay::chc::SmtContext, constraints: &[ChcExpr]) -> bool {
    let formula = ChcExpr::and_all(constraints.iter().cloned());
    smt.reset();
    matches!(smt.check_sat(&formula), SmtResult::Sat(_))
}

/// Re-solve `constraints` and return the raw satisfying model as an ordinary
/// `HashMap`. Returns `None` if the embedded solver does not return `Sat`.
fn constraints_sat_raw_model(
    smt: &mut ay::chc::SmtContext,
    constraints: &[ChcExpr],
) -> Option<HashMap<String, SmtValue>> {
    let formula = ChcExpr::and_all(constraints.iter().cloned());
    smt.reset();
    match smt.check_sat(&formula) {
        SmtResult::Sat(model) => Some(model.iter().map(|(k, v)| (k.clone(), v.clone())).collect()),
        _ => None,
    }
}

/// Render a model as a JSON object mapping each variable to its value.
fn render_model_json(model: &HashMap<String, SmtValue>) -> serde_json::Value {
    let mut assignments = serde_json::Map::new();
    for (name, value) in model {
        assignments.insert(name.clone(), serde_json::Value::String(format!("{value:?}")));
    }
    serde_json::Value::Object(assignments)
}

fn fact_signature(args: &[ChcExpr], constraints: &[ChcExpr]) -> String {
    let mut out = String::new();
    for arg in args {
        out.push_str(&arg.to_string());
        out.push('\n');
    }
    out.push_str("--\n");
    for constraint in constraints {
        out.push_str(&constraint.to_string());
        out.push('\n');
    }
    out
}

struct FactCombinationIter {
    options: Vec<Vec<ReachFact>>,
    indices: Vec<usize>,
    done: bool,
}

impl FactCombinationIter {
    fn new(options: Vec<Vec<ReachFact>>) -> Self {
        let len = options.len();
        Self { options, indices: vec![0; len], done: false }
    }
}

impl Iterator for FactCombinationIter {
    type Item = Vec<ReachFact>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let item: Vec<ReachFact> = self
            .options
            .iter()
            .zip(&self.indices)
            .map(|(facts, index)| facts[*index].clone())
            .collect();

        if self.indices.is_empty() {
            self.done = true;
            return Some(item);
        }

        for pos in (0..self.indices.len()).rev() {
            self.indices[pos] += 1;
            if self.indices[pos] < self.options[pos].len() {
                return Some(item);
            }
            self.indices[pos] = 0;
        }
        self.done = true;
        Some(item)
    }
}

/// Names of all forward-reachable relations in `problem`.
///
/// Monotone forward closure over predicate reachability, ignoring constraint
/// satisfiability. This is EXACT for the constraint-free propositional / acyclic
/// subset that reaches `interpret_chc_trivial_unsafe` (every clause on such a
/// derivation has a `true` constraint), and a conservative over-approximation
/// otherwise. Over-approximation only ever makes a should_panic verdict MORE
/// strict (fail-closed): an extra "reachable" non-panic check flips PanicsOnly
/// to Other, never the reverse.
fn forward_reachable_relation_names(problem: &ChcProblem) -> HashSet<String> {
    let mut reachable: HashSet<PredicateId> = HashSet::new();
    loop {
        let mut changed = false;
        for clause in problem.clauses() {
            let body_reachable =
                clause.body.predicates.iter().all(|(pred, _)| reachable.contains(pred));
            if !body_reachable {
                continue;
            }
            if let ClauseHead::Predicate(pred, _) = &clause.head {
                changed |= reachable.insert(*pred);
            }
        }
        if !changed {
            break;
        }
    }
    reachable
        .iter()
        .filter_map(|pred| problem.get_predicate(*pred).map(|p| p.name.clone()))
        .collect()
}

impl KaniSession {
    /// Interpret a propositional CHC system where `error` is syntactically
    /// reachable through zero-arity, constraint-free Horn rules.
    ///
    /// `derived_failing_relations`: when the caller holds an exact derivation
    /// witness (the acyclic SAT-backed shortcut), the names of the predicates
    /// on the winning derivation path. Used to attribute the failure to its
    /// per-check property (precise fn/class/span/description) instead of the
    /// legacy aggregate `chc.0` property. `None` (or no match against the
    /// harness's per-property table) keeps the legacy behavior exactly.
    pub(super) fn interpret_chc_trivial_unsafe(
        &self,
        smt_content: &str,
        smt_file: &std::path::Path,
        problem: &ChcProblem,
        harness: &HarnessMetadata,
        derived_failing_relations: Option<&HashSet<String>>,
    ) -> anyhow::Result<ChcSolverResult> {
        solver_stdout!(
            "[AY:CTREX] CHC verification: counterexample reachable \
             (exact CHC derivation)"
        );

        // Precise attribution (derivation-witness): when the exact derivation
        // path is known, report the per-check property that actually fired —
        // matching Kani's per-property failure output — rather than one
        // aggregate `chc` property. Verdict is unchanged either way; only the
        // property list (and thus should_panic class + ctrex classification)
        // gains precision.
        let precise_properties =
            derived_failing_relations.filter(|derived| !derived.is_empty()).and_then(|derived| {
                super::property_report::chc_failure_properties(smt_file, harness, derived)
            });

        let (failed_class, properties) = if let Some(props) = precise_properties {
            let failed_class = crate::ay_parse::determine_failed_from_properties(&props);
            (failed_class, props)
        } else {
            // Legacy aggregate path. Derive `failed_properties` from the class
            // of the reachable per-property check(s), not a hard-coded
            // PanicsOnly. A reachable memory_safety / pointer-deref / UB
            // `error_p` ⇒ Other (→ FAILED under #[should_panic]); a reachable
            // assertion/panic `error_p` — or a direct `error` head with no
            // per-property relation at all (a panic call) — ⇒ PanicsOnly.
            let reachable = forward_reachable_relation_names(problem);
            let failed_class =
                match super::property_report::chc_failure_properties(smt_file, harness, &reachable)
                {
                    Some(props) => crate::ay_parse::determine_failed_from_properties(&props),
                    None => FailedProperties::PanicsOnly,
                };
            let properties = vec![Property {
                description: Cow::Borrowed(
                    "CHC verification: error reachable (exact CHC derivation)",
                ),
                property_id: PropertyId { fn_name: None, class: Cow::Borrowed("chc"), id: 0 },
                source_location: RawSourceLocation {
                    column: None,
                    file: None,
                    function: None,
                    line: None,
                },
                status: CheckStatus::Failure,
                trace: None,
            }];
            (failed_class, properties)
        };

        let has_recursive_unwind = smt_has_recursive_unwind_assertion(smt_content);
        let (status, failed_props, properties, _) = apply_recursion_unwind_verdict(
            has_recursive_unwind,
            ChcOutcomeKind::Counterexample,
            VerificationStatus::Failure,
            failed_class,
            properties,
            Some(harness.pretty_name.as_str()),
        );

        Ok(ChcSolverResult {
            status,
            failed_properties: failed_props,
            properties,
            proof_crosscheck: ProofCrosscheck::NotRun,
            proof_qualifiers: Vec::new(),
            proof_transcript_metadata: None,
            native_full_verification_verdict: None,
        })
    }
}

#[cfg(test)]
mod propositional_reachability_tests {
    use super::*;
    use ay::chc::ChcParser;

    #[test]
    fn detects_constraint_free_nullary_error_derivation() {
        let smt = r#"
(set-logic HORN)
(declare-rel entry ())
(declare-rel error ())
(rule (=> true entry))
(rule (=> entry error))
(query error)
"#;
        let mut problem = ChcParser::parse(smt).expect("test CHC should parse");
        problem.expand_nullary_fail_queries(false);

        assert!(has_constraint_free_nullary_error_derivation(&problem));
    }

    #[test]
    fn propositional_derivation_returns_exact_path_relations() {
        // error_p_check mirrors a per-property error relation; `unrelated` is
        // reachable but NOT on the derivation path to `false` — the exact
        // witness set must contain the path (entry, error_p_check, error) and
        // exclude `unrelated`.
        let smt = r#"
(set-logic HORN)
(declare-rel entry ())
(declare-rel error_p_check ())
(declare-rel unrelated ())
(declare-rel error ())
(rule (=> true entry))
(rule (=> true unrelated))
(rule (=> entry error_p_check))
(rule (=> error_p_check error))
(query error)
"#;
        let mut problem = ChcParser::parse(smt).expect("test CHC should parse");
        problem.expand_nullary_fail_queries(false);

        let derived = constraint_free_nullary_error_derivation_relations(&problem)
            .expect("derivation should be found");
        assert!(derived.contains("entry"), "path root missing: {derived:?}");
        assert!(derived.contains("error_p_check"), "per-check relation missing: {derived:?}");
        assert!(!derived.contains("unrelated"), "off-path relation must be excluded: {derived:?}");
    }

    #[test]
    fn rejects_false_constraint_on_nullary_fact() {
        let smt = r#"
(set-logic HORN)
(declare-rel entry ())
(declare-rel error ())
(rule (=> false entry))
(rule (=> entry error))
(query error)
"#;
        let mut problem = ChcParser::parse(smt).expect("test CHC should parse");
        problem.expand_nullary_fail_queries(false);

        assert!(!has_constraint_free_nullary_error_derivation(&problem));
    }

    #[test]
    fn rejects_non_nullary_derivation() {
        let smt = r#"
(set-logic HORN)
(declare-var x Int)
(declare-rel entry (Int))
(declare-rel error ())
(rule (=> true (entry x)))
(rule (=> (entry x) error))
(query error)
"#;
        let mut problem = ChcParser::parse(smt).expect("test CHC should parse");
        problem.expand_nullary_fail_queries(false);

        assert!(!has_constraint_free_nullary_error_derivation(&problem));
    }

    #[test]
    fn detects_satisfiable_acyclic_error_derivation() {
        let smt = r#"
(set-logic HORN)
(declare-var x (_ BitVec 8))
(declare-rel entry ((_ BitVec 8)))
(declare-rel mid ((_ BitVec 8)))
(declare-rel error ())
(rule (=> true (entry x)))
(rule (=> (and (entry x) (= x #x01)) (mid x)))
(rule (=> (mid x) error))
(query error)
"#;
        let mut problem = ChcParser::parse(smt).expect("test CHC should parse");
        problem.expand_nullary_fail_queries(false);

        assert!(has_satisfiable_acyclic_error_derivation(&problem));
    }

    #[test]
    fn rejects_unsatisfiable_acyclic_error_derivation() {
        let smt = r#"
(set-logic HORN)
(declare-var x (_ BitVec 8))
(declare-rel entry ((_ BitVec 8)))
(declare-rel mid ((_ BitVec 8)))
(declare-rel error ())
(rule (=> true (entry x)))
(rule (=> (and (entry x) (= x #x01)) (mid x)))
(rule (=> (and (mid x) (= x #x02)) error))
(query error)
"#;
        let mut problem = ChcParser::parse(smt).expect("test CHC should parse");
        problem.expand_nullary_fail_queries(false);

        assert!(!has_satisfiable_acyclic_error_derivation(&problem));
    }

    /// Regression repro: the low 32 bits of `concat(#x00000090, #x00000000)` are
    /// zero, so `error` is UNREACHABLE (both z3 and the ay CLI prove this UNSAT).
    /// The acyclic shortcut must NOT report a satisfiable error derivation.
    /// Mirrors the `simple_ensures_pass` proof_for_contract false positive.
    #[test]
    fn rejects_concat_extract_low_bits_error_derivation() {
        let smt = r#"
(set-logic HORN)
(declare-var a (_ BitVec 64))
(declare-var b (_ BitVec 64))
(declare-rel P ((_ BitVec 64)))
(declare-rel Q ((_ BitVec 64)))
(declare-rel error ())
(rule (=> (= a (concat (_ bv144 32) (_ bv0 32))) (P a)))
(rule (=> (and (P a) (= b a)) (Q b)))
(rule (=> (and (Q b) (not (= ((_ extract 31 0) b) (_ bv0 32)))) error))
(query error)
"#;
        let mut problem = ChcParser::parse(smt).expect("test CHC should parse");
        problem.expand_nullary_fail_queries(false);

        assert!(
            !has_satisfiable_acyclic_error_derivation(&problem),
            "low 32 bits of concat(_, 0) are 0, so error is unreachable (UNSAT)"
        );
    }
}
