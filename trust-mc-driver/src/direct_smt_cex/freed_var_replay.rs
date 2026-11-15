// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Replay-validated reachability of one `error_pN` along a derivation that
//! never reads a set of named, threaded state variables.
//!
//! The CHC encoder over-approximates some operations by a READ from a state
//! variable no rule constrains: a symbolic float `a + b` is
//! `select(float_binop_tbl_f32, key)`, and the table is threaded through every
//! relation unchanged. A proof over every table is a proof under IEEE 754 (one
//! interpretation of it). A counterexample is evidence only if it holds for
//! the real operation too, which the solver's model does not show: the model
//! picks one table.
//!
//! This module answers the narrower question that certifies such a
//! counterexample without trusting the per-property taint analysis: is `target`
//! derivable using ONLY clauses in which the variables are never read? It
//! builds the cut system
//!
//! - every argument position a variable occupies is dropped from its relation
//!   — refused outright when that position ever carries anything but one of the
//!   variables themselves, since dropping it would then free a real value;
//! - every clause that mentions a variable anywhere else (its constraint, or
//!   inside another argument) is removed;
//! - the queries are replaced by the single query `target => false`,
//!
//! decides it with the exact acyclic composer, and REPLAYS the composer's trace
//! and total model against a second, independently built copy of the cut system
//! ([`super::replay_acyclic_direct_smt_witness`]). Removing clauses only removes
//! derivations, and no retained clause reads a variable, so a replayed
//! derivation of the cut system is a derivation of the original one for EVERY
//! value of the variables — in particular for the one the real program
//! computes. Any refusal, undecided search or failed replay is an error: the
//! caller keeps the counterexample uncertified.

use std::collections::HashSet;

use ay_chc::{ChcExpr, ChcParser, ChcProblem, ClauseBody, ClauseHead, HornClause, PredicateId};

use super::{AcyclicDecision, acyclic_direct_smt_decision, replay_acyclic_direct_smt_witness};

/// Clause ceiling for the cut system. The composer's per-query budget is one
/// second; beyond this size the replay is not the cheap confirmation it is
/// meant to be, and refusing only leaves a counterexample uncertified.
const MAX_CUT_CLAUSES: usize = 4096;

/// Name of the aggregate error relation every `error_pN` feeds.
const AGGREGATE_ERROR: &str = "error";

/// Whether `expr` mentions a variable accepted by `is_cut`. `None` for an
/// expression shape this walk does not know (fail closed).
fn mentions_cut_var(expr: &ChcExpr, is_cut: &impl Fn(&str) -> bool) -> Option<bool> {
    let mut seen: HashSet<*const ChcExpr> = HashSet::new();
    let mut pending = vec![expr];
    while let Some(node) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(node)) {
            continue;
        }
        match node {
            ChcExpr::Var(var) => {
                if is_cut(&var.name) {
                    return Some(true);
                }
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => pending.extend(args.iter().map(|arg| arg.as_ref())),
            ChcExpr::ConstArray(_, value) => pending.push(value.as_ref()),
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
            _ => return None,
        }
    }
    Some(false)
}

/// Collect every variable name `expr` mentions into `names`. `None` for an
/// expression shape this walk does not know (fail closed).
fn collect_var_names(expr: &ChcExpr, names: &mut HashSet<String>) -> Option<()> {
    let mut seen: HashSet<*const ChcExpr> = HashSet::new();
    let mut pending = vec![expr];
    while let Some(node) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(node)) {
            continue;
        }
        match node {
            ChcExpr::Var(var) => {
                names.insert(var.name.clone());
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => pending.extend(args.iter().map(|arg| arg.as_ref())),
            ChcExpr::ConstArray(_, value) => pending.push(value.as_ref()),
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
            _ => return None,
        }
    }
    Some(())
}

/// The cut is only as good as `is_cut`'s view of the variables' spellings.
/// Refuse when the system never mentions a variable `is_cut` accepts (the cut
/// would remove nothing and the replay would confirm the original system), or
/// when it mentions a variable spelled like a cut variable that `is_cut` does
/// not accept (a renamed or derived spelling — the scalarizer's
/// `<array>_dead_const_lane_N`, or a future one — would be left in place and
/// read by the retained clauses). T1 review, 2026-09-24.
fn check_cut_spellings(
    parsed: &ChcProblem,
    cut_vars: &[&str],
    is_cut: &impl Fn(&str) -> bool,
) -> Result<(), String> {
    let mut names: HashSet<String> = HashSet::new();
    let unknown = || "unrecognized expression shape while listing variables".to_string();
    for clause in parsed.clauses() {
        for (_, args) in &clause.body.predicates {
            for arg in args {
                collect_var_names(arg, &mut names).ok_or_else(unknown)?;
            }
        }
        if let Some(constraint) = &clause.body.constraint {
            collect_var_names(constraint, &mut names).ok_or_else(unknown)?;
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for arg in args {
                collect_var_names(arg, &mut names).ok_or_else(unknown)?;
            }
        }
    }
    let mut unrecognized: Vec<&String> = names
        .iter()
        .filter(|name| !is_cut(name) && cut_vars.iter().any(|v| name.contains(*v)))
        .collect();
    if !unrecognized.is_empty() {
        unrecognized.sort();
        return Err(format!(
            "variables spelled like a cut variable are not recognized as one: {unrecognized:?}"
        ));
    }
    if !names.iter().any(|name| is_cut(name)) {
        return Err(format!(
            "the system never mentions {cut_vars:?}: the cut would remove nothing"
        ));
    }
    Ok(())
}

/// Build the cut system described in the module doc from `chc_text`.
pub(super) fn cut_problem(
    chc_text: &str,
    target: &str,
    cut_vars: &[&str],
) -> Result<ChcProblem, String> {
    if cut_vars.is_empty() {
        return Err("no variables to cut".to_string());
    }
    // A cut array's constant-index scalarized cells (`A_at_0x…`) are the same
    // freed value: tests/expected/test6/main.rs read the float table through
    // such a cell, and a name-only cut left that read in place.
    let is_cut = |name: &str| {
        let own = name.strip_suffix("__out").unwrap_or(name);
        let parent = trust_mc_core::chc::scalarized_cell_parent(name);
        cut_vars.iter().any(|v| *v == own || parent == Some(*v))
    };
    let parsed =
        ChcParser::parse(chc_text).map_err(|error| format!("CHC parse failed: {error}"))?;
    let target_id = parsed
        .lookup_predicate(target)
        .ok_or_else(|| format!("the system declares no relation `{target}`"))?;
    if parsed.get_predicate(target_id).is_none_or(|pred| !pred.arg_sorts.is_empty()) {
        return Err(format!("`{target}` is not a nullary error relation"));
    }
    check_cut_spellings(&parsed, cut_vars, &is_cut)?;

    // Positions a cut variable occupies, and positions something else occupies.
    let arity: Vec<usize> = parsed.predicates().iter().map(|p| p.arg_sorts.len()).collect();
    let mut cut_pos: Vec<Vec<bool>> = arity.iter().map(|n| vec![false; *n]).collect();
    let mut other_pos: Vec<Vec<bool>> = arity.iter().map(|n| vec![false; *n]).collect();
    let mut note_app = |pred: PredicateId, args: &[ChcExpr]| {
        for (i, arg) in args.iter().enumerate() {
            match arg {
                ChcExpr::Var(var) if is_cut(&var.name) => cut_pos[pred.index()][i] = true,
                _ => other_pos[pred.index()][i] = true,
            }
        }
    };
    for clause in parsed.clauses() {
        for (pred, args) in &clause.body.predicates {
            note_app(*pred, args);
        }
        if let ClauseHead::Predicate(pred, args) = &clause.head {
            note_app(*pred, args);
        }
    }
    let mut projected: Vec<Vec<bool>> = Vec::with_capacity(arity.len());
    for (pred, (cut, other)) in cut_pos.iter().zip(&other_pos).enumerate() {
        if cut.iter().zip(other).any(|(c, o)| *c && *o) {
            let name = parsed.predicates()[pred].name.as_str();
            return Err(format!(
                "relation `{name}` carries a cut variable and another value in one position"
            ));
        }
        projected.push(cut.clone());
    }

    let mut cut = ChcProblem::new();
    for (pred, decl) in parsed.predicates().iter().enumerate() {
        let sorts = decl
            .arg_sorts
            .iter()
            .zip(&projected[pred])
            .filter(|(_, dropped)| !**dropped)
            .map(|(sort, _)| sort.clone())
            .collect();
        let id = cut.declare_predicate(decl.name.clone(), sorts);
        if id.index() != pred {
            return Err("predicate ids moved while rebuilding the system".to_string());
        }
    }
    let project = |pred: PredicateId, args: &[ChcExpr]| -> Option<Vec<ChcExpr>> {
        let mut kept = Vec::with_capacity(args.len());
        for (arg, dropped) in args.iter().zip(&projected[pred.index()]) {
            if *dropped {
                continue;
            }
            // A cut variable inside a kept argument carries its value into a
            // slot: the clause reads it.
            if mentions_cut_var(arg, &is_cut)? {
                return None;
            }
            kept.push(arg.clone());
        }
        Some(kept)
    };

    let aggregate = parsed.lookup_predicate(AGGREGATE_ERROR);
    let mut kept_clauses = Vec::new();
    for clause in parsed.clauses() {
        let head = match &clause.head {
            ClauseHead::False => continue,
            ClauseHead::Predicate(pred, _) if Some(*pred) == aggregate => continue,
            ClauseHead::Predicate(pred, args) => match project(*pred, args) {
                Some(args) => ClauseHead::Predicate(*pred, args),
                None => continue,
            },
            _ => return Err("unrecognized clause head shape".to_string()),
        };
        if let Some(constraint) = &clause.body.constraint {
            match mentions_cut_var(constraint, &is_cut) {
                Some(false) => {}
                Some(true) => continue,
                None => return Err("unrecognized expression shape in a constraint".to_string()),
            }
        }
        let mut body = Vec::with_capacity(clause.body.predicates.len());
        let mut reads_cut = false;
        for (pred, args) in &clause.body.predicates {
            match project(*pred, args) {
                Some(args) => body.push((*pred, args)),
                None => {
                    reads_cut = true;
                    break;
                }
            }
        }
        if reads_cut {
            continue;
        }
        kept_clauses
            .push(HornClause::new(ClauseBody::new(body, clause.body.constraint.clone()), head));
    }

    // Keep only what can contribute to deriving `target`.
    let mut live: HashSet<PredicateId> = HashSet::from([target_id]);
    loop {
        let before = live.len();
        for clause in &kept_clauses {
            if let ClauseHead::Predicate(head, _) = &clause.head
                && live.contains(head)
            {
                live.extend(clause.body.predicates.iter().map(|(pred, _)| *pred));
            }
        }
        if live.len() == before {
            break;
        }
    }
    let mut count = 0usize;
    for clause in kept_clauses {
        if matches!(&clause.head, ClauseHead::Predicate(head, _) if live.contains(head)) {
            count += 1;
            if count > MAX_CUT_CLAUSES {
                return Err(format!("the cut system exceeds {MAX_CUT_CLAUSES} clauses"));
            }
            cut.add_clause(clause);
        }
    }
    cut.add_clause(HornClause::new(
        ClauseBody::new(vec![(target_id, Vec::new())], None),
        ClauseHead::False,
    ));
    Ok(cut)
}

/// Replay-validate that `target` (a nullary `error_pN`) is derivable in the
/// HORN system `chc_text` along a derivation that never reads `cut_vars`
/// (normalized state-variable names; the `__out` post-state spelling is the
/// same variable). See the module doc for the construction and why a replayed
/// derivation holds for every value of the cut variables.
///
/// `Ok` carries a one-line summary. Every other outcome — a refused cut, a
/// cyclic or oversized cut system, no derivation, an undecided search, a failed
/// replay — is `Err`, and the caller must keep the counterexample uncertified.
pub fn replay_error_derivation_free_of(
    chc_text: &str,
    target: &str,
    cut_vars: &[&str],
) -> Result<String, String> {
    let producer = cut_problem(chc_text, target, cut_vars)?;
    let witness = match acyclic_direct_smt_decision(&producer) {
        AcyclicDecision::Unsafe(witness) => witness,
        AcyclicDecision::Safe => {
            return Err(format!("`{target}` is not derivable without reading {cut_vars:?}"));
        }
        AcyclicDecision::Inconclusive => {
            return Err(format!("the cut system for `{target}` is cyclic, nonlinear or undecided"));
        }
    };
    let consumer = cut_problem(chc_text, target, cut_vars)?;
    replay_acyclic_direct_smt_witness(&consumer, &witness)?;
    let bindings = witness.model.as_object().map_or(0, serde_json::Map::len);
    Ok(format!(
        "`{target}` replayed on a fresh cut system without {cut_vars:?} \
         ({} clauses on the derivation, {bindings} bindings)",
        witness.derivation_clause_indices.len()
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The FastMath shape (kani/Intrinsics/FastMath/add_overflow_f32.rs, as
    /// emitted at 9e086301c): the operand-finiteness check reads only `x`; the
    /// sum is a table select on the transition out of the check's block.
    const OPERAND_CHECK: &str = r#"
(set-logic HORN)
(declare-var x (_ BitVec 32))
(declare-var y (_ BitVec 32))
(declare-var z (_ BitVec 32))
(declare-var z__out (_ BitVec 32))
(declare-var float_binop_tbl_f32 (Array (_ BitVec 72) (_ BitVec 32)))
(declare-rel bb0 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (Array (_ BitVec 72) (_ BitVec 32))))
(declare-rel bb1 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (Array (_ BitVec 72) (_ BitVec 32))))
(declare-rel error ())
(declare-rel error_p0 ())
(declare-rel error_p1 ())
(rule (=> true (bb0 x y z float_binop_tbl_f32)))
(rule (=> error_p0 error))
(rule (=> (and (bb0 x y z float_binop_tbl_f32) (= ((_ extract 30 23) x) #xff)) error_p0))
(rule (=> (and (bb0 x y z float_binop_tbl_f32) (= z__out (select float_binop_tbl_f32 (concat (concat #x00 x) y)))) (bb1 x y z__out float_binop_tbl_f32)))
(rule (=> error_p1 error))
(rule (=> (and (bb1 x y z float_binop_tbl_f32) (= ((_ extract 30 23) z) #xff)) error_p1))
(query error)
"#;

    #[test]
    fn a_check_that_never_reads_the_table_replays() {
        let summary =
            replay_error_derivation_free_of(OPERAND_CHECK, "error_p0", &["float_binop_tbl_f32"])
                .expect("the operand check is derivable without the table");
        assert!(summary.contains("error_p0"), "{summary}");
    }

    /// The result check reads `z`, which only a table select defines: removing
    /// that transition removes every derivation, so nothing is certified.
    #[test]
    fn a_check_on_a_table_value_does_not_replay() {
        let err =
            replay_error_derivation_free_of(OPERAND_CHECK, "error_p1", &["float_binop_tbl_f32"])
                .expect_err("the result check depends on the table");
        assert!(err.contains("not derivable"), "{err}");
    }

    /// A table select handed straight to a relation argument (no constraint
    /// names it) still counts as a read: the clause is removed.
    #[test]
    fn a_select_in_a_head_argument_is_a_read() {
        let smt = OPERAND_CHECK.replace(
            "(rule (=> (and (bb0 x y z float_binop_tbl_f32) (= z__out (select float_binop_tbl_f32 (concat (concat #x00 x) y)))) (bb1 x y z__out float_binop_tbl_f32)))",
            "(rule (=> (bb0 x y z float_binop_tbl_f32) (bb1 x y (select float_binop_tbl_f32 (concat (concat #x00 x) y)) float_binop_tbl_f32)))",
        );
        assert_ne!(smt, OPERAND_CHECK, "the fixture edit must apply");
        assert!(
            replay_error_derivation_free_of(&smt, "error_p1", &["float_binop_tbl_f32"]).is_err(),
            "a head-argument select must not be dropped as if unread"
        );
    }

    /// tests/expected/test6/main.rs as emitted: `add2(1, 1) == 2.0` reads the
    /// table at the constant key `1.0 + 1.0`, which scalarization turned into
    /// the cell `float_binop_tbl_f32_at_0x3f8000003f800000_bv72`. The check
    /// holds in Rust, so it must not replay without the table.
    #[test]
    fn a_scalarized_table_cell_is_a_read_of_the_table() {
        let smt = r#"
(set-logic HORN)
(declare-var r (_ BitVec 32))
(declare-var r__out (_ BitVec 32))
(declare-var float_binop_tbl_f32_at_0x3f8000003f800000_bv72 (_ BitVec 32))
(declare-rel bb0 ((_ BitVec 32) (_ BitVec 32)))
(declare-rel bb1 ((_ BitVec 32) (_ BitVec 32)))
(declare-rel error ())
(declare-rel error_p0 ())
(rule (=> true (bb0 r float_binop_tbl_f32_at_0x3f8000003f800000_bv72)))
(rule (=> (and (bb0 r float_binop_tbl_f32_at_0x3f8000003f800000_bv72) (= r__out float_binop_tbl_f32_at_0x3f8000003f800000_bv72)) (bb1 r__out float_binop_tbl_f32_at_0x3f8000003f800000_bv72)))
(rule (=> error_p0 error))
(rule (=> (and (bb1 r float_binop_tbl_f32_at_0x3f8000003f800000_bv72) (not (= r #x40000000))) error_p0))
(query error)
"#;
        // The parser substitutes `r__out` by the cell, so the cell also lands
        // in `bb1`'s value slot and the cut is refused outright; either way no
        // derivation of the check is replayed.
        assert!(
            replay_error_derivation_free_of(smt, "error_p0", &["float_binop_tbl_f32"]).is_err(),
            "the check reads the table through a scalarized cell"
        );
        // A cut of a variable the system never mentions removes nothing, so it
        // would replay the original system and confirm trivially: refused.
        let err = replay_error_derivation_free_of(smt, "error_p0", &["unrelated"])
            .expect_err("a cut that removes nothing must be refused");
        assert!(err.contains("never mentions"), "{err}");
    }

    /// A freed table read under a spelling `is_cut` does not map back to the
    /// table (the scalarizer's `<array>_dead_const_lane_N`) would be left in
    /// place by the cut: refused instead of replayed (T1 review, 2026-09-24).
    #[test]
    fn an_unrecognized_spelling_of_the_table_is_refused() {
        let smt = OPERAND_CHECK
            .replace(
                "(rule (=> (and (bb0 x y z float_binop_tbl_f32) (= ((_ extract 30 23) x) #xff)) error_p0))",
                "(rule (=> (and (bb0 x y z float_binop_tbl_f32) (= x float_binop_tbl_f32_dead_const_lane_0)) error_p0))",
            )
            .replace(
                "(declare-var float_binop_tbl_f32 ",
                "(declare-var float_binop_tbl_f32_dead_const_lane_0 (_ BitVec 32))\n(declare-var float_binop_tbl_f32 ",
            );
        assert_ne!(smt, OPERAND_CHECK, "the fixture edit must apply");
        let err = replay_error_derivation_free_of(&smt, "error_p0", &["float_binop_tbl_f32"])
            .expect_err("an unrecognized spelling of the table must be refused");
        assert!(err.contains("not recognized"), "{err}");
    }

    /// A relation slot that carries the table on one edge and an ordinary value
    /// on another cannot be dropped without freeing that value: refused.
    #[test]
    fn a_slot_shared_with_an_ordinary_value_is_refused() {
        let smt = OPERAND_CHECK.replace(
            "(rule (=> true (bb0 x y z float_binop_tbl_f32)))",
            "(declare-var other (Array (_ BitVec 72) (_ BitVec 32)))\n(rule (=> true (bb0 x y z other)))",
        );
        let err = cut_problem(&smt, "error_p0", &["float_binop_tbl_f32"])
            .expect_err("a mixed slot must be refused");
        assert!(err.contains("one position"), "{err}");
    }

    #[test]
    fn an_unknown_target_is_refused() {
        assert!(
            replay_error_derivation_free_of(OPERAND_CHECK, "error_p9", &["float_binop_tbl_f32"])
                .is_err()
        );
    }
}
