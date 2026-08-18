// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Sound reject/prune-only abstraction for the acyclic direct-SMT decision.
//!
//! Concrete SAT witnesses always come from the original body. This module is
//! consulted only after that body is undecided, and it can authorize only a
//! definitive UNSAT over a pure over-approximation.

use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;

use ay_chc::{ChcExpr, ChcOp, ChcSort, ChcVar};

/// Sound over-approximation of a flat constraint list for a *last-resort* UNSAT
/// retry (see [`super::solve_constraints`]). Every MAXIMAL integer-sorted subterm that is
/// "wide" — its subtree carries an integer literal beyond `i64::MAX` in magnitude
/// (the base-`1e9` Horner encoding of a `>i128`/`u128` constant that chokes the
/// LIA/NIA core), OR it is headed by a nonlinear `Mul`/`Div`/`Mod` with a
/// non-literal operand — is replaced by a FRESH, otherwise-unconstrained `Int`
/// variable. The boolean / comparison skeleton (`And`/`Or`/`Not`/`Ite`/`Eq`/`Le`/
/// `Lt`/…) is rebuilt verbatim, so a trivial *linear* contradiction (e.g.
/// `_0 = lo ∧ lo ≤ hi ∧ ¬(lo ≤ _0 ≤ hi)`) survives while the irrelevant
/// wide/nonlinear noise is havoced away.
///
/// SOUNDNESS — this is a pure over-approximation. Replacing a deterministic
/// subterm `t` by a fresh variable `f` can only ADD models: for any model `m` of
/// the concrete body, `m ∪ {f := eval(t, m)}` models the abstract body, so
/// `models(concrete) ⊆ models(abstract)`, hence `UNSAT(abstract) ⟹
/// UNSAT(concrete)`. A definitive abstract-UNSAT is therefore a genuine proof the
/// concrete body is unsatisfiable. The freshness of `f` is load-bearing: the
/// generated names are checked against every variable that actually occurs in the
/// input (`existing`), because reusing an already-constrained program variable
/// would NOT be an over-approximation and could manufacture a spurious UNSAT (a
/// false proof). The abstract model is meaningless for the concrete body and, per
/// the caller's contract, is never read.
pub(super) fn abstract_wide_nonlinear(constraints: &[ChcExpr]) -> Vec<ChcExpr> {
    let mut existing: HashSet<String> = HashSet::new();
    let mut census_complete = true;
    for c in constraints {
        census_complete &= collect_var_names(c, &mut existing);
    }
    if !census_complete {
        // `ChcExpr` is `#[non_exhaustive]`: a variant we do not model could hide a
        // `Var` from the census above, so we cannot certify the minted
        // `__abs_wide_N` names are collision-free. Refuse to abstract — the caller
        // then keeps its fail-closed `Undecided`. (No abstraction ⟹ no promotion.)
        return constraints.to_vec();
    }
    let mut counter: usize = 0;
    let mut memo: BTreeMap<ChcExpr, ChcExpr> = BTreeMap::new();
    // LCG Fix 2 (2026-08-06): word-level lemmas attached to fresh replacements (see
    // `emit_wide_replacement_lemmas`). Each lemma is TRUE of the replaced concrete
    // term for EVERY model, so `models(concrete) ⊆ models(abstract)` is preserved:
    // the abstraction stays a pure over-approximation and a definitive abstract-UNSAT
    // still proves the concrete body unsatisfiable. Appended AFTER the rewritten
    // skeleton (order is irrelevant under `and_all`). ONLY the max/min shape is
    // lemma'd; the `Mod` bound is DELIBERATELY omitted (symbolic-divisor `mod` is
    // uninterpreted in ay, so a bound would remove concrete models — a false proof).
    let mut lemmas: Vec<ChcExpr> = Vec::new();
    let mut out: Vec<ChcExpr> = constraints
        .iter()
        .map(|c| abstract_expr(c, &existing, &mut counter, &mut memo, &mut lemmas))
        .collect();
    out.extend(lemmas);
    out
}

/// Gather every variable name occurring in `e` into `out`, returning `true` iff
/// every subexpression was a variant this walker explicitly models. A `false`
/// result means a variable may be hidden in an unmodeled variant, so the
/// collision census is INCOMPLETE and the caller must not mint fresh names
/// against it (see the soundness note on [`abstract_wide_nonlinear`]).
fn collect_var_names(e: &ChcExpr, out: &mut HashSet<String>) -> bool {
    match e {
        // Leaves that carry no variable.
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => true,
        ChcExpr::Var(v) => {
            out.insert(v.name.clone());
            true
        }
        ChcExpr::Op(_, args) | ChcExpr::FuncApp(_, _, args) | ChcExpr::PredicateApp(_, _, args) => {
            let mut complete = true;
            for a in args {
                complete &= collect_var_names(a, out);
            }
            complete
        }
        ChcExpr::ConstArray(_, inner) => collect_var_names(inner, out),
        // Unknown future variant — fail closed.
        _ => false,
    }
}

/// Recursively rewrite `e`, replacing each maximal wide integer subterm
/// ([`is_wide_int_term`]) with a fresh `Int` variable (memoized by structural
/// identity so equal subterms map to the same variable, which preserves any
/// linear relation that happens to run *through* the havoced term). Non-wide
/// structure is rebuilt verbatim.
fn abstract_expr(
    e: &ChcExpr,
    existing: &HashSet<String>,
    counter: &mut usize,
    memo: &mut BTreeMap<ChcExpr, ChcExpr>,
    lemmas: &mut Vec<ChcExpr>,
) -> ChcExpr {
    if is_wide_int_term(e) {
        if let Some(v) = memo.get(e) {
            return v.clone();
        }
        // Mint a name guaranteed disjoint from every program variable AND from
        // every name minted so far (the counter is monotonic and we skip
        // collisions), so the replacement is genuinely unconstrained.
        let name = loop {
            let candidate = format!("__abs_wide_{}", *counter);
            *counter += 1;
            if !existing.contains(&candidate) {
                break candidate;
            }
        };
        let fresh = ChcExpr::var(ChcVar::new(name, ChcSort::Int));
        memo.insert(e.clone(), fresh.clone());
        // Attach SOUND word-level lemmas relating `fresh` to the abstractions of
        // `e`'s operands. Emitted exactly once per distinct `fresh` (this arm is
        // reached only on a memo MISS), so equal wide subterms share one var and
        // one lemma set.
        emit_wide_replacement_lemmas(e, &fresh, existing, counter, memo, lemmas);
        return fresh;
    }
    match e {
        ChcExpr::Op(op, args) => ChcExpr::Op(
            *op,
            args.iter()
                .map(|a| Arc::new(abstract_expr(a, existing, counter, memo, lemmas)))
                .collect(),
        ),
        ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
            name.clone(),
            sort.clone(),
            args.iter()
                .map(|a| Arc::new(abstract_expr(a, existing, counter, memo, lemmas)))
                .collect(),
        ),
        ChcExpr::PredicateApp(name, id, args) => ChcExpr::PredicateApp(
            name.clone(),
            *id,
            args.iter()
                .map(|a| Arc::new(abstract_expr(a, existing, counter, memo, lemmas)))
                .collect(),
        ),
        ChcExpr::ConstArray(sort, inner) => ChcExpr::ConstArray(
            sort.clone(),
            Arc::new(abstract_expr(inner, existing, counter, memo, lemmas)),
        ),
        // Leaves and internal markers are copied unchanged.
        _ => e.clone(),
    }
}

/// Attach SOUND word-level lemmas to the fresh var `fresh` that replaced a maximal
/// wide integer term `e`, keyed on `e`'s head. Lemmas reference the ABSTRACTIONS of
/// `e`'s operands (recursively abstracted here, since `e` itself is replaced) and
/// are pushed onto `lemmas`; the caller folds them into the abstract body.
///
/// SOUNDNESS — every lemma is TRUE of the concrete term for EVERY model, so
/// `models(concrete) ⊆ models(abstract)` is preserved and a definitive
/// abstract-UNSAT still proves the concrete body unsatisfiable. Only shapes whose
/// truth follows from the CORE, interpretation-independent semantics of
/// `ite`/`≥`/`≤` are handled:
///   * max — `ite(a ≥ b, a, b)` ⟹ `fresh ≥ a ∧ fresh ≥ b`
///   * min — `ite(a ≤ b, a, b)` ⟹ `fresh ≤ a ∧ fresh ≤ b`
/// The `ite` condition operands must be STRUCTURALLY the two branches, in order,
/// which pins `fresh`'s value to `max`/`min(a, b)`. Any other shape is left
/// un-lemma'd (fail-closed).
///
/// `Mod`/`Div`/`Mul` are DELIBERATELY not lemma'd: a symbolic-divisor `(mod a b)`
/// is left UNINTERPRETED in ay (Euclidean bounds are axiomatized only for a literal
/// divisor `k`), so asserting `0 ≤ f < b` would REMOVE concrete models — a false
/// proof — on exactly the LCG target (`raw % (width+1).max(1)`).
fn emit_wide_replacement_lemmas(
    e: &ChcExpr,
    fresh: &ChcExpr,
    existing: &HashSet<String>,
    counter: &mut usize,
    memo: &mut BTreeMap<ChcExpr, ChcExpr>,
    lemmas: &mut Vec<ChcExpr>,
) {
    // max/min lower to `ite(cmp(a, b), a, b)` (no dedicated ChcOp). Match that exact
    // shape and require the comparison operands to be the two branches in order.
    if let ChcExpr::Op(ChcOp::Ite, args) = e {
        if args.len() != 3 {
            return;
        }
        let then_ = args[1].as_ref();
        let else_ = args[2].as_ref();
        if let ChcExpr::Op(cmp, cargs) = args[0].as_ref() {
            if cargs.len() != 2 || cargs[0].as_ref() != then_ || cargs[1].as_ref() != else_ {
                return;
            }
            let is_max = matches!(cmp, ChcOp::Ge);
            let is_min = matches!(cmp, ChcOp::Le);
            if !is_max && !is_min {
                return;
            }
            // Abstract the branches — they may themselves be wide; the shared
            // counter/memo keep fresh names collision-free and emit any nested
            // max/min lemma here too.
            let a_abs = abstract_expr(then_, existing, counter, memo, lemmas);
            let b_abs = abstract_expr(else_, existing, counter, memo, lemmas);
            if is_max {
                // e == max(a, b): fresh ≥ a ∧ fresh ≥ b.
                lemmas.push(ChcExpr::ge(fresh.clone(), a_abs));
                lemmas.push(ChcExpr::ge(fresh.clone(), b_abs));
            } else {
                // e == min(a, b): fresh ≤ a ∧ fresh ≤ b.
                lemmas.push(ChcExpr::le(fresh.clone(), a_abs));
                lemmas.push(ChcExpr::le(fresh.clone(), b_abs));
            }
        }
    }
}

/// True iff `e` is an INTEGER-sorted term that is "wide": its subtree carries an
/// integer literal with magnitude beyond `i64::MAX`, OR it is headed by a
/// nonlinear `Mul`/`Div`/`Mod` (an arithmetic product/quotient/remainder with a
/// non-literal operand). Only integer-sorted terms qualify, so the boolean /
/// comparison skeleton is never replaced (a type error and a structure loss).
/// Bitvector operations are a separate, tractable theory and are left intact.
fn is_wide_int_term(e: &ChcExpr) -> bool {
    is_int_sorted(e) && subtree_is_wide(e)
}

/// Conservative integer-sort check. Returns `true` only for terms the fresh `Int`
/// replacement can stand in for; anything uncertain returns `false` (fail-closed:
/// the term is then left untouched, never mis-replaced by an `Int` variable).
///
/// SOUNDNESS-CRITICAL: `Add`/`Sub`/`Mul`/`Div`/`Mod`/`Neg` are POLYMORPHIC over
/// `Int` and `Real` in ay (`ChcExpr::sort()` returns the operand's sort for these
/// ops), so their result sort is NOT constant. A term is treated as integer-sorted
/// only when EVERY operand is (recursively) integer-sorted — this refuses any
/// term that is real-valued (or mixed/coerced-to-real). Standing a `ℤ`-domain
/// fresh variable in for a real-valued subterm would be a strict UNDER-set of its
/// range, not an over-approximation, and could manufacture a spurious UNSAT (a
/// false proof) via ay's `to_real` integrality reasoning. Requiring all operands
/// integer is stricter than `e.sort() == Int` on purpose: `sort()` reports only
/// the FIRST operand's sort, so it would wrongly accept `Add(int, real)`.
fn is_int_sorted(e: &ChcExpr) -> bool {
    match e {
        ChcExpr::Int(_) => true,
        ChcExpr::Var(v) => v.sort == ChcSort::Int,
        ChcExpr::FuncApp(_, sort, _) => *sort == ChcSort::Int,
        ChcExpr::Op(op, args) => match op {
            ChcOp::Add | ChcOp::Sub | ChcOp::Mul | ChcOp::Div | ChcOp::Mod => {
                !args.is_empty() && args.iter().all(|a| is_int_sorted(a))
            }
            ChcOp::Neg => args.first().is_some_and(|a| is_int_sorted(a)),
            // An `Ite` is integer-sorted only when BOTH branches are.
            ChcOp::Ite => {
                args.get(1).is_some_and(|a| is_int_sorted(a))
                    && args.get(2).is_some_and(|a| is_int_sorted(a))
            }
            _ => false,
        },
        _ => false,
    }
}

/// True iff `e`'s subtree carries an integer literal beyond `i64::MAX` in
/// magnitude, or a nonlinear `Mul`/`Div`/`Mod` (one whose operand is not a plain
/// integer literal). This is the "hard for LIA/NIA" predicate the abstraction
/// targets.
fn subtree_is_wide(e: &ChcExpr) -> bool {
    match e {
        ChcExpr::Int(v) => v.unsigned_abs() > i64::MAX as u128,
        ChcExpr::Op(op, args) => {
            let nonlinear = matches!(op, ChcOp::Mul | ChcOp::Div | ChcOp::Mod)
                && args.iter().any(|a| !matches!(a.as_ref(), ChcExpr::Int(_)));
            nonlinear || args.iter().any(|a| subtree_is_wide(a))
        }
        ChcExpr::FuncApp(_, _, args) | ChcExpr::PredicateApp(_, _, args) => {
            args.iter().any(|a| subtree_is_wide(a))
        }
        ChcExpr::ConstArray(_, inner) => subtree_is_wide(inner),
        _ => false,
    }
}

#[cfg(test)]
mod tests;
