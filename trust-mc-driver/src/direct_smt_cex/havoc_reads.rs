// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Reads of values no clause defines: the certification side of a CHC
//! counterexample.
//!
//! A `[AY:CTREX_CAT:Genuine]` counterexample says the program really fails.
//! The category used to rest on one fact: the compiler booked no approximation
//! for the harness. Two encoding defects free a value WITHOUT booking anything,
//! and both certified counterexamples on programs Kani proves
//! (fix/chc-false-certificates):
//!
//! - **An unbound read.** A clause's constraint (or a compound argument of its
//!   head) names a state variable its body predicates do not bind. In a Horn
//!   clause every variable is universally quantified per clause, so that read
//!   is ANY value. The liveness pruning of relation arguments dropped the
//!   variable from the body relation while the clause still reads it:
//!   `review_r13_closure.rs::closure_capture_refjoin_safe` read `mem_u8` in its
//!   `error_p4` clause from a relation that no longer carried it.
//! - **A read of memory no clause writes.** A typed memory array (or one of its
//!   scalarized cells) that no clause ever writes holds its entry value, which
//!   is unconstrained. Every byte a Rust program reads was written first, so a
//!   read of such memory is a store the encoder lost: `review_r01_const_ref_join.rs`
//!   read two promoted constants through a joined reference from `mem_Color`,
//!   which nothing initialized; `review_r17_aggregate_field_join.rs` read the
//!   payload of `Some(&m)` from the cell at address 0.
//!
//! Neither read is a sound approximation the proof side needs to know about —
//! a free value only ADDS behaviours, so an UNSAT answer still holds — but a
//! counterexample that uses one is not evidence of a real failure.
//! [`certify_error_free_of_havoc`] answers the counterexample question: some
//! violated `error_pN` must be derivable without any such read. It is when no
//! clause in the check's backward cone depends on a freed value
//! ([`super::havoc_taint`]), or when the cut system without the dependent
//! clauses still derives the check with a replayed witness. Anything else is a
//! refusal, and the caller must not report `Genuine`.
//!
//! The unwritten rule is deliberately narrow. Entry-state freedom is also how
//! the encoder models a MAY-uninitialized local, and such a local or an
//! allocation-size cell read on some path is common in counterexamples that
//! ARE real (measured on the soundness-dual suite, 2026-09-26). Only state
//! that no clause writes AT ALL — typed memory, or a MIR local's slot — is a
//! lost write by construction: Rust reads no local it never assigned.
//!
//! Review follow-up (2026-09-27):
//!
//! - a freed read does not refuse a check it cannot reach: the violated check
//!   must DEPEND on it (`super::havoc_taint`), so an independent bug downstream
//!   of an unrelated freed read keeps `Genuine`;
//! - a read of unwritten state counts in either spelling (`X__out` is `X`);
//! - a slot the encoder pins by an equality (a scalarized constant cell, a
//!   cell register) is defined, not unwritten.
//!
//! **Post-state reads.** An unbound read also covers the POST-state spelling
//! `X__out` of a state variable that the clause neither binds, nor defines
//! (`(= X__out e)` from defined values), nor carries into its head, unless a
//! sibling transition of the same block makes `X__out` a nondeterministic
//! update (`kani::any_where` checks its predicate on the fresh value that
//! way). In an ERROR clause (a nullary head) this rule holds in every mode:
//! nothing after the check can use a value it defines, and the error clause of
//! `sgn_read_b_safe` read `_2_fld1__out` from nothing (review finding 2). In a
//! transition it is a strict-mode rule (below).
//!
//! **Strict mode.** For a `#[kani::should_panic]` harness a `Genuine`
//! counterexample is the PROOF (`harness_runner`, V6), so a false certificate
//! is a false pass: `sp_union_sgn_b`, `sp_union_two` and `sp_union_words_nd`
//! (review probes) were SUCCESSFUL where Kani fails. The strict mode adds two
//! rules there:
//!
//! - the post-state rule above in every clause, transitions included;
//! - a MIR local's slot that no clause ever writes is unwritten state, like
//!   memory (`two_read_safe` read `_2_fld1` carried from entry).
//!
//! Both rules also fire on values the encoder leaves free BY DESIGN: the
//! payload fields of a flattened enum's inactive variant are never written and
//! are copied with the enum by a TRANSITION (joined_enum_constant_payloads.rs,
//! `res_err_ordering_join_must_fail`), and the SMT text cannot tell that
//! freedom from a lost write. On an ordinary harness a false certificate only
//! mislabels a FAILED verdict, while a refused real bug loses its parity, so
//! the rules are confined to the harnesses whose verdict they decide
//! (measured on the soundness-dual Genuine rows, 2026-09-27).

use std::collections::{BTreeSet, HashMap, HashSet};

use ay_chc::{ChcExpr, ChcParser, ChcProblem, ClauseHead, PredicateId};

use super::havoc_taint::{
    FreedReads, Independence, Strategy, Tautologies, analyze, backward_cone,
    replay_error_derivation_tainted, top_level_conjuncts,
};

/// What [`scan_havoc_reads`] found in one CHC system.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(super) struct HavocReads {
    /// Clauses (indices into [`ChcProblem::clauses`]) whose constraint, or a
    /// compound head argument, reads a state variable their body predicates do
    /// not bind, with those variables.
    pub unbound: Vec<(usize, Vec<String>)>,
    /// Clauses reading a memory or MIR-local state variable no clause writes,
    /// with those variables.
    pub unwritten: Vec<(usize, Vec<String>)>,
}

impl HavocReads {
    /// Whether the system reads no undefined value at all.
    pub(super) fn is_empty(&self) -> bool {
        self.unbound.is_empty() && self.unwritten.is_empty()
    }
}

/// How a counterexample was certified free of undefined reads.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HavocCertificate {
    /// The system reads no undefined value.
    Clean,
    /// Undefined values reach the violated check's cone only through
    /// definitions and carried slots: no derivation depends on them.
    Independent(String),
    /// The violated check replayed on the system without every clause that
    /// depends on an undefined value.
    Replayed(String),
}

/// Every variable name `expr` mentions, or `None` for an expression shape this
/// walk does not know (the caller fails closed).
fn var_names(expr: &ChcExpr, names: &mut HashSet<String>) -> Option<()> {
    let mut pending = vec![expr];
    while let Some(node) = pending.pop() {
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

/// Whether `name` (either state spelling) names encoder MEMORY: the flat byte
/// array `mem`, a typed memory array `_<fn>_mem_<type>`, or a constant-index
/// scalarized cell of one (`<array>_at_0x…`). A MIR local's state variable
/// (`_<fn>_<index>` with `_fld<k>` / cell suffixes) is never memory, even when
/// the function's own name contains `_mem_`.
pub(super) fn is_memory_state_var(name: &str) -> bool {
    let own = trust_mc_core::chc::normalize_approx_var(name);
    let array = trust_mc_core::chc::scalarized_cell_parent(own).unwrap_or(own);
    if array == "mem" {
        return true;
    }
    if !array.starts_with('_') || ends_with_local_suffix(array) {
        return false;
    }
    array.rfind("_mem_").is_some_and(|pos| pos > 0 && pos + "_mem_".len() < array.len())
}

/// Whether `name` (either state spelling, or a scalarized cell of one) names a
/// MIR local's state variable `_<fn>_<index>` (with `_fld<k>` suffixes), and
/// not memory.
pub(super) fn is_local_state_var(name: &str) -> bool {
    let own = trust_mc_core::chc::normalize_approx_var(name);
    let own = trust_mc_core::chc::scalarized_cell_parent(own).unwrap_or(own);
    own.starts_with('_') && ends_with_local_suffix(own) && !is_memory_state_var(own)
}

/// Whether `name` ends like a MIR local's state variable: `_3`, `_3_fld0`,
/// `_12_fld1_fld2`.
fn ends_with_local_suffix(name: &str) -> bool {
    let mut parts: Vec<&str> = name.rsplit('_').collect();
    // `rsplit` yields the tail first: strip `fld<k>` parts, then one index.
    while parts.first().is_some_and(|part| {
        part.strip_prefix("fld")
            .is_some_and(|k| !k.is_empty() && k.bytes().all(|b| b.is_ascii_digit()))
    }) {
        parts.remove(0);
    }
    parts.first().is_some_and(|part| !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()))
        && parts.len() > 1
}

/// The variables a clause READS: its constraint and every head argument that
/// is not a bare variable (a bare variable in a head slot is carried, not
/// read). With `copies`, also every bare variable a head slot receives under
/// another slot's name: the parser folds `(= v__out m)` into the head, so a
/// copy of undefined memory into a local only shows up as that bare argument
/// (`wide_pointer_carriers.rs::slice_behind_dyn_safe` copied the never-written
/// cell `mem_u8_at_0x3` into the local its check read). The copies count for
/// the memory rule only: a local re-entering a relation under a shifted slot
/// is ordinary. `None` for an unknown expression shape.
fn clause_reads(
    problem: &ChcProblem,
    index: usize,
    canon: &HashMap<(PredicateId, usize), String>,
    copies: bool,
) -> Option<HashSet<String>> {
    let clause = &problem.clauses()[index];
    let mut reads = HashSet::new();
    if let Some(constraint) = &clause.body.constraint {
        var_names(constraint, &mut reads)?;
    }
    if let ClauseHead::Predicate(pred, args) = &clause.head {
        for (i, arg) in args.iter().enumerate() {
            match arg {
                ChcExpr::Var(var) => {
                    if copies && canon.get(&(*pred, i)).is_some_and(|name| *name != var.name) {
                        reads.insert(var.name.clone());
                    }
                }
                _ => var_names(arg, &mut reads)?,
            }
        }
    }
    Some(reads)
}

/// Scan `problem` for the two kinds of undefined read described in the module
/// documentation. `strict` adds the two rules that decide a `should_panic`
/// harness (module documentation). `Err` for an expression shape the scan does
/// not know.
pub(super) fn scan_havoc_reads(problem: &ChcProblem, strict: bool) -> Result<HavocReads, String> {
    let unknown = || "unrecognized expression shape while scanning reads".to_string();
    let clauses = problem.clauses();

    // State variables: every name a body predicate carries in a slot. The
    // canonical name of a slot is the first variable seen in it.
    let mut state: HashSet<String> = HashSet::new();
    let mut canon: HashMap<(PredicateId, usize), String> = HashMap::new();
    for clause in clauses {
        for (pred, args) in &clause.body.predicates {
            for (i, arg) in args.iter().enumerate() {
                if let ChcExpr::Var(var) = arg {
                    state.insert(var.name.clone());
                    canon.entry((*pred, i)).or_insert_with(|| var.name.clone());
                }
            }
        }
    }

    // A read is of STATE when it is a state variable's spelling. The POST-state
    // spelling `X__out` of one counts in the strict mode everywhere, and in
    // every mode in a clause that derives an error relation: nothing after an
    // error clause can use a value it defines, so an `X__out` it reads is
    // either defined there, a nondeterministic update of its block (below), or
    // free — the `sgn_read_b_safe` false certificate read `_2_fld1__out` in
    // its error clause from nothing (review finding 2).
    let is_plain_state = |name: &str| state.contains(name);
    let is_post_state = |name: &str| {
        name.ends_with("__out") && state.contains(trust_mc_core::chc::normalize_approx_var(name))
    };
    let post_rule = |index: usize| {
        strict
            || match &clauses[index].head {
                ClauseHead::False => true,
                ClauseHead::Predicate(_, args) => args.is_empty(),
                _ => false,
            }
    };

    let mut result = HavocReads::default();

    // Per clause: what it defines without the bare-head rule — once with the
    // post-state spellings as state and once with them as fresh names — and
    // the spellings it carries bare into its head.
    struct Digest {
        defined_post: HashSet<String>,
        defined_plain: HashSet<String>,
        bare_head: HashSet<String>,
    }
    let close_definitions = |clause: &ay_chc::HornClause,
                             defined: &mut HashSet<String>|
     -> Result<(), String> {
        if let Some(constraint) = &clause.body.constraint {
            let conjuncts = top_level_conjuncts(constraint);
            loop {
                let before = defined.len();
                for conjunct in &conjuncts {
                    let ChcExpr::Op(ay_chc::ChcOp::Eq, args) = conjunct else { continue };
                    let [lhs, rhs] = args.as_slice() else { continue };
                    for (side, other) in [(lhs, rhs), (rhs, lhs)] {
                        if let ChcExpr::Var(var) = side.as_ref()
                            && !defined.contains(&var.name)
                        {
                            let mut names = HashSet::new();
                            var_names(other, &mut names).ok_or_else(unknown)?;
                            if names.iter().all(|name| defined.contains(name)) {
                                defined.insert(var.name.clone());
                            }
                        }
                    }
                }
                if defined.len() == before {
                    break;
                }
            }
        }
        Ok(())
    };
    let mut digests: Vec<Option<Digest>> = Vec::with_capacity(clauses.len());
    for clause in clauses {
        if clause.body.predicates.is_empty() {
            digests.push(None);
            continue;
        }
        // Defined here: every variable a body predicate binds, every variable
        // that is not a state spelling (a fresh value the encoder declares on
        // purpose), and, to a fixpoint, the variable of a definition `(= v e)`
        // whose right side is defined.
        let mut bound = HashSet::new();
        for (_, args) in &clause.body.predicates {
            for arg in args {
                var_names(arg, &mut bound).ok_or_else(unknown)?;
            }
        }
        let mut all = HashSet::new();
        if let Some(constraint) = &clause.body.constraint {
            var_names(constraint, &mut all).ok_or_else(unknown)?;
        }
        let mut bare_head = HashSet::new();
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for arg in args {
                match arg {
                    ChcExpr::Var(var) => {
                        bare_head.insert(var.name.clone());
                    }
                    _ => var_names(arg, &mut all).ok_or_else(unknown)?,
                }
            }
        }
        let mut defined_post = bound.clone();
        defined_post.extend(
            all.iter().filter(|name| !is_plain_state(name) && !is_post_state(name)).cloned(),
        );
        close_definitions(clause, &mut defined_post)?;
        let mut defined_plain = bound;
        defined_plain.extend(all.iter().filter(|name| !is_plain_state(name)).cloned());
        close_definitions(clause, &mut defined_plain)?;
        digests.push(Some(Digest { defined_post, defined_plain, bare_head }));
    }
    // A post-state spelling a transition carries bare into its head, and does
    // not define, is a NONDETERMINISTIC update of its block (`kani::any`,
    // `kani::any_where`): a sibling clause of the same block (same body
    // relations) may read that fresh value, as `any_where` checks its
    // predicate on it (walker_value_only_closure_dual.rs::bug_any_where_unchecked).
    let signature = |index: usize| -> Vec<PredicateId> {
        let mut sig: Vec<PredicateId> =
            clauses[index].body.predicates.iter().map(|(pred, _)| *pred).collect();
        sig.sort_by_key(|pred| pred.index());
        sig
    };
    let mut nondet_by_block: HashMap<Vec<PredicateId>, HashSet<String>> = HashMap::new();
    for (index, digest) in digests.iter().enumerate() {
        let Some(digest) = digest else { continue };
        let fresh = digest
            .bare_head
            .iter()
            .filter(|name| is_post_state(name) && !digest.defined_post.contains(*name));
        nondet_by_block.entry(signature(index)).or_default().extend(fresh.cloned());
    }

    let mut reads_by_clause: Vec<Option<HashSet<String>>> = Vec::with_capacity(clauses.len());
    for (index, digest) in digests.iter().enumerate() {
        let Some(digest) = digest else {
            reads_by_clause.push(None);
            continue;
        };
        let post = post_rule(index);
        let defined = if post { &digest.defined_post } else { &digest.defined_plain };
        let reads = clause_reads(problem, index, &canon, false).ok_or_else(unknown)?;
        let nondet = nondet_by_block.get(&signature(index));
        let mut free: Vec<String> = reads
            .iter()
            .filter(|v| {
                (is_plain_state(v) || (post && is_post_state(v)))
                    && !defined.contains(*v)
                    && !digest.bare_head.contains(*v)
                    && !nondet.is_some_and(|fresh| fresh.contains(*v))
            })
            .cloned()
            .collect();
        if !free.is_empty() {
            free.sort();
            result.unbound.push((index, free));
        }
        reads_by_clause.push(Some(clause_reads(problem, index, &canon, true).ok_or_else(unknown)?));
    }

    // Written slots. At entry a slot holds a defined value only when the entry
    // constraint pins it from already-defined values (a conjunct whose other
    // variables are all defined); elsewhere any argument other than the slot's
    // own name carried through is a write.
    let mut written: HashSet<(PredicateId, usize)> = HashSet::new();
    for clause in clauses {
        let ClauseHead::Predicate(pred, args) = &clause.head else { continue };
        if clause.body.predicates.is_empty() {
            let mut defined: HashSet<String> = HashSet::new();
            let conjuncts: Vec<HashSet<String>> = match &clause.body.constraint {
                Some(constraint) => {
                    let mut out = Vec::new();
                    for conjunct in top_level_conjuncts(constraint) {
                        let mut names = HashSet::new();
                        var_names(conjunct, &mut names).ok_or_else(unknown)?;
                        out.push(names);
                    }
                    out
                }
                None => Vec::new(),
            };
            loop {
                let before = defined.len();
                for names in &conjuncts {
                    let rest: Vec<&String> =
                        names.iter().filter(|n| !defined.contains(*n)).collect();
                    if let [only] = rest.as_slice() {
                        defined.insert((*only).clone());
                    }
                }
                if defined.len() == before {
                    break;
                }
            }
            for (i, arg) in args.iter().enumerate() {
                match arg {
                    ChcExpr::Var(var) if !defined.contains(&var.name) => {}
                    _ => {
                        written.insert((*pred, i));
                    }
                }
            }
            continue;
        }
        for (i, arg) in args.iter().enumerate() {
            let carried = matches!(
                (arg, canon.get(&(*pred, i))),
                (ChcExpr::Var(var), Some(name)) if &var.name == name
            );
            if !carried {
                written.insert((*pred, i));
            }
        }
    }
    let mut unwritten: HashSet<&String> = HashSet::new();
    let mut written_names: HashSet<&String> = HashSet::new();
    for (slot, name) in &canon {
        if written.contains(slot) {
            written_names.insert(name);
        } else if is_memory_state_var(name) || (strict && is_local_state_var(name)) {
            unwritten.insert(name);
        }
    }
    unwritten.retain(|name| !written_names.contains(*name));
    // A slot the encoder PINS to one constant (a scalarized cell of a constant
    // array, a cell register asserted equal to its initial value in every
    // transition) is defined even though no head writes it. Pinned means:
    // every constraint conjunct that mentions the slot (either spelling) is
    // that same equality with a constant, or a carry `(= X__out X)`. An
    // `assert!(x == 1)` on an unwritten cell also puts `(= x 1)` on its
    // passing branch, but its error branch reads `(not (= x 1))`, so it is
    // not a pin (review probe g3_written_later.rs).
    let own = |name: &str| trust_mc_core::chc::normalize_approx_var(name).to_string();
    let unwritten_own: HashSet<String> = unwritten.iter().map(|name| own(name)).collect();
    let mut pin_value: HashMap<String, Option<String>> = HashMap::new();
    for clause in clauses {
        let Some(constraint) = &clause.body.constraint else { continue };
        for conjunct in top_level_conjuncts(constraint) {
            let mut names = HashSet::new();
            var_names(conjunct, &mut names).ok_or_else(unknown)?;
            let mentioned: HashSet<String> = names
                .iter()
                .map(|name| own(name))
                .filter(|name| unwritten_own.contains(name))
                .collect();
            if mentioned.is_empty() {
                continue;
            }
            // `Some(Some(value))`: a pin to `value`; `Some(None)`: a carry.
            let shape = match conjunct {
                ChcExpr::Op(ay_chc::ChcOp::Eq, args) if mentioned.len() == 1 => {
                    match args.as_slice() {
                        [a, b] => match (a.as_ref(), b.as_ref()) {
                            (ChcExpr::Var(x), ChcExpr::Var(y)) if own(&x.name) == own(&y.name) => {
                                Some(None)
                            }
                            (ChcExpr::Var(_), value) | (value, ChcExpr::Var(_)) => {
                                let mut value_names = HashSet::new();
                                var_names(value, &mut value_names).ok_or_else(unknown)?;
                                value_names.is_empty().then(|| Some(format!("{value:?}")))
                            }
                            _ => None,
                        },
                        _ => None,
                    }
                }
                _ => None,
            };
            for name in mentioned {
                let entry = pin_value.entry(name.clone()).or_insert(Some(String::new()));
                match (&shape, entry.as_ref()) {
                    (Some(None), _) | (_, None) => {}
                    (Some(Some(value)), Some(seen)) if seen.is_empty() || seen == value => {
                        *entry = Some(value.clone());
                    }
                    _ => *entry = None,
                }
            }
        }
    }
    let pinned: HashSet<String> = pin_value
        .into_iter()
        .filter_map(|(name, value)| value.filter(|value| !value.is_empty()).map(|_| name))
        .collect();
    let unwritten_own: HashSet<String> =
        unwritten_own.into_iter().filter(|name| !pinned.contains(name)).collect();
    if !unwritten_own.is_empty() {
        for (index, reads) in reads_by_clause.iter().enumerate() {
            let Some(reads) = reads else { continue };
            // Either spelling: a read of `X__out` is a read of `X`.
            let mut hit: Vec<String> =
                reads.iter().filter(|v| unwritten_own.contains(&own(v))).cloned().collect();
            if !hit.is_empty() {
                hit.sort();
                result.unwritten.push((index, hit));
            }
        }
    }
    Ok(result)
}

/// Certify that at least one of `targets` (violated error relations: an
/// `error_pN`, or the aggregate `error` when the counterexample names no
/// check) is derivable in the HORN system `chc_text` without depending on an
/// undefined value (module documentation). `strict` is for a harness whose
/// verdict the certificate decides (`should_panic`). `Err` carries the refusal
/// the caller reports.
pub fn certify_error_free_of_havoc(
    chc_text: &str,
    targets: &[&str],
    strict: bool,
) -> Result<HavocCertificate, String> {
    let problem =
        ChcParser::parse(chc_text).map_err(|error| format!("CHC parse failed: {error}"))?;
    let scan = scan_havoc_reads(&problem, strict)?;
    if scan.is_empty() {
        return Ok(HavocCertificate::Clean);
    }
    if targets.is_empty() {
        return Err("no violated check names an error relation".to_string());
    }
    let names: BTreeSet<String> = scan
        .unwritten
        .iter()
        .flat_map(|(_, vars)| vars.iter())
        .map(|var| trust_mc_core::chc::normalize_approx_var(var).to_string())
        .collect();
    let clause_local: HashMap<usize, BTreeSet<String>> =
        scan.unbound.iter().map(|(index, vars)| (*index, vars.iter().cloned().collect())).collect();
    let freed = FreedReads { names: &names, clause_local: &clause_local };
    let mut tautologies = Tautologies::new();
    let mut read: BTreeSet<&str> = names.iter().map(String::as_str).collect();
    read.extend(clause_local.values().flatten().map(String::as_str));
    let mut refusals = Vec::new();
    for target in targets {
        let Some(target_id) = problem.lookup_predicate(target) else {
            refusals.push(format!("{target}: not declared"));
            continue;
        };
        let cone = backward_cone(&problem, target_id);
        let taint = analyze(&problem, &freed, &cone, &mut tautologies)?;
        let dependent = match taint.independence(&problem, target_id) {
            Independence::Independent => {
                return Ok(HavocCertificate::Independent(format!(
                    "`{target}` does not depend on the {} undefined value(s) the system reads \
                     ({read:?})",
                    read.len()
                )));
            }
            Independence::Dependent(dependent) => dependent,
        };
        let mut reasons = Vec::new();
        for strategy in [Strategy::DropSources, Strategy::Carry] {
            match replay_error_derivation_tainted(
                chc_text,
                target,
                &freed,
                strategy,
                &mut tautologies,
            ) {
                Ok(summary) => return Ok(HavocCertificate::Replayed(summary)),
                Err(reason) => reasons.push(format!("{strategy:?}: {reason}")),
            }
        }
        let why: BTreeSet<&str> =
            dependent.iter().filter_map(|index| taint.dependence_reason(*index)).collect();
        refusals.push(format!(
            "{target} reads {read:?} ({} dependent clause(s): {why:?}): {}",
            dependent.len(),
            reasons.join("; ")
        ));
    }
    Err(refusals.join("; "))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The r13 shape: `bb1` no longer carries `mem`, but its error clause
    /// still reads it.
    const UNBOUND: &str = r#"
(set-logic HORN)
(declare-var x (_ BitVec 8))
(declare-var x__out (_ BitVec 8))
(declare-var p (_ BitVec 64))
(declare-var _f_mem_u8 (Array (_ BitVec 64) (_ BitVec 8)))
(declare-rel bb0 ((_ BitVec 8) (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8))))
(declare-rel bb1 ((_ BitVec 8) (_ BitVec 64)))
(declare-rel error ())
(declare-rel error_p0 ())
(declare-rel error_p1 ())
(rule (=> true (bb0 x p _f_mem_u8)))
(rule (=> (and (bb0 x p _f_mem_u8) (= x__out #x01)) (bb1 x__out #x0000000200000000)))
(rule (=> error_p0 error))
(rule (=> (and (bb1 x p) (not (= (select _f_mem_u8 p) #x01))) error_p0))
(rule (=> error_p1 error))
(rule (=> (and (bb1 x p) (= x #x01)) error_p1))
(query error)
"#;

    #[test]
    fn an_unbound_read_is_found_and_refused() {
        let problem = ChcParser::parse(UNBOUND).expect("parses");
        let scan = scan_havoc_reads(&problem, true).expect("scans");
        assert_eq!(scan.unbound.len(), 1, "{scan:?}");
        assert_eq!(scan.unbound[0].1, vec!["_f_mem_u8".to_string()]);
        let err = certify_error_free_of_havoc(UNBOUND, &["error_p0"], true)
            .expect_err("the only derivation reads the unbound memory");
        assert!(err.contains("_f_mem_u8"), "{err}");
    }

    /// A violated check whose cone does not depend on the undefined read
    /// certifies as is.
    #[test]
    fn a_check_outside_the_unbound_read_cone_is_independent() {
        assert!(matches!(
            certify_error_free_of_havoc(UNBOUND, &["error_p1"], true),
            Ok(HavocCertificate::Independent(_))
        ));
    }

    /// An undefined read on a SIBLING transition of the check's cone: the cut
    /// removes that transition and the check still derives along the other,
    /// so it certifies by replay.
    #[test]
    fn a_check_reachable_around_the_unbound_read_replays() {
        let smt = UNBOUND.replace(
            "(rule (=> error_p1 error))",
            "(rule (=> (and (bb0 x p _f_mem_u8) (= x__out (select _f_mem_u8 p))) (bb1 x__out p)))\n(rule (=> error_p1 error))",
        );
        assert_ne!(smt, UNBOUND, "the fixture edit must apply");
        match certify_error_free_of_havoc(&smt, &["error_p1"], true) {
            Ok(HavocCertificate::Replayed(summary)) => assert!(summary.contains("error_p1")),
            other => panic!("expected a replayed certificate, got {other:?}"),
        }
    }

    /// The r01 shape: a typed memory array no clause writes, read through a
    /// joined reference to promoted constants.
    const UNWRITTEN: &str = r#"
(set-logic HORN)
(declare-var b Bool)
(declare-var r (_ BitVec 64))
(declare-var r__out (_ BitVec 64))
(declare-var _f_mem_Color (Array (_ BitVec 64) (_ BitVec 32)))
(declare-rel bb0 (Bool (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 32))))
(declare-rel bb1 (Bool (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 32))))
(declare-rel error ())
(declare-rel error_p0 ())
(rule (=> true (bb0 b r _f_mem_Color)))
(rule (=> (and (bb0 b r _f_mem_Color) b) (bb1 b #x0000000200000000 _f_mem_Color)))
(rule (=> (and (bb0 b r _f_mem_Color) (not b)) (bb1 b #x0000000300000000 _f_mem_Color)))
(rule (=> error_p0 error))
(rule (=> (and (bb1 b r _f_mem_Color) (not (= (= (select _f_mem_Color r) #x00000000) b))) error_p0))
(query error)
"#;

    #[test]
    fn a_read_of_unwritten_memory_is_refused() {
        let problem = ChcParser::parse(UNWRITTEN).expect("parses");
        let scan = scan_havoc_reads(&problem, true).expect("scans");
        assert!(scan.unbound.is_empty(), "{scan:?}");
        assert_eq!(scan.unwritten.len(), 1, "{scan:?}");
        assert!(certify_error_free_of_havoc(UNWRITTEN, &["error_p0"], true).is_err());
    }

    /// The same system with the constants stored: nothing undefined is read.
    #[test]
    fn written_memory_is_clean() {
        let smt = UNWRITTEN
            .replace(
                "(rule (=> (and (bb0 b r _f_mem_Color) b) (bb1 b #x0000000200000000 _f_mem_Color)))",
                "(rule (=> (and (bb0 b r _f_mem_Color) b) (bb1 b #x0000000200000000 (store _f_mem_Color #x0000000200000000 #x00000000))))",
            )
            .replace(
                "(rule (=> (and (bb0 b r _f_mem_Color) (not b)) (bb1 b #x0000000300000000 _f_mem_Color)))",
                "(rule (=> (and (bb0 b r _f_mem_Color) (not b)) (bb1 b #x0000000300000000 (store _f_mem_Color #x0000000300000000 #x00000001))))",
            );
        assert_ne!(smt, UNWRITTEN, "the fixture edit must apply");
        let problem = ChcParser::parse(&smt).expect("parses");
        assert!(scan_havoc_reads(&problem, true).expect("scans").is_empty());
        assert_eq!(
            certify_error_free_of_havoc(&smt, &["error_p0"], true),
            Ok(HavocCertificate::Clean)
        );
    }

    /// A MIR local's slot no clause ever writes is unwritten state like
    /// memory (the `two_read_safe` shape: `_2_fld1` carried from entry).
    #[test]
    fn a_never_written_local_is_unwritten_state() {
        let smt = UNWRITTEN.replace("_f_mem_Color", "_f_7");
        let problem = ChcParser::parse(&smt).expect("parses");
        let scan = scan_havoc_reads(&problem, true).expect("scans");
        assert!(scan.unbound.is_empty(), "{scan:?}");
        assert_eq!(scan.unwritten.len(), 1, "{scan:?}");
        assert!(certify_error_free_of_havoc(&smt, &["error_p0"], true).is_err());
        // Outside the strict mode the rule does not fire (module documentation).
        assert!(scan_havoc_reads(&problem, false).expect("scans").is_empty());
    }

    /// A local written on SOME path (may-uninitialized at entry) is not
    /// unwritten: the rule is narrow on purpose (module documentation).
    #[test]
    fn a_local_written_on_some_path_is_not_unwritten() {
        let smt = UNWRITTEN.replace("_f_mem_Color", "_f_7").replace(
            "(rule (=> (and (bb0 b r _f_7) b) (bb1 b #x0000000200000000 _f_7)))",
            "(rule (=> (and (bb0 b r _f_7) b) (bb1 b #x0000000200000000 ((as const (Array (_ BitVec 64) (_ BitVec 32))) #x00000000))))",
        );
        assert!(smt.contains("as const"), "the fixture edit must apply");
        let problem = ChcParser::parse(&smt).expect("parses");
        assert!(scan_havoc_reads(&problem, true).expect("scans").is_empty());
    }

    /// The `sgn_read_b_safe` shape: the error clause reads the POST-state
    /// spelling of a state variable that nothing binds or defines. Under
    /// `should_panic` this false certificate was a false proof.
    const UNBOUND_OUT: &str = r#"
(set-logic HORN)
(declare-var _h_2_fld1 (_ BitVec 32))
(declare-var _h_2_fld1__out (_ BitVec 32))
(declare-rel bb0 ((_ BitVec 32)))
(declare-rel error ())
(declare-rel error_p0 ())
(rule (=> (= _h_2_fld1 #x00000002) (bb0 _h_2_fld1)))
(rule (=> error_p0 error))
(rule (=> (and (bb0 _h_2_fld1) (not (= _h_2_fld1__out #x00000002))) error_p0))
(query error)
"#;

    #[test]
    fn an_unbound_post_state_read_is_refused() {
        let problem = ChcParser::parse(UNBOUND_OUT).expect("parses");
        let scan = scan_havoc_reads(&problem, true).expect("scans");
        assert_eq!(scan.unbound.len(), 1, "{scan:?}");
        assert_eq!(scan.unbound[0].1, vec!["_h_2_fld1__out".to_string()]);
        assert!(certify_error_free_of_havoc(UNBOUND_OUT, &["error_p0"], true).is_err());
        // The read is in an ERROR clause, so the ordinary mode refuses it too.
        assert_eq!(scan_havoc_reads(&problem, false).expect("scans"), scan);
        assert!(certify_error_free_of_havoc(UNBOUND_OUT, &["error_p0"], false).is_err());
    }

    /// The joined-enum shape (joined_enum_constant_payloads.rs,
    /// `res_err_ordering_join_must_fail`): a TRANSITION copies the inactive
    /// payload field of `Err(Less)`, a post-state spelling nothing defines.
    /// That freedom is by design, and the ordinary mode leaves a transition's
    /// post-state reads alone; the strict mode refuses them.
    #[test]
    fn an_unbound_post_state_read_in_a_transition_is_strict_only() {
        let smt = r#"
(set-logic HORN)
(declare-var _h_2_fld1 (_ BitVec 8))
(declare-var _h_2_fld1__out (_ BitVec 8))
(declare-var _h_4 (_ BitVec 8))
(declare-var _h_4__out (_ BitVec 8))
(declare-rel bb0 ((_ BitVec 8) (_ BitVec 8)))
(declare-rel bb1 ((_ BitVec 8) (_ BitVec 8)))
(declare-rel error ())
(declare-rel error_p0 ())
(rule (=> (= _h_4 #x00) (bb0 _h_2_fld1 _h_4)))
(rule (=> (and (bb0 _h_2_fld1 _h_4) (= _h_4__out _h_2_fld1__out)) (bb1 _h_2_fld1 _h_4__out)))
(rule (=> error_p0 error))
(rule (=> (and (bb1 _h_2_fld1 _h_4) (= _h_4 #x07)) error_p0))
(query error)
"#;
        let problem = ChcParser::parse(smt).expect("parses");
        assert!(scan_havoc_reads(&problem, false).expect("scans").unbound.is_empty());
        assert_eq!(scan_havoc_reads(&problem, true).expect("scans").unbound.len(), 1);
    }

    /// A post-state spelling the clause DEFINES from bound values is not an
    /// unbound read.
    #[test]
    fn a_defined_post_state_read_is_clean() {
        let smt = UNBOUND_OUT.replace(
            "(not (= _h_2_fld1__out #x00000002))",
            "(= _h_2_fld1__out (bvadd _h_2_fld1 #x00000001)) (not (= _h_2_fld1__out #x00000003))",
        );
        assert_ne!(smt, UNBOUND_OUT, "the fixture edit must apply");
        let problem = ChcParser::parse(&smt).expect("parses");
        assert!(scan_havoc_reads(&problem, true).expect("scans").is_empty());
        assert_eq!(
            certify_error_free_of_havoc(&smt, &["error_p0"], true),
            Ok(HavocCertificate::Clean)
        );
    }

    /// A post-state spelling carried bare into the head is a nondeterministic
    /// update (`kani::any`), even when the clause also constrains it.
    #[test]
    fn a_nondeterministic_update_is_not_an_unbound_read() {
        let smt = r#"
(set-logic HORN)
(declare-var _h_1 (_ BitVec 8))
(declare-var _h_1__out (_ BitVec 8))
(declare-rel bb0 ((_ BitVec 8)))
(declare-rel bb1 ((_ BitVec 8)))
(declare-rel error ())
(declare-rel error_p0 ())
(rule (=> (= _h_1 #x00) (bb0 _h_1)))
(rule (=> (and (bb0 _h_1) (bvult _h_1__out #x0a)) (bb1 _h_1__out)))
(rule (=> error_p0 error))
(rule (=> (and (bb1 _h_1) (= _h_1 #x07)) error_p0))
(query error)
"#;
        let problem = ChcParser::parse(smt).expect("parses");
        assert!(scan_havoc_reads(&problem, true).expect("scans").is_empty());
    }

    /// The `kani::any_where` shape (walker_value_only_closure_dual.rs,
    /// bug_any_where_unchecked): one transition carries the fresh value bare
    /// into its head, and a SIBLING clause of the same block checks the
    /// predicate on it. That read is of a nondeterministic value, not an
    /// unbound one.
    #[test]
    fn a_nondeterministic_value_checked_by_a_sibling_is_not_an_unbound_read() {
        let smt = r#"
(set-logic HORN)
(declare-var _h_1 (_ BitVec 8))
(declare-var _h_1__out (_ BitVec 8))
(declare-rel bb0 ((_ BitVec 8)))
(declare-rel bb1 ((_ BitVec 8)))
(declare-rel error ())
(declare-rel error_p0 ())
(rule (=> true (bb0 _h_1)))
(rule (=> error_p0 error))
(rule (=> (and (bb0 _h_1) (not (bvuge (bvadd _h_1__out #xc8) _h_1__out))) error_p0))
(rule (=> (and (bb0 _h_1) (bvugt (bvadd _h_1__out #xc8) #x0a)) (bb1 _h_1__out)))
(query error)
"#;
        let problem = ChcParser::parse(smt).expect("parses");
        let scan = scan_havoc_reads(&problem, true).expect("scans");
        assert!(scan.unbound.is_empty(), "{scan:?}");
        // Without the sibling's nondeterministic update the read is unbound.
        let lost = smt.replace(
            "(rule (=> (and (bb0 _h_1) (bvugt (bvadd _h_1__out #xc8) #x0a)) (bb1 _h_1__out)))",
            "(rule (=> (and (bb0 _h_1) (bvugt (bvadd _h_1 #xc8) #x0a)) (bb1 _h_1)))",
        );
        assert_ne!(lost, smt, "the fixture edit must apply");
        let problem = ChcParser::parse(&lost).expect("parses");
        assert_eq!(scan_havoc_reads(&problem, true).expect("scans").unbound.len(), 1);
    }

    /// A never-written cell the encoder PINS by an equality in its transitions
    /// (the cell register of cell_register_review_dual.rs, the constant cells
    /// of dual69_shrink_index.rs) is defined, not unwritten.
    #[test]
    fn a_pinned_cell_is_not_unwritten() {
        let smt = r#"
(set-logic HORN)
(declare-var _h_1_fld1_at_0x0_bv64 (_ BitVec 8))
(declare-var _h_2 (_ BitVec 8))
(declare-var _h_2__out (_ BitVec 8))
(declare-rel bb0 ((_ BitVec 8) (_ BitVec 8)))
(declare-rel bb1 ((_ BitVec 8) (_ BitVec 8)))
(declare-rel error ())
(declare-rel error_p0 ())
(rule (=> (= _h_2 #x00) (bb0 _h_1_fld1_at_0x0_bv64 _h_2)))
(rule (=> (and (bb0 _h_1_fld1_at_0x0_bv64 _h_2) (= _h_1_fld1_at_0x0_bv64 #x07)) (bb1 _h_1_fld1_at_0x0_bv64 (bvadd _h_1_fld1_at_0x0_bv64 #x01))))
(rule (=> error_p0 error))
(rule (=> (and (bb1 _h_1_fld1_at_0x0_bv64 _h_2) (= _h_2 #x08)) error_p0))
(query error)
"#;
        let problem = ChcParser::parse(smt).expect("parses");
        assert!(scan_havoc_reads(&problem, true).expect("scans").is_empty());
    }

    /// An `assert!(x == 1)` on an unwritten cell puts `(= x 1)` on its passing
    /// branch and `(not (= x 1))` on its error branch: a guard, not a pin
    /// (review probe g3_written_later.rs, `mut_read_only_safe`).
    #[test]
    fn an_assert_guard_is_not_a_pin() {
        let smt = r#"
(set-logic HORN)
(declare-var _h_mem_u128_at_0x200000000_bv64 (_ BitVec 128))
(declare-var _h_5 (_ BitVec 128))
(declare-rel bb3 ((_ BitVec 128) (_ BitVec 128)))
(declare-rel bb1 ((_ BitVec 128)))
(declare-rel error ())
(declare-rel error_p6 ())
(rule (=> true (bb3 _h_5 _h_mem_u128_at_0x200000000_bv64)))
(rule (=> (and (bb3 _h_5 _h_mem_u128_at_0x200000000_bv64) (= _h_mem_u128_at_0x200000000_bv64 #x00000000000000000000000000000001)) (bb1 _h_mem_u128_at_0x200000000_bv64)))
(rule (=> error_p6 error))
(rule (=> (and (bb3 _h_5 _h_mem_u128_at_0x200000000_bv64) (not (= _h_mem_u128_at_0x200000000_bv64 #x00000000000000000000000000000001))) error_p6))
(query error)
"#;
        let problem = ChcParser::parse(smt).expect("parses");
        let scan = scan_havoc_reads(&problem, false).expect("scans");
        assert!(!scan.unwritten.is_empty(), "{scan:?}");
        assert!(certify_error_free_of_havoc(smt, &["error_p6"], false).is_err());
    }

    /// The `g7_unattr_real_bug.rs` shape: an unwritten cell copied into a
    /// local, a TAUTOLOGICAL guard over that local on the only path, then an
    /// independent real bug. The bug does not depend on the cell.
    const DOWNSTREAM: &str = r#"
(set-logic HORN)
(declare-var v (_ BitVec 8))
(declare-var v__out (_ BitVec 8))
(declare-var x (_ BitVec 32))
(declare-var x__out (_ BitVec 32))
(declare-var _g_mem_u8_at_0x0_bv64 (_ BitVec 8))
(declare-rel bb0 ((_ BitVec 8) (_ BitVec 32) (_ BitVec 8)))
(declare-rel bb1 ((_ BitVec 8) (_ BitVec 32)))
(declare-rel bb2 ((_ BitVec 8) (_ BitVec 32)))
(declare-rel error ())
(declare-rel error_p0 ())
(declare-rel error_p1 ())
(rule (=> (and (= v #x00) (= x #x00000000)) (bb0 v x _g_mem_u8_at_0x0_bv64)))
(rule (=> (and (bb0 v x _g_mem_u8_at_0x0_bv64) (= v__out _g_mem_u8_at_0x0_bv64)) (bb1 v__out x)))
(rule (=> (and (bb1 v x) (bvule ((_ zero_extend 8) v) #x00ff)) (bb2 v x__out)))
(rule (=> error_p0 error))
(rule (=> (and (bb1 v x) (not (bvule ((_ zero_extend 8) v) #x00ff))) error_p0))
(rule (=> error_p1 error))
(rule (=> (and (bb2 v x) (= x #x00000007)) error_p1))
(query error)
"#;

    #[test]
    fn an_independent_bug_downstream_of_a_freed_read_is_independent() {
        let problem = ChcParser::parse(DOWNSTREAM).expect("parses");
        assert_eq!(scan_havoc_reads(&problem, true).expect("scans").unwritten.len(), 1);
        match certify_error_free_of_havoc(DOWNSTREAM, &["error_p1"], true) {
            Ok(HavocCertificate::Independent(summary)) => assert!(summary.contains("error_p1")),
            other => panic!("expected an independent certificate, got {other:?}"),
        }
        // The aggregate target (an unattributed counterexample) replays: its
        // cone also holds the dependent `error_p0` clause.
        match certify_error_free_of_havoc(DOWNSTREAM, &["error"], true) {
            Ok(HavocCertificate::Replayed(summary)) => assert!(summary.contains("`error`")),
            other => panic!("expected a replayed certificate, got {other:?}"),
        }
    }

    /// The same shape with a guard that is NOT a tautology: the bug is reached
    /// only when the freed value satisfies it, so the check depends on it.
    #[test]
    fn a_bug_behind_a_guard_on_a_freed_read_is_refused() {
        let smt = DOWNSTREAM.replace(
            "(rule (=> (and (bb1 v x) (bvule ((_ zero_extend 8) v) #x00ff)) (bb2 v x__out)))",
            "(rule (=> (and (bb1 v x) (= v #x01)) (bb2 v x__out)))",
        );
        assert_ne!(smt, DOWNSTREAM, "the fixture edit must apply");
        let err = certify_error_free_of_havoc(&smt, &["error_p1"], true)
            .expect_err("the only path to the bug tests the freed value");
        assert!(err.contains("a guard reads a tainted variable"), "{err}");
    }

    /// The wpc shape: the parser folds `(= v__out cell)` into the head, so
    /// the read of the unwritten cell is a bare argument under another name.
    #[test]
    fn a_copy_of_unwritten_memory_into_a_local_is_a_read() {
        let smt = r#"
(set-logic HORN)
(declare-var v (_ BitVec 8))
(declare-var v__out (_ BitVec 8))
(declare-var _f_mem_u8_at_0x3_bv64 (_ BitVec 8))
(declare-rel bb0 ((_ BitVec 8) (_ BitVec 8)))
(declare-rel bb1 ((_ BitVec 8)))
(declare-rel error ())
(declare-rel error_p0 ())
(rule (=> true (bb0 v _f_mem_u8_at_0x3_bv64)))
(rule (=> (and (bb0 v _f_mem_u8_at_0x3_bv64) (= v__out _f_mem_u8_at_0x3_bv64)) (bb1 v__out)))
(rule (=> error_p0 error))
(rule (=> (and (bb1 v) (not (= v #x01))) error_p0))
(query error)
"#;
        let problem = ChcParser::parse(smt).expect("parses");
        let scan = scan_havoc_reads(&problem, true).expect("scans");
        assert_eq!(scan.unwritten.len(), 1, "{scan:?}");
        assert!(certify_error_free_of_havoc(smt, &["error_p0"], true).is_err());
    }

    #[test]
    fn memory_names() {
        assert!(is_memory_state_var("mem"));
        assert!(is_memory_state_var("mem__out"));
        assert!(is_memory_state_var("_f_mem_u8"));
        assert!(is_memory_state_var("_f_mem_u8__out"));
        assert!(is_memory_state_var("_f_mem_u8_at_0x0_bv64"));
        assert!(is_memory_state_var("_f_mem_std_option_Option_u8"));
        assert!(is_memory_state_var("_check_mem_x_mem_u32"));
        assert!(!is_memory_state_var("_check_mem_x_3"));
        assert!(!is_memory_state_var("_check_mem_x_12_fld0"));
        assert!(!is_memory_state_var("_f_7"));
        assert!(!is_memory_state_var("obj_size_at_0x15_bv32"));
        assert!(!is_memory_state_var("memory"));
    }
}
