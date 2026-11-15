// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Kani's unwinding assertion on a walked loop, discharged at compile time
//! where the host's own assumption makes it unviolable.
//!
//! Under a declared `#[kani::unwind(U)]` the walker replays a loop pass for
//! pass as Kani does and states "unwinding assertion loop" where a path needs
//! pass `U + 1` (`walker.rs`, `LoopHeaderVisit::UnwindExceeded`). That check
//! is a property of its own, and the driver solves the harness's properties
//! one after another out of one budget: `rv_loops.rs::l_free_sym_safe`
//! (`kani::assume(n <= 10)`, a `while i < n` loop under `unwind(12)`) spent
//! 9 s proving the unwinding row and left the assertion row 21 s, too little
//! for the schedule that proves it in 13 s with the whole budget; main, with
//! no unwinding row, proved it every time (walker fail-closed review 6
//! round 3, repair round 1's finding 6).
//!
//! When the host assumes a bound on the call's arguments on every path to the
//! call, an unwinding check that holds for every value of everything else
//! under those bounds can never fail, and is not emitted: its violation set is
//! empty. Decided exactly, in process, by one small SMT query per check
//! (`¬check ∧ bounds` unsatisfiable); anything the query cannot express, and
//! any answer other than UNSAT, keeps the check.
//!
//! The walker's reach check on an abandoned SwitchInt arm (`t` wherever a
//! path takes an arm the replay did not walk) is discharged the same way: it
//! is valid under the bounds exactly when no allowed path takes the arm.
//!
//! The same bounds discharge the walk's assume guard
//! ([`drop_host_discharged_assume_guard`]): the path a thirteenth pass would
//! take ends, as Kani's `assume(false)` after the assertion ends it, and the
//! host states that cut as a transition constraint. Where the bounds imply
//! the guard it cuts nothing, and dropping it is exact; keeping it left
//! `free_sym_unwind12_safe` a twelve-arm chain the solver had to see through,
//! and its one property missed the 30 s budget at high load (repair round 4).

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{
    BinOp, Operand, Place, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{BTreeMap, HashMap};
use tracing::debug;

use super::super::ChcCtx;
use super::super::inline_body::DeferredInlineCheck;

/// The message the walker gives Kani's unwinding assertion on a walked loop.
pub(in crate::codegen_ay::chc) const LOOP_UNWINDING_ASSERTION_MESSAGE: &str =
    "unwinding assertion loop";

/// The start of the message of the walker's reach check on an abandoned
/// SwitchInt arm (`switchint.rs`, Mechanism C): `t` wherever a path takes the
/// arm, which the replay did not walk.
pub(in crate::codegen_ay::chc) const WALKER_BAILED_ARM_REACH_MESSAGE: &str =
    "a check the CHC walker could not translate is reachable here";

/// Keep every check of `checks` except an unwinding assertion, or a reach
/// check on an abandoned arm, that the host call's dominating argument bounds
/// discharge (see the module docs). The reach check is `¬guard ∨ t` with `t`
/// free: valid under the bounds exactly when no path the bounds allow takes
/// the arm, so it can never fail (`walker_loop_exit_test_dual.rs`
/// `safe_break_sym_bound_small`, `assume(n <= 5)` and a loop the replay
/// leaves past its fuel).
pub(in crate::codegen_ay::chc) fn drop_host_discharged_unwinding_checks(
    ctx: &mut ChcCtx<'_, '_>,
    bb_idx: usize,
    modified_locals: &std::collections::HashSet<usize>,
    checks: Vec<DeferredInlineCheck>,
) -> Vec<DeferredInlineCheck> {
    let is_unwinding = |check: &DeferredInlineCheck| {
        check.message.as_deref().is_some_and(|message| {
            message == LOOP_UNWINDING_ASSERTION_MESSAGE || message.starts_with(WALKER_BAILED_ARM_REACH_MESSAGE)
        })
    };
    if !checks.iter().any(is_unwinding) {
        return checks;
    }
    let facts = host_call_bound_facts(ctx, bb_idx, modified_locals);
    if facts.is_empty() {
        return checks;
    }
    checks
        .into_iter()
        .filter(|check| {
            let discharged = is_unwinding(check) && valid_under(&check.check, &facts);
            if discharged {
                debug!(
                    bb_idx,
                    message = check.message.as_deref().unwrap_or(""),
                    "unwinding assertion or abandoned-arm reach check discharged by the host's assumed bounds"
                );
            }
            !discharged
        })
        .collect()
}

/// The assume guard of a call the walker replayed (the condition under which
/// no replayed path was cut: a pass past the declared unwind bound, or an
/// `assume` in the callee), or `None` where the host call's dominating
/// argument bounds make it hold on every path to the call. Such a guard cuts
/// nothing the host's own assumption has not cut already, so dropping it is
/// exact, and stating it is pure cost: `walker_replay_cost_dual.rs`
/// `free_sym_unwind12_safe` carried a twelve-arm chain saying "no path needs
/// a thirteenth pass" beside `kani::assume(n <= 10)`, which already says so,
/// and its one property missed the 30 s budget at load 29 where main proves
/// it in 13 s (walker fail-closed review 6 round 3, finding 5).
pub(in crate::codegen_ay::chc) fn drop_host_discharged_assume_guard(
    ctx: &mut ChcCtx<'_, '_>,
    bb_idx: usize,
    modified_locals: &std::collections::HashSet<usize>,
    guard: Option<Expr>,
) -> Option<Expr> {
    let guard = guard?;
    let facts = host_call_bound_facts(ctx, bb_idx, modified_locals);
    if !facts.is_empty() && valid_under(&guard, &facts) {
        debug!(bb_idx, "inline assume guard discharged by the host's assumed bounds");
        return None;
    }
    Some(guard)
}

/// `arg <= K` for each bound [`host_call_dominating_bounds`] finds, over the
/// argument's value at the call.
fn host_call_bound_facts(
    ctx: &mut ChcCtx<'_, '_>,
    bb_idx: usize,
    modified_locals: &std::collections::HashSet<usize>,
) -> Vec<Expr> {
    let bounds = host_call_dominating_bounds(ctx, bb_idx);
    let mut facts = Vec::with_capacity(bounds.len());
    for (local, bound) in bounds {
        let operand = Operand::Copy(Place { local, projection: vec![] });
        let Some(value) = ctx.translate_operand_with_modified(&operand, modified_locals) else {
            continue;
        };
        let Some(width) = value.sort().bitvec_width() else {
            continue;
        };
        facts.push(value.bvule(Expr::bitvec_const(bound, width)));
    }
    facts
}

/// The host call's unsigned integer arguments with a bound the host assumes
/// of them on every path to the call: `kani::assume(arg <= K)` (or `<`, `>=`,
/// `>` with the constant on the other side) whose block dominates the call
/// block, for an argument local that is assigned once in the host body (or is
/// a parameter never assigned) and never borrowed or pointed to (so the value
/// the assumption constrains is the value the call passes).
fn host_call_dominating_bounds(ctx: &ChcCtx<'_, '_>, bb_idx: usize) -> Vec<(usize, u128)> {
    let host = ctx.body;
    let Some(TerminatorKind::Call { args, .. }) = host.blocks.get(bb_idx).map(|b| &b.terminator.kind)
    else {
        return Vec::new();
    };
    let locals = host.locals();
    let unsigned = |local: usize| {
        locals.get(local).is_some_and(|decl| matches!(decl.ty.kind(), TyKind::RigidTy(RigidTy::Uint(_))))
    };
    let arg_locals: Vec<usize> = args
        .iter()
        .filter_map(|arg| match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        })
        .filter(|&local| unsigned(local))
        .collect();
    if arg_locals.is_empty() {
        return Vec::new();
    }
    // Definitions and borrows of every local, over the whole body.
    let mut defs: HashMap<usize, usize> = HashMap::new();
    let mut borrowed: Vec<usize> = Vec::new();
    for block in &host.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                continue;
            };
            *defs.entry(place.local).or_insert(0) += 1;
            if let Rvalue::Ref(_, _, borrowed_place) | Rvalue::AddressOf(_, borrowed_place) = rvalue {
                borrowed.push(borrowed_place.local);
            }
        }
        if let TerminatorKind::Call { destination, .. } = &block.terminator.kind {
            *defs.entry(destination.local).or_insert(0) += 1;
        }
    }
    // Assigned once in the body, or an argument never assigned, and never
    // borrowed.
    let arg_count = host.arg_locals().len();
    let stable = |local: usize| {
        let assigned = defs.get(&local).copied().unwrap_or(0);
        (assigned == 1 || (assigned == 0 && (1..=arg_count).contains(&local)))
            && !borrowed.contains(&local)
    };
    // Each bool local defined by a comparison of a stable argument with a
    // constant: the argument and its (inclusive) upper bound.
    let mut bound_of_cond: HashMap<usize, (usize, u128)> = HashMap::new();
    for block in &host.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(place, Rvalue::BinaryOp(op, lhs, rhs)) = &stmt.kind else {
                continue;
            };
            if !place.projection.is_empty() || !stable(place.local) {
                continue;
            }
            let local_of = |op: &Operand| match op {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                _ => None,
            };
            let constant =
                |op: &Operand| super::super::codegen_call_vec_builder_pattern::extract_operand_const_uint(op);
            let bound = match (op, local_of(lhs), constant(rhs), local_of(rhs), constant(lhs)) {
                (BinOp::Le, Some(l), Some(k), _, _) => Some((l, k)),
                (BinOp::Lt, Some(l), Some(k), _, _) => k.checked_sub(1).map(|k| (l, k)),
                (BinOp::Ge, _, _, Some(l), Some(k)) => Some((l, k)),
                (BinOp::Gt, _, _, Some(l), Some(k)) => k.checked_sub(1).map(|k| (l, k)),
                _ => None,
            };
            if let Some((local, bound)) = bound
                && arg_locals.contains(&local)
                && stable(local)
            {
                bound_of_cond.insert(place.local, (local, bound));
            }
        }
    }
    if bound_of_cond.is_empty() {
        return Vec::new();
    }
    let cfg = crate::codegen_ay::loop_unroll::Cfg::from_body(host);
    let idom = crate::codegen_ay::loop_unroll::compute_idom_lengauer_tarjan(&cfg);
    let dominates = |a: usize, mut b: usize| {
        for _ in 0..=idom.len() {
            if a == b {
                return true;
            }
            match idom.get(b) {
                Some(&parent) if parent != usize::MAX && parent != b => b = parent,
                _ => return false,
            }
        }
        false
    };
    let mut tightest: BTreeMap<usize, u128> = BTreeMap::new();
    for (block_idx, block) in host.blocks.iter().enumerate() {
        let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
            continue;
        };
        if !matches!(
            ctx.detect_kani_hook(func),
            Some(crate::kani_middle::kani_functions::KaniHook::Assume)
        ) || !dominates(block_idx, bb_idx)
            || block_idx == bb_idx
        {
            continue;
        }
        if let Some(Operand::Copy(cond) | Operand::Move(cond)) = args.first()
            && cond.projection.is_empty()
            && let Some(&(local, bound)) = bound_of_cond.get(&cond.local)
        {
            let entry = tightest.entry(local).or_insert(bound);
            *entry = (*entry).min(bound);
        }
    }
    tightest.into_iter().collect()
}

/// Does `check` hold for every value of its free variables that satisfies
/// every fact of `facts`? Exactly when `facts ∧ ¬check` is unsatisfiable. A
/// term with a subterm of any sort but Bool or a bitvector, or any answer
/// other than UNSAT (an error, `unknown`), is `false`.
fn valid_under(check: &Expr, facts: &[Expr]) -> bool {
    let mut vars: BTreeMap<String, Sort> = BTreeMap::new();
    for term in std::iter::once(check).chain(facts.iter()) {
        if !collect_scalar_vars(term, &mut vars) {
            return false;
        }
    }
    let mut smt2 = String::from("(set-logic QF_BV)\n");
    for (name, sort) in &vars {
        smt2.push_str(&format!("(declare-fun {} () {sort})\n", Expr::var(name.as_str(), sort.clone())));
    }
    for fact in facts {
        smt2.push_str(&format!("(assert {fact})\n"));
    }
    smt2.push_str(&format!("(assert (not {check}))\n(check-sat)\n"));
    let Ok(commands) = ay_frontend::parse(&smt2) else {
        return false;
    };
    let mut executor = ay_dpll::Executor::new();
    // Verdict only (as `template_check.rs`'s `ay_check_unsat`).
    executor.set_competition_mode(true);
    executor.set_timeout(Some(std::time::Duration::from_secs(5)));
    let Ok(outputs) = executor.execute_all(&commands) else {
        return false;
    };
    outputs.iter().any(|output| output.trim() == "unsat")
}

/// Collect the free variables of `expr` with their sorts; `false` when a
/// subterm has a sort other than Bool or a bitvector, or a variable occurs
/// with two sorts.
fn collect_scalar_vars(expr: &Expr, vars: &mut BTreeMap<String, Sort>) -> bool {
    let mut stack = vec![expr];
    let mut seen = std::collections::HashSet::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(term.value())) {
            continue;
        }
        let sort = term.sort();
        if !(sort.is_bool() || sort.is_bitvec()) {
            return false;
        }
        if let ExprValue::Var { name } = term.value() {
            match vars.get(name.as_str()) {
                Some(existing) if existing != sort => return false,
                Some(_) => {}
                None => {
                    vars.insert(name.to_string(), sort.clone());
                }
            }
        }
        stack.extend(term.children());
    }
    true
}
