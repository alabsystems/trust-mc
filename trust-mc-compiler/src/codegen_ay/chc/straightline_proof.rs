// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bounded syntactic proof for scalarized straight-line CHCs.
//!
//! This is intentionally conservative: it only succeeds when relation-argument
//! substitution and equality simplification make every reachable `error` edge
//! syntactically false. On any unsupported shape or budget overflow it leaves
//! PDR's original CHC obligation intact.

use std::collections::{HashMap, HashSet, VecDeque};

use ay_bindings::{Expr, ExprValue, rebuild_with_children};
use trust_mc_core::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody};

const MAX_RULES: usize = 256;
const MAX_FRAMES_PER_RELATION: usize = 64;
const MAX_TOTAL_FRAMES: usize = 512;

/// Maximum recursion depth for the straight-line prover's Expr walkers
/// (`substitute_inner`, `simplify_with_facts`, `select_from_simplified`).
///
/// Deep memory-array Store chains (Box/Rc<dyn> heap+vtable encoding, complex
/// contract-param destructuring) can drive these hand-written recursive walkers
/// past the native stack limit → SIGABRT. Unlike the verdict-identical array
/// rewriters, these walkers must NOT grow the stack (that would expand the
/// straight-line discharge proof surface, which MEMORY flags as able to
/// false-prove on abstracted edges). Instead we DEPTH-BAIL: on exceeding this
/// budget the walker returns `None`, so `prove_straightline_safety` returns
/// `false`, `discharge_straightline_safety` declines, and the VC is sent to ay
/// UNCHANGED (the real solver runs). Sound: bailing never turns a bug into a
/// proof; it only forgoes a syntactic shortcut.
const MAX_STRAIGHTLINE_RECURSION_DEPTH: usize = 512;

thread_local! {
    static STRAIGHTLINE_RECURSION_DEPTH: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

/// RAII depth counter for the straight-line prover's recursive Expr walkers.
///
/// [`StraightlineDepthGuard::enter`] returns `None` once the recursion budget is
/// exhausted; the walkers propagate that `None` (via `?`) to bail to the solver.
/// The counter is decremented on drop, so budget is per-descent, not global.
struct StraightlineDepthGuard;

impl StraightlineDepthGuard {
    fn enter() -> Option<Self> {
        STRAIGHTLINE_RECURSION_DEPTH.with(|depth| {
            let current = depth.get();
            if current >= MAX_STRAIGHTLINE_RECURSION_DEPTH {
                tracing::debug!(
                    depth = current,
                    limit = MAX_STRAIGHTLINE_RECURSION_DEPTH,
                    "straightline proof bailed: recursion depth budget exceeded"
                );
                return None;
            }
            depth.set(current + 1);
            Some(StraightlineDepthGuard)
        })
    }
}

impl Drop for StraightlineDepthGuard {
    fn drop(&mut self) {
        STRAIGHTLINE_RECURSION_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct Frame {
    args: Vec<Expr>,
    facts: PathFacts,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
struct PathFacts {
    disequalities: Vec<(Expr, Expr)>,
    unsigned_upper_bounds: Vec<(Expr, u128, u32)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstraintStatus {
    Feasible,
    Infeasible,
    Unsupported,
}

impl PathFacts {
    fn add_disequality(&mut self, lhs: Expr, rhs: Expr) {
        if lhs == rhs || self.are_disequal(&lhs, &rhs) {
            return;
        }
        self.disequalities.push((lhs, rhs));
    }

    fn are_disequal(&self, lhs: &Expr, rhs: &Expr) -> bool {
        if self.disequalities.iter().any(|(a, b)| (a == lhs && b == rhs) || (a == rhs && b == lhs))
        {
            return true;
        }
        if let (ExprValue::Bv2Int(lhs_inner), ExprValue::Bv2Int(rhs_inner)) =
            (lhs.value(), rhs.value())
        {
            return lhs_inner.sort() == rhs_inner.sort()
                && lhs_inner.sort().is_bitvec()
                && self.are_disequal(lhs_inner, rhs_inner);
        }
        false
    }

    fn add_unsigned_upper_bound(&mut self, expr: Expr, bound: u128, width: u32) {
        if let Some((_, existing_bound, _)) =
            self.unsigned_upper_bounds.iter_mut().find(|(existing_expr, _, existing_width)| {
                existing_expr == &expr && *existing_width == width
            })
        {
            *existing_bound = (*existing_bound).min(bound);
            return;
        }
        self.unsigned_upper_bounds.push((expr, bound, width));
    }

    fn unsigned_upper_bound(&self, expr: &Expr) -> Option<(u128, u32)> {
        self.unsigned_upper_bounds
            .iter()
            .filter(|(candidate, _, _)| candidate == expr)
            .map(|(_, bound, width)| (*bound, *width))
            .min_by_key(|(bound, _)| *bound)
    }
}

/// Prove safety for bounded, scalarized, straight-line VCs.
pub(in crate::codegen_ay) fn prove_straightline_safety(vc: &ChcVc) -> bool {
    if vc.rules.len() > MAX_RULES {
        tracing::debug!(
            rules = vc.rules.len(),
            limit = MAX_RULES,
            "straightline proof bailed: rule budget exceeded"
        );
        return false;
    }
    // #47 FAIL-CLOSE: HAVOC edges (nondet rebinds marked by `__havoc_*`
    // binding vars, e.g. the loop-contract rule's modified-set havoc) make
    // the bounded concrete enumeration untrustworthy — after const-prop the
    // surviving fragment can look enumerable while the havoc admits states
    // the enumeration never visits (observed: a vacuous "proof" of a
    // refutable post-loop assertion). Defer such VCs to the real solver.
    let mentions_havoc = |expr: &Expr| {
        let mut stack = vec![expr];
        while let Some(e) = stack.pop() {
            if let ExprValue::Var { name } = e.value()
                && name.contains("__havoc_")
            {
                return true;
            }
            stack.extend(e.value().children());
        }
        false
    };
    for rule in &vc.rules {
        if rule.body.constraints.iter().any(&mentions_havoc)
            || rule.head.args.iter().any(&mentions_havoc)
        {
            tracing::debug!(
                head = %rule.head.name,
                "straightline proof bailed: VC contains havoc edges (fail-closed)"
            );
            return false;
        }
    }
    let has_error_rule = vc.rules.iter().any(|rule| rule.head.name.as_str() == "error");
    if !has_error_rule {
        tracing::debug!("straightline proof skipped: no error-headed rule");
        return false;
    }
    let relation_sorts = relation_sorts(vc);
    // Relations that lie on a loop (a nontrivial SCC / self-loop) in the
    // block-relation graph. The bounded concrete enumeration below is a sound
    // proof ONLY if it fully traverses every loop; if it saturates without
    // reaching some loop node, it collapsed the loop to fewer iterations than
    // are actually reachable (e.g. a for-loop whose exit condition it
    // mis-evaluated as immediately true), so a "no reachable error" verdict is
    // untrustworthy. We check this after saturation and fail closed to the
    // real solver. See `loop_relations`.
    let loop_rels = loop_relations(vc);
    let mut reachable: HashMap<String, HashSet<Frame>> = HashMap::new();
    let mut worklist: VecDeque<String> = VecDeque::new();
    let mut total_frames = 0usize;

    loop {
        let mut changed = false;
        for rule in &vc.rules {
            let body_frames = match &rule.body.relation {
                Some(body) => match reachable.get(body.name.as_str()) {
                    Some(frames) => frames.iter().cloned().collect::<Vec<_>>(),
                    None => continue,
                },
                None => vec![Frame { args: Vec::new(), facts: PathFacts::default() }],
            };

            for frame in body_frames {
                let Some(mut env) = initial_env(rule.body.relation.as_ref(), &frame) else {
                    tracing::debug!(
                        head = %rule.head.name,
                        "straightline proof bailed: non-variable body relation argument"
                    );
                    return false;
                };
                let mut facts = frame.facts.clone();
                match apply_constraints(&rule.body.constraints, &mut env, &mut facts) {
                    ConstraintStatus::Feasible => {}
                    ConstraintStatus::Infeasible => continue,
                    ConstraintStatus::Unsupported => {
                        tracing::debug!(
                            head = %rule.head.name,
                            body = ?rule.body.relation,
                            constraints = ?rule.body.constraints,
                            "straightline proof bailed: unsupported body constraints"
                        );
                        return false;
                    }
                }

                if rule.head.name.as_str() == "error" {
                    tracing::debug!(
                        ?rule.body.constraints,
                        "straightline proof bailed: reachable error edge"
                    );
                    return false;
                }

                let mut head_args = Vec::with_capacity(rule.head.args.len());
                for arg in rule.head.args.iter() {
                    let Some(substituted) = substitute(arg, &env) else {
                        tracing::debug!(
                            head = %rule.head.name,
                            ?arg,
                            "straightline proof bailed: unsupported head argument substitution"
                        );
                        return false;
                    };
                    let Some(simplified) = simplify_with_facts(&substituted, &facts) else {
                        tracing::debug!(
                            head = %rule.head.name,
                            "straightline proof bailed: unsupported head argument simplification"
                        );
                        return false;
                    };
                    head_args.push(simplified);
                }
                if !relation_args_match_decl(rule.head.name.as_str(), &head_args, &relation_sorts) {
                    tracing::debug!(
                        head = %rule.head.name,
                        "straightline proof bailed: head argument sort mismatch"
                    );
                    return false;
                }
                let head_frame = Frame { args: head_args, facts };
                let frames = reachable.entry(rule.head.name.to_string()).or_default();
                if frames.insert(head_frame) {
                    if frames.len() > MAX_FRAMES_PER_RELATION {
                        tracing::debug!(
                            relation = %rule.head.name,
                            frames = frames.len(),
                            "straightline proof bailed: relation frame budget exceeded"
                        );
                        return false;
                    }
                    total_frames += 1;
                    if total_frames > MAX_TOTAL_FRAMES {
                        tracing::debug!(
                            total_frames,
                            "straightline proof bailed: total frame budget exceeded"
                        );
                        return false;
                    }
                    worklist.push_back(rule.head.name.to_string());
                    changed = true;
                }
            }
        }

        if !changed || worklist.pop_front().is_none() {
            break;
        }
    }

    // Fail closed on loops the enumeration did not fully unroll. If any relation
    // on a loop (nontrivial SCC / self-loop) was never reached, the concrete
    // saturation exited the loop earlier than the real semantics allow (a
    // mis-evaluated exit condition — e.g. a `for i in 0..n` whose flattened
    // range fields resolve so the first `Some`/`None` test collapses to `None`),
    // so "error unreachable" here is unsound. Decline; the real CHC solver runs.
    // Loops the enumeration genuinely walks (every loop node reached) keep their
    // fast bounded proof.
    if !loop_rels.is_empty() && !loop_rels.iter().all(|rel| reachable.contains_key(rel)) {
        tracing::debug!(
            "straightline proof bailed: loop body not fully reached (possible \
             mis-evaluated loop exit); deferring to CHC solver"
        );
        return false;
    }

    true
}

/// Relation names that lie on a loop in the block-relation graph: a relation `r`
/// such that there is a nontrivial path `r ->+ r` (i.e. `r` participates in a
/// cycle, including a direct self-loop).
///
/// This is a TRUE cycle-membership test (order-independent), NOT a naive
/// `reaches(head, body)` back-edge heuristic — the latter flags every edge
/// inside a strongly-connected component and so cannot distinguish a loop that
/// iterated from one that did not. `error` / `error_p*` sink relations are
/// excluded (they are never loop headers).
fn loop_relations(vc: &ChcVc) -> HashSet<String> {
    // Build the block-relation adjacency: body relation -> head relation.
    let mut adj: HashMap<&str, Vec<&str>> = HashMap::new();
    let mut nodes: HashSet<&str> = HashSet::new();
    for rule in &vc.rules {
        let head = rule.head.name.as_str();
        if is_error_reachable_head(head) {
            continue;
        }
        nodes.insert(head);
        if let Some(body_rel) = &rule.body.relation {
            let body = body_rel.name.as_str();
            if is_error_reachable_head(body) {
                continue;
            }
            nodes.insert(body);
            adj.entry(body).or_default().push(head);
        }
    }

    let mut cyclic: HashSet<String> = HashSet::new();
    for &start in &nodes {
        // Can `start` reach itself via at least one edge? BFS over successors.
        let mut stack: Vec<&str> = adj.get(start).cloned().unwrap_or_default();
        let mut seen: HashSet<&str> = HashSet::new();
        while let Some(node) = stack.pop() {
            if node == start {
                cyclic.insert(start.to_string());
                break;
            }
            if !seen.insert(node) {
                continue;
            }
            if let Some(succs) = adj.get(node) {
                stack.extend(succs.iter().copied());
            }
        }
    }
    cyclic
}

fn is_error_reachable_head(name: &str) -> bool {
    name == "error" || name.starts_with("error_p")
}

fn relation_sorts(vc: &ChcVc) -> HashMap<&str, &[ay_bindings::Sort]> {
    vc.relations.iter().map(|rel| (rel.name.as_str(), rel.arg_sorts.as_slice())).collect()
}

fn relation_args_match_decl(
    relation_name: &str,
    args: &[Expr],
    relation_sorts: &HashMap<&str, &[ay_bindings::Sort]>,
) -> bool {
    let Some(decl_sorts) = relation_sorts.get(relation_name) else {
        return false;
    };
    args.len() == decl_sorts.len()
        && args.iter().zip(*decl_sorts).all(|(arg, decl_sort)| arg.sort() == decl_sort)
}

/// Process-global flag (test-only) gating the straight-line discharge at the
/// MIR→CHC translation call sites.
///
/// When set, translation skips [`discharge_straightline_safety`] so that
/// encoding-inspection tests can observe the full pre-discharge VC (e.g. to
/// confirm the realloc-grow memory model retains a written heap value).
///
/// Soundness: the discharge only ever *replaces* a system it has already
/// proven UNSAT with another trivially-UNSAT system, so skipping it leaves an
/// equisatisfiable VC for the solver — it NEVER changes a verdict. A process
/// global (rather than a thread-local) is required because the rustc driver
/// runs codegen on a worker thread distinct from the test thread. The
/// inspection helper serializes via a dedicated mutex so a concurrent test
/// never observes the disabled state; even if it did, the only effect is a
/// richer-but-equisatisfiable encoding.
#[cfg(test)]
static SKIP_STRAIGHTLINE_DISCHARGE: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Set/clear the process-global straight-line discharge skip flag (test-only).
/// Returns the previous value so callers can restore it.
#[cfg(test)]
pub(in crate::codegen_ay) fn set_straightline_discharge_disabled(disabled: bool) -> bool {
    SKIP_STRAIGHTLINE_DISCHARGE.swap(disabled, std::sync::atomic::Ordering::SeqCst)
}

/// Whether the MIR→CHC translation should skip the straight-line discharge.
#[cfg(test)]
pub(in crate::codegen_ay) fn straightline_discharge_disabled() -> bool {
    SKIP_STRAIGHTLINE_DISCHARGE.load(std::sync::atomic::Ordering::SeqCst)
}

#[cfg(not(test))]
pub(in crate::codegen_ay) fn straightline_discharge_disabled() -> bool {
    // Diagnostic lever: lets a triage run observe the full pre-discharge VC.
    // Skipping the discharge is always sound (see the doc comment above).
    std::env::var("TRUST_MC_NO_STRAIGHTLINE_DISCHARGE").map(|v| v == "1").unwrap_or(false)
}

/// Discharge a syntactically-proven straight-line VC while preserving a
/// non-empty `error` obligation for downstream proof-quality accounting.
pub(in crate::codegen_ay) fn discharge_straightline_safety(vc: &mut ChcVc) -> bool {
    if has_error_rule(vc) {
        if !prove_straightline_safety(vc) {
            return false;
        }
    } else if !has_error_relation(vc) {
        return false;
    } else if !vc.properties.is_empty() {
        // SOUNDNESS (#67): the error relation is declared and check sites
        // REGISTERED per-property relations, yet zero error rules exist. The
        // error rules were LOST (silently collapsed encoding — walk abort,
        // const-prop + orphan-prune cascade), not discharged: nothing was
        // proved here, so refusing to manufacture the unsat error obligation
        // keeps the degenerate-system fail-close (translate/emitter) in
        // charge of the verdict. Live probes: loop_assigns_for_ptr_fail
        // (v23 gate), fail_missing_recursion_attr (v24 gate) — both were
        // 1-2s false Safes minted by this exact branch.
        tracing::warn!(
            properties = vc.properties.len(),
            "CHC: straightline discharge refused — registered properties but no error rules (lost checks, not proved checks)"
        );
        return false;
    }

    replace_with_unsat_error_obligation(vc);
    vc.trivially_safe_discharged = true;
    true
}

fn has_error_relation(vc: &ChcVc) -> bool {
    vc.relations.iter().any(|rel| rel.name == "error")
}

fn has_error_rule(vc: &ChcVc) -> bool {
    vc.rules.iter().any(|rule| rule.head.name.as_str() == "error")
}

fn replace_with_unsat_error_obligation(vc: &mut ChcVc) {
    if !vc.relations.iter().any(|rel| rel.name == "error") {
        vc.relations.push(RelationDecl::nullary("error"));
    }
    vc.rules.clear();
    vc.rules.push(Rule::new(
        RuleBody::new(None, vec![Expr::bool_const(false)]),
        RelationApp::new("error", Vec::new()),
    ));
}

fn initial_env(body: Option<&RelationApp>, frame: &Frame) -> Option<HashMap<String, Expr>> {
    let mut env = HashMap::new();
    let Some(body) = body else {
        return Some(env);
    };
    if body.args.len() != frame.args.len() {
        return None;
    }
    for (arg, value) in body.args.iter().zip(&frame.args) {
        let ExprValue::Var { name } = arg.value() else {
            return None;
        };
        if arg.sort() != value.sort() {
            tracing::debug!(
                var = %name,
                expected_sort = ?arg.sort(),
                actual_sort = ?value.sort(),
                "straightline proof bailed: body relation frame sort mismatch"
            );
            return None;
        }
        env.insert(name.clone(), value.clone());
    }
    Some(env)
}

fn apply_constraints(
    constraints: &trust_mc_core::constraints::Constraints,
    env: &mut HashMap<String, Expr>,
    facts: &mut PathFacts,
) -> ConstraintStatus {
    let constraints = constraints.iter().collect::<Vec<_>>();
    apply_constraint_fixpoint(&constraints, env, facts)
}

fn apply_constraint_fixpoint(
    constraints: &[&Expr],
    env: &mut HashMap<String, Expr>,
    facts: &mut PathFacts,
) -> ConstraintStatus {
    let max_passes = constraints.len().saturating_mul(4).saturating_add(8).max(16);
    for _ in 0..max_passes {
        let before_env = env.clone();
        let before_facts = facts.clone();
        let mut saw_unsupported = false;

        for constraint in constraints {
            match apply_constraint(constraint, env, facts) {
                ConstraintStatus::Feasible => {}
                ConstraintStatus::Infeasible => return ConstraintStatus::Infeasible,
                ConstraintStatus::Unsupported => saw_unsupported = true,
            }
        }

        if *env == before_env && *facts == before_facts {
            return if saw_unsupported {
                ConstraintStatus::Unsupported
            } else {
                ConstraintStatus::Feasible
            };
        }
    }

    ConstraintStatus::Unsupported
}

fn apply_constraint(
    constraint: &Expr,
    env: &mut HashMap<String, Expr>,
    facts: &mut PathFacts,
) -> ConstraintStatus {
    let Some(substituted) = substitute(constraint, env) else {
        return ConstraintStatus::Unsupported;
    };
    let Some(simplified) = simplify_with_facts(&substituted, facts) else {
        return ConstraintStatus::Unsupported;
    };
    match simplified.value() {
        ExprValue::BoolConst(false) => return ConstraintStatus::Infeasible,
        ExprValue::BoolConst(true) => {}
        ExprValue::Var { name } if simplified.sort().is_bool() => {
            return bind_env_var(env, name, Expr::bool_const(true));
        }
        ExprValue::And(children) => {
            let children = children.iter().collect::<Vec<_>>();
            return apply_constraint_fixpoint(&children, env, facts);
        }
        ExprValue::Eq(lhs, rhs) => match (lhs.value(), rhs.value()) {
            (ExprValue::Var { name }, _) if !expr_mentions_var(rhs, name) => {
                if lhs.sort() != rhs.sort() {
                    return ConstraintStatus::Unsupported;
                }
                return bind_env_var(env, name, rhs.clone());
            }
            (_, ExprValue::Var { name }) if !expr_mentions_var(lhs, name) => {
                if lhs.sort() != rhs.sort() {
                    return ConstraintStatus::Unsupported;
                }
                return bind_env_var(env, name, lhs.clone());
            }
            _ => {}
        },
        ExprValue::BvULt(lhs, rhs) => {
            if let Some(status) = record_unsigned_upper_bound(lhs, rhs, facts) {
                return status;
            }
        }
        ExprValue::Not(inner) => {
            if let ExprValue::Eq(lhs, rhs) = inner.value() {
                facts.add_disequality(lhs.clone(), rhs.clone());
                return ConstraintStatus::Feasible;
            }
            if let ExprValue::Var { name } = inner.value()
                && inner.sort().is_bool()
            {
                return bind_env_var(env, name, Expr::bool_const(false));
            }
        }
        _ => {}
    }
    ConstraintStatus::Feasible
}

fn record_unsigned_upper_bound(
    lhs: &Expr,
    rhs: &Expr,
    facts: &mut PathFacts,
) -> Option<ConstraintStatus> {
    if lhs.sort() != rhs.sort() || !lhs.sort().is_bitvec() {
        return Some(ConstraintStatus::Unsupported);
    }
    let (bound, width) = bv_const_u128(rhs)?;
    if bound == 0 {
        return Some(ConstraintStatus::Infeasible);
    }
    facts.add_unsigned_upper_bound(lhs.clone(), bound, width);
    Some(ConstraintStatus::Feasible)
}

fn bind_env_var(env: &mut HashMap<String, Expr>, name: &str, value: Expr) -> ConstraintStatus {
    if let Some(existing) = env.get(name) {
        let Some(eq) = simplify(&existing.clone().eq(value)) else {
            return ConstraintStatus::Unsupported;
        };
        return match eq.value() {
            ExprValue::BoolConst(true) => ConstraintStatus::Feasible,
            ExprValue::BoolConst(false) => ConstraintStatus::Infeasible,
            _ => ConstraintStatus::Unsupported,
        };
    }
    env.insert(name.to_string(), value);
    ConstraintStatus::Feasible
}

fn substitute(expr: &Expr, env: &HashMap<String, Expr>) -> Option<Expr> {
    substitute_inner(expr, env, &mut HashSet::new())
}

fn substitute_inner(
    expr: &Expr,
    env: &HashMap<String, Expr>,
    resolving: &mut HashSet<String>,
) -> Option<Expr> {
    let _depth_guard = StraightlineDepthGuard::enter()?;
    match expr.value() {
        ExprValue::Var { name } => {
            let Some(replacement) = env.get(name) else {
                return Some(expr.clone());
            };
            if !resolving.insert(name.clone()) {
                return Some(expr.clone());
            }
            let resolved = substitute_inner(replacement, env, resolving);
            resolving.remove(name);
            let resolved = resolved?;
            if resolved.sort() != expr.sort() {
                tracing::debug!(
                    var = %name,
                    expected_sort = ?expr.sort(),
                    actual_sort = ?resolved.sort(),
                    "straightline proof bailed: substitution sort mismatch"
                );
                return None;
            }
            Some(resolved)
        }
        _ => {
            let mut children = Vec::new();
            for child in expr.children() {
                children.push(substitute_inner(&child, env, resolving)?);
            }
            Some(rebuild_with_children(expr, children))
        }
    }
}

fn simplify(expr: &Expr) -> Option<Expr> {
    simplify_with_facts(expr, &PathFacts::default())
}

fn simplify_with_facts(expr: &Expr, facts: &PathFacts) -> Option<Expr> {
    let _depth_guard = StraightlineDepthGuard::enter()?;
    match expr.value() {
        ExprValue::Not(inner) => {
            let inner = simplify_with_facts(inner, facts)?;
            match inner.value() {
                ExprValue::BoolConst(value) => Some(Expr::bool_const(!value)),
                ExprValue::Not(double) => simplify_with_facts(double, facts),
                _ => inner.try_not().ok(),
            }
        }
        ExprValue::Eq(lhs, rhs) => simplify_eq_with_facts(lhs, rhs, facts),
        ExprValue::And(children) => simplify_bool_nary(children, true, facts),
        ExprValue::Or(children) => simplify_bool_nary(children, false, facts),
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let cond = simplify_with_facts(cond, facts)?;
            match cond.value() {
                ExprValue::BoolConst(true) => simplify_with_facts(then_expr, facts),
                ExprValue::BoolConst(false) => simplify_with_facts(else_expr, facts),
                _ => simplify_ite_with_facts(cond, then_expr, else_expr, facts),
            }
        }
        value if is_bv_simplifiable(value) => simplify_bv_expr(expr, facts),
        ExprValue::Select { array, index } => simplify_select(array, index, facts),
        ExprValue::Store { array, index, value } => {
            let array = simplify_with_facts(array, facts)?;
            let index = simplify_with_facts(index, facts)?;
            let value = simplify_with_facts(value, facts)?;
            Some(array.store(index, value))
        }
        ExprValue::ConstArray { index_sort, value } => {
            let value = simplify_with_facts(value, facts)?;
            Some(Expr::const_array(index_sort.clone(), value))
        }
        ExprValue::DatatypeSelector { datatype_name, selector_name, expr: target } => {
            simplify_datatype_selector(expr, datatype_name, selector_name, target, facts)
        }
        ExprValue::DatatypeTester { datatype_name, constructor_name, expr: target } => {
            simplify_datatype_tester(datatype_name, constructor_name, target, facts)
        }
        _ => simplify_rebuilt_children(expr, facts),
    }
}

fn is_bv_simplifiable(value: &ExprValue) -> bool {
    matches!(
        value,
        ExprValue::BvAdd(_, _)
            | ExprValue::BvSub(_, _)
            | ExprValue::BvMul(_, _)
            | ExprValue::BvAnd(_, _)
            | ExprValue::BvOr(_, _)
            | ExprValue::BvXor(_, _)
            | ExprValue::BvURem(_, _)
            | ExprValue::BvConcat(_, _)
            | ExprValue::BvExtract { .. }
            | ExprValue::BvZeroExtend { .. }
            | ExprValue::BvUGe(_, _)
            | ExprValue::BvUGt(_, _)
            | ExprValue::BvULe(_, _)
            | ExprValue::BvULt(_, _)
            | ExprValue::BvSGe(_, _)
            | ExprValue::BvSGt(_, _)
            | ExprValue::BvSLe(_, _)
            | ExprValue::BvSLt(_, _)
            | ExprValue::BvMulNoOverflowUnsigned(_, _)
    )
}

fn simplify_bv_expr(expr: &Expr, facts: &PathFacts) -> Option<Expr> {
    match expr.value() {
        ExprValue::BvAdd(lhs, rhs) => simplify_bv_binop(
            lhs,
            rhs,
            facts,
            |l, r, width| Some(l.wrapping_add(r) & bv_mask(width)),
            |l, r| l.try_bvadd(r).ok(),
        ),
        ExprValue::BvSub(lhs, rhs) => simplify_bv_binop(
            lhs,
            rhs,
            facts,
            |l, r, width| Some(l.wrapping_sub(r) & bv_mask(width)),
            |l, r| l.try_bvsub(r).ok(),
        ),
        ExprValue::BvAnd(lhs, rhs) => {
            simplify_bv_binop(lhs, rhs, facts, |l, r, _| Some(l & r), |l, r| l.try_bvand(r).ok())
        }
        ExprValue::BvOr(lhs, rhs) => {
            simplify_bv_binop(lhs, rhs, facts, |l, r, _| Some(l | r), |l, r| l.try_bvor(r).ok())
        }
        ExprValue::BvXor(lhs, rhs) => {
            simplify_bv_binop(lhs, rhs, facts, |l, r, _| Some(l ^ r), |l, r| l.try_bvxor(r).ok())
        }
        ExprValue::BvURem(lhs, rhs) => simplify_bv_binop(
            lhs,
            rhs,
            facts,
            // `.then(|| ..)` NOT `.then_some(..)`: then_some eagerly evaluates
            // `l % r` before the r != 0 check, panicking the host compiler on a
            // folded zero divisor reachable only under an assumed-away path
            // (gcd_* family: requires(y != 0) is an assumption, not a fact here).
            |l, r, _| (r != 0).then(|| l % r),
            |l, r| l.try_bvurem(r).ok(),
        ),
        ExprValue::BvMul(lhs, rhs) => simplify_bv_binop(
            lhs,
            rhs,
            facts,
            |l, r, width| l.checked_mul(r).map(|value| value & bv_mask(width)),
            |l, r| l.try_bvmul(r).ok(),
        ),
        ExprValue::BvConcat(lhs, rhs) => simplify_bv_concat(lhs, rhs, facts),
        ExprValue::BvZeroExtend { expr, extra_bits } => {
            simplify_bv_zero_extend(expr, *extra_bits, facts)
        }
        ExprValue::BvExtract { expr, high, low } => simplify_bv_extract(expr, *high, *low, facts),
        ExprValue::BvMulNoOverflowUnsigned(lhs, rhs) => {
            simplify_bv_mul_no_overflow_unsigned(lhs, rhs, facts)
        }
        _ => simplify_bv_cmp_expr(expr, facts),
    }
}

fn simplify_bv_cmp_expr(expr: &Expr, facts: &PathFacts) -> Option<Expr> {
    match expr.value() {
        ExprValue::BvUGe(lhs, rhs) => {
            simplify_bv_cmp(lhs, rhs, facts, |l, r| l >= r, |l, r| l.try_bvuge(r).ok())
        }
        ExprValue::BvUGt(lhs, rhs) => {
            simplify_bv_cmp(lhs, rhs, facts, |l, r| l > r, |l, r| l.try_bvugt(r).ok())
        }
        ExprValue::BvULe(lhs, rhs) => {
            simplify_bv_cmp(lhs, rhs, facts, |l, r| l <= r, |l, r| l.try_bvule(r).ok())
        }
        ExprValue::BvULt(lhs, rhs) => {
            simplify_bv_cmp(lhs, rhs, facts, |l, r| l < r, |l, r| l.try_bvult(r).ok())
        }
        ExprValue::BvSGe(lhs, rhs) => {
            simplify_bv_signed_cmp(lhs, rhs, facts, |ord| ord >= 0, |l, r| l.try_bvsge(r).ok())
        }
        ExprValue::BvSGt(lhs, rhs) => {
            simplify_bv_signed_cmp(lhs, rhs, facts, |ord| ord > 0, |l, r| l.try_bvsgt(r).ok())
        }
        ExprValue::BvSLe(lhs, rhs) => {
            simplify_bv_signed_cmp(lhs, rhs, facts, |ord| ord <= 0, |l, r| l.try_bvsle(r).ok())
        }
        ExprValue::BvSLt(lhs, rhs) => {
            simplify_bv_signed_cmp(lhs, rhs, facts, |ord| ord < 0, |l, r| l.try_bvslt(r).ok())
        }
        _ => None,
    }
}

fn simplify_eq_with_facts(lhs: &Expr, rhs: &Expr, facts: &PathFacts) -> Option<Expr> {
    let lhs = simplify_with_facts(lhs, facts)?;
    let rhs = simplify_with_facts(rhs, facts)?;
    if lhs == rhs {
        return Some(Expr::bool_const(true));
    }
    if facts.are_disequal(&lhs, &rhs) {
        return Some(Expr::bool_const(false));
    }
    if let Some(simplified) = simplify_bool_const_eq(&lhs, &rhs, facts) {
        return Some(simplified);
    }
    if let Some(simplified) = simplify_bool_const_eq(&rhs, &lhs, facts) {
        return Some(simplified);
    }
    if let Some(simplified) = simplify_bool_bit_ite_eq(&lhs, &rhs, facts) {
        return Some(simplified);
    }
    if let Some(simplified) = simplify_bool_bit_ite_eq(&rhs, &lhs, facts) {
        return Some(simplified);
    }
    match (lhs.value(), rhs.value()) {
        (ExprValue::BoolConst(a), ExprValue::BoolConst(b)) => Some(Expr::bool_const(a == b)),
        (
            ExprValue::BitVecConst { value: lhs_value, width: lhs_width },
            ExprValue::BitVecConst { value: rhs_value, width: rhs_width },
        ) => {
            if lhs_width != rhs_width {
                return None;
            }
            Some(Expr::bool_const(lhs_value == rhs_value))
        }
        _ => lhs.try_eq(rhs).ok(),
    }
}

fn simplify_bool_const_eq(expr: &Expr, constant: &Expr, facts: &PathFacts) -> Option<Expr> {
    let ExprValue::BoolConst(value) = constant.value() else {
        return None;
    };
    if !expr.sort().is_bool() {
        return None;
    }
    if *value { Some(expr.clone()) } else { simplify_with_facts(&expr.clone().not(), facts) }
}

fn simplify_bool_bit_ite_eq(ite_expr: &Expr, rhs: &Expr, facts: &PathFacts) -> Option<Expr> {
    let ExprValue::Ite { cond, then_expr, else_expr } = ite_expr.value() else {
        return None;
    };
    let (then_value, then_width) = bv_const_u128(then_expr)?;
    let (else_value, else_width) = bv_const_u128(else_expr)?;
    let (rhs_value, rhs_width) = bv_const_u128(rhs)?;
    if then_width != else_width || then_width != rhs_width {
        return None;
    }

    let cond = simplify_with_facts(cond, facts)?;
    match (then_value, else_value, rhs_value) {
        (1, 0, 1) | (0, 1, 0) => Some(cond),
        (1, 0, 0) | (0, 1, 1) => simplify_with_facts(&cond.not(), facts),
        (1, 0, _) | (0, 1, _) => Some(Expr::bool_const(false)),
        _ => None,
    }
}

fn simplify_ite_with_facts(
    cond: Expr,
    then_expr: &Expr,
    else_expr: &Expr,
    facts: &PathFacts,
) -> Option<Expr> {
    let then_expr = simplify_with_facts(then_expr, facts)?;
    let else_expr = simplify_with_facts(else_expr, facts)?;
    if then_expr == else_expr {
        return Some(then_expr);
    }
    if then_expr.sort().is_bool() && else_expr.sort().is_bool() {
        return simplify_bool_ite(cond, then_expr, else_expr, facts);
    }
    Expr::try_ite(cond, then_expr, else_expr).ok()
}

fn simplify_bool_ite(
    cond: Expr,
    then_expr: Expr,
    else_expr: Expr,
    facts: &PathFacts,
) -> Option<Expr> {
    match (then_expr.value(), else_expr.value()) {
        (ExprValue::BoolConst(true), ExprValue::BoolConst(false)) => Some(cond),
        (ExprValue::BoolConst(false), ExprValue::BoolConst(true)) => {
            simplify_with_facts(&cond.not(), facts)
        }
        (ExprValue::BoolConst(false), _) => {
            let expr = Expr::try_and_many(vec![cond.not(), else_expr]).ok()?;
            simplify_with_facts(&expr, facts)
        }
        (ExprValue::BoolConst(true), _) => {
            let expr = Expr::try_or_many(vec![cond, else_expr]).ok()?;
            simplify_with_facts(&expr, facts)
        }
        (_, ExprValue::BoolConst(false)) => {
            let expr = Expr::try_and_many(vec![cond, then_expr]).ok()?;
            simplify_with_facts(&expr, facts)
        }
        (_, ExprValue::BoolConst(true)) => {
            let expr = Expr::try_or_many(vec![cond.not(), then_expr]).ok()?;
            simplify_with_facts(&expr, facts)
        }
        _ => Expr::try_ite(cond, then_expr, else_expr).ok(),
    }
}

fn simplify_bool_nary(children: &[Expr], is_and: bool, facts: &PathFacts) -> Option<Expr> {
    let mut kept = Vec::new();
    for child in children {
        let child = simplify_with_facts(child, facts)?;
        match child.value() {
            ExprValue::BoolConst(value) if *value != is_and => {
                return Some(Expr::bool_const(!is_and));
            }
            ExprValue::BoolConst(_) => {}
            ExprValue::And(nested) if is_and => kept.extend(nested.iter().cloned()),
            ExprValue::Or(nested) if !is_and => kept.extend(nested.iter().cloned()),
            _ => kept.push(child),
        }
    }
    match kept.len() {
        0 => Some(Expr::bool_const(is_and)),
        1 => kept.pop(),
        _ if is_and => Expr::try_and_many(kept).ok(),
        _ => Expr::try_or_many(kept).ok(),
    }
}

fn simplify_select(array: &Expr, index: &Expr, facts: &PathFacts) -> Option<Expr> {
    // Simplify the array and index ONCE up front, then walk the (now fully
    // simplified) Store/ConstArray chain without re-simplifying it. The old
    // code re-ran `simplify_with_facts(array)` at every level of the recursion
    // (via a self-call on `base`), re-walking the whole store chain each time —
    // O(depth^2) on the deep memory-array selects that raw-pointer deref null
    // obligations inject into the VC (859f29ea5), which blew straightline
    // discharge past the harness timeout. Because `simplify_with_facts` is a
    // one-pass bottom-up rewrite (idempotent on already-simplified terms, and
    // the children of a simplified `Store`/`ConstArray` are themselves
    // simplified), skipping the redundant re-simplification is verdict-identical.
    let array = simplify_with_facts(array, facts)?;
    let index = simplify_with_facts(index, facts)?;
    select_from_simplified(&array, &index, facts)
}

/// Resolve `select(array, index)` over an already-fully-simplified `array` and
/// `index`. Precondition: both arguments (and hence, for a `Store`/`ConstArray`
/// array, every child in the store chain) are in simplified form, so no
/// argument is re-simplified here. Split out of [`simplify_select`] to make the
/// store-chain walk linear instead of quadratic.
fn select_from_simplified(array: &Expr, index: &Expr, facts: &PathFacts) -> Option<Expr> {
    let _depth_guard = StraightlineDepthGuard::enter()?;
    match array.value() {
        ExprValue::ConstArray { value, .. } => Some(value.clone()),
        ExprValue::Store { array: base, index: store_index, value } => {
            if simplify_eq_with_facts(store_index, index, facts)?.value()
                == &ExprValue::BoolConst(true)
            {
                return Some(value.clone());
            }
            if facts.are_disequal(store_index, index)
                || simplify_eq_with_facts(store_index, index, facts)?.value()
                    == &ExprValue::BoolConst(false)
            {
                return select_from_simplified(base, index, facts);
            }
            Some(array.clone().select(index.clone()))
        }
        _ => Some(array.clone().select(index.clone())),
    }
}

fn simplify_bv_concat(lhs: &Expr, rhs: &Expr, facts: &PathFacts) -> Option<Expr> {
    let lhs = simplify_with_facts(lhs, facts)?;
    let rhs = simplify_with_facts(rhs, facts)?;
    if let (Some((lhs_value, lhs_width)), Some((rhs_value, rhs_width))) =
        (bv_const_u128(&lhs), bv_const_u128(&rhs))
    {
        let width = lhs_width.checked_add(rhs_width)?;
        if width > 128 {
            return None;
        }
        return Some(Expr::bitvec_const((lhs_value << rhs_width) | rhs_value, width));
    }
    lhs.try_concat(rhs).ok()
}

fn simplify_bv_zero_extend(expr: &Expr, extra_bits: u32, facts: &PathFacts) -> Option<Expr> {
    let expr = simplify_with_facts(expr, facts)?;
    let input_width = expr.sort().bitvec_sort()?.width;
    let output_width = input_width.checked_add(extra_bits)?;
    if output_width > 128 {
        return expr.try_zero_extend(extra_bits).ok();
    }
    if let Some((value, _)) = bv_const_u128(&expr) {
        return Some(Expr::bitvec_const(value, output_width));
    }
    expr.try_zero_extend(extra_bits).ok()
}

fn simplify_bv_extract(expr: &Expr, high: u32, low: u32, facts: &PathFacts) -> Option<Expr> {
    let expr = simplify_with_facts(expr, facts)?;
    let width = expr.sort().bitvec_sort()?.width;
    if high < low || high >= width || high >= 128 {
        return None;
    }
    let Some((value, _)) = bv_const_u128(&expr) else {
        return expr.try_extract(high, low).ok();
    };
    let out_width = high - low + 1;
    Some(Expr::bitvec_const((value >> low) & bv_mask(out_width), out_width))
}

fn simplify_bv_mul_no_overflow_unsigned(lhs: &Expr, rhs: &Expr, facts: &PathFacts) -> Option<Expr> {
    let lhs = simplify_with_facts(lhs, facts)?;
    let rhs = simplify_with_facts(rhs, facts)?;
    if lhs.sort() != rhs.sort() || !lhs.sort().is_bitvec() {
        return None;
    }
    let width = lhs.sort().bitvec_sort()?.width;
    if width == 0 || width > 128 {
        return lhs.try_bvmul_no_overflow_unsigned(rhs).ok();
    }
    if let (Some((lhs_value, lhs_width)), Some((rhs_value, rhs_width))) =
        (bv_const_u128(&lhs), bv_const_u128(&rhs))
    {
        if lhs_width != rhs_width {
            return None;
        }
        return Some(Expr::bool_const(unsigned_mul_fits_width(lhs_value, rhs_value, width)));
    }
    if let Some((constant, variable)) = one_const_one_expr(&lhs, &rhs)
        && unsigned_bound_proves_mul_no_overflow(variable, constant, width, facts)
    {
        return Some(Expr::bool_const(true));
    }
    lhs.try_bvmul_no_overflow_unsigned(rhs).ok()
}

fn one_const_one_expr<'a>(lhs: &'a Expr, rhs: &'a Expr) -> Option<(u128, &'a Expr)> {
    if let Some((value, _)) = bv_const_u128(lhs) {
        return Some((value, rhs));
    }
    if let Some((value, _)) = bv_const_u128(rhs) {
        return Some((value, lhs));
    }
    None
}

fn unsigned_bound_proves_mul_no_overflow(
    variable: &Expr,
    constant: u128,
    width: u32,
    facts: &PathFacts,
) -> bool {
    if constant == 0 {
        return true;
    }
    let Some((exclusive_bound, bound_width)) = facts.unsigned_upper_bound(variable) else {
        return false;
    };
    if bound_width != width {
        return false;
    }
    let max_value = exclusive_bound.saturating_sub(1);
    unsigned_mul_fits_width(max_value, constant, width)
}

fn unsigned_mul_fits_width(lhs: u128, rhs: u128, width: u32) -> bool {
    let max_value = bv_mask(width);
    lhs.checked_mul(rhs).is_some_and(|product| product <= max_value)
}

fn simplify_datatype_selector(
    expr: &Expr,
    datatype_name: &str,
    selector_name: &str,
    target: &Expr,
    facts: &PathFacts,
) -> Option<Expr> {
    let selected_from = simplify_with_facts(target, facts)?;
    if let ExprValue::DatatypeConstructor { datatype_name: ctor_dt_name, constructor_name, args } =
        selected_from.value()
    {
        if ctor_dt_name != datatype_name {
            return None;
        }
        let dt = selected_from.sort().datatype_sort()?;
        let Some(ctor) = dt.constructors.iter().find(|ctor| ctor.name == *constructor_name) else {
            return Some(rebuild_with_children(expr, vec![selected_from]));
        };
        let Some(field_idx) = ctor.fields.iter().position(|field| field.name == *selector_name)
        else {
            return Some(rebuild_with_children(expr, vec![selected_from]));
        };
        return args
            .get(field_idx)
            .cloned()
            .or_else(|| Some(rebuild_with_children(expr, vec![selected_from])));
    }
    if let ExprValue::Ite { cond, then_expr, else_expr } = selected_from.value() {
        let then_selected = then_expr.clone().try_field_select(
            datatype_name.to_owned(),
            selector_name.to_owned(),
            expr.sort().clone(),
        );
        let else_selected = else_expr.clone().try_field_select(
            datatype_name.to_owned(),
            selector_name.to_owned(),
            expr.sort().clone(),
        );
        if let (Ok(then_selected), Ok(else_selected)) = (then_selected, else_selected) {
            let selected = Expr::try_ite(
                simplify_with_facts(cond, facts)?,
                simplify_with_facts(&then_selected, facts)?,
                simplify_with_facts(&else_selected, facts)?,
            )
            .ok()?;
            return simplify_with_facts(&selected, facts);
        }
    }
    Some(rebuild_with_children(expr, vec![selected_from]))
}

fn simplify_datatype_tester(
    datatype_name: &str,
    constructor_name: &str,
    target: &Expr,
    facts: &PathFacts,
) -> Option<Expr> {
    let tested = simplify_with_facts(target, facts)?;
    if let ExprValue::DatatypeConstructor {
        datatype_name: ctor_dt_name,
        constructor_name: ctor_name,
        ..
    } = tested.value()
    {
        if ctor_dt_name != datatype_name {
            return None;
        }
        return Some(Expr::bool_const(ctor_name == constructor_name));
    }
    if let ExprValue::Ite { cond, then_expr, else_expr } = tested.value() {
        let tested = Expr::try_ite(
            simplify_with_facts(cond, facts)?,
            simplify_datatype_tester(datatype_name, constructor_name, then_expr, facts)?,
            simplify_datatype_tester(datatype_name, constructor_name, else_expr, facts)?,
        )
        .ok()?;
        return simplify_with_facts(&tested, facts);
    }
    tested.try_is_constructor(datatype_name.to_owned(), constructor_name.to_owned()).ok()
}

fn simplify_rebuilt_children(expr: &Expr, facts: &PathFacts) -> Option<Expr> {
    let mut children = Vec::new();
    for child in expr.children() {
        children.push(simplify_with_facts(&child, facts)?);
    }
    Some(rebuild_with_children(expr, children))
}

fn simplify_bv_binop(
    lhs: &Expr,
    rhs: &Expr,
    facts: &PathFacts,
    op: impl FnOnce(u128, u128, u32) -> Option<u128>,
    rebuild: impl FnOnce(Expr, Expr) -> Option<Expr>,
) -> Option<Expr> {
    let lhs = simplify_with_facts(lhs, facts)?;
    let rhs = simplify_with_facts(rhs, facts)?;
    if lhs.sort() != rhs.sort() || !lhs.sort().is_bitvec() {
        return None;
    }
    if let (Some((lhs_value, lhs_width)), Some((rhs_value, rhs_width))) =
        (bv_const_u128(&lhs), bv_const_u128(&rhs))
    {
        if lhs_width != rhs_width {
            return None;
        }
        if let Some(value) = op(lhs_value, rhs_value, lhs_width) {
            return Some(Expr::bitvec_const(value, lhs_width));
        }
    }
    rebuild(lhs, rhs)
}

fn simplify_bv_cmp(
    lhs: &Expr,
    rhs: &Expr,
    facts: &PathFacts,
    op: impl FnOnce(u128, u128) -> bool,
    rebuild: impl FnOnce(Expr, Expr) -> Option<Expr>,
) -> Option<Expr> {
    let lhs = simplify_with_facts(lhs, facts)?;
    let rhs = simplify_with_facts(rhs, facts)?;
    if lhs.sort() != rhs.sort() || !lhs.sort().is_bitvec() {
        return None;
    }
    if let (Some((lhs_value, lhs_width)), Some((rhs_value, rhs_width))) =
        (bv_const_u128(&lhs), bv_const_u128(&rhs))
    {
        if lhs_width != rhs_width {
            return None;
        }
        return Some(Expr::bool_const(op(lhs_value, rhs_value)));
    }
    rebuild(lhs, rhs)
}

fn simplify_bv_signed_cmp(
    lhs: &Expr,
    rhs: &Expr,
    facts: &PathFacts,
    op: impl FnOnce(i8) -> bool,
    rebuild: impl FnOnce(Expr, Expr) -> Option<Expr>,
) -> Option<Expr> {
    let lhs = simplify_with_facts(lhs, facts)?;
    let rhs = simplify_with_facts(rhs, facts)?;
    if lhs.sort() != rhs.sort() || !lhs.sort().is_bitvec() {
        return None;
    }
    if let (Some((lhs_value, lhs_width)), Some((rhs_value, rhs_width))) =
        (bv_const_u128(&lhs), bv_const_u128(&rhs))
    {
        if lhs_width != rhs_width || lhs_width == 0 {
            return None;
        }
        return Some(Expr::bool_const(op(signed_bv_order(lhs_value, rhs_value, lhs_width))));
    }
    rebuild(lhs, rhs)
}

fn signed_bv_order(lhs: u128, rhs: u128, width: u32) -> i8 {
    let sign_bit = 1u128 << (width - 1);
    let lhs_negative = lhs & sign_bit != 0;
    let rhs_negative = rhs & sign_bit != 0;
    match (lhs_negative, rhs_negative) {
        (true, false) => -1,
        (false, true) => 1,
        _ if lhs < rhs => -1,
        _ if lhs > rhs => 1,
        _ => 0,
    }
}

fn bv_const_u128(expr: &Expr) -> Option<(u128, u32)> {
    let ExprValue::BitVecConst { value, width } = expr.value() else {
        return None;
    };
    if *width > 128 {
        return None;
    }
    Some((u128::try_from(value.clone()).ok()? & bv_mask(*width), *width))
}

fn bv_mask(width: u32) -> u128 {
    if width == 0 {
        0
    } else if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

fn expr_mentions_var(expr: &Expr, target: &str) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if matches!(node.value(), ExprValue::Var { name } if name == target) {
            return true;
        }
        stack.extend(node.children());
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_bindings::Sort;
    use trust_mc_core::chc::ChcQuery;

    fn apply_constraint_without_facts(
        constraint: &Expr,
        env: &mut HashMap<String, Expr>,
    ) -> ConstraintStatus {
        apply_constraint(constraint, env, &mut PathFacts::default())
    }

    #[test]
    fn substitute_follows_transitive_equalities() {
        let sort = Sort::bitvec(64);
        let x = Expr::var("x", sort.clone());
        let y = Expr::var("y", sort);
        let one = Expr::bitvec_const(1u64, 64);
        let mut env = HashMap::new();

        assert_eq!(
            apply_constraint_without_facts(&x.clone().eq(y.clone()), &mut env),
            ConstraintStatus::Feasible
        );
        assert_eq!(
            apply_constraint_without_facts(&y.eq(one.clone()), &mut env),
            ConstraintStatus::Feasible
        );

        let substituted = substitute(&x, &env).expect("well-sorted substitution");
        assert_eq!(simplify(&substituted), Some(one));
    }

    #[test]
    fn substitution_sort_mismatch_bails_without_panic() {
        let x8 = Expr::var("x", Sort::bitvec(8));
        let y8 = Expr::var("y", Sort::bitvec(8));
        let y64 = Expr::var("wide_y", Sort::bitvec(64));
        let mut env = HashMap::new();
        env.insert("x".to_string(), y64);

        assert_eq!(
            apply_constraint_without_facts(&x8.eq(y8), &mut env),
            ConstraintStatus::Unsupported
        );
    }

    #[test]
    fn mixed_width_eq_simplification_bails_without_panic() {
        let x8 = Expr::var("x", Sort::bitvec(8));
        let y8 = Expr::var("y", Sort::bitvec(8));
        let y64 = Expr::var("wide_y", Sort::bitvec(64));
        let original = x8.clone().eq(y8);
        let mixed = rebuild_with_children(&original, vec![x8, y64]);

        assert_eq!(simplify(&mixed), None);
    }

    #[test]
    fn relation_frame_sort_mismatch_bails_without_panic() {
        let x8 = Expr::var("x", Sort::bitvec(8));
        let x64 = Expr::var("x64", Sort::bitvec(64));
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(64)]));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::init(
            x64.clone().eq(Expr::bitvec_const(1u64, 64)),
            RelationApp::new("bb0", vec![x64]),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("bb0", vec![x8.clone()])),
                vec![x8.eq(Expr::bitvec_const(1u8, 8))],
            ),
            RelationApp::new("error", Vec::new()),
        ));

        assert!(!prove_straightline_safety(&vc));
    }

    #[test]
    fn concrete_bitvec_disequality_is_infeasible() {
        let zero = Expr::bitvec_const(0u8, 8);
        let one = Expr::bitvec_const(1u8, 8);
        let mut env = HashMap::new();

        assert_eq!(
            apply_constraint_without_facts(&zero.eq(one), &mut env),
            ConstraintStatus::Infeasible
        );
    }

    #[test]
    fn signed_bitvec_comparisons_simplify_constants() {
        let minus_one = Expr::bitvec_const(0xffu8, 8);
        let zero = Expr::bitvec_const(0u8, 8);
        let one = Expr::bitvec_const(1u8, 8);

        assert_eq!(simplify(&minus_one.clone().bvslt(zero.clone())), Some(Expr::bool_const(true)));
        assert_eq!(simplify(&zero.clone().bvslt(minus_one.clone())), Some(Expr::bool_const(false)));
        assert_eq!(simplify(&one.clone().bvsge(zero.clone())), Some(Expr::bool_const(true)));
        assert_eq!(simplify(&minus_one.bvsle(one)), Some(Expr::bool_const(true)));
    }

    #[test]
    fn encoded_bool_ite_equality_simplifies_to_boolean_condition() {
        let flag = Expr::var("flag", Sort::bool());
        let encoded =
            Expr::try_ite(flag.clone(), Expr::bitvec_const(1u8, 64), Expr::bitvec_const(0u8, 64))
                .expect("well-sorted encoded bool");

        assert_eq!(simplify(&encoded.clone().eq(Expr::bitvec_const(1u8, 64))), Some(flag.clone()));
        assert_eq!(simplify(&encoded.eq(Expr::bitvec_const(0u8, 64))), Some(flag.not()));
    }

    #[test]
    fn datatype_tester_simplifies_constructor_and_ite() {
        let opt_sort = Sort::enum_type(
            "ProofOptU8",
            vec![("SomeProofOptU8", vec![("value", Sort::bitvec(8))]), ("NoneProofOptU8", vec![])],
        );
        let flag = Expr::var("flag", Sort::bool());
        let some = Expr::datatype_constructor(
            "ProofOptU8",
            "SomeProofOptU8",
            vec![Expr::bitvec_const(7u8, 8)],
            opt_sort.clone(),
        );
        let none =
            Expr::datatype_constructor("ProofOptU8", "NoneProofOptU8", vec![], opt_sort.clone());
        let branch =
            Expr::try_ite(flag.clone(), some.clone(), none).expect("well-sorted option branch");

        assert_eq!(
            simplify(&some.is_constructor("ProofOptU8", "SomeProofOptU8")),
            Some(Expr::bool_const(true))
        );
        assert_eq!(simplify(&branch.is_constructor("ProofOptU8", "SomeProofOptU8")), Some(flag));
    }

    #[test]
    fn option_like_iter_next_shape_proves_error_unreachable() {
        let opt_sort = Sort::enum_type(
            "ProofNextOptU32",
            vec![
                ("SomeProofNextOptU32", vec![("value", Sort::bitvec(32))]),
                ("NoneProofNextOptU32", vec![]),
            ],
        );
        let cond = Expr::var("cond", Sort::bool());
        let cond_in = Expr::var("cond_in", Sort::bool());
        let result = Expr::var("result", Sort::bool());
        let result_in = Expr::var("result_in", Sort::bool());
        let some = Expr::datatype_constructor(
            "ProofNextOptU32",
            "SomeProofNextOptU32",
            vec![Expr::bitvec_const(0u8, 32)],
            opt_sort.clone(),
        );
        let none =
            Expr::datatype_constructor("ProofNextOptU32", "NoneProofNextOptU32", vec![], opt_sort);
        let next_value =
            Expr::try_ite(cond_in.clone(), some, none).expect("well-sorted next value");
        let is_some = next_value.clone().is_constructor("ProofNextOptU32", "SomeProofNextOptU32");
        let payload = next_value.field_select("ProofNextOptU32", "value", Sort::bitvec(32));
        let encoded_is_some =
            Expr::try_ite(is_some, Expr::bitvec_const(1u8, 64), Expr::bitvec_const(0u8, 64))
                .expect("well-sorted encoded discriminant");
        let computed = Expr::try_ite(
            encoded_is_some.eq(Expr::bitvec_const(0u8, 64)),
            Expr::bool_const(false),
            payload.eq(Expr::bitvec_const(0u8, 32)),
        )
        .expect("well-sorted postcondition");

        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("after_next", vec![Sort::bool()]));
        vc.add_relation(RelationDecl::new("checked", vec![Sort::bool()]));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::init(
            cond.clone().eq(Expr::bool_const(true)),
            RelationApp::new("after_next", vec![cond]),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("after_next", vec![cond_in])),
                vec![result.clone().eq(computed)],
            ),
            RelationApp::new("checked", vec![result]),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("checked", vec![result_in.clone()])),
                vec![result_in.not()],
            ),
            RelationApp::new("error", Vec::new()),
        ));

        assert!(prove_straightline_safety(&vc));
    }

    #[test]
    fn unsigned_upper_bound_proves_mul_no_overflow_error_unreachable() {
        let x = Expr::var("x", Sort::bitvec(32));
        let v = Expr::var("v", Sort::bitvec(32));
        let hundred = Expr::bitvec_const(100u8, 32);
        let two = Expr::bitvec_const(2u8, 32);
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("after_assume", vec![Sort::bitvec(32)]));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::init(
            x.clone().bvult(hundred),
            RelationApp::new("after_assume", vec![x]),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("after_assume", vec![v.clone()])),
                vec![v.bvmul_no_overflow_unsigned(two).not()],
            ),
            RelationApp::new("error", Vec::new()),
        ));

        assert!(prove_straightline_safety(&vc));
    }

    #[test]
    fn signed_loop_exit_guard_error_is_infeasible() {
        let i = Expr::var("i", Sort::bitvec(32));
        let end = Expr::var("end", Sort::bitvec(32));
        let has_next = Expr::var("has_next", Sort::bool());
        let five = Expr::bitvec_const(5u8, 32);
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("range_exit", vec![Sort::bitvec(32), Sort::bitvec(32)]));
        vc.add_relation(RelationDecl::new("checked", vec![Sort::bool()]));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::init(
            Expr::bool_const(true),
            RelationApp::new("range_exit", vec![five.clone(), five.clone()]),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("range_exit", vec![i.clone(), end.clone()])),
                vec![has_next.clone().eq(i.bvslt(end))],
            ),
            RelationApp::new("checked", vec![has_next.clone()]),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("checked", vec![has_next.clone()])),
                vec![has_next],
            ),
            RelationApp::new("error", Vec::new()),
        ));

        assert!(prove_straightline_safety(&vc));
    }

    #[test]
    fn array_store_hit_error_is_infeasible() {
        let key_sort = Sort::bitvec(32);
        let value_sort = Sort::bitvec(32);
        let data_sort = Sort::array(key_sort.clone(), value_sort.clone());
        let present_sort = Sort::array(key_sort.clone(), Sort::bool());
        let data = Expr::var("data", data_sort.clone());
        let present = Expr::var("present", present_sort.clone());
        let i = Expr::var("i", key_sort.clone());
        let value = Expr::var("value", value_sort.clone());
        let empty_data = Expr::const_array(key_sort.clone(), Expr::bitvec_const(0u8, 32));
        let empty_present = Expr::const_array(key_sort.clone(), Expr::bool_const(false));
        let stored_data = empty_data.store(i.clone(), value.clone());
        let stored_present = empty_present.store(i.clone(), Expr::bool_const(true));
        let selected = Expr::try_ite(
            present.clone().select(i.clone()),
            data.clone().select(i.clone()),
            Expr::bitvec_const(0u8, 32),
        )
        .expect("well-sorted map select");

        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new(
            "after_store",
            vec![data_sort, present_sort, key_sort, value_sort],
        ));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::init(
            Expr::bool_const(true),
            RelationApp::new(
                "after_store",
                vec![stored_data, stored_present, i.clone(), value.clone()],
            ),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("after_store", vec![data, present, i, value.clone()])),
                vec![selected.eq(value).not()],
            ),
            RelationApp::new("error", Vec::new()),
        ));

        assert!(prove_straightline_safety(&vc));
    }

    #[test]
    fn array_store_miss_uses_path_disequality() {
        let key_sort = Sort::bitvec(32);
        let value_sort = Sort::bitvec(32);
        let data_sort = Sort::array(key_sort.clone(), value_sort.clone());
        let present_sort = Sort::array(key_sort.clone(), Sort::bool());
        let data = Expr::var("data", data_sort.clone());
        let present = Expr::var("present", present_sort.clone());
        let i = Expr::var("i", key_sort.clone());
        let j = Expr::var("j", key_sort.clone());
        let len = Expr::var("len", Sort::bitvec(64));
        let len_out = Expr::var("len_out", Sort::bitvec(64));
        let default = Expr::var("default", value_sort.clone());
        let value = Expr::var("value", value_sort.clone());
        let empty_data = Expr::const_array(key_sort.clone(), Expr::bitvec_const(0u8, 32));
        let empty_present = Expr::const_array(key_sort.clone(), Expr::bool_const(false));
        let stored_data = empty_data.store(i.clone(), value.clone());
        let stored_present = empty_present.store(i.clone(), Expr::bool_const(true));
        let selected = Expr::try_ite(
            present.clone().select(j.clone()),
            data.clone().select(j.clone()),
            default.clone(),
        )
        .expect("well-sorted map select");

        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new(
            "after_store",
            vec![
                data_sort,
                present_sort,
                key_sort.clone(),
                key_sort,
                Sort::bitvec(64),
                value_sort.clone(),
                value_sort,
            ],
        ));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::init(
            Expr::bool_const(true),
            RelationApp::new(
                "after_store",
                vec![
                    stored_data,
                    stored_present,
                    i.clone(),
                    j.clone(),
                    len.clone(),
                    default.clone(),
                    value,
                ],
            ),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new(
                    "after_store",
                    vec![
                        data,
                        present,
                        i.clone(),
                        j.clone(),
                        len.clone(),
                        default.clone(),
                        Expr::var("value2", Sort::bitvec(32)),
                    ],
                )),
                vec![
                    len_out.eq(len.bvadd(Expr::bitvec_const(1u8, 64))),
                    i.eq(j).not(),
                    selected.eq(default).not(),
                ],
            ),
            RelationApp::new("error", Vec::new()),
        ));

        assert!(prove_straightline_safety(&vc));
    }

    #[test]
    fn array_store_miss_uses_bv2int_path_disequality() {
        let key_sort = Sort::bitvec(32);
        let value_sort = Sort::bitvec(32);
        let data_sort = Sort::array(key_sort.clone(), value_sort.clone());
        let present_sort = Sort::array(Sort::int(), Sort::bool());
        let data = Expr::var("data", data_sort.clone());
        let present = Expr::var("present", present_sort.clone());
        let i = Expr::var("i", key_sort.clone());
        let j = Expr::var("j", key_sort.clone());
        let default = Expr::var("default", value_sort.clone());
        let value = Expr::var("value", value_sort.clone());
        let empty_data = Expr::const_array(key_sort.clone(), Expr::bitvec_const(0u8, 32));
        let empty_present = Expr::const_array(Sort::int(), Expr::bool_const(false));
        let stored_data = empty_data.store(i.clone(), value.clone());
        let stored_present = empty_present.store(i.clone().bv2int(), Expr::bool_const(true));
        let selected = Expr::try_ite(
            present.clone().select(j.clone().bv2int()),
            data.clone().select(j.clone()),
            default.clone(),
        )
        .expect("well-sorted map select");

        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new(
            "after_store",
            vec![
                data_sort,
                present_sort,
                key_sort.clone(),
                key_sort,
                value_sort.clone(),
                value_sort,
            ],
        ));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::init(
            Expr::bool_const(true),
            RelationApp::new(
                "after_store",
                vec![stored_data, stored_present, i.clone(), j.clone(), default.clone(), value],
            ),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new(
                    "after_store",
                    vec![
                        data,
                        present,
                        i.clone(),
                        j.clone(),
                        default.clone(),
                        Expr::var("value2", Sort::bitvec(32)),
                    ],
                )),
                vec![i.eq(j).not(), selected.eq(default).not()],
            ),
            RelationApp::new("error", Vec::new()),
        ));

        assert!(prove_straightline_safety(&vc));
    }

    #[test]
    fn discharge_preserves_error_headed_rule() {
        let x = Expr::var("x", Sort::bitvec(8));
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(8)]));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::init(
            x.clone().eq(Expr::bitvec_const(1u8, 8)),
            RelationApp::new("bb0", vec![x.clone()]),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::new("bb0", vec![x])), vec![Expr::bool_const(false)]),
            RelationApp::new("error", Vec::new()),
        ));
        vc.query = ChcQuery::new().with_target("error");

        assert!(discharge_straightline_safety(&mut vc));
        assert_eq!(vc.rules.len(), 1);
        assert_eq!(vc.rules[0].head.name, "error");
        assert_eq!(vc.rules[0].body.constraints.first(), Some(&Expr::bool_const(false)));
    }

    #[test]
    fn discharge_preserves_no_error_rule_as_unsat_obligation() {
        let x = Expr::var("x", Sort::bitvec(8));
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("bb0", vec![Sort::bitvec(8)]));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::init(
            x.clone().eq(Expr::bitvec_const(1u8, 8)),
            RelationApp::new("bb0", vec![x]),
        ));
        vc.query = ChcQuery::new().with_target("error");

        assert!(discharge_straightline_safety(&mut vc));
        assert_eq!(vc.rules.len(), 1);
        assert_eq!(vc.rules[0].head.name, "error");
        assert_eq!(vc.rules[0].body.constraints.first(), Some(&Expr::bool_const(false)));
    }
}
