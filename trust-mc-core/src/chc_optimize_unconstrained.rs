// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Exact projection of unconstrained relation arguments.
//!
//! The MIR encoding gives every basic-block relation one column per state
//! variable of the enclosing function, and every transition rule copies the
//! whole frame from body to head. On a straight-line harness with hundreds of
//! blocks that is tens of thousands of argument positions, almost all of which
//! carry a variable that no clause ever reads: it occurs at one body position,
//! is forwarded to the head, and appears in no constraint. AY's executor
//! admission (`ay-chc/src/smt/executor_adapter/logic_detection.rs`) charges
//! every such occurrence against `MAX_DT_SORT_NODES` / `MAX_EXECUTOR_EXPR_ROOTS`
//! for the WHOLE problem before any per-property slice is cut, so the frame
//! width alone can make AY reject the query slice (`ChcParseError` in the
//! driver) before a solver ever runs.
//!
//! This pass removes exactly the argument positions whose value can never
//! influence derivability — the "unbound argument" slice of Z3's `dl_mk_slice`
//! and of AY's own dead-parameter elimination, which runs only AFTER the
//! admission charge and therefore cannot help here.
//!
//! ## What "unconstrained" means
//!
//! A relation position `(R, i)` is LIVE (kept) when some clause READS it, i.e.
//! `R` occurs in a clause body with an argument at `i` that is
//!
//! * not a bare universally quantified variable (a constant, a compound term,
//!   or a `declare-const` symbol — all of which test the column's value), or
//! * a variable that also occurs in the clause's constraint, in a cover
//!   assertion, or at another argument position of the body application
//!   (an implicit equality), or
//! * a variable that flows into a LIVE position of the clause's head — a
//!   variable inside a head argument at a live position is needed there.
//!
//! Head occurrences never make a position live on their own: a head argument
//! only DEFINES the column, and a column nobody reads can be projected away
//! without changing which facts are derivable. Liveness is a least fixpoint
//! over the rules, so a column that is read three blocks downstream stays live
//! through every relay in between. Removing the dead positions from the
//! declarations and every application is an exact least-fixpoint equivalence:
//! the projected system derives the query target iff the original does.
//!
//! ## Fail-closed edges
//!
//! * The query target relation, any relation applied INSIDE a constraint
//!   expression, any relation whose application arity disagrees with its
//!   declaration, and any relation applied as a head without a declaration
//!   keep every position.
//! * Only names declared as rule variables (`declare-var`) count as bare
//!   variables; anything else anchors its position.
//! * Relations that occur in no rule are left untouched.
//!
//! The pass never rewrites a constraint: a variable that occurs in one is live
//! at every position it occupies, so no constraint can mention a stripped
//! variable afterwards. Stale `declare-var` entries are dropped the same way
//! `prune_dead_vars_and_constraints` drops them.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use ay_bindings::{Expr, ExprValue};

use crate::chc::{ChcVc, RelationApp};

/// Every variable name in `expr`, walked through `Expr::children` so a new
/// expression variant cannot hide an occurrence from the liveness analysis.
fn collect_var_names(expr: &Expr, out: &mut HashSet<String>) {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let ExprValue::Var { name } = node.value() {
            out.insert(name.clone());
        }
        stack.extend(node.children());
    }
}

/// One relation application as the liveness analysis sees it.
struct AppShape {
    relation: String,
    /// Per position: `Some(name)` when the argument is a bare declared rule
    /// variable; `None` for a constant, a compound term, or a symbol that is
    /// not a declared rule variable.
    bare: Vec<Option<String>>,
    /// Per position: every variable name occurring anywhere in the argument.
    vars: Vec<Vec<String>>,
}

struct ClauseShape {
    /// Variables this clause anchors: constraint variables, cover-assertion
    /// variables, variables inside non-bare body arguments, and variables that
    /// occupy more than one body argument position.
    anchored: HashSet<String>,
    body: Option<AppShape>,
    head: AppShape,
}

/// Project away every relation argument position no clause reads.
///
/// Returns the number of argument positions removed across all relations.
pub(super) fn prune_unconstrained_relation_args(vc: &mut ChcVc) -> usize {
    let arity: HashMap<String, usize> =
        vc.relations.iter().map(|rel| (rel.name.clone(), rel.arg_sorts.len())).collect();
    let quantified: HashSet<String> = vc.vars().iter().map(|var| var.name.to_string()).collect();

    let mut protected: HashSet<String> = HashSet::new();
    if let Some(target) = &vc.query.target {
        protected.insert(target.clone());
    }
    let mut cover_vars: HashSet<String> = HashSet::new();
    for (_, condition) in &vc.cover_assertions {
        collect_var_names(condition, &mut cover_vars);
    }

    let mut occurs: HashSet<String> = HashSet::new();
    let mut clauses: Vec<ClauseShape> = Vec::with_capacity(vc.rules.len());
    for rule in &vc.rules {
        let mut anchored = cover_vars.clone();
        for constraint in rule.body.constraints.iter() {
            collect_var_names(constraint, &mut anchored);
            protect_embedded_relations(constraint, &arity, &mut protected);
        }

        let head = shape_of(&rule.head, &quantified);
        let body = rule.body.relation.as_ref().map(|app| shape_of(app, &quantified));
        if let Some(body) = &body {
            let mut seen: HashSet<&str> = HashSet::new();
            for (position, bare) in body.bare.iter().enumerate() {
                match bare {
                    Some(name) => {
                        if !seen.insert(name.as_str()) {
                            anchored.insert(name.clone());
                        }
                    }
                    None => anchored.extend(body.vars[position].iter().cloned()),
                }
            }
        }

        for app in std::iter::once(&head).chain(body.iter()) {
            occurs.insert(app.relation.clone());
            match arity.get(&app.relation) {
                Some(&declared) if declared == app.bare.len() => {}
                _ => {
                    protected.insert(app.relation.clone());
                }
            }
        }

        clauses.push(ClauseShape { anchored, body, head });
    }

    let mut live: HashMap<String, Vec<bool>> = vc
        .relations
        .iter()
        .map(|rel| (rel.name.clone(), vec![protected.contains(&rel.name); rel.arg_sorts.len()]))
        .collect();

    // Least fixpoint: a body position becomes live when its argument is read
    // by the clause itself or feeds a head position that is already live.
    loop {
        let mut changed = false;
        for clause in &clauses {
            let Some(body) = &clause.body else {
                continue;
            };
            let mut needed: HashSet<&str> = HashSet::new();
            match live.get(&clause.head.relation) {
                Some(mask) => {
                    for (position, is_live) in mask.iter().enumerate() {
                        if *is_live {
                            needed.extend(clause.head.vars[position].iter().map(String::as_str));
                        }
                    }
                }
                None => {
                    for vars in &clause.head.vars {
                        needed.extend(vars.iter().map(String::as_str));
                    }
                }
            }
            let Some(mask) = live.get_mut(&body.relation) else {
                continue;
            };
            for (position, bare) in body.bare.iter().enumerate() {
                if mask[position] {
                    continue;
                }
                let read = match bare {
                    Some(name) => clause.anchored.contains(name) || needed.contains(name.as_str()),
                    None => true,
                };
                if read {
                    mask[position] = true;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    let dead: HashMap<String, Vec<bool>> = live
        .into_iter()
        .filter(|(name, mask)| occurs.contains(name) && mask.iter().any(|is_live| !is_live))
        .map(|(name, mask)| (name, mask.iter().map(|is_live| !is_live).collect()))
        .collect();
    if dead.is_empty() {
        return 0;
    }

    let stripped = dead.values().map(|mask| mask.iter().filter(|is_dead| **is_dead).count()).sum();
    for rel in &mut vc.relations {
        if let Some(mask) = dead.get(&rel.name) {
            rel.arg_sorts = keep_live(&rel.arg_sorts, mask);
        }
    }
    for rule in &mut vc.rules {
        strip_app(&mut rule.head, &dead);
        if let Some(body) = &mut rule.body.relation {
            strip_app(body, &dead);
        }
    }
    retain_referenced_vars(vc);
    stripped
}

fn shape_of(app: &RelationApp, quantified: &HashSet<String>) -> AppShape {
    let mut bare = Vec::with_capacity(app.args.len());
    let mut vars = Vec::with_capacity(app.args.len());
    for arg in app.args.iter() {
        let mut names = HashSet::new();
        collect_var_names(arg, &mut names);
        let mut names: Vec<String> = names.into_iter().collect();
        names.sort_unstable();
        bare.push(match arg.value() {
            ExprValue::Var { name } if quantified.contains(name) => Some(name.clone()),
            _ => None,
        });
        vars.push(names);
    }
    AppShape { relation: app.name.to_string(), bare, vars }
}

/// A relation applied inside a constraint is read through a channel this pass
/// does not model; keep every one of its positions.
fn protect_embedded_relations(
    expr: &Expr,
    arity: &HashMap<String, usize>,
    protected: &mut HashSet<String>,
) {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let ExprValue::FuncApp { name, .. } = node.value()
            && arity.contains_key(name)
        {
            protected.insert(name.clone());
        }
        stack.extend(node.children());
    }
}

fn keep_live<T: Clone>(items: &[T], dead: &[bool]) -> Vec<T> {
    items
        .iter()
        .zip(dead.iter())
        .filter(|(_, is_dead)| !**is_dead)
        .map(|(item, _)| item.clone())
        .collect()
}

fn strip_app(app: &mut RelationApp, dead: &HashMap<String, Vec<bool>>) {
    let Some(mask) = dead.get(app.name.as_str()) else {
        return;
    };
    if app.args.len() != mask.len() {
        return;
    }
    app.args = Arc::new(keep_live(&app.args, mask));
}

fn retain_referenced_vars(vc: &mut ChcVc) {
    let mut referenced: HashSet<String> = HashSet::new();
    for rule in &vc.rules {
        for arg in rule.head.args.iter() {
            collect_var_names(arg, &mut referenced);
        }
        if let Some(body) = &rule.body.relation {
            for arg in body.args.iter() {
                collect_var_names(arg, &mut referenced);
            }
        }
        for constraint in rule.body.constraints.iter() {
            collect_var_names(constraint, &mut referenced);
        }
    }
    for (_, condition) in &vc.cover_assertions {
        collect_var_names(condition, &mut referenced);
    }
    vc.retain_vars(&referenced);
}
