// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Naming the links of a deep bitvector `ite` chain.
//!
//! The CHC inline walker replays a loop it cannot summarise and merges the
//! value each exit leaves with the SwitchInt guard of that exit, so a loop
//! that runs up to `n` passes leaves a value that is an `ite` chain `n` deep:
//!
//! ```text
//! (= i_out (ite (not (bvuge #x00 n)) (ite (not (bvuge #x01 n)) ... #x01) #x00))
//! ```
//!
//! AY `d80d17a90` decides such a rule in time exponential in the depth of the
//! chain (measured 2026-10-14 on an 8-bit chain over one input: 0.05 s at depth
//! 4, 0.23 s at 6, 2.3 s at 8, about 5.5 minutes at 13; the progress line
//! stays in `initializing` and the time goes to `ground-result-mapping`), and
//! its per-property batch does not stop on time, so one such harness starved
//! every harness after it in a whole-file run
//! (`tools/soundness-duals/walker_loop_fuel_exit_dual.rs`,
//! `docs/ay-asks/2026-10-14-acyclic-8bit-ite-chain-takes-5-minutes-d80d17a90`).
//! The same rule with each link of the chain named by a fresh variable is
//! decided in under half a second at depths 12, 32 and 64.
//!
//! This pass does that naming: in a rule whose deepest bitvector `ite` chain is
//! more than [`ITE_CHAIN_DEPTH_THRESHOLD`] deep, every bitvector `ite` that heads
//! a chain [`ITE_CHAIN_LINK_DEPTH`] deep is replaced by a fresh variable `v`,
//! and `(= v <that ite>)` is added to the rule's body.
//!
//! Exact. `v` occurs in no other rule, so it is existentially quantified in
//! this one, and the added equality determines it: every assignment of the
//! rule's other variables that satisfied the body still does (with `v` the
//! value of the term it names), and no other does. The least model of every
//! relation is unchanged, and so is every derivation of an error relation.
//! The pass runs last, after every other emit-time pass, so none of them
//! substitutes the definitions back; the per-property approximation-dependence
//! verdicts were computed over the rules before it and stay valid for the
//! renamed rules, whose added equalities copy values only into the new
//! variables.
//!
//! A shared subterm (the walker's merges share them) is named once per rule. The
//! body of a quantifier is left alone: a term there may read a bound variable,
//! which a definition at the rule's level cannot.
//! `TRUST_MC_CHC_NAME_ITE_CHAINS=off` turns the pass off, for A/B measurement.

use std::collections::HashMap;
use std::sync::Arc;

use ay_bindings::{Expr, ExprValue, Sort};

use crate::chc::{ChcVc, RelationApp, VarDecl};
use crate::constraints::Constraints;

/// A rule is renamed only when one of its bitvector `ite` chains is deeper than
/// this. AY decides a chain this deep in a fraction of a second (0.23 s at 6),
/// so the shallow merges that make up nearly every rule are left as they are.
pub(crate) const ITE_CHAIN_DEPTH_THRESHOLD: usize = 6;

/// The depth of each named link. A link this deep costs AY about 0.05 s.
pub(crate) const ITE_CHAIN_LINK_DEPTH: usize = 4;

/// Prefix of the variables the pass introduces.
pub(crate) const ITE_CHAIN_VAR_PREFIX: &str = "__ite_link";

/// The lever. Read once per process.
fn naming_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("TRUST_MC_CHC_NAME_ITE_CHAINS").map(|v| v != "off").unwrap_or(true)
    })
}

/// Names the links of every bitvector `ite` chain deeper than
/// [`ITE_CHAIN_DEPTH_THRESHOLD`] (see the module docs). Returns the number of
/// variables introduced.
pub(super) fn name_deep_ite_chains(vc: &mut ChcVc) -> usize {
    if !naming_enabled() {
        return 0;
    }
    name_deep_ite_chains_unconditionally(vc)
}

/// [`name_deep_ite_chains`] without the lever, for tests.
pub(super) fn name_deep_ite_chains_unconditionally(vc: &mut ChcVc) -> usize {
    let mut introduced: Vec<VarDecl> = Vec::new();
    for (rule_idx, rule) in vc.rules.iter_mut().enumerate() {
        let mut depths = DepthMemo::default();
        let deepest = rule
            .body
            .constraints
            .iter()
            .chain(rule.head.args.iter())
            .chain(rule.body.relation.iter().flat_map(|app| app.args.iter()))
            .map(|expr| depths.bv_ite_depth(expr))
            .max()
            .unwrap_or(0);
        if deepest <= ITE_CHAIN_DEPTH_THRESHOLD {
            continue;
        }
        let mut namer = Namer { rule_idx, memo: HashMap::new(), definitions: Vec::new() };
        let constraints: Vec<Expr> =
            rule.body.constraints.iter().map(|expr| namer.rewrite(expr).0).collect();
        let head = rename_app(&mut namer, &rule.head);
        let body_relation = rule.body.relation.as_ref().map(|app| rename_app(&mut namer, app));
        if namer.definitions.is_empty() {
            continue;
        }
        let mut constraints = constraints;
        for (var, sort, term) in namer.definitions {
            constraints.push(Expr::var(var.clone(), sort.clone()).eq(term));
            introduced.push(VarDecl::new(var, sort));
        }
        rule.body.constraints = Constraints::Owned(constraints);
        rule.head = head;
        rule.body.relation = body_relation;
    }
    let count = introduced.len();
    for decl in introduced {
        vc.add_var(decl);
    }
    count
}

fn rename_app(namer: &mut Namer, app: &RelationApp) -> RelationApp {
    let args: Vec<Expr> = app.args.iter().map(|expr| namer.rewrite(expr).0).collect();
    RelationApp { name: app.name.clone(), args: Arc::new(args) }
}

fn is_bv_ite(expr: &Expr) -> bool {
    matches!(expr.value(), ExprValue::Ite { .. }) && expr.sort().is_bitvec()
}

/// The depth of the deepest bitvector `ite` chain in a term: a bitvector
/// `ite` adds one to the deepest of its operands, any other node takes the
/// deepest of its children. Memoised on node identity, so a DAG costs its
/// node count, not its written-out size.
#[derive(Default)]
struct DepthMemo {
    memo: HashMap<*const ExprValue, usize>,
}

impl DepthMemo {
    fn bv_ite_depth(&mut self, expr: &Expr) -> usize {
        let key = std::ptr::from_ref(expr.value());
        if let Some(&depth) = self.memo.get(&key) {
            return depth;
        }
        let deepest_child =
            expr.children().map(|child| self.bv_ite_depth(child)).max().unwrap_or(0);
        let depth = deepest_child + usize::from(is_bv_ite(expr));
        self.memo.insert(key, depth);
        depth
    }
}

/// Rewrites one rule's terms bottom up, naming each link.
struct Namer {
    rule_idx: usize,
    /// Node identity to (rewritten term, depth of its unnamed chain).
    memo: HashMap<*const ExprValue, (Expr, usize)>,
    /// `(variable, sort, the term it names)`, in definition order.
    definitions: Vec<(String, Sort, Expr)>,
}

impl Namer {
    fn rewrite(&mut self, expr: &Expr) -> (Expr, usize) {
        let key = std::ptr::from_ref(expr.value());
        if let Some(done) = self.memo.get(&key) {
            return done.clone();
        }
        let done = self.rewrite_node(expr);
        self.memo.insert(key, done.clone());
        done
    }

    fn rewrite_node(&mut self, expr: &Expr) -> (Expr, usize) {
        // A quantifier's body may read its bound variables, which a rule-level
        // definition cannot: it is left as it is.
        if matches!(expr.value(), ExprValue::Forall { .. } | ExprValue::Exists { .. }) {
            return (expr.clone(), 0);
        }
        let children: Vec<&Expr> = expr.children().collect();
        if children.is_empty() || !expr.value().is_known_variant() {
            return (expr.clone(), 0);
        }
        let mut changed = false;
        let mut deepest = 0;
        let mut rewritten = Vec::with_capacity(children.len());
        for child in children {
            let (new_child, depth) = self.rewrite(child);
            changed |= !std::ptr::eq(new_child.value(), child.value());
            deepest = deepest.max(depth);
            rewritten.push(new_child);
        }
        let node = if changed {
            ay_bindings::rebuild_with_children(expr, rewritten)
        } else {
            expr.clone()
        };
        if !is_bv_ite(expr) {
            return (node, deepest);
        }
        let depth = deepest + 1;
        if depth < ITE_CHAIN_LINK_DEPTH {
            return (node, depth);
        }
        let name = format!("{ITE_CHAIN_VAR_PREFIX}_{}_{}", self.rule_idx, self.definitions.len());
        let sort = expr.sort().clone();
        let var = Expr::var(name.clone(), sort.clone());
        self.definitions.push((name, sort, node));
        (var, 0)
    }
}
