// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! LARGE-BLOCK ENCODING of an acyclic function (design step 8e).
//!
//! # Why
//!
//! The per-block encoding (call it S) gives every basic block `B` a relation
//! `bbB` whose columns are the values live into `B` — threaded SSA values,
//! promoted cells, `B`'s own parameters — one rule per transition the block's
//! translation emits and one per error site. A value live across a chain of `k`
//! blocks is a column of each of the `k` relations, so the declared relation
//! arguments total `Σ_B |live_in(B)|`. On the ever-init family (`N` drop-flagged
//! locals) every drop flag stays live down the whole cleanup chain: the total is
//! `Θ(N²)`, and the lowering, the normalized-input identity, every row's evidence
//! and the engine all pay it.
//!
//! # What
//!
//! When the blocks reachable from the entry form an acyclic graph (and there is
//! more than the entry), this encoding (call it L) keeps ONE relation, the
//! entry's, and makes the function one non-recursive query:
//!
//! ```text
//!   bbE(x̄) ← ⊤                                   the entry fact, unchanged
//!   error  ← bbE(x̄) ∧ Φ ∧ (f₁ ∨ … ∨ fₘ)           the one query rule
//! ```
//!
//! `Φ` conjoins, for each block `B` of the region (the entry `E` and every block
//! reachable from it, translated in a topological order) that has a path to an
//! error site — a block without one can be on no derivation of `error`, so its
//! formulas are dropped and every transition into it is `¬s_e`:
//!
//! * REACHABILITY: `r_B ⇒ (s_e₁ ∨ … ∨ s_eₖ)` over the transitions emitted INTO
//!   `B` (`r_E` is `true`; a block nothing transfers to gets `¬r_B`);
//! * the PATH-CONSTRAINT CHAIN of `B`: `p_{B,L} ⇒ (p_{B,L'} ∧ pc_B[L'..L])`, one
//!   Boolean per prefix length `L` at which `B` emitted a rule, `L'` the previous
//!   one and `p_{B,0} = r_B` — each path constraint appears once, so a block's
//!   share of `Φ` is linear in the block (S copies the prefix into every rule);
//! * each emitted TRANSITION `e` of `B` with prefix `L` and guard `g`:
//!   `s_e ⇒ (p_{B,L} ∧ g)`, with `s_e` a FREE selector the solver chooses;
//! * each emitted ERROR SITE with prefix `L` and condition `c`:
//!   `f ⇒ (p_{B,L} ∧ c)`;
//! * the COLUMNS of a non-entry block (S's relation arguments, in S's order). In-
//!   edge terms are compared by IDENTITY — an atom (a variable or a literal) by
//!   value, any other term by its shared node — never by a structural walk:
//!   - if every emitted in-edge passes the same atom `a`, `B` reads `a` itself;
//!   - if every in-edge passes the same compound term `a`, `B` reads a column
//!     variable `c` defined as `c = a`, or `c = ite(r_B, a, d)` if `a` mentions a
//!     translation havoc (so the refutation gate need not read it off the path);
//!   - otherwise `M` is the term most in-edges pass (the first in emission order
//!     among the most frequent), and the in-edges `e₁ … e_t` that pass another
//!     term (in emission order) get a CHAIN of column variables
//!     `c₁ = ite(s_e₁, a_e₁, c₂)`, …, `c_t = ite(s_e_t, a_e_t, tail)`, with
//!     `tail` being `M` (or `ite(r_B, M, d)` when `M` mentions a havoc); `B`
//!     reads `c₁`.
//!
//!   `d` is a variable-free default of the column's sort. Every column variable
//!   is defined ONCE, by an unconditional equality, so no term a block reads is
//!   ever deeper or larger than one in-edge's own term plus one `ite`: the
//!   query's depth does not grow with a join's in-degree, and a selection is
//!   never inlined into the block's uses. (A column is never defined under an
//!   implication: the pinned ay answers `unknown` — "INVALID model", its
//!   soundness gate — on an array equality under a guard; measured on the
//!   TMC-1/TMC-2 differential families, 2026-10-01.);
//! * AT MOST ONE IN-EDGE of a block whose columns select (a column with
//!   differing in-edge terms) is taken: the sequential ladder
//!   `s_e₁ ⇒ o₁`, `o_{j-1} ⇒ o_j`, `s_e_j ⇒ o_j`, `s_e_j ⇒ ¬o_{j-1}` over its
//!   in-edges in emission order (`k - 1` Booleans `o`, `O(k)` clauses). A
//!   column's chain lists only the in-edges that pass another term than `M`, so
//!   it selects the taken in-edge's term exactly when no other in-edge is taken;
//! * JUSTIFICATION, so that a model's true Booleans are one derivation and no
//!   more: `s_e ⇒ r_T` for a transition into `T`; `p_{B,L} ⇒ (∨ emissions at
//!   prefix L ∨ p_{B,L''})`, `L''` the next longer prefix, so a prefix Boolean
//!   holds only for a rule that uses it; and, for an error site `f` of `B`,
//!   `f ⇒ ¬t_B` with `s_e ⇒ t_B` for every selector out of `B` (`t_B` is the
//!   lone out-selector itself when `B` emits one, and is not needed with one
//!   site), so a path ends at the block whose site fires. These are pure Boolean
//!   constraints; they let the refutation gate read only the blocks of the
//!   counterexample's path (trust-mc-driver, `derivation_reads_translation_havoc`).
//!
//! `B`'s instructions are translated by the SAME per-block translator as in S —
//! from the column terms where S has relation formals. Every formula of `B` sits
//! under an implication whose antecedent is one of `B`'s Booleans, except the
//! definitions of `B`'s column variables (and of the cross-block part variables
//! below), which any assignment of the rest satisfies by giving each variable its
//! definition's value; so a block off the executed path constrains nothing.
//!
//! # Equisatisfiability with S
//!
//! Claim: `error` is derivable in S iff it is derivable in L.
//!
//! (S ⇒ L) A derivation of `error` in S is the entry fact, transitions
//! `e₁ … eₙ` along a CFG path `π = E = B₀ → … → Bₙ`, and one error rule of
//! `Bₙ`, each rule with its own witness `σᵢ` for its variables. (A derivation
//! through a block outside the region is impossible in both systems: such a
//! block has no fact and no in-transition from a derivable relation.) Set
//! `r`, `s`, `f` and the chain Booleans true exactly on `π` — the chain up to
//! the prefix of the rule `π` uses there — and false elsewhere; each ladder
//! Boolean `o_j` of a block to "one of its first `j` in-selectors is true"; each
//! `t_B` to "a selector out of `B` is true"; `Bᵢ`'s own variables to `σᵢ`; and
//! every column and part variable to its definition's value. Every implication
//! with a false antecedent holds, every definition holds, and so does each
//! ladder (a path enters a block once, so at most one in-selector of it is
//! true). On `π` each formula holds: `σᵢ` satisfies exactly the constraints of
//! the S rule it was used for — the emitted prefix of `Bᵢ`'s path constraints
//! plus its guard or condition, which is precisely what the chain and the
//! selector/site encode — and `Bᵢ`'s column terms evaluate to the arguments S's
//! relation application carries (by induction along `π`: a column is the term
//! every in-edge passes, or a chain whose only true selector, if any, is `π`'s
//! in-edge's, falling through to `M` exactly when `π`'s in-edge passes `M`). The
//! justification constraints hold too: `π`'s selectors reach `π`'s blocks (every
//! block of `π` has a path to `Bₙ`'s site, so none was dropped, and no `¬s_e`
//! names an edge of `π`); each true prefix Boolean is the used rule's prefix or
//! a shorter one; and only `Bₙ` has a true site, where no selector out of `Bₙ`
//! is true. The variables of a block off `π` occur only under that block's own
//! false antecedents or in definitions. So the query body holds.
//!
//! (L ⇒ S) A model of the query body makes some site Boolean `f` true; its
//! implication makes its prefix Boolean — and, down the chain, `r_{Bₙ}` — true
//! and the site's prefix and condition hold. `r_B` of a non-entry block makes
//! some in-edge selector `s_e` true, which makes the source block's prefix
//! chain (hence its `r`) true and the guard hold. Walking selectors back reaches
//! `E` (the region is acyclic, so the walk terminates) and yields a path `π`
//! whose every used prefix, guard and condition is true in the model. The S
//! rules along `π`, instantiated with the model's values — `B`'s relation
//! arguments := the model's values of `B`'s column terms, which equal the
//! passed terms under the selected in-edge — derive `error`. That walk is
//! [`LargeBlockMap::counterexample_path`]: it maps a model of L back to the
//! block path of S and the error site it reaches. A block whose columns select
//! has exactly one true in-selector (the ladder), and that in-edge's terms are
//! what every column of the block reads; in a block whose columns do not select,
//! every in-edge passes the same terms, so whichever true in-selector the walk
//! takes (the first in emission order) carries them.
//!
//! The argument rests on three facts this module enforces:
//!
//! 1. Each S rule's constraints are a PREFIX of its block's path-constraint
//!    list plus the rule's guard or condition. Every emission site receives the
//!    block's running list, which only grows by `push`; at every emission the
//!    absorbed prefix is re-identified (its length cannot shrink and its last
//!    element must be the very `Expr` absorbed last). A violation abandons L for
//!    the function, which is then translated per block
//!    (`ChcTranslationWork::large_block_fallbacks`, pinned at 0).
//! 2. A block's translation is the same function of its input terms in both
//!    encodings: L binds the inputs before the block is translated, exactly
//!    where S binds the formals, and runs the same code. The only cross-block
//!    state the translator keeps outside the relation columns is what it
//!    records per SSA value about a fat pointer: its parts (`ptr_parts`, the
//!    terms a `PtrFromParts` was built from) and its metadata symbols
//!    (`ptr_metadata_syms`, `ptr_opaque_metadata`). A symbol is a free variable
//!    (a translation havoc) chosen once per SSA value; a fat pointer's real
//!    metadata is a function of the value, so sharing one symbol between reads
//!    excludes no execution. Parts recorded in block `A` are read in block `C`
//!    as they are when they mention no variable, when `C` is `A`, or — in L —
//!    when `A` DOMINATES `C` in the region (`RegionDominators`): every path to
//!    `C` runs through `A`, and every variable of the parts is then an input of
//!    the entry, a column or part variable defined on that path, or a variable
//!    of `A` constrained by `A`'s own formulas on that path, so in every model
//!    the terms evaluate to the values `A` built — the parts EXACTLY. (A
//!    compound part is read through a part variable `m = part`, or
//!    `m = ite(r_C, part, d)` if it mentions a havoc, defined for `C`, so a term
//!    never grows across blocks.) Any other read sees an OPAQUE value: its
//!    metadata is a fresh unconstrained havoc and its data the value's own
//!    binding — never the `isize::MAX`-bounded `slice_len` symbol, which is a
//!    fact about a reference, not about whatever a `PtrFromParts` was given. S
//!    reads parts across blocks only when they mention no variable, so a later
//!    rule never reads an earlier rule's variables free.
//!    When an input is a literal rather than a variable, the per-block
//!    translator — whose soundness argument is stated for arbitrary input terms
//!    — may specialize to it; that can only remove spurious behaviours, never
//!    real ones, so L stays sound and at least as precise as S there.
//! 3. A block outside the region (unreachable from the entry) keeps its S
//!    relation and rules; its transitions INTO the region are dropped, since the
//!    target has no relation and the source relation is underivable in both
//!    encodings.
//!
//! Diagnostics, inductive-hypothesis sites and census rows are the same per
//! block in both encodings; they are restored to S's order (block order, then
//! instruction order).
//!
//! # Cost
//!
//! L declares one relation (the entry's) for the region. `Φ` holds each path
//! constraint, guard and error condition once; one Boolean per emission, prefix
//! and block; `O(k)` ladder clauses for a block with `k` in-edges; and, per
//! column, one variable for a compound term every in-edge passes or one per
//! in-edge that passes another term than the column's most frequent one. On a
//! join where every arm changes one cell, that is one variable per cell, not
//! one per (cell, arm). Every term a block reads is atomic, so a tree-spelled
//! consumer pays each in-edge term once. What stays proportional to
//! `Σ_B |live_in(B)| · |preds(B)|` is the translator's own analysis: the
//! liveness that lays out the columns, the arguments every emitted in-edge
//! passes, and their one-word identity comparison (`live_in_insertions`,
//! `large_block_column_merges`) — values already built, not CHC the consumers
//! carry, but still super-linear on the ever-init family. Removing it needs a
//! merged block's inputs resolved sparsely, by dominance, instead of enumerated
//! (see `docs/DECISION_QUEUE.md`, 8e). The dominator tree is built in
//! `O(E log B)` (skew-binary jump pointers) and each cross-block part read asks
//! it once, in `O(log B)`; term facts (variables, havocs) are computed once per
//! shared node (`TermFacts`).
//!
//! # Scope
//!
//! A function whose reachable CFG has a cycle keeps S. Merging the acyclic
//! parts of such a function needs exits from a region into loop relations, and
//! the refutation gates of the cyclic lane (`bounded_unroll`'s grounding gate)
//! accept only definitional clauses; both are follow-ups.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap};

use ay_bindings::{Expr, ExprValue, Sort};
use trust_ir::inst::Inst;
use trust_ir::ty::Ty;
use trust_ir::value::BlockId;
use trust_ir::{Block, Function, Module};
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};

use super::{
    AggregateValue, ArrayValue, ChcFuncTranslator, CompositeShape, ERROR_REL, ValueBinding,
    composite_shape_of, lifted_sort, ty_to_sort,
};

/// The blocks the large-block encoding merges, and the order it translates them.
#[derive(Debug, Clone)]
pub(super) struct LargeBlockPlan {
    /// The region in translation order: the entry first, then every block
    /// reachable from it, each after all of its predecessors.
    pub(super) order: Vec<BlockId>,
    /// The region's blocks other than the entry. They get no relation.
    pub(super) merged: BTreeSet<BlockId>,
    /// Every block's position in `Function::blocks`, to restore S's order of
    /// the per-block records (diagnostics, sites, census rows).
    pub(super) position: BTreeMap<BlockId, usize>,
    /// The region's dominator tree.
    pub(super) dominators: RegionDominators,
}

/// The dominator tree of an acyclic region, over its translation order.
///
/// In a DAG visited in topological order, a block's immediate dominator is the
/// nearest common ancestor, in the tree built so far, of its predecessors. The
/// tree keeps skew-binary jump pointers (Myers, 1983), so an ancestor at a given
/// depth — and hence a common ancestor and a dominance query — costs `O(log B)`
/// with `O(1)` words per block: the tree is built in `O(E log B)`.
#[derive(Debug, Clone)]
pub(super) struct RegionDominators {
    /// Each region block's index into the tree (its translation order).
    rank: BTreeMap<BlockId, usize>,
    parent: Vec<usize>,
    jump: Vec<usize>,
    depth: Vec<usize>,
}

impl RegionDominators {
    /// The tree of `order` (a topological order, the root first), where
    /// `preds[i]` lists the order indices of block `order[i]`'s predecessors in
    /// the region.
    pub(super) fn new(order: &[BlockId], preds: &[Vec<usize>]) -> Self {
        let mut tree = Self {
            rank: order.iter().enumerate().map(|(index, block)| (*block, index)).collect(),
            parent: vec![0; order.len()],
            jump: vec![0; order.len()],
            depth: vec![0; order.len()],
        };
        for (node, sources) in preds.iter().enumerate().skip(1) {
            let mut idom: Option<usize> = None;
            for &pred in sources {
                idom = Some(match idom {
                    None => pred,
                    Some(other) => tree.nearest_common_ancestor(other, pred),
                });
            }
            // Every non-root block of the region has a predecessor in it.
            tree.add_leaf(node, idom.unwrap_or(0));
        }
        tree
    }

    fn add_leaf(&mut self, node: usize, parent: usize) {
        let up = self.jump[parent];
        let jump =
            if self.depth[parent] - self.depth[up] == self.depth[up] - self.depth[self.jump[up]] {
                self.jump[up]
            } else {
                parent
            };
        self.parent[node] = parent;
        self.depth[node] = self.depth[parent] + 1;
        self.jump[node] = jump;
    }

    /// The ancestor of `node` at `depth` (at most `node`'s own depth).
    fn ancestor_at(&self, mut node: usize, depth: usize) -> usize {
        while self.depth[node] > depth {
            node = if self.depth[self.jump[node]] >= depth {
                self.jump[node]
            } else {
                self.parent[node]
            };
        }
        node
    }

    fn nearest_common_ancestor(&self, a: usize, b: usize) -> usize {
        let (mut a, mut b) = if self.depth[a] >= self.depth[b] { (a, b) } else { (b, a) };
        a = self.ancestor_at(a, self.depth[b]);
        while a != b {
            if self.jump[a] == self.jump[b] {
                a = self.parent[a];
                b = self.parent[b];
            } else {
                a = self.jump[a];
                b = self.jump[b];
            }
        }
        a
    }

    /// Whether `dominator` dominates `block` (every path from the region's root
    /// to `block` runs through `dominator`; a block dominates itself). `false`
    /// for a block outside the region.
    pub(super) fn dominates(&self, dominator: BlockId, block: BlockId) -> bool {
        let (Some(&a), Some(&b)) = (self.rank.get(&dominator), self.rank.get(&block)) else {
            return false;
        };
        self.depth[a] <= self.depth[b] && self.ancestor_at(b, self.depth[a]) == a
    }
}

/// The blocks a block's translation can transfer to: the targets of every
/// `Br`, `CondBr` and `Switch` in it. These are the only instructions whose
/// translation emits a transition (`ChcFuncTranslator::add_transition_rule`),
/// so this is a superset of the transitions the translation emits — and
/// dominance over these edges implies dominance over the emitted ones.
fn branch_targets(inst: &Inst, targets: &mut Vec<BlockId>) {
    match inst {
        Inst::Br { target, .. } => targets.push(*target),
        Inst::CondBr { then_target, else_target, .. } => {
            targets.push(*then_target);
            targets.push(*else_target);
        }
        Inst::Switch { default, cases, .. } => {
            targets.extend(cases.iter().map(|case| case.target));
            targets.push(*default);
        }
        _ => {}
    }
}

/// The large-block plan of `func`, or `None` when the encoding does not apply
/// and the function keeps the per-block encoding: a repeated block id, a
/// missing entry, a branch to an unknown block, a cycle among the blocks
/// reachable from the entry, or no block but the entry reachable (one relation
/// already). `O(E log B)`: a heap orders the ready blocks by position, and the
/// dominator tree answers each predecessor merge in `O(log B)`.
pub(super) fn plan_large_block(func: &Function) -> Option<LargeBlockPlan> {
    let mut position: BTreeMap<BlockId, usize> = BTreeMap::new();
    for (index, block) in func.blocks.iter().enumerate() {
        if position.insert(block.id, index).is_some() {
            return None;
        }
    }
    let entry = *position.get(&func.entry)?;
    let count = func.blocks.len();
    let mut successors: Vec<Vec<usize>> = vec![Vec::new(); count];
    for (index, block) in func.blocks.iter().enumerate() {
        let mut targets = Vec::new();
        for node in &block.body {
            branch_targets(&node.inst, &mut targets);
        }
        for target in targets {
            successors[index].push(*position.get(&target)?);
        }
    }

    let mut reachable = vec![false; count];
    reachable[entry] = true;
    let mut stack = vec![entry];
    while let Some(node) = stack.pop() {
        for &successor in &successors[node] {
            if !reachable[successor] {
                reachable[successor] = true;
                stack.push(successor);
            }
        }
    }

    // Kahn's order over the reachable subgraph, smallest position first, so the
    // order is a pure function of the CFG. Every reachable block other than the
    // entry has a reachable predecessor, so it is processed exactly when the
    // subgraph is acyclic.
    let mut indegree = vec![0usize; count];
    for node in (0..count).filter(|node| reachable[*node]) {
        for &successor in &successors[node] {
            indegree[successor] += 1;
        }
    }
    if indegree[entry] != 0 {
        return None;
    }
    let mut ready = BinaryHeap::from([Reverse(entry)]);
    let mut order_positions = Vec::new();
    while let Some(Reverse(node)) = ready.pop() {
        order_positions.push(node);
        for &successor in &successors[node] {
            indegree[successor] -= 1;
            if indegree[successor] == 0 {
                ready.push(Reverse(successor));
            }
        }
    }
    let reachable_count = reachable.iter().filter(|reached| **reached).count();
    if order_positions.len() != reachable_count || order_positions.len() < 2 {
        return None;
    }
    let mut rank_of_position = vec![usize::MAX; count];
    for (rank, &node) in order_positions.iter().enumerate() {
        rank_of_position[node] = rank;
    }
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); order_positions.len()];
    for (rank, &node) in order_positions.iter().enumerate() {
        for &successor in &successors[node] {
            preds[rank_of_position[successor]].push(rank);
        }
    }
    let order: Vec<BlockId> = order_positions.iter().map(|&node| func.blocks[node].id).collect();
    let dominators = RegionDominators::new(&order, &preds);
    let merged = order.iter().skip(1).copied().collect();
    Some(LargeBlockPlan { order, merged, position, dominators })
}

#[cfg(test)]
thread_local! {
    /// Test-only: make every large-block translation on this thread abandon the
    /// encoding at its end, to exercise the per-block fallback.
    pub(super) static FORCE_VIOLATION: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The identity of a term, for comparing in-edge terms in `O(1)`: an atom (a
/// variable or a literal) by value, any other term by its shared node. Two
/// structurally equal compound terms built separately are different identities;
/// they then get a selection, which is merely less compact, never wrong.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TermKey {
    Atom(Expr),
    Node(usize, Sort),
}

fn term_key(expr: &Expr) -> TermKey {
    if is_atomic(expr) {
        TermKey::Atom(expr.clone())
    } else {
        TermKey::Node(node_address(expr), expr.sort().clone())
    }
}

/// The address of `expr`'s shared node. Only compared while the node is alive.
fn node_address(expr: &Expr) -> usize {
    std::ptr::from_ref(expr.value()) as usize
}

/// What a term mentions, computed once per shared node over a translation.
#[derive(Debug, Clone, Default)]
pub(super) struct TermFacts {
    /// Per node address: the node (kept alive, so its address is not reused)
    /// and its facts (`HAS_VAR`, `HAS_HAVOC`).
    memo: HashMap<usize, (Expr, u8)>,
}

const HAS_VAR: u8 = 1;
const HAS_HAVOC: u8 = 2;

impl TermFacts {
    fn facts(&mut self, expr: &Expr) -> u8 {
        if let Some((_, facts)) = self.memo.get(&node_address(expr)) {
            return *facts;
        }
        // Iterative post-order: a node's facts are its children's, or its own
        // for a variable.
        let mut stack: Vec<(Expr, bool)> = vec![(expr.clone(), false)];
        while let Some((node, expanded)) = stack.pop() {
            let address = node_address(&node);
            if self.memo.contains_key(&address) {
                continue;
            }
            if let ExprValue::Var { name } = node.value() {
                let facts = if trust_mc_core::chc::is_translation_havoc_var(name) {
                    HAS_VAR | HAS_HAVOC
                } else {
                    HAS_VAR
                };
                self.memo.insert(address, (node, facts));
                continue;
            }
            if expanded {
                let facts = node
                    .children()
                    .map(|child| self.memo.get(&node_address(child)).map_or(0, |(_, f)| *f))
                    .fold(0, |all, one| all | one);
                self.memo.insert(address, (node, facts));
            } else {
                let children: Vec<Expr> = node
                    .children()
                    .filter(|child| !self.memo.contains_key(&node_address(child)))
                    .cloned()
                    .collect();
                stack.push((node, true));
                stack.extend(children.into_iter().map(|child| (child, false)));
            }
        }
        self.memo.get(&node_address(expr)).map_or(HAS_VAR | HAS_HAVOC, |(_, facts)| *facts)
    }

    /// Whether `expr` mentions no variable (a literal term).
    pub(super) fn is_closed(&mut self, expr: &Expr) -> bool {
        self.facts(expr) & HAS_VAR == 0
    }

    /// Whether `expr` mentions a translation havoc (`ChcVc::declare_havoc_var`).
    pub(super) fn mentions_havoc(&mut self, expr: &Expr) -> bool {
        self.facts(expr) & HAS_HAVOC != 0
    }
}

/// One transition emitted into a merged block: its selector, its source and
/// the relation arguments S would pass, in the target's column order.
#[derive(Debug, Clone)]
struct InEdge {
    selector: Expr,
    selector_name: String,
    source: BlockId,
    args: Vec<Expr>,
}

/// The block whose rules are being absorbed: its prefix chain.
#[derive(Debug, Clone)]
struct Cursor {
    block: BlockId,
    /// The Boolean of the longest prefix absorbed so far (`r_B` before any).
    chain: Expr,
    /// How many of the block's path constraints the chain covers.
    chain_len: usize,
    /// The last path constraint absorbed, by identity (`Expr` is `Arc`-shared).
    last: Option<Expr>,
    /// Emissions of this block so far, to name its Booleans.
    emitted: usize,
    /// Every prefix Boolean of the block, shortest first (`r_B` first), each
    /// with the emissions made at exactly its prefix: what justifies it.
    prefixes: Vec<(Expr, Vec<Expr>)>,
    /// The selectors of the transitions this block emitted.
    out_selectors: Vec<Expr>,
    /// The Booleans of the error sites this block emitted.
    sites: Vec<Expr>,
}

impl Cursor {
    fn new(block: BlockId, reach: Expr) -> Self {
        Self {
            block,
            chain: reach.clone(),
            chain_len: 0,
            last: None,
            emitted: 0,
            prefixes: vec![(reach, Vec::new())],
            out_selectors: Vec::new(),
            sites: Vec::new(),
        }
    }
}

/// The large-block encoding of one function while it is translated.
#[derive(Debug, Clone)]
pub(super) struct LargeBlock {
    pub(super) plan: LargeBlockPlan,
    in_edges: BTreeMap<BlockId, Vec<InEdge>>,
    /// Merged blocks already translated: an emission into one would be an edge
    /// the plan's order missed.
    entered: BTreeSet<BlockId>,
    /// Every translated region block's reachability (`true` for the root).
    reach: BTreeMap<BlockId, Expr>,
    /// The conjuncts of the query rule's body (`Φ`), each with the block whose
    /// formula it is.
    constraints: Vec<(BlockId, Expr)>,
    /// The error-site Booleans (the query's disjuncts).
    error_sites: Vec<Expr>,
    cursor: Option<Cursor>,
    /// Part variables already defined: per compound part (by node address, the
    /// part kept alive) and reading block, or per part alone when it mentions
    /// no havoc.
    parts: HashMap<(usize, Option<BlockId>), (Expr, Expr)>,
    /// Why the encoding was abandoned, if it was.
    pub(super) violation: Option<&'static str>,
    pub(super) map: LargeBlockMap,
}

impl LargeBlock {
    pub(super) fn new(plan: LargeBlockPlan) -> Self {
        let root = plan.order[0];
        Self {
            plan,
            in_edges: BTreeMap::new(),
            entered: BTreeSet::new(),
            reach: BTreeMap::new(),
            constraints: Vec::new(),
            error_sites: Vec::new(),
            cursor: None,
            parts: HashMap::new(),
            violation: None,
            map: LargeBlockMap {
                root,
                sites: Vec::new(),
                in_edges: BTreeMap::new(),
                columns: BTreeSet::new(),
            },
        }
    }

    fn fail(&mut self, why: &'static str) {
        self.violation.get_or_insert(why);
    }
}

/// How a large-block query maps back to the per-block encoding: which Boolean
/// is which error site, and which selector is which transition. Linear in the
/// region's emissions.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct LargeBlockMap {
    /// The region's root: the function's entry block, the one relation kept.
    pub root: BlockId,
    /// Every error site, in emission order.
    pub sites: Vec<LargeBlockErrorSite>,
    /// For every merged block, the transitions emitted into it, in emission
    /// order.
    pub in_edges: BTreeMap<BlockId, Vec<LargeBlockEdge>>,
    /// The DEFINITIONAL variables: every column variable (a merged block's
    /// input, or a link of its selection chain) and every cross-block part
    /// variable, each defined exactly once by an UNCONDITIONAL equality
    /// `c = t`. They are the only variables an array-sorted equality of the
    /// encoding has on its left — a definition of a fresh variable, not a
    /// hypothesis on two program arrays (the junk-lane invariant on
    /// `ArrayValue`, which `vc_equates_array_terms_beyond` checks, a second
    /// definition included).
    pub columns: BTreeSet<String>,
}

/// One error site of a large-block query: `site ⇒ (prefix ∧ condition)`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct LargeBlockErrorSite {
    /// The site's Boolean variable.
    pub var: String,
    /// The block whose translation emitted it.
    pub block: BlockId,
    /// The instruction of that block it was emitted for.
    pub instruction_index: usize,
}

/// One transition of a large-block query: `selector ⇒ (prefix ∧ guard)`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct LargeBlockEdge {
    /// The transition's selector variable.
    pub selector: String,
    /// The block whose translation emitted it.
    pub source: BlockId,
}

/// The block path of a large-block counterexample: the per-block derivation it
/// stands for (see the module documentation, "L ⇒ S").
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct LargeBlockPath {
    /// The blocks from the entry to the erroring block, in execution order.
    pub blocks: Vec<BlockId>,
    /// The error site the path reaches.
    pub site: LargeBlockErrorSite,
}

impl LargeBlockMap {
    /// The block path a model of the large-block query takes: the first error
    /// site the model makes true, then, from its block back to the entry, the
    /// first true selector into each block. `model` answers a Boolean
    /// variable's value; `None` (unknown variable, missing value, or no true
    /// selector where the query's implications require one) means the
    /// assignment is not a model of the query.
    ///
    /// A model of the query maps to a path the per-block encoding derives
    /// `error` along, with the model's values (module documentation,
    /// "L ⇒ S"). The walk is linear in the sites and in-edges it scans, plus a
    /// logarithmic set probe per block of the path.
    pub fn counterexample_path(
        &self,
        mut model: impl FnMut(&str) -> Option<bool>,
    ) -> Option<LargeBlockPath> {
        let mut site = None;
        for candidate in &self.sites {
            if model(&candidate.var)? {
                site = Some(candidate.clone());
                break;
            }
        }
        let site = site?;
        let mut blocks = vec![site.block];
        let mut visited = BTreeSet::from([site.block]);
        let mut current = site.block;
        while current != self.root {
            let edges = self.in_edges.get(&current)?;
            let mut source = None;
            for edge in edges {
                if model(&edge.selector)? {
                    source = Some(edge.source);
                    break;
                }
            }
            current = source?;
            // An acyclic region never revisits a block; a model that seems to
            // is not a model of the query.
            if !visited.insert(current) {
                return None;
            }
            blocks.push(current);
        }
        blocks.reverse();
        Some(LargeBlockPath { blocks, site })
    }
}

/// Whether `expr` is a variable or a literal, which a merged block may read
/// directly without a column variable.
fn is_atomic(expr: &Expr) -> bool {
    matches!(
        expr.value(),
        ExprValue::Var { .. }
            | ExprValue::BoolConst(_)
            | ExprValue::BitVecConst { .. }
            | ExprValue::IntConst(_)
            | ExprValue::RealConst(_)
    )
}

/// A variable-free term of `sort`, the value a column takes where no in-edge is
/// selected (the block is not reached, so nothing reads it). `None` for a sort
/// with no literal here; the caller then keeps the in-edge's own term.
fn default_term(sort: &Sort) -> Option<Expr> {
    if sort.is_bool() {
        return Some(Expr::bool_const(false));
    }
    if let Some(width) = sort.bitvec_width() {
        return Some(Expr::bitvec_const(0u64, width));
    }
    if let Some(array) = sort.array_sort() {
        let element = default_term(&array.element_sort)?;
        return Some(Expr::const_array(array.index_sort.clone(), element));
    }
    None
}

/// Whether `expr` is the literal `true` (the root block's reachability).
fn is_true(expr: &Expr) -> bool {
    matches!(expr.value(), ExprValue::BoolConst(true))
}

/// `prefix ∧ condition`, or `condition` alone under the literal `true`.
fn and_after(prefix: Expr, condition: Expr) -> Result<Expr, ay_bindings::SortError> {
    if is_true(&prefix) { Ok(condition) } else { prefix.try_and(condition) }
}

/// `antecedent ⇒ consequent`, or `consequent` alone under the literal `true`.
fn implied_by(antecedent: Expr, consequent: Expr) -> Expr {
    if is_true(&antecedent) { consequent } else { antecedent.implies(consequent) }
}

/// `term` where `reach` holds, else `default` (the term itself without one):
/// what a definition reads so that a havoc in `term` is read only where its
/// block is reached.
fn while_reached(
    reach: &Expr,
    term: Expr,
    default: Option<Expr>,
) -> Result<Expr, ay_bindings::SortError> {
    match default {
        Some(default) if !is_true(reach) => Expr::try_ite(reach.clone(), term, default),
        _ => Ok(term),
    }
}

/// The sorts of the relation columns a value of `ty` occupies, in the order
/// `declare_relation_binding_lifted` declares them.
pub(super) fn relation_leaf_sorts(
    module: &Module,
    ty: &Ty,
    depth: u32,
    smt_arrays: bool,
    sorts: &mut Vec<Sort>,
) {
    match composite_shape_of(module, ty) {
        Some(CompositeShape::Fields(field_tys)) => {
            for field_ty in &field_tys {
                relation_leaf_sorts(module, field_ty, depth, smt_arrays, sorts);
            }
        }
        Some(CompositeShape::Array { .. }) if !smt_arrays => {}
        Some(CompositeShape::Array { elem, .. }) => {
            relation_leaf_sorts(module, &elem, depth + 1, smt_arrays, sorts);
        }
        None => sorts.push(lifted_sort(ty_to_sort(ty), depth)),
    }
}

/// The binding of a value of `ty` whose relation columns are the next leaves
/// of `leaves` — the shape `declare_relation_binding_lifted` gives it, with
/// these terms where it declares formals. `None` when `leaves` runs out.
pub(super) fn relation_binding_from_leaves(
    module: &Module,
    ty: &Ty,
    depth: u32,
    smt_arrays: bool,
    leaves: &mut impl Iterator<Item = Expr>,
) -> Option<ValueBinding> {
    Some(match composite_shape_of(module, ty) {
        Some(CompositeShape::Fields(field_tys)) => {
            let mut fields = Vec::with_capacity(field_tys.len());
            for field_ty in &field_tys {
                fields.push(relation_binding_from_leaves(
                    module, field_ty, depth, smt_arrays, leaves,
                )?);
            }
            ValueBinding::Aggregate(AggregateValue { fields })
        }
        Some(CompositeShape::Array { len, .. }) if !smt_arrays => {
            ValueBinding::Array(ArrayValue::shape_only(len))
        }
        Some(CompositeShape::Array { elem, len }) => ValueBinding::Array(ArrayValue {
            len,
            lanes: Some(Box::new(relation_binding_from_leaves(
                module,
                &elem,
                depth + 1,
                smt_arrays,
                leaves,
            )?)),
        }),
        None => ValueBinding::Scalar(leaves.next()?),
    })
}

impl ChcFuncTranslator<'_> {
    /// Whether the rules of the block being translated are absorbed into the
    /// large-block query.
    pub(super) fn absorbing_large_block(&self) -> bool {
        self.large_block.as_ref().is_some_and(|large| large.cursor.is_some())
    }

    /// Whether `block` is a merged block (no relation of its own).
    pub(super) fn is_merged_block(&self, block: BlockId) -> bool {
        self.large_block.as_ref().is_some_and(|large| large.plan.merged.contains(&block))
    }

    /// Whether the large-block encoding applies and `dominator` dominates
    /// `block` in its region (fact 2: the parts `dominator` built are then
    /// exact in `block`).
    pub(super) fn large_block_dominates(&self, dominator: BlockId, block: BlockId) -> bool {
        self.large_block
            .as_ref()
            .is_some_and(|large| large.plan.dominators.dominates(dominator, block))
    }

    fn large_block_var(&mut self, name: String, sort: Sort) -> Expr {
        self.work.large_block_variables += 1;
        self.vc.declare_var(name, sort)
    }

    /// A fresh definitional variable `name = definition`, owned by `block`.
    fn large_block_define(
        &mut self,
        block: BlockId,
        name: String,
        definition: Expr,
    ) -> Option<Expr> {
        let var = self.large_block_var(name.clone(), definition.sort().clone());
        self.work.large_block_column_variables += 1;
        let Ok(equation) = var.clone().try_eq(definition) else {
            self.large_block_fail("a definition's sides have different sorts");
            return None;
        };
        self.large_block_push(block, equation);
        if let Some(large) = self.large_block.as_mut() {
            large.map.columns.insert(name);
        }
        Some(var)
    }

    /// Start absorbing the root block: its reachability is `true`.
    pub(super) fn large_block_begin_root(&mut self, block: BlockId) {
        if let Some(large) = self.large_block.as_mut() {
            large.cursor = Some(Cursor::new(block, Expr::true_()));
            large.reach.insert(block, Expr::true_());
        }
    }

    /// Start absorbing merged block `block`: declare its reachability, merge
    /// the terms its emitted in-edges pass into its columns, and bind them
    /// where S binds the relation formals.
    pub(super) fn large_block_enter(&mut self, block: &Block) {
        let id = block.id;
        let Some(large) = self.large_block.as_mut() else {
            return;
        };
        large.entered.insert(id);
        let edges = large.in_edges.remove(&id).unwrap_or_default();
        large.map.in_edges.insert(
            id,
            edges
                .iter()
                .map(|edge| LargeBlockEdge {
                    selector: edge.selector_name.clone(),
                    source: edge.source,
                })
                .collect(),
        );

        let reach = self.large_block_var(format!("bb{}_lbe_r", id.index()), Sort::bool());
        if let Some(large) = self.large_block.as_mut() {
            large.reach.insert(id, reach.clone());
        }
        let any_in_edge = Expr::or_many(edges.iter().map(|edge| edge.selector.clone()).collect());
        self.large_block_push(id, reach.clone().implies(any_in_edge));
        // A taken transition reaches its target (JUSTIFICATION, downward).
        for edge in &edges {
            self.large_block_push(id, edge.selector.clone().implies(reach.clone()));
        }
        // Absorb from here on, also if the layout below fails: the block's
        // emissions must never reach the per-block path without a relation.
        if let Some(large) = self.large_block.as_mut() {
            large.cursor = Some(Cursor::new(id, reach.clone()));
        }

        let threaded = self.block_threaded_params.get(&id).cloned().unwrap_or_default();
        let cells = self.block_promoted_cells.get(&id).cloned().unwrap_or_default();
        let smt_arrays = self.array_content_blocks.contains(&id);
        let mut sorts = Vec::new();
        for (_, ty) in threaded.iter().chain(cells.iter()).chain(block.params.iter()) {
            relation_leaf_sorts(self.module, ty, 0, smt_arrays, &mut sorts);
        }
        if edges.iter().any(|edge| edge.args.len() != sorts.len()) {
            self.large_block_fail("an in-edge passes a different number of columns");
            return;
        }

        let mut leaves = Vec::with_capacity(sorts.len());
        let mut selects = false;
        for (column, sort) in sorts.iter().enumerate() {
            self.work.large_block_column_merges += 1;
            if edges.is_empty() {
                // Nothing transfers here: `¬r_B` holds and every formula of the
                // block is vacuous; its inputs are free.
                leaves.push(self.fresh_large_block_unreached(id, column, sort));
                continue;
            }
            let Some(leaf) =
                self.large_block_column(id, &reach, &edges, column, sort, &mut selects)
            else {
                return;
            };
            leaves.push(leaf);
        }
        if selects && edges.len() > 1 {
            self.large_block_at_most_one(id, &edges);
        }

        let module = self.module;
        let mut leaves = leaves.into_iter();
        let mut bind = |values: &[(trust_ir::value::ValueId, Ty)]| {
            values
                .iter()
                .map(|(_, ty)| relation_binding_from_leaves(module, ty, 0, smt_arrays, &mut leaves))
                .collect::<Option<Vec<_>>>()
        };
        let (Some(threaded_bindings), Some(cell_bindings), Some(param_bindings)) =
            (bind(&threaded), bind(&cells), bind(&block.params))
        else {
            self.large_block_fail("the column layout does not fit the block's values");
            return;
        };
        self.block_threaded_bindings.insert(id, threaded_bindings);
        self.block_cell_bindings.insert(id, cell_bindings);
        self.block_param_bindings.insert(id, param_bindings);
    }

    /// The term merged block `block` reads for `column`, from the terms its
    /// (non-empty) in-edges pass, compared by identity (`TermKey`): an atom
    /// every in-edge passes; else a column variable defined as the compound
    /// term every in-edge passes; else the head of a chain of column variables
    /// over the in-edges that pass another term than the most frequent one
    /// (`selects` is then set: the block needs its at-most-one ladder). `None`
    /// when the encoding was abandoned.
    fn large_block_column(
        &mut self,
        block: BlockId,
        reach: &Expr,
        edges: &[InEdge],
        column: usize,
        sort: &Sort,
        selects: &mut bool,
    ) -> Option<Expr> {
        let keys: Vec<TermKey> = edges.iter().map(|edge| term_key(&edge.args[column])).collect();
        let mut counts: HashMap<&TermKey, usize> = HashMap::with_capacity(keys.len());
        for key in &keys {
            *counts.entry(key).or_insert(0) += 1;
        }
        // The most frequent term, the first in emission order among the ties.
        let mut majority = 0;
        for (index, key) in keys.iter().enumerate() {
            if counts[key] > counts[&keys[majority]] {
                majority = index;
            }
        }
        let common = edges[majority].args[column].clone();
        if counts[&keys[majority]] == edges.len() && is_atomic(&common) {
            return Some(common);
        }
        // The term the block reads where no listed in-edge is taken.
        let tail = if self.term_facts.mentions_havoc(&common) {
            match while_reached(reach, common.clone(), default_term(sort)) {
                Ok(tail) => tail,
                Err(_) => {
                    self.large_block_fail("an in-edge passes a column of another sort");
                    return None;
                }
            }
        } else {
            common
        };
        let others: Vec<&InEdge> = edges
            .iter()
            .zip(&keys)
            .filter(|(_, key)| **key != keys[majority])
            .map(|(edge, _)| edge)
            .collect();
        if others.is_empty() {
            // One compound term on every in-edge.
            return self.large_block_define(
                block,
                format!("bb{}_lbe_c{column}", block.index()),
                tail,
            );
        }
        *selects = true;
        // The chain, built from its end: `c_i = ite(s_i, a_i, c_{i+1})`.
        let mut next = tail;
        for (link, edge) in others.iter().enumerate().rev() {
            let name = if link == 0 {
                format!("bb{}_lbe_c{column}", block.index())
            } else {
                format!("bb{}_lbe_c{column}_{link}", block.index())
            };
            let Ok(selection) =
                Expr::try_ite(edge.selector.clone(), edge.args[column].clone(), next)
            else {
                self.large_block_fail("an in-edge passes a column of another sort");
                return None;
            };
            next = self.large_block_define(block, name, selection)?;
        }
        Some(next)
    }

    /// AT MOST ONE of `edges`' selectors holds: the sequential ladder
    /// `s₁ ⇒ o₁`, `o_{j-1} ⇒ o_j`, `s_j ⇒ o_j`, `s_j ⇒ ¬o_{j-1}`, with `o_j`
    /// "one of the first `j` selectors holds" (`k - 1` Booleans, `O(k)` clauses).
    fn large_block_at_most_one(&mut self, block: BlockId, edges: &[InEdge]) {
        let mut previous: Option<Expr> = None;
        for (index, edge) in edges.iter().enumerate() {
            if let Some(before) = &previous {
                self.large_block_push(block, edge.selector.clone().implies(before.clone().not()));
            }
            if index + 1 == edges.len() {
                break;
            }
            let some =
                self.large_block_var(format!("bb{}_lbe_o{index}", block.index()), Sort::bool());
            self.large_block_push(block, edge.selector.clone().implies(some.clone()));
            if let Some(before) = previous {
                self.large_block_push(block, before.implies(some.clone()));
            }
            previous = Some(some);
        }
    }

    /// A free input of a merged block nothing transfers to. Declared as a
    /// translation havoc: no execution reaches the block.
    fn fresh_large_block_unreached(&mut self, block: BlockId, column: usize, sort: &Sort) -> Expr {
        self.work.large_block_variables += 1;
        self.vc.declare_havoc_var(
            &format!("lbe_unreached_bb{}_c{column}", block.index()),
            sort.clone(),
        )
    }

    /// The term block `reader` reads for `part`, a fat-pointer part that block
    /// `owner` built and that dominates `reader` (fact 2): an atom as it is;
    /// a compound part through a part variable defined as it — one per part, or
    /// one per (part, reader) as `ite(r_reader, part, d)` when it mentions a
    /// havoc, so the refutation gate reads that havoc only where `reader` is
    /// reached. `None` when the encoding was abandoned.
    pub(super) fn large_block_part(
        &mut self,
        owner: BlockId,
        reader: BlockId,
        part: Expr,
    ) -> Option<Expr> {
        if is_atomic(&part) {
            return Some(part);
        }
        let havoc = self.term_facts.mentions_havoc(&part);
        let key = (node_address(&part), havoc.then_some(reader));
        let large = self.large_block.as_mut()?;
        if let Some((_, var)) = large.parts.get(&key) {
            return Some(var.clone());
        }
        let index = large.parts.len();
        let (definer, definition) = if havoc {
            let reach = large.reach.get(&reader)?.clone();
            let default = default_term(part.sort());
            match while_reached(&reach, part.clone(), default) {
                Ok(definition) => (reader, definition),
                Err(_) => {
                    self.large_block_fail("a part's default has another sort");
                    return None;
                }
            }
        } else {
            (owner, part.clone())
        };
        let var = self.large_block_define(
            definer,
            format!("bb{}_lbe_m{index}", definer.index()),
            definition,
        )?;
        self.large_block.as_mut()?.parts.insert(key, (part, var.clone()));
        Some(var)
    }

    /// Stop absorbing the block being translated. A merged block's bindings are
    /// dropped: nothing reads them after its translation.
    pub(super) fn large_block_leave(&mut self, block: BlockId) {
        let Some(mut cursor) = self.large_block.as_mut().and_then(|large| large.cursor.take())
        else {
            self.drop_merged_bindings(block);
            return;
        };
        // JUSTIFICATION, upward: a prefix Boolean holds only for an emission
        // made at it or at a longer prefix, so a model's true Booleans of a
        // block are exactly what one of its rules uses; and a block whose error
        // site fires takes no transition, so the path ends there.
        let owner = cursor.block;
        let mut prefixes = std::mem::take(&mut cursor.prefixes).into_iter().peekable();
        while let Some((prefix, emitted)) = prefixes.next() {
            let mut justifications = emitted;
            if let Some((longer, _)) = prefixes.peek() {
                justifications.push(longer.clone());
            }
            self.large_block_push(owner, implied_by(prefix, Expr::or_many(justifications)));
        }
        if !cursor.out_selectors.is_empty() && !cursor.sites.is_empty() {
            // `t_B`: some selector out of `B` holds. One clause per selector and
            // per site, whatever the block's out-degree and site count.
            let taken = if cursor.out_selectors.len() == 1 || cursor.sites.len() == 1 {
                None
            } else {
                Some(self.large_block_var(format!("bb{}_lbe_t", owner.index()), Sort::bool()))
            };
            match taken {
                Some(taken) => {
                    for selector in cursor.out_selectors {
                        self.large_block_push(owner, selector.implies(taken.clone()));
                    }
                    for site in cursor.sites {
                        self.large_block_push(owner, site.implies(taken.clone().not()));
                    }
                }
                None => {
                    let any_transition = Expr::or_many(cursor.out_selectors);
                    for site in cursor.sites {
                        self.large_block_push(owner, site.implies(any_transition.clone().not()));
                    }
                }
            }
        }
        self.drop_merged_bindings(block);
    }

    fn drop_merged_bindings(&mut self, block: BlockId) {
        if self.is_merged_block(block) {
            self.block_threaded_bindings.remove(&block);
            self.block_cell_bindings.remove(&block);
            self.block_param_bindings.remove(&block);
        }
    }

    fn large_block_push(&mut self, block: BlockId, constraint: Expr) {
        if let Some(large) = self.large_block.as_mut() {
            large.constraints.push((block, constraint));
        }
    }

    fn large_block_fail(&mut self, why: &'static str) {
        if let Some(large) = self.large_block.as_mut() {
            large.fail(why);
        }
    }

    /// The prefix Boolean of `path_constraints`, the running list of the block
    /// being absorbed at an emission: extends the block's chain by the
    /// constraints pushed since its last emission. `None` (and the encoding is
    /// abandoned) when the list is not an extension of the absorbed prefix.
    fn large_block_prefix(&mut self, path_constraints: &[Expr]) -> Option<Expr> {
        let large = self.large_block.as_mut()?;
        if large.violation.is_some() {
            return None;
        }
        let cursor = large.cursor.as_ref()?;
        let len = path_constraints.len();
        let extends = len >= cursor.chain_len
            && match &cursor.last {
                None => cursor.chain_len == 0,
                Some(last) => {
                    std::ptr::eq(path_constraints[cursor.chain_len - 1].value(), last.value())
                }
            };
        if !extends {
            large.fail("an emitted rule's constraints are not its block's path-constraint prefix");
            return None;
        }
        if len == cursor.chain_len {
            return Some(cursor.chain.clone());
        }
        let (block, chain, chain_len) = (cursor.block, cursor.chain.clone(), cursor.chain_len);
        let prefix = self.large_block_var(format!("bb{}_lbe_p{len}", block.index()), Sort::bool());
        let mut conjuncts = Vec::with_capacity(len - chain_len + 1);
        if !is_true(&chain) {
            conjuncts.push(chain);
        }
        conjuncts.extend(path_constraints[chain_len..len].iter().cloned());
        let Ok(segment) = Expr::try_and_many(conjuncts) else {
            self.large_block_fail("a path constraint is not Boolean");
            return None;
        };
        self.large_block_push(block, prefix.clone().implies(segment));
        let large = self.large_block.as_mut()?;
        let cursor = large.cursor.as_mut()?;
        cursor.chain = prefix.clone();
        cursor.chain_len = len;
        cursor.last = Some(path_constraints[len - 1].clone());
        cursor.prefixes.push((prefix.clone(), Vec::new()));
        Some(prefix)
    }

    /// The next name of an emission of the block being absorbed.
    fn large_block_emission(&mut self) -> Option<(BlockId, usize)> {
        let cursor = self.large_block.as_mut()?.cursor.as_mut()?;
        let index = cursor.emitted;
        cursor.emitted += 1;
        Some((cursor.block, index))
    }

    /// Record emission Boolean `var` at the block's current (longest) prefix,
    /// the prefix it was emitted under; `site` tells an error site from a
    /// transition selector.
    fn large_block_record(&mut self, var: &Expr, site: bool) {
        let Some(cursor) = self.large_block.as_mut().and_then(|large| large.cursor.as_mut()) else {
            return;
        };
        if let Some((_, emitted)) = cursor.prefixes.last_mut() {
            emitted.push(var.clone());
        }
        if site {
            cursor.sites.push(var.clone());
        } else {
            cursor.out_selectors.push(var.clone());
        }
    }

    /// Absorb an error rule `error ← B ∧ path_constraints ∧ condition`.
    pub(super) fn large_block_error(&mut self, path_constraints: &[Expr], condition: Expr) {
        let Some(prefix) = self.large_block_prefix(path_constraints) else {
            return;
        };
        let Some((block, index)) = self.large_block_emission() else {
            return;
        };
        let name = format!("bb{}_lbe_e{index}", block.index());
        let site = self.large_block_var(name.clone(), Sort::bool());
        let Ok(body) = and_after(prefix, condition) else {
            self.large_block_fail("an error condition is not Boolean");
            return;
        };
        self.large_block_push(block, site.clone().implies(body));
        self.large_block_record(&site, true);
        let instruction_index = self.current_instruction;
        if let Some(large) = self.large_block.as_mut() {
            large.error_sites.push(site);
            large.map.sites.push(LargeBlockErrorSite { var: name, block, instruction_index });
        }
    }

    /// Absorb a transition `target(head_args) ← B ∧ path_constraints ∧ guard`.
    pub(super) fn large_block_transition(
        &mut self,
        target: BlockId,
        guard: Option<Expr>,
        path_constraints: &[Expr],
        head_args: Vec<Expr>,
    ) {
        if self.large_block.as_ref().is_none_or(|large| large.violation.is_some()) {
            return;
        }
        let into_region = self.large_block.as_ref().is_some_and(|large| {
            large.plan.merged.contains(&target) && !large.entered.contains(&target)
        });
        if !into_region {
            self.large_block_fail("a transition leaves the region or targets a translated block");
            return;
        }
        let Some(prefix) = self.large_block_prefix(path_constraints) else {
            return;
        };
        let Some((block, index)) = self.large_block_emission() else {
            return;
        };
        let selector_name = format!("bb{}_lbe_s{index}", block.index());
        let selector = self.large_block_var(selector_name.clone(), Sort::bool());
        let condition = match guard {
            Some(guard) => match and_after(prefix, guard) {
                Ok(condition) => condition,
                Err(_) => {
                    self.large_block_fail("a transition guard is not Boolean");
                    return;
                }
            },
            None => prefix,
        };
        self.large_block_push(block, selector.clone().implies(condition));
        self.large_block_record(&selector, false);
        if let Some(large) = self.large_block.as_mut() {
            large.in_edges.entry(target).or_default().push(InEdge {
                selector,
                selector_name,
                source: block,
                args: head_args,
            });
        }
    }

    /// Emit the query rule `error ← bbE(x̄) ∧ Φ ∧ (f₁ ∨ … ∨ fₘ)`. No error site, no
    /// rule: nothing in the region can fail, as in S.
    pub(super) fn large_block_finish(&mut self) {
        let Some(large) = self.large_block.as_mut() else {
            return;
        };
        #[cfg(test)]
        if FORCE_VIOLATION.with(std::cell::Cell::get) {
            large.fail("forced by a test");
        }
        if large.violation.is_none() && !large.in_edges.is_empty() {
            large.fail("a transition targets a block the region never translated");
        }
        if large.violation.is_some() || large.error_sites.is_empty() {
            return;
        }
        let root = large.map.root;
        // Only the blocks with a path to an error site can be on a derivation:
        // the others' formulas are dropped, and a transition into one of them is
        // never taken (`¬s`), so justification stays exact. Linear in the
        // region's transitions.
        let mut cone: BTreeSet<BlockId> = large.map.sites.iter().map(|site| site.block).collect();
        let mut pending: Vec<BlockId> = cone.iter().copied().collect();
        while let Some(block) = pending.pop() {
            for edge in large.map.in_edges.get(&block).into_iter().flatten() {
                if cone.insert(edge.source) {
                    pending.push(edge.source);
                }
            }
        }
        let mut body: Vec<Expr> = std::mem::take(&mut large.constraints)
            .into_iter()
            .filter_map(|(block, constraint)| cone.contains(&block).then_some(constraint))
            .collect();
        for (target, edges) in &large.map.in_edges {
            if cone.contains(target) {
                continue;
            }
            for edge in edges.iter().filter(|edge| cone.contains(&edge.source)) {
                body.push(Expr::var(edge.selector.clone(), Sort::bool()).not());
            }
        }
        body.push(Expr::or_many(std::mem::take(&mut large.error_sites)));
        let Some(entry) = self.block_app(root) else {
            self.large_block_fail("the region's root has no relation");
            return;
        };
        self.vc
            .add_rule(Rule::new(RuleBody::new(Some(entry), body), RelationApp::nullary(ERROR_REL)));
    }
}
