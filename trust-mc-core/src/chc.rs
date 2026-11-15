// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Constrained Horn Clause (CHC) verification conditions.
//!
//! CHC VCs represent unbounded verification problems where:
//! - UNSAT means the property holds (no reachable error state)
//! - SAT means a counterexample exists (error state reachable)
//!
//! ## CHC Encoding
//!
//! Each basic block becomes a relation, and edges become Horn rules:
//! ```text
//! (declare-rel block_0 (State))
//! (declare-rel block_1 (State))
//! (declare-rel error ())
//!
//! (rule (=> (init state) (block_0 state)))
//! (rule (=> (and (block_0 state) (guard) (transition)) (block_1 state')))
//! (rule (=> (and (block_n state) (violation)) error))
//!
//! (query error)
//! ```
//!
//! The solver synthesizes invariants to prove error is unreachable.

use std::collections::HashSet;
use std::sync::Arc;

use crate::constraints::Constraints;
use crate::decl::Decl;
use crate::ident::SourceLocation;
use crate::violation::PropertyKind;
use ay_bindings::{AYProgram, Expr, ExprValue, Sort};

/// Reserved name prefix of every TRANSLATION HAVOC variable: a fresh, unconstrained
/// value a translator introduces where it does not model a value exactly (an opaque
/// call's result, a value with no binding in the block, a read of lanes it does not
/// carry). Declared only through [`ChcVc::declare_havoc_var`].
///
/// A havoc is a sound over-approximation for a PROOF, never a value of the program:
/// a constraint that mentions it — even an equality `(= h 263)` that looks like a
/// definition — is a restriction the solver satisfies by CHOOSING `h`, so a model
/// that assigns it need not correspond to any execution. A refutation gate reads
/// this prefix to tell such a variable from one the program defines
/// (`trust_mc_driver`'s bounded-unroll grounding gate and the consumer's
/// independent replay). The name carries the identity because the variable's name
/// is what survives into the lowered CHC problem and into its normalized-input
/// digest, so the producer's gate and the consumer's replay classify the same
/// digest-bound problem the same way.
///
/// Every other variable the native translator declares is a block-relation
/// argument (`bb{N}_…`), so a relation argument never carries this prefix; a name
/// that carries it wrongly can only make a refutation gate decline (fail closed).
pub const TRANSLATION_HAVOC_VAR_PREFIX: &str = "havoc__";

/// Whether `name` names a translation havoc (see [`TRANSLATION_HAVOC_VAR_PREFIX`]).
#[must_use]
pub fn is_translation_havoc_var(name: &str) -> bool {
    name.starts_with(TRANSLATION_HAVOC_VAR_PREFIX)
}

/// Per-property metadata for a single CHC check site (BSEM-18).
///
/// The CHC encoder emits one `error_p{id}` relation per distinct check site
/// (bounds, overflow, alignment, div-by-zero, user assert, UB check, …), each
/// bridged into the aggregate `error` query relation via a rule
/// `error_p{id} → error`. This record carries the deterministic property
/// identity so the driver can report each check's verdict independently
/// (FAILED / VERIFIED / UNREACHABLE) instead of one undifferentiated `error`.
///
/// The `id` is a per-harness sequence number allocated in deterministic MIR
/// traversal order (no RNG, no hashmap iteration order, no timestamps) so
/// results are stable and diffable across runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChcProperty {
    /// Per-harness deterministic property id (also the `error_p{id}` suffix).
    pub id: u32,
    /// The kind of check (assertion, overflow, bounds, …).
    pub kind: PropertyKind,
    /// The MIR basic block the check was emitted from (for traceability).
    pub bb: usize,
    /// The per-property error relation name, e.g. `error_p3`.
    pub relation: String,
    /// Optional human-readable message (e.g. the assert expression text).
    pub message: Option<String>,
    /// Optional source location of the check.
    pub location: Option<SourceLocation>,
    /// Task #78: whether this check's reachability is DATA-DEPENDENT on any
    /// sound-approximation-freed SMT variable (see [`ChcVc::approximated_vars`]).
    ///
    /// Computed at VC finalization by a transitive constraint-chain analysis:
    /// `Some(true)` means the violated `error_p{id}` rule (or an ancestor guard
    /// that gates it) reads a value derived from a freed var, so a tainted SAT
    /// counterexample here may be a pure havoc artifact — it must STAY
    /// OverApproximation. `Some(false)` means the check's reachability is
    /// independent of every freed var, so the driver MAY certify it Genuine
    /// (subject to [`ChcVc::approximation_identity_complete`]). `None` means the
    /// analysis was not run — the driver treats it as dependent (fail-closed).
    pub approximation_dependent: Option<bool>,

    /// Set when the ENCODER proved this check cannot fire and therefore emitted
    /// no `error_p{id}` rule — the reason, for the record.
    ///
    /// A registered property with no rule is ambiguous to the driver: it cannot
    /// tell "discharged at encode time" from "the encoder dropped the check",
    /// so it fails closed with `[AY:UNKNOWN_REASON:LostErrorRules]`. Measured
    /// 2026-09-17: that reason was 32 of 32 unparked CHC `unknown` rows.
    /// This field removes the ambiguity at the only place that knows the
    /// answer. It is NOT a verdict on its own — see
    /// `ChcVc::all_properties_discharged_at_encode`, which is what licenses the
    /// canonical discharge, and only when EVERY property is accounted for.
    pub discharged_at_encode: Option<&'static str>,
}

/// A Constrained Horn Clause verification condition.
///
/// This represents an unbounded verification problem for a single harness.
/// The emitter converts this to CHC format where SAT indicates a reachable
/// error state.
#[derive(Debug, Clone)]
pub struct ChcVc {
    /// Declarations for symbolic constants and datatypes.
    pub decls: Vec<Decl>,

    /// Implicitly universally quantified variables for use in rules.
    /// These become `declare-var` in SMT-LIB2.
    vars: Vec<VarDecl>,

    /// Tracks declared variable names for deduplication.
    ///
    /// z3's CHC parser rejects duplicate `(declare-var ...)` commands.
    /// Multiple call sites (fragment fallback, intermediate variables)
    /// may attempt to re-declare the same variables. This set ensures
    /// each name appears at most once in `vars`.
    declared_var_names: HashSet<Arc<str>>,

    /// Relation declarations (one per basic block plus error relation).
    pub relations: Vec<RelationDecl>,

    /// Horn rules encoding control flow and transitions.
    pub rules: Vec<Rule>,

    /// The query (which relation to check for reachability).
    pub query: ChcQuery,

    /// Cover property declarations for secondary satisfiability checks.
    ///
    /// Each entry is `(name, condition)` where `name` becomes a `(declare-const name Bool)`
    /// and `condition` is the cover guard. The driver's secondary SAT check
    /// (`build_cover_sat_query_for_chc`) extracts these from the emitted SMT-LIB.
    /// Part of #1162: Cover semantics for CHC/PDR path.
    pub cover_assertions: Vec<(String, Expr)>,

    /// Per-property metadata, one entry per distinct check site (BSEM-18).
    ///
    /// Populated by the encoder as each check emits its `error_p{id}` relation.
    /// Serialized into the VC artifact so the driver can report per-property
    /// verdicts. This is pure metadata — it is NOT emitted into the SMT-LIB
    /// program (the `error_p{id}` relations/rules themselves carry the semantics).
    pub properties: Vec<ChcProperty>,

    /// Set by a LEGITIMATE trivially-safe discharge (TIC template check,
    /// bounded straight-line discharge) when it deliberately empties the rule
    /// system after proving the obligations by other means.
    ///
    /// The degenerate-system soundness fail-close (#67) treats a VC with
    /// registered properties but no program rules as a silently-collapsed
    /// encoding and demotes it — this flag is the exemption channel that
    /// distinguishes "proved then cleared" from "silently discarded".
    pub trivially_safe_discharged: bool,

    /// KEEP-ERROR-OBLIGATIONS mode for the rule-pruning passes.
    ///
    /// Set only by the lost-checks recovery (`passes_lost_every_error_obligation`):
    /// a pass sequence turned a VC with error obligations and registered
    /// properties into one with no error obligation left. Nothing was proved
    /// there: the driver cannot tell that shape from checks the encoding lost,
    /// and a real missed bug (a loop body the encoding never reaches) hid behind
    /// it. With the flag set, `prune_orphan_block_rules` keeps error obligations
    /// whose body relation nothing derives, and the false-rule pruning passes
    /// keep error obligations whose body folded to `false` (as a literal-`false`
    /// body over the same body relation). The obligations then reach the
    /// straight-line discharge and the solver, whose Safe / vacuous / refuted
    /// answers decide the harness instead of the collapse.
    pub keep_error_obligations: bool,

    /// Set when a trivially-safe discharge proved the obligations UNREACHABLE
    /// rather than SAFE — i.e. no check site was reachable at all, because
    /// every path into it was pruned as infeasible (`kani::assume(false)`, two
    /// assumptions that cannot both hold, an unreachable body).
    ///
    /// The discharge replaces the whole system with `false => error`, and at
    /// that point a genuine proof and a vacuous one are byte-identical — the
    /// BMC lane's reachability probe has nothing left to read. This flag is
    /// the channel that carries the distinction across the discharge, so the
    /// driver can hand the run to the same V4 vacuity gate BMC uses instead of
    /// reporting a clean proof of nothing.
    pub vacuous_all_checks_unreachable: bool,

    /// Task #78: SMT-var identities freed by RECORDED sound-approximation sites.
    ///
    /// Each entry is the base SMT variable name whose defining constraint a
    /// sound approximation deleted (a havoc leaving an unconstrained value).
    /// Names are stored WITHOUT the per-transition `__out` suffix (see
    /// [`normalize_approx_var`]) so that the pre- and post-state forms of the
    /// same state slot compare equal. The driver certifies a tainted SAT
    /// counterexample Genuine only when the violated `error_p{N}`'s transitive
    /// constraint chain reads NONE of these — the dependence analysis run at
    /// finalization records that verdict per-property in
    /// [`ChcProperty::approximation_dependent`].
    pub approximated_vars: Vec<String>,

    /// Task #78: number of sound-approximation EVENTS that recorded their
    /// freed-var identity (via [`record_approximation_identity`], counting both
    /// the "freed a named live var" and the "freed value is dead" cases).
    ///
    /// Compared at finalization against the sound-approximation counter total to
    /// derive [`approximation_identity_complete`]. Every approximation that does
    /// NOT flow through `record_approximation_identity` raises the counter total
    /// but not this count, so partial plumbing is fail-closed: an unaccounted
    /// approximation forces incompleteness for the whole harness.
    ///
    /// [`record_approximation_identity`]: ChcVc::record_approximation_identity
    /// [`approximation_identity_complete`]: ChcVc::approximation_identity_complete
    pub accounted_approximations: usize,

    /// Task #78: TRUE iff EVERY sound-approximation on this harness recorded its
    /// freed-var identity. Set at finalization (`accounted_approximations`
    /// covers the full sound-approximation counter total). Default FALSE so that
    /// an un-finalized or legacy VC never certifies. The driver refuses to
    /// certify a tainted counterexample Genuine unless this holds — an unplumbed
    /// approximation blocks certification for the whole harness (fail-closed).
    pub approximation_identity_complete: bool,
}

/// Task #78: strip the per-transition `__out` suffix so a state slot's pre-state
/// (`_x`) and post-state (`_x__out`) names normalize to the same identity.
#[must_use]
pub fn normalize_approx_var(name: &str) -> &str {
    name.strip_suffix("__out").unwrap_or(name)
}

/// Separator the constant-index array scalarization puts between an array
/// state variable and one of its cells: `A` becomes `A_at_0x<index>_bv<w>`
/// (`trust-mc-compiler`'s `scalarize_const_index_arrays`).
const SCALARIZED_CELL_SEPARATOR: &str = "_at_0x";

/// The array a constant-index scalarized cell was split from, if `name` (either
/// state spelling) is one: `float_binop_tbl_f32_at_0x3f8000003f800000_bv72`
/// belongs to `float_binop_tbl_f32`.
///
/// A freed array's cells are the SAME freed value read at a constant index, so
/// whoever decides "does this read a freed value" must see through the split.
/// Measured 2026-09-24 on tests/expected/test6/main.rs: `add2(1, 1) == 2.0`
/// became a select of the float-binop table at the constant key `1.0 + 1.0`,
/// scalarization renamed it to such a cell, and the taint closure (which only
/// knew the table's own name) marked the check independent of the table.
#[must_use]
pub fn scalarized_cell_parent(name: &str) -> Option<&str> {
    let name = normalize_approx_var(name);
    name.find(SCALARIZED_CELL_SEPARATOR).map(|pos| normalize_approx_var(&name[..pos]))
}

/// Whether `name` names a value in the freed set `tainted` (normalized names):
/// the variable itself, either state spelling, or a scalarized cell of a freed
/// array.
fn is_tainted_name(name: &str, tainted: &HashSet<String>) -> bool {
    tainted.contains(normalize_approx_var(name))
        || scalarized_cell_parent(name).is_some_and(|parent| tainted.contains(parent))
}

/// SMT name of the congruent f32 float-binop table.
///
/// The CHC encoder translates a symbolic float `a op b` to
/// `select(<table>, op ++ a ++ b)` over a read-only array no rule constrains
/// (`trust-mc-compiler`'s `float_binop_table.rs`), threads the table through
/// every relation unchanged, and records each select as an IDENTIFIED sound
/// approximation freeing this variable. Shared here because the driver's
/// counterexample recertification treats these variables specially: a
/// counterexample the dependence analysis certifies independent of a table is
/// also REPLAYED on a system with every table read removed before it may be
/// reported `Genuine` (`trust_mc_driver::replay_error_derivation_free_of`).
pub const FLOAT_BINOP_TABLE_F32: &str = "float_binop_tbl_f32";
/// SMT name of the congruent f64 float-binop table ([`FLOAT_BINOP_TABLE_F32`]).
pub const FLOAT_BINOP_TABLE_F64: &str = "float_binop_tbl_f64";

/// Whether `name` (either state spelling) is a congruent float-binop table.
#[must_use]
pub fn is_float_binop_table_var(name: &str) -> bool {
    matches!(normalize_approx_var(name), FLOAT_BINOP_TABLE_F32 | FLOAT_BINOP_TABLE_F64)
}

/// A variable declaration for CHC rules.
///
/// Variables declared with declare-var can be used in rules without
/// explicit quantification.
///
/// Part of #2267: `name` uses `Arc<str>` (O(1) clone) to match
/// `StateVarMgr::state_vars` without String allocation at creation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarDecl {
    /// The variable name.
    pub name: Arc<str>,
    /// The variable sort.
    pub sort: Sort,
}

impl VarDecl {
    /// Creates a new variable declaration.
    pub fn new(name: impl Into<Arc<str>>, sort: Sort) -> Self {
        Self { name: name.into(), sort }
    }
}

impl ChcVc {
    /// Creates a new empty CHC VC.
    pub fn new() -> Self {
        Self {
            decls: Vec::new(),
            vars: Vec::new(),
            declared_var_names: HashSet::new(),
            relations: Vec::new(),
            rules: Vec::new(),
            query: ChcQuery::default(),
            cover_assertions: Vec::new(),
            properties: Vec::new(),
            trivially_safe_discharged: false,
            keep_error_obligations: false,
            vacuous_all_checks_unreachable: false,
            approximated_vars: Vec::new(),
            accounted_approximations: 0,
            approximation_identity_complete: false,
        }
    }

    /// Adds a variable declaration, skipping duplicates.
    ///
    /// z3's CHC parser rejects duplicate `(declare-var ...)` commands,
    /// so each variable name is emitted at most once. Subsequent calls
    /// with the same name are silently ignored.
    pub fn add_var(&mut self, var: VarDecl) {
        if self.declared_var_names.insert(Arc::clone(&var.name)) {
            self.vars.push(var);
        }
    }

    /// Returns the declared variables in insertion order.
    #[must_use]
    pub fn vars(&self) -> &[VarDecl] {
        &self.vars
    }

    /// Retains only variables whose names are in the given set.
    /// Also updates the deduplication set to match.
    pub fn retain_vars(&mut self, keep: &HashSet<String>) {
        self.vars.retain(|v| keep.contains(&*v.name));
        self.declared_var_names.retain(|n| keep.contains(&**n));
    }

    /// Declares a universally quantified variable and returns an Expr referencing it.
    ///
    /// Duplicate names are silently skipped (the Expr is still returned).
    ///
    /// # Example
    /// ```text
    /// use trust_mc_core::chc::ChcVc;
    /// use ay_bindings::Sort;
    ///
    /// let mut vc = ChcVc::new();
    /// let x = vc.declare_var("x", Sort::int());
    /// // x is guaranteed to have the correct sort
    /// ```
    pub fn declare_var(&mut self, name: impl Into<Arc<str>>, sort: Sort) -> Expr {
        let name: Arc<str> = name.into();
        if self.declared_var_names.insert(Arc::clone(&name)) {
            self.vars.push(VarDecl { name: name.clone(), sort: sort.clone() });
        }
        Expr::var(&*name, sort)
    }

    /// Declares a TRANSLATION HAVOC — a fresh unconstrained value, not a value the
    /// program defines — named `stem` behind [`TRANSLATION_HAVOC_VAR_PREFIX`], and
    /// returns an Expr referencing it. A translator declares every such value
    /// through this method, so a refutation gate can recognize it by name
    /// ([`is_translation_havoc_var`]).
    pub fn declare_havoc_var(&mut self, stem: &str, sort: Sort) -> Expr {
        self.declare_var(format!("{TRANSLATION_HAVOC_VAR_PREFIX}{stem}"), sort)
    }

    /// Adds a declaration.
    pub fn add_decl(&mut self, decl: Decl) {
        self.decls.push(decl);
    }

    /// Adds a relation declaration.
    pub fn add_relation(&mut self, relation: RelationDecl) {
        self.relations.push(relation);
    }

    /// Adds a Horn rule.
    #[track_caller]
    pub fn add_rule(&mut self, rule: Rule) {
        self.rules.push(rule);
    }

    /// Adds a cover property for secondary satisfiability checking.
    ///
    /// Part of #1162: In CHC mode, cover properties are emitted as
    /// `(declare-const name Bool)` + `(assert (= name condition))` after the
    /// Horn rules. The driver extracts these for a secondary SAT check.
    pub fn add_cover_assertion(&mut self, name: String, condition: Expr) {
        self.cover_assertions.push((name, condition));
    }

    /// Registers a per-property check record (BSEM-18).
    ///
    /// Called by the encoder as each check site emits its `error_p{id}`
    /// relation. Order is significant and deterministic (MIR traversal order).
    pub fn add_property(&mut self, property: ChcProperty) {
        self.properties.push(property);
    }

    /// The number of registered per-property check records.
    #[must_use]
    pub fn property_count(&self) -> usize {
        self.properties.len()
    }

    /// Record that the encoder discharged property `id` at encode time.
    pub fn mark_property_discharged_at_encode(&mut self, id: u32, reason: &'static str) {
        if let Some(p) = self.properties.iter_mut().find(|p| p.id == id) {
            p.discharged_at_encode = Some(reason);
        }
    }

    /// Is this VC's ENTIRE obligation discharged at encode time?
    ///
    /// True only when there is at least one property, EVERY property carries a
    /// `discharged_at_encode` reason, and no `error_p{id}`-headed rule exists.
    /// That last clause is what keeps this honest: a property whose rule was
    /// emitted and later deleted — by `eliminate_trivially_false_rules`, or by
    /// `prune_orphan_block_rules` taking a rule whose block relation became an
    /// orphan — was never marked, so the conjunction fails and the caller must
    /// leave the VC alone. The driver then keeps failing closed with
    /// `LostErrorRules`, which is the correct answer for a check nobody can
    /// account for.
    ///
    /// Bridges (`error_p{id} -> error`) have head `error`, not `error_p…`, so
    /// they do not defeat the test.
    #[must_use]
    pub fn all_properties_discharged_at_encode(&self) -> bool {
        if self.trivially_safe_discharged || self.properties.is_empty() {
            return false;
        }
        if !self.properties.iter().all(|prop| prop.discharged_at_encode.is_some()) {
            return false;
        }
        // No surviving per-property rule...
        if self.rules.iter().any(|rule| rule.head.name.as_str().starts_with("error_p")) {
            return false;
        }
        // ...AND nothing derives the AGGREGATE `error` directly either.
        //
        // This clause is not redundant, and omitting it was a missed bug.
        // `error_only_region_head` gives an `Unreachable` target the aggregate
        // `error` head and registers NO property
        // (rules/codegen_rules/unreachable_error.rs:45), so a live
        // `from_app /\ guard -> error` rule is invisible to a property-only
        // test. Since the canonical discharge CLEARS every rule, firing on such
        // a VC deletes a real error path: measured 2026-09-18,
        // `unreachable_discharge_dual.rs::bug_reachable_unreachable` and
        // `obligation_free_walk_dual.rs::bug_unreachable_unchecked_one_deep`
        // — both genuinely reachable `unreachable_unchecked` — were reported
        // SUCCESSFUL.
        //
        // Bridges are exempt: their body relation IS an `error_p{id}`, and those
        // are already accounted for above.
        !self.rules.iter().any(|rule| {
            rule.head.name.as_str() == "error"
                && !rule
                    .body
                    .relation
                    .as_ref()
                    .is_some_and(|app| app.name.as_str().starts_with("error_p"))
        })
    }

    /// Task #78: record that a sound-approximation event freed a value, and its
    /// SMT-var identity if the freed value has a live state slot.
    ///
    /// `freed_var` is the (output) SMT variable name whose defining constraint
    /// the approximation deleted, or `None` when the freed value has no live
    /// state slot (dead — provably unreadable, so certification stays sound).
    /// EITHER way the event is ACCOUNTED, incrementing
    /// [`accounted_approximations`](Self::accounted_approximations). Approximation
    /// events that never reach this method are left unaccounted and force
    /// incompleteness at finalization.
    pub fn record_approximation_identity(&mut self, freed_var: Option<&str>) {
        if let Some(name) = freed_var {
            self.note_additional_freed_var(name);
        }
        self.accounted_approximations += 1;
    }

    /// Task #78: record an ADDITIONAL freed-var identity for an approximation
    /// event that was ALREADY accounted via [`record_approximation_identity`].
    ///
    /// Some sites havoc more than one destination in a SINGLE approximation
    /// event (e.g. `write_bytes` leaves both the return place and the written
    /// referent unconstrained under one `place_translation_drop`). Recording the
    /// extra identities keeps the dependence analysis complete WITHOUT
    /// double-counting the event (the completeness gate compares
    /// `accounted_approximations` against the counter total).
    pub fn note_additional_freed_var(&mut self, freed_var: &str) {
        let normalized = normalize_approx_var(freed_var).to_string();
        if !self.approximated_vars.contains(&normalized) {
            self.approximated_vars.push(normalized);
        }
    }

    /// Task #78: finalize per-property approximation-dependence and the
    /// harness-level identity-completeness flag.
    ///
    /// `total_sound_approximations` is the count of sound-approximation events
    /// the encoder recorded for this harness (the sum of the per-harness
    /// sound-approximation counters that free a value). Completeness holds iff
    /// every such event was accounted (`accounted_approximations` matches). When
    /// complete, each `error_p{N}` property gets an
    /// [`approximation_dependent`](ChcProperty::approximation_dependent) verdict
    /// from a transitive constraint-chain analysis over the finalized rules; the
    /// driver certifies Genuine only for a violated property whose verdict is
    /// `Some(false)` under a complete harness.
    pub fn finalize_approximation_identity(&mut self, total_sound_approximations: usize) {
        self.approximation_identity_complete =
            self.accounted_approximations >= total_sound_approximations;

        // The tainted set: the freed vars plus everything a definition-equality
        // copies a freed value INTO (rename/copy chains through `_x__out = rhs`).
        // Forward value-flow closure over the whole rule system is a sound
        // over-approximation of "reads a freed value".
        let mut tainted: HashSet<String> = self.approximated_vars.iter().cloned().collect();
        if !tainted.is_empty() {
            let mut changed = true;
            while changed {
                changed = false;
                for rule in &self.rules {
                    for constraint in rule.body.constraints.iter() {
                        if let Some((lhs, rhs_vars)) = definition_lhs_and_rhs_vars(constraint) {
                            if rhs_vars.iter().any(|v| is_tainted_name(v, &tainted))
                                && tainted.insert(lhs)
                            {
                                changed = true;
                            }
                        }
                    }
                }
            }
        }

        // For each property, decide dependence: does any GUARD constraint on a
        // rule that can derive this `error_p{N}` read a tainted var?
        let property_relations: Vec<String> =
            self.properties.iter().map(|p| p.relation.clone()).collect();
        let verdicts: Vec<bool> = property_relations
            .iter()
            .map(|rel| self.property_reads_tainted(rel, &tainted))
            .collect();
        for (prop, dependent) in self.properties.iter_mut().zip(verdicts) {
            prop.approximation_dependent = Some(dependent);
        }
    }

    /// Task #78: does any guard constraint on a rule that can derive `target`
    /// read a tainted var? Sound over-approximation of data-dependence.
    fn property_reads_tainted(&self, target: &str, tainted: &HashSet<String>) -> bool {
        if tainted.is_empty() {
            return false;
        }
        // Backward-reachable relations that can contribute to deriving `target`:
        // start from `target` and follow head → body-relation predecessor edges.
        let mut reachable: HashSet<String> = HashSet::new();
        reachable.insert(target.to_string());
        let mut changed = true;
        while changed {
            changed = false;
            for rule in &self.rules {
                if reachable.contains(&*rule.head.name)
                    && let Some(ref body_rel) = rule.body.relation
                    && reachable.insert(body_rel.name.to_string())
                {
                    changed = true;
                }
            }
        }
        // Any GUARD (non-definition) constraint on a reachable-headed rule that
        // reads a tainted var makes the property data-dependent on the havoc.
        for rule in &self.rules {
            if !reachable.contains(&*rule.head.name) {
                continue;
            }
            for constraint in rule.body.constraints.iter() {
                if is_definition_constraint(constraint) {
                    continue;
                }
                if expr_reads_tainted(constraint, tainted) {
                    return true;
                }
            }
        }
        false
    }

    /// Returns `true` if there are no rules.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }

    /// Render this typed CHC VC as fixedpoint-style SMT-LIB HORN input.
    ///
    /// This is a lossless bridge for solver APIs that still accept `declare-rel`
    /// / `rule` / `query` text, and is intentionally derived from the typed
    /// [`ChcVc`] structure rather than caller-provided SMT strings.
    #[must_use]
    pub fn to_horn_smt2(&self) -> String {
        self.to_horn_program().to_string()
    }

    /// Convert this typed CHC VC to a AY HORN program.
    #[must_use]
    pub fn to_horn_program(&self) -> AYProgram {
        let mut program = AYProgram::horn();

        for decl in &self.decls {
            emit_decl(&mut program, decl);
        }

        for var in self.vars() {
            program.declare_var(&*var.name, var.sort.clone());
        }

        for rel in &self.relations {
            program.declare_rel(rel.name.clone(), rel.arg_sorts.clone());
        }

        for rule in &self.rules {
            let body_expr = build_rule_body(&rule.body);
            let head_expr = build_relation_app(&rule.head);
            program.rule(head_expr, body_expr);
        }

        if let Some(ref target) = self.query.target {
            program.query(Expr::var(target.as_str(), Sort::bool()));
        }

        for (name, condition) in &self.cover_assertions {
            let pred = program.declare_const(name, Sort::bool());
            program.assert(pred.eq(condition.clone()));
        }

        program
    }

    /// Removes rules originating from orphan blocks.
    ///
    /// An orphan block is a relation that appears as a body source (premise)
    /// in some rule but never appears as a head (conclusion) in any rule.
    /// Since PDR treats such relations as unconstrained, it can freely
    /// instantiate them and construct spurious counterexamples through
    /// otherwise unreachable paths.
    ///
    /// Part of #3793: fixes CTREX(Genuine) caused by orphan deallocation
    /// blocks in Box<dyn T> drop encodings.
    pub fn prune_orphan_block_rules(&mut self) {
        use std::collections::HashSet;

        // Iterate until fixed-point: removing orphan rules may create new
        // orphans (e.g., bb23 was bb40's only predecessor; removing bb23's
        // rules makes bb40 orphaned too).
        loop {
            let targeted: HashSet<RelName> =
                self.rules.iter().map(|rule| rule.head.name.clone()).collect();

            let before = self.rules.len();
            let keep_error_obligations = self.keep_error_obligations;
            self.rules.retain(|rule| {
                // Lost-checks recovery: an error obligation over an orphan
                // block is still an obligation. An underivable body relation
                // is EMPTY in CHC semantics, so keeping the rule changes no
                // answer; it only lets the discharge and the solver say so.
                if keep_error_obligations && rule_is_error_obligation(rule) {
                    return true;
                }
                if let Some(ref body_rel) = rule.body.relation {
                    targeted.contains(&body_rel.name)
                } else {
                    true
                }
            });
            let pruned = before - self.rules.len();
            // (An `eprintln!` of the pruned/remaining rule counts lived here.
            // It fired on ordinary --ay-chc runs, so every user saw internal
            // rule counts on stderr. trust-mc-core has no logging dependency
            // and this was its only print, so it is removed rather than gated:
            // the counts are reconstructible from --keep-temps.)
            if pruned == 0 {
                break;
            }
        }

        // Rule pruning can leave stale block relation declarations behind.
        // These declarations do not participate in the CHC, but still widen
        // emitted HORN signatures and can trip solver diagnostics.
        let query_target = self.query.target.as_deref().unwrap_or("error");
        let relation_names: HashSet<String> =
            self.relations.iter().map(|rel| rel.name.clone()).collect();
        let mut referenced: HashSet<String> = HashSet::new();
        referenced.insert(query_target.to_string());
        for rule in &self.rules {
            referenced.insert(rule.head.name.to_string());
            if let Some(ref body_rel) = rule.body.relation {
                referenced.insert(body_rel.name.to_string());
            }
            for constraint in rule.body.constraints.iter() {
                collect_relation_refs_in_expr(constraint, &relation_names, &mut referenced);
            }
        }
        self.relations.retain(|rel| referenced.contains(rel.name.as_str()));

        fn collect_relation_refs_in_expr(
            expr: &Expr,
            relation_names: &HashSet<String>,
            referenced: &mut HashSet<String>,
        ) {
            let mut stack = vec![expr];
            while let Some(node) = stack.pop() {
                if let ExprValue::FuncApp { name, .. } = node.value()
                    && relation_names.contains(name.as_str())
                {
                    referenced.insert(name.to_string());
                }
                stack.extend(node.children());
            }
        }
    }
}

/// Task #78: collect the normalized (`__out`-stripped) names of every variable
/// referenced in `expr`'s subtree.
fn collect_var_names(expr: &Expr, out: &mut Vec<String>) {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let ExprValue::Var { name } = node.value() {
            out.push(normalize_approx_var(name).to_string());
        }
        stack.extend(node.children());
    }
}

/// Task #78: true if any variable referenced in `expr` normalizes to a name in
/// `tainted`.
fn expr_reads_tainted(expr: &Expr, tainted: &HashSet<String>) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let ExprValue::Var { name } = node.value()
            && is_tainted_name(name, tainted)
        {
            return true;
        }
        stack.extend(node.children());
    }
    false
}

/// Task #78: if `constraint` is a state-slot DEFINITION `(= _x__out rhs)`,
/// return `(normalized lhs, normalized rhs vars)` for forward taint flow.
///
/// Directional (lhs receives rhs's taint): a definition copies the rhs value
/// into the post-state slot, so if the rhs reads a freed value the slot becomes
/// tainted too. This tracks rename/copy chains (`_y__out = _freed` then a later
/// read of `_y`). It intentionally does NOT taint the rhs from the lhs, so a
/// bare equality guard `(= _freed _input)` never taints the constrained input.
fn definition_lhs_and_rhs_vars(constraint: &Expr) -> Option<(String, Vec<String>)> {
    if let ExprValue::Eq(a, b) = constraint.value()
        && let ExprValue::Var { name } = a.value()
        && name.ends_with("__out")
    {
        let lhs = normalize_approx_var(name).to_string();
        let mut rhs_vars = Vec::new();
        collect_var_names(b, &mut rhs_vars);
        return Some((lhs, rhs_vars));
    }
    None
}

/// Task #78: true if `constraint` is a state-slot definition `(= _x__out rhs)`.
///
/// Such constraints assign a fresh output var and are always satisfiable, so
/// they never GATE a derivation path — they are excluded from the dependence
/// guard scan (only true guards can make a check data-dependent on a havoc).
fn is_definition_constraint(constraint: &Expr) -> bool {
    if let ExprValue::Eq(a, _) = constraint.value()
        && let ExprValue::Var { name } = a.value()
    {
        return name.ends_with("__out");
    }
    false
}

fn emit_decl(program: &mut AYProgram, decl: &Decl) {
    match decl {
        Decl::Const { name, sort } => {
            let _ = program.declare_const(name, sort.clone());
        }
        Decl::Fun { name, arg_sorts, ret_sort } => {
            program.declare_fun(name, arg_sorts.clone(), ret_sort.clone());
        }
        Decl::Datatype { datatype } => {
            program.declare_datatype(ay_bindings::DatatypeSort::clone(datatype));
        }
    }
}

fn build_rule_body(body: &RuleBody) -> Expr {
    let mut conjuncts: Vec<Expr> =
        Vec::with_capacity(body.constraints.len() + usize::from(body.relation.is_some()));

    if let Some(ref rel_app) = body.relation {
        conjuncts.push(build_relation_app(rel_app));
    }
    conjuncts.extend(body.constraints.iter().cloned());

    Expr::and_many(conjuncts)
}

fn build_relation_app(app: &RelationApp) -> Expr {
    if app.args.is_empty() {
        Expr::var(&*app.name, Sort::bool())
    } else {
        Expr::func_app(&*app.name, (*app.args).clone())
    }
}

/// Whether `rule` is an ERROR OBLIGATION: a rule headed by `error` or by a
/// per-property `error_p{id}` relation.
pub fn rule_is_error_obligation(rule: &Rule) -> bool {
    let head: &str = rule.head.name.as_ref();
    head == "error" || head.starts_with("error_p")
}

/// Whether a rule/column pass sequence turned `before`, a VC that carries error
/// obligations, into `after`, a VC that registered properties and carries NO
/// error obligation: the shape the compiler calls lost checks, not proved checks
/// (`discharge_straightline_safety`, SOUNDNESS #67) and the driver reports
/// INCONCLUSIVE (`LostErrorRules`).
///
/// Exempt: a certified discharge (`trivially_safe_discharged`), a VC already
/// re-run in keep mode, a VC with no registered property, and — the case that
/// belongs to somebody else's mechanism — a VC whose EVERY property was recorded
/// `discharged_at_encode`. That last one is not a lost check: emission turns it
/// into the canonical `false => error` obligation
/// (`ChcVc::all_properties_discharged_at_encode`), which the driver reads as a
/// clean proof with no solver run. Re-encoding it in keep mode would pin live
/// `error_p{id}` rules, defeat that gate, and hand the solver an infeasibility to
/// re-derive — the 1.8x slowdown the in-band marker cost before it was reverted.
pub fn passes_lost_every_error_obligation(before: &ChcVc, after: &ChcVc) -> bool {
    !after.trivially_safe_discharged
        && !after.keep_error_obligations
        && !after.properties.is_empty()
        && !after.properties.iter().all(|prop| prop.discharged_at_encode.is_some())
        && !after.rules.iter().any(rule_is_error_obligation)
        && before.rules.iter().any(rule_is_error_obligation)
}

/// Keep mode's replacement for deleting an error obligation whose body folded
/// to `false`: the same head and body relation over a literal-`false`
/// constraint, which no solver has to re-derive.
pub(crate) fn pin_false_error_obligation(rule: &mut Rule) {
    rule.body.constraints = Constraints::Owned(vec![Expr::bool_const(false)]);
}

impl Default for ChcVc {
    fn default() -> Self {
        Self::new()
    }
}

/// A relation declaration for CHC.
///
/// Relations represent sets of reachable states at program points.
/// In SMT-LIB Horn syntax: `(declare-rel name (sort₁ sort₂ ...))`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelationDecl {
    /// The name of the relation.
    pub name: String,

    /// The sorts of the relation's arguments.
    ///
    /// Each argument typically represents part of the program state
    /// (e.g., variable values, memory state).
    pub arg_sorts: Vec<Sort>,
}

impl RelationDecl {
    /// Creates a new relation declaration.
    pub fn new(name: impl Into<String>, arg_sorts: Vec<Sort>) -> Self {
        Self { name: name.into(), arg_sorts }
    }

    /// Creates a nullary (0-argument) relation.
    ///
    /// Commonly used for the error relation.
    pub fn nullary(name: impl Into<String>) -> Self {
        Self::new(name, Vec::new())
    }

    /// Returns the arity (number of arguments) of this relation.
    #[must_use]
    pub fn arity(&self) -> usize {
        self.arg_sorts.len()
    }
}

/// A Horn rule encoding a transition.
///
/// A rule has the form: `(rule (=> body head))`
/// where body is a conjunction and head is a relation application.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Rule {
    /// The rule body (premises).
    ///
    /// This is implicitly a conjunction of conditions and relation applications.
    pub body: RuleBody,

    /// The rule head (conclusion).
    ///
    /// This is a single relation application.
    pub head: RelationApp,
}

impl Rule {
    /// Creates a new rule.
    pub fn new(body: RuleBody, head: RelationApp) -> Self {
        Self { body, head }
    }

    /// Creates an initialization rule (fact with constraint body).
    pub fn init(constraint: Expr, head: RelationApp) -> Self {
        Self { body: RuleBody::new(None, vec![constraint]), head }
    }

    /// Creates a transition rule from one relation to another.
    pub fn transition(
        from: RelationApp,
        guard: Option<Expr>,
        transition: Expr,
        to: RelationApp,
    ) -> Self {
        let mut constraints = vec![transition];
        if let Some(g) = guard {
            constraints.push(g);
        }
        Self { body: RuleBody::new(Some(from), constraints), head: to }
    }
}

/// The body of a Horn rule.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RuleBody {
    /// An optional relation application in the body.
    pub relation: Option<RelationApp>,

    /// Constraint expressions that must hold.
    pub constraints: Constraints,
}

impl RuleBody {
    /// Creates a new rule body.
    pub fn new(relation: Option<RelationApp>, constraints: Vec<Expr>) -> Self {
        Self { relation, constraints: Constraints::Owned(constraints) }
    }

    /// Creates a rule body from a shared base constraint slice plus extra constraints.
    ///
    /// The `Arc<[Expr]>` base is shared across all rules emitted from the same
    /// basic block, avoiding O(K) copies of the constraint vector for SwitchInt
    /// blocks with K branches. Part of #2507: O(N²) rule cloning fix.
    pub fn from_shared_base(
        relation: Option<RelationApp>,
        base: Arc<[Expr]>,
        extra: impl IntoIterator<Item = Expr>,
    ) -> Self {
        let extra: Vec<Expr> = extra.into_iter().collect();
        Self { relation, constraints: Constraints::Shared { base, extra } }
    }

    /// Creates a rule body by extending base constraints with extra constraints.
    ///
    /// Avoids the `base.to_vec()` + `push()` pattern that allocates a full copy
    /// of the base constraints at each call site. Instead, builds the combined
    /// Vec once with pre-allocated capacity.
    /// Part of #2267: allocation debt reduction.
    pub fn from_base_and_extra(
        relation: Option<RelationApp>,
        base: &[Expr],
        extra: impl IntoIterator<Item = Expr>,
    ) -> Self {
        let extra_iter = extra.into_iter();
        let (extra_low, _) = extra_iter.size_hint();
        let mut constraints = Vec::with_capacity(base.len() + extra_low);
        constraints.extend_from_slice(base);
        constraints.extend(extra_iter);
        Self { relation, constraints: Constraints::Owned(constraints) }
    }

    /// Creates an empty rule body (for facts).
    pub fn empty() -> Self {
        Self { relation: None, constraints: Constraints::Owned(Vec::new()) }
    }
}

/// Reference-counted relation name — O(1) clone for rule emission.
///
/// Wraps `Arc<str>` with ergonomic comparison support (`==`/`!=` against
/// `&str`, `String`, and other `RelName`). Part of #2507.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelName(Arc<str>);

impl RelName {
    /// Borrows the underlying `&str`.
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::ops::Deref for RelName {
    type Target = str;
    #[inline]
    fn deref(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for RelName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl<T: AsRef<str>> From<T> for RelName {
    fn from(s: T) -> Self {
        Self(Arc::from(s.as_ref()))
    }
}

impl PartialEq<str> for RelName {
    fn eq(&self, other: &str) -> bool {
        &*self.0 == other
    }
}

impl PartialEq<&str> for RelName {
    fn eq(&self, other: &&str) -> bool {
        &*self.0 == *other
    }
}

impl PartialEq<String> for RelName {
    fn eq(&self, other: &String) -> bool {
        &*self.0 == other.as_str()
    }
}

impl PartialEq<Arc<str>> for RelName {
    fn eq(&self, other: &Arc<str>) -> bool {
        self.0 == *other
    }
}

/// A relation application (relation name with arguments).
///
/// Both `name` and `args` are reference-counted so that cloning a
/// `RelationApp` for each emitted rule body is O(1) — no String or
/// Vec allocation.  Part of #2507.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelationApp {
    /// The name of the relation being applied.
    ///
    /// Stored as [`RelName`] (Arc-backed) so cloning does not allocate.
    pub name: RelName,

    /// The argument expressions.
    ///
    /// Stored behind `Arc` so cloning `RelationApp` for each emitted rule body
    /// does not clone the full argument vector.
    pub args: Arc<Vec<Expr>>,
}

impl RelationApp {
    /// Creates a new relation application.
    pub fn new(name: impl AsRef<str>, args: Vec<Expr>) -> Self {
        Self { name: RelName::from(name), args: Arc::new(args) }
    }

    /// Creates a nullary relation application.
    pub fn nullary(name: impl AsRef<str>) -> Self {
        Self::new(name, Vec::new())
    }
}

/// Query configuration for CHC verification.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct ChcQuery {
    /// The relation to query for reachability.
    ///
    /// Typically "error" - if reachable, the property fails.
    pub target: Option<String>,

    /// Optional timeout in milliseconds.
    pub timeout_ms: Option<u64>,
}

impl ChcQuery {
    /// Creates a new query configuration.
    pub fn new() -> Self {
        Self::default()
    }

    /// Sets the target relation to query.
    #[must_use]
    pub fn with_target(mut self, target: impl Into<String>) -> Self {
        self.target = Some(target.into());
        self
    }

    /// Sets the timeout.
    #[must_use]
    pub fn with_timeout(mut self, ms: u64) -> Self {
        self.timeout_ms = Some(ms);
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::violation::PropertyKind;

    /// Task #78: build a minimal `bb2 → error_p3 → error` VC whose `error_p3`
    /// guard reads `guard_var` (a bare equality, i.e. a real gate). `bb2` carries
    /// both `_1` (raw input) and `freed` in its state, mirroring the twin duals.
    fn dual_shape_vc(freed_state_var: &str, guard_var: &str) -> ChcVc {
        let bv = Sort::bitvec(32);
        let input = Expr::var("_1", bv.clone());
        let freed = Expr::var(freed_state_var, bv.clone());
        let guard = Expr::var(guard_var, bv.clone());
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("bb2", vec![bv.clone(), bv.clone()]));
        vc.add_relation(RelationDecl::nullary("error_p3"));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::nullary("error_p3")), vec![]),
            RelationApp::nullary("error"),
        ));
        // (and (bb2 _1 freed) (= guard 100)) -> error_p3  [`= guard 100` is a guard]
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("bb2", vec![input, freed])),
                vec![guard.eq(Expr::bitvec_const(100u64, 32))],
            ),
            RelationApp::nullary("error_p3"),
        ));
        vc.add_property(ChcProperty {
            id: 3,
            kind: PropertyKind::Assertion,
            bb: 2,
            relation: "error_p3".to_owned(),
            message: None,
            location: None,
            approximation_dependent: None,
            discharged_at_encode: None,
        });
        vc.query = ChcQuery::new().with_target("error");
        vc
    }

    #[test]
    fn test_task78_error_reading_freed_var_is_dependent() {
        // Dependent-dual shape: the failing check's guard reads the freed var
        // `_4` (recorded via its `__out` post-state name, normalized to `_4`).
        let mut vc = dual_shape_vc("_4", "_4");
        vc.record_approximation_identity(Some("_4__out"));
        assert_eq!(vc.approximated_vars, vec!["_4".to_string()]);
        vc.finalize_approximation_identity(1);
        assert!(vc.approximation_identity_complete, "1 accounted == 1 total");
        assert_eq!(
            vc.properties[0].approximation_dependent,
            Some(true),
            "guard reads the freed var → dependent → STAY OverApproximation"
        );
    }

    #[test]
    fn test_task78_error_reading_raw_input_is_independent() {
        // Independent-dual shape: the freed var `_2` is carried in state but the
        // failing check's guard reads only the raw input `_1`.
        let mut vc = dual_shape_vc("_2", "_1");
        vc.record_approximation_identity(Some("_2__out"));
        vc.finalize_approximation_identity(1);
        assert!(vc.approximation_identity_complete);
        assert_eq!(
            vc.properties[0].approximation_dependent,
            Some(false),
            "guard reads only raw input → independent → MAY certify Genuine"
        );
    }

    /// A float-binop table identity: `bb2` carries the input `_1` and the table;
    /// the transition `bb2 -> bb3` defines `_3 = select(tbl, _1)`; `error_p3`
    /// guards on `guard` from `bb2` (when `from_bb3` is false) or on `_3` from
    /// `bb3`.
    fn table_shape_vc(guard: Expr, from_bb3: bool) -> ChcVc {
        let bv = Sort::bitvec(32);
        let tbl_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));
        let input = Expr::var("_1", bv.clone());
        let out3 = Expr::var("_3", bv.clone());
        let tbl = Expr::var(FLOAT_BINOP_TABLE_F32, tbl_sort.clone());
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("bb2", vec![bv.clone(), tbl_sort.clone()]));
        vc.add_relation(RelationDecl::new("bb3", vec![bv.clone(), bv.clone(), tbl_sort]));
        vc.add_relation(RelationDecl::nullary("error_p3"));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("bb2", vec![input.clone(), tbl.clone()])),
                vec![Expr::var("_3__out", bv).eq(tbl.clone().select(input.clone()))],
            ),
            RelationApp::new(
                "bb3",
                vec![input.clone(), Expr::var("_3__out", Sort::bitvec(32)), tbl.clone()],
            ),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::nullary("error_p3")), vec![]),
            RelationApp::nullary("error"),
        ));
        let from = if from_bb3 {
            RelationApp::new("bb3", vec![input, out3, tbl])
        } else {
            RelationApp::new("bb2", vec![input, tbl])
        };
        vc.add_rule(Rule::new(
            RuleBody::new(Some(from), vec![guard]),
            RelationApp::nullary("error_p3"),
        ));
        vc.add_property(ChcProperty {
            id: 3,
            kind: PropertyKind::MemorySafety,
            bb: 2,
            relation: "error_p3".to_owned(),
            message: None,
            location: None,
            approximation_dependent: None,
            discharged_at_encode: None,
        });
        vc.query = ChcQuery::new().with_target("error");
        vc.record_approximation_identity(Some(FLOAT_BINOP_TABLE_F32));
        vc.finalize_approximation_identity(1);
        vc
    }

    #[test]
    fn float_table_identity_leaves_an_operand_check_independent() {
        let vc = table_shape_vc(
            Expr::var("_1", Sort::bitvec(32)).eq(Expr::bitvec_const(0x7f80_0000u64, 32)),
            false,
        );
        assert!(vc.approximation_identity_complete);
        assert_eq!(vc.approximated_vars, vec![FLOAT_BINOP_TABLE_F32.to_string()]);
        assert_eq!(vc.properties[0].approximation_dependent, Some(false));
    }

    #[test]
    fn a_select_on_the_float_table_is_a_read_of_it() {
        let tbl = Expr::var(FLOAT_BINOP_TABLE_F32, Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
        let direct = table_shape_vc(
            tbl.select(Expr::var("_1", Sort::bitvec(32))).eq(Expr::bitvec_const(0u64, 32)),
            false,
        );
        assert_eq!(direct.properties[0].approximation_dependent, Some(true), "guard selects");
        let through_a_definition = table_shape_vc(
            Expr::var("_3", Sort::bitvec(32)).eq(Expr::bitvec_const(0u64, 32)),
            true,
        );
        assert_eq!(
            through_a_definition.properties[0].approximation_dependent,
            Some(true),
            "guard reads a slot a table select defined"
        );
        assert!(is_float_binop_table_var("float_binop_tbl_f64__out"));
        assert!(!is_float_binop_table_var("float_binop_tbl_f16"));
    }

    /// tests/expected/test6/main.rs: the table select at a constant key was
    /// scalarized into a cell before finalization; the check reads the cell.
    #[test]
    fn a_scalarized_cell_of_the_float_table_is_a_read_of_it() {
        let cell = format!("{FLOAT_BINOP_TABLE_F32}_at_0x3f8000003f800000_bv72");
        assert_eq!(scalarized_cell_parent(&cell), Some(FLOAT_BINOP_TABLE_F32));
        assert_eq!(scalarized_cell_parent(&format!("{cell}__out")), Some(FLOAT_BINOP_TABLE_F32));
        assert_eq!(scalarized_cell_parent("_main_5"), None);
        let direct = table_shape_vc(
            Expr::var(cell.as_str(), Sort::bitvec(32)).eq(Expr::bitvec_const(0x4000_0000u64, 32)),
            false,
        );
        assert_eq!(direct.properties[0].approximation_dependent, Some(true), "guard reads a cell");
    }

    #[test]
    fn test_task78_unaccounted_approximation_forces_incompleteness() {
        // Only one of two approximations recorded its identity: the harness is
        // INCOMPLETE, so the driver must never certify (fail-closed).
        let mut vc = dual_shape_vc("_2", "_1");
        vc.record_approximation_identity(Some("_2__out"));
        vc.finalize_approximation_identity(2); // total 2, accounted 1
        assert!(
            !vc.approximation_identity_complete,
            "an unaccounted approximation blocks certification for the whole harness"
        );
    }

    #[test]
    fn test_task78_dead_freed_value_is_accounted_without_a_var() {
        // A dead (no live slot) freed value is accounted with `None`: it counts
        // toward completeness but adds no readable identity, so an
        // independent check still certifies.
        let mut vc = dual_shape_vc("_2", "_1");
        vc.record_approximation_identity(None);
        assert!(vc.approximated_vars.is_empty());
        assert_eq!(vc.accounted_approximations, 1);
        vc.finalize_approximation_identity(1);
        assert!(vc.approximation_identity_complete);
        // No freed vars ⇒ nothing to depend on ⇒ independent.
        assert_eq!(vc.properties[0].approximation_dependent, Some(false));
    }

    #[test]
    fn test_declare_var_returns_expr_with_correct_sort() {
        let mut vc = ChcVc::new();
        let x = vc.declare_var("x", Sort::int());

        // Verify the returned expr has the correct sort
        assert_eq!(*x.sort(), Sort::int());

        // Verify the variable was added to the VC
        assert_eq!(vc.vars().len(), 1);
        assert_eq!(&*vc.vars()[0].name, "x");
        assert_eq!(vc.vars()[0].sort, Sort::int());
    }

    #[test]
    fn test_declare_var_multiple_variables() {
        let mut vc = ChcVc::new();
        let x = vc.declare_var("x", Sort::int());
        let y = vc.declare_var("y", Sort::bool());
        let z = vc.declare_var("z", Sort::bitvec(32));

        // Verify sorts match
        assert_eq!(*x.sort(), Sort::int());
        assert_eq!(*y.sort(), Sort::bool());
        assert_eq!(*z.sort(), Sort::bitvec(32));

        // Verify all variables were added
        assert_eq!(vc.vars().len(), 3);
    }

    #[test]
    fn test_add_var_skips_duplicate_names() {
        let mut vc = ChcVc::new();
        vc.add_var(VarDecl::new("x", Sort::int()));
        vc.add_var(VarDecl::new("x", Sort::int()));

        assert_eq!(vc.vars().len(), 1);
    }

    #[test]
    fn test_relation_app_clone_shares_storage() {
        let app = RelationApp::new("bb0", vec![Expr::int_const(1), Expr::int_const(2)]);
        let cloned = app.clone();

        // args (Arc<Vec<Expr>>) share storage — O(1) clone.
        assert!(Arc::ptr_eq(&app.args, &cloned.args));
        assert_eq!(app.args.len(), 2);

        // name (RelName) shares storage — same data pointer after clone.
        assert!(std::ptr::eq(app.name.as_str(), cloned.name.as_str()));

        // RelName comparison works with &str and String.
        assert_eq!(app.name, "bb0");
        assert_eq!(app.name, String::from("bb0"));
    }

    #[test]
    fn test_chc_vc_is_empty() {
        let vc = ChcVc::new();
        assert!(vc.is_empty());
    }

    #[test]
    fn test_relation_decl_arity() {
        let rel = RelationDecl::new("block_0", vec![Sort::int(), Sort::bool()]);
        assert_eq!(rel.arity(), 2);

        let nullary = RelationDecl::nullary("error");
        assert_eq!(nullary.arity(), 0);
    }

    #[test]
    fn test_to_horn_smt2_renders_typed_chc() {
        let mut vc = ChcVc::new();
        let x = vc.declare_var("x", Sort::int());
        vc.add_relation(RelationDecl::new("entry", vec![Sort::int()]));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::new(
            RuleBody::empty(),
            RelationApp::new("entry", vec![Expr::int_const(0)]),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("entry", vec![x.clone()])),
                vec![x.int_lt(Expr::int_const(0))],
            ),
            RelationApp::nullary("error"),
        ));
        vc.query = ChcQuery::new().with_target("error");

        let smt = vc.to_horn_smt2();

        assert!(smt.contains("(set-logic HORN)"));
        assert!(smt.contains("(declare-var x Int)"));
        assert!(smt.contains("(declare-rel entry (Int))"));
        assert!(smt.contains("(rule (=> true (entry 0)))"));
        assert!(smt.contains("(rule (=> (and (entry x) (< x 0)) error))"));
        assert!(smt.contains("(query error)"));
    }

    #[test]
    fn test_prune_orphan_block_rules_removes_stale_relation_declarations() {
        let arr_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));
        let x = Expr::var("x", Sort::int());
        let dead_arr = Expr::var("dead_arr", arr_sort.clone());

        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("live", vec![Sort::int()]));
        vc.add_relation(RelationDecl::new("orphan", vec![arr_sort.clone()]));
        vc.add_relation(RelationDecl::new("dead_target", vec![arr_sort]));
        vc.add_relation(RelationDecl::nullary("error"));

        vc.add_rule(Rule::new(RuleBody::empty(), RelationApp::new("live", vec![x.clone()])));
        vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::new("live", vec![x])), vec![]),
            RelationApp::nullary("error"),
        ));
        vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::new("orphan", vec![dead_arr.clone()])), vec![]),
            RelationApp::new("dead_target", vec![dead_arr]),
        ));

        vc.prune_orphan_block_rules();

        let names: HashSet<&str> = vc.relations.iter().map(|rel| rel.name.as_str()).collect();
        assert_eq!(names, HashSet::from(["live", "error"]));
        assert!(vc.rules.iter().all(|rule| rule.head.name != "dead_target"));
    }

    #[test]
    fn test_prune_orphan_block_rules_keeps_query_target_without_error_rules() {
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("live", vec![]));
        vc.add_relation(RelationDecl::new("stale", vec![Sort::array(Sort::int(), Sort::int())]));
        vc.add_relation(RelationDecl::nullary("error"));

        vc.add_rule(Rule::new(RuleBody::empty(), RelationApp::nullary("live")));
        vc.prune_orphan_block_rules();

        let names: HashSet<&str> = vc.relations.iter().map(|rel| rel.name.as_str()).collect();
        assert_eq!(names, HashSet::from(["live", "error"]));
    }

    #[test]
    fn test_prune_orphan_block_rules_keeps_constraint_relation_declarations() {
        let x = Expr::var("x", Sort::int());
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::new("live", vec![]));
        vc.add_relation(RelationDecl::new("constraint_rel", vec![Sort::int()]));
        vc.add_relation(RelationDecl::new("stale", vec![Sort::int()]));
        vc.add_relation(RelationDecl::nullary("error"));

        vc.add_rule(Rule::new(
            RuleBody::new(None, vec![Expr::func_app("constraint_rel", vec![x])]),
            RelationApp::nullary("live"),
        ));
        vc.prune_orphan_block_rules();

        let names: HashSet<&str> = vc.relations.iter().map(|rel| rel.name.as_str()).collect();
        assert_eq!(names, HashSet::from(["live", "constraint_rel", "error"]));
    }

    /// A havoc declared through `declare_havoc_var` carries the reserved prefix the
    /// refutation gates read; an ordinary declaration does not, and the prefix is the
    /// whole test (a havoc stem that looks like a relation argument stays a havoc).
    #[test]
    fn declare_havoc_var_marks_the_name_a_refutation_gate_reads() {
        let mut vc = ChcVc::new();
        let havoc = vc.declare_havoc_var("bb3_v7", Sort::bitvec(32));
        let ExprValue::Var { name } = havoc.value() else {
            panic!("a declared havoc is a variable: {havoc:?}");
        };
        assert_eq!(name, &format!("{TRANSLATION_HAVOC_VAR_PREFIX}bb3_v7"));
        assert!(is_translation_havoc_var(name));
        let relation_arg = vc.declare_var("bb3_v7", Sort::bitvec(32));
        let ExprValue::Var { name } = relation_arg.value() else {
            panic!("a declared variable is a variable: {relation_arg:?}");
        };
        assert!(!is_translation_havoc_var(name));
    }
}

#[cfg(test)]
#[path = "chc_keep_error_obligations_tests.rs"]
mod keep_error_obligations_tests;
