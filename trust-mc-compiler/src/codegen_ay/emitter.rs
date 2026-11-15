// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Emitter for converting trust_mc_core IR to AY SMT-LIB2.
//!
//! This module bridges the abstract verification condition IR (`BmcVc`, `ChcVc`)
//! to concrete AY solver commands. It implements the "emitter" phase of the
//! two-phase codegen architecture:
//!
//! ```text
//! MIR → trust_mc_core IR → emitter → ay_bindings::AYProgram → .smt2 file
//! ```
//!
//! ## Design
//!
//! The emitter is stateless - it takes an IR container and produces a AYProgram.
//! This separation enables:
//! - Testing IR construction independently of SMT emission
//! - Future support for multiple solver backends
//! - Cleaner error boundaries between phases

use std::collections::{BTreeMap, BTreeSet};

use ay_bindings::{AYProgram, Expr, ExprValue, Sort, SortInner};
use tracing::{debug, warn};

use crate::codegen_ay::types::bool_sort;
use trust_mc_core::{BmcVc, ChcVc, Decl};

/// Define a named Boolean flag with an equivalent solver-facing encoding.
///
/// A visible datatype carrier selects two exact implications; other conditions
/// retain Boolean equality. This is a syntactic encoding heuristic, not a claim
/// that the equality branch is independent of datatype theory. In particular,
/// separately asserted definitions of Bool leaves are not traversed.
///
/// Both representations retain every model of `flag = condition`, including
/// secondary queries that do not assert the flag. Keep implication nodes in the
/// datatype branch: a top-level OR of violation flags denotes the driver's
/// legacy counterexample query goal.
pub(in crate::codegen_ay) fn define_property_flag(
    program: &mut AYProgram,
    flag: Expr,
    condition: Expr,
) {
    if property_condition_has_datatype_witness(&condition) {
        program.assert(flag.clone().implies(condition.clone()));
        program.assert(condition.implies(flag));
    } else {
        program.assert(flag.eq(condition));
    }
}

/// Find positive typed datatype evidence in this condition's visible syntax.
///
/// No name matching or program-wide declaration test is used. Unrecognized
/// forms that provide no visible witness select the default equality encoding;
/// returning false does not certify absence of transitive datatype dependence.
fn property_condition_has_datatype_witness(condition: &Expr) -> bool {
    let mut expressions = vec![condition];
    let mut sorts = Vec::new();
    let mut seen_exprs = std::collections::HashSet::<*const ExprValue>::new();
    let mut seen_sorts = std::collections::HashSet::<*const SortInner>::new();

    while let Some(expr) = expressions.pop() {
        // The outer sort belongs to Expr, separately from its shared value.
        // Inspect each occurrence's metadata before deduplicating its children.
        sorts.push(expr.sort());
        if !seen_exprs.insert(std::ptr::from_ref(expr.value())) {
            continue;
        }
        match expr.value() {
            ExprValue::Forall { vars, .. } | ExprValue::Exists { vars, .. } => {
                sorts.extend(vars.iter().map(|(_, sort)| sort));
            }
            _ => {}
        }
        if expr.value().is_known_variant() {
            expressions.extend(expr.children());
        }
    }

    while let Some(sort) = sorts.pop() {
        if !seen_sorts.insert(std::ptr::from_ref(sort.inner())) {
            continue;
        }
        match sort.inner() {
            SortInner::Datatype(_) | SortInner::DatatypeRef(_) => return true,
            SortInner::Array(array) => {
                sorts.push(&array.index_sort);
                sorts.push(&array.element_sort);
            }
            SortInner::Seq(element) => sorts.push(element),
            _ => {}
        }
    }
    false
}

/// Emits a BMC verification condition to a AY program.
///
/// Converts the abstract `BmcVc` to a concrete `AYProgram` that can be
/// serialized to SMT-LIB2. The query is structured as:
///
/// ```text
/// (set-logic ...)
/// (set-option :produce-models ...)
/// (declare-const ...) ; for each decl
/// (assert ...) ; for each constraint
/// (assert (or viol_1 ... viol_n)) ; violation disjunction
/// (check-sat)
/// (get-value ...) ; for models
/// ```
///
/// # Arguments
///
/// * `vc` - The BMC verification condition to emit
///
/// # Returns
///
/// A `AYProgram` ready for serialization to SMT-LIB2.
///
/// REQUIRES: vc.decls contains valid declaration entries (Const, Fun, or Datatype)
/// REQUIRES: vc.constraints and vc.violations contain well-formed Exprs
/// ENSURES: Output program contains one declare-const per Const decl
/// ENSURES: Output program contains one assert per constraint
/// ENSURES: Output program contains violation disjunction or assert false if no violations
/// ENSURES: Output program ends with check-sat (and get-value if produce_model)
#[cfg_attr(not(test), allow(dead_code))]
pub(in crate::codegen_ay) fn emit_bmc(vc: BmcVc) -> AYProgram {
    emit_bmc_with_logic_override(vc, false)
}

/// [`emit_bmc`] for a VC whose logic the user may have named (`--ay-logic`,
/// `AYConfig::logic_override`). A named logic is kept even when the VC uses
/// floating point: the user's logic takes precedence over automatic selection
/// (#621). The datatype upgrade still applies, as it always has.
pub(in crate::codegen_ay) fn emit_bmc_with_logic_override(
    vc: BmcVc,
    logic_override: bool,
) -> AYProgram {
    let mut program = AYProgram::new();

    // Set logic if specified
    if let Some(ref logic) = vc.query.logic {
        program.set_logic(logic);
    }

    // Configure model/unsat-core production
    if vc.query.produce_model {
        program.produce_models();
    }

    let mut implicit_vars = BTreeMap::new();
    collect_implicit_bmc_vars(&vc, &mut implicit_vars);

    // Emit declarations
    for decl in &vc.decls {
        emit_decl(&mut program, decl);
    }

    // Some sound-overapproximation paths build fresh Expr::var leaves outside
    // the mutable CodegenCtx. They still carry exact sorts, so materialize the
    // corresponding declarations here instead of emitting malformed SMT-LIB.
    for (name, sort) in implicit_vars {
        if !program.is_declared(&name) {
            ensure_sort_declared(&mut program, &sort);
            let _ = program.declare_const(name, sort);
        }
    }

    // Declare any datatype/array/seq sort that surfaces ONLY as the result sort
    // of an intermediate node (e.g. a DatatypeConstructor or FieldSelect produced
    // inside a constraint / violation condition, never as a top-level Var leaf).
    // collect_implicit_bmc_vars records a sort only at Var leaves, so such a sort
    // would otherwise reach an assert below with no (declare-datatypes ...) — the
    // undeclared/double-named constructor bug (e.g. RangeInclusive_u8). This walks
    // every subexpression's own result sort; declare_datatype dedups by name, so
    // sorts already emitted via vc.decls or the implicit vars above are not
    // re-declared. Must run BEFORE the asserts that reference these sorts.
    declare_intermediate_sorts(&mut program, &vc);
    let uses_floating_point = bmc_vc_uses_floating_point(&vc);

    // Emit path constraints (move each Expr — no clones)
    for constraint in vc.constraints {
        program.assert(constraint);
    }

    // Upgrade logic if datatypes were declared (QF_AUFBV doesn't support datatypes)
    // This must happen after declarations but before the final query.
    program.upgrade_logic_for_datatypes();
    // Likewise for floating point (`uses_floating_point` was read before the
    // constraints were moved into the program), unless the user named the logic.
    upgrade_logic_for_floating_point(&mut program, uses_floating_point && !logic_override);

    // Build and emit violation disjunction (consume violations via into_iter)
    let violation_preds: Vec<Expr> = vc
        .violations
        .into_iter()
        .enumerate()
        .map(|(i, v)| {
            // Preserve the exact recorded SMT var when available (#2078). This keeps
            // emit_bmc output aligned with legacy naming and VC artifact metadata.
            let pred_name: std::borrow::Cow<'_, str> = match v.smt_var.as_deref() {
                Some(name) => std::borrow::Cow::Borrowed(name),
                None => {
                    use std::fmt::Write;
                    let label = v.kind.label();
                    let mut s = String::with_capacity(14 + label.len() + 4);
                    s.push_str("ay_violation_");
                    s.push_str(label);
                    s.push('_');
                    let _ = write!(s, "{i}");
                    std::borrow::Cow::Owned(s)
                }
            };
            let pred = program.declare_const(&*pred_name, bool_sort());
            define_property_flag(&mut program, pred.clone(), v.condition);
            pred
        })
        .collect();

    // Final assertion: at least one violation must be satisfiable
    if let Some((first, rest)) = violation_preds.split_first() {
        let any_violation = rest.iter().fold(first.clone(), |a, b| a.or(b.clone()));
        program.assert(any_violation);
    } else {
        // No violations to check - assert false to make query trivially UNSAT
        program.assert(Expr::bool_const(false));
    }

    // Add check-sat
    program.check_sat();

    // Emit get-value for model queries and violation predicates (if produce_model is enabled)
    // The violation predicates allow the driver to identify which property failed.
    // model_queries typically contains kani::any_raw vars for concrete playback.
    if vc.query.produce_model {
        let mut get_value_exprs = violation_preds;
        // Move model_queries directly — no clones
        get_value_exprs.extend(vc.model_queries);
        if !get_value_exprs.is_empty() {
            program.get_value(get_value_exprs);
        }
    }

    program
}

/// Emits a single declaration to the AY program.
///
/// Clones the sort/arg_sorts/datatype from the reference. Since sorts and
/// datatypes use Arc internally, cloning is cheap (refcount bump).
///
/// REQUIRES: decl is a valid Decl variant (Const, Fun, or Datatype)
/// ENSURES: Decl::Const => program gains one declare-const command
/// ENSURES: Decl::Fun => program gains one declare-fun command
/// ENSURES: Decl::Datatype => program gains one declare-datatype command
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

/// Whether some term or declaration of `vc` reaches the floating-point theory.
///
/// A Rust float is carried as a bit-vector and enters the theory only inside
/// an operation (`(fp.to_ieee_bv (fp.rem (fp ..) (fp ..)))` has sort
/// `BitVec`), so every subterm's sort is read, not only the declarations.
/// Subterms an `Arc` shares are visited once.
pub(in crate::codegen_ay) fn bmc_vc_uses_floating_point(vc: &BmcVc) -> bool {
    fn sort_uses_fp(sort: &Sort) -> bool {
        match sort.inner() {
            SortInner::FloatingPoint(..) => true,
            SortInner::Array(array) => {
                sort_uses_fp(&array.index_sort) || sort_uses_fp(&array.element_sort)
            }
            SortInner::Seq(element) => sort_uses_fp(element),
            // A datatype already widens the logic to `ALL`
            // (`upgrade_logic_for_datatypes`), whatever its fields are.
            _ => false,
        }
    }
    fn expr_uses_fp(expr: &Expr, seen: &mut std::collections::HashSet<*const ExprValue>) -> bool {
        if sort_uses_fp(expr.sort()) {
            return true;
        }
        seen.insert(std::ptr::from_ref(expr.value()))
            && expr.children().any(|child| expr_uses_fp(child, seen))
    }
    let decl_uses_fp = |decl: &Decl| match decl {
        Decl::Const { sort, .. } => sort_uses_fp(sort),
        Decl::Fun { arg_sorts, ret_sort, .. } => {
            arg_sorts.iter().any(sort_uses_fp) || sort_uses_fp(ret_sort)
        }
        Decl::Datatype { .. } => false,
    };
    let mut seen = std::collections::HashSet::new();
    vc.decls.iter().any(decl_uses_fp)
        || vc.constraints.iter().any(|expr| expr_uses_fp(expr, &mut seen))
        || vc.violations.iter().any(|violation| expr_uses_fp(&violation.condition, &mut seen))
        || vc.model_queries.iter().any(|expr| expr_uses_fp(expr, &mut seen))
}

/// Widen a BMC program's declared logic to `ALL` when its terms use the
/// floating-point theory, as `upgrade_logic_for_datatypes` does for datatypes.
///
/// The default BMC logic is `QF_AUFBV`, which has no floating point, and a
/// float operation (`fp.rem`, `fp.add`, ..) under it is outside the declared
/// logic. ay takes a mapped declared logic as its routing, so such a VC goes
/// to the array/bit-vector procedure, which does not interpret the FP
/// operations. Its candidate model then fails ay's FP-aware model check and
/// the verdict is `unknown`: measured on the float `%` / `rem_euclid` /
/// `div_euclid` e2e tests (`x == 5.0 => x % 3.0 == 2.0`), with every ay CLI
/// from 501caafdf to d80d17a90 and in process at d80d17a90, and a bare
/// `fp.add` under `QF_BV` is `unknown` too. Under `ALL` ay picks the procedure
/// from the content, `QF_ABVFP` for these VCs, and proves them. `ALL` rather
/// than a named FP logic because the VC can also carry uninterpreted
/// functions, integers or datatypes, and `ALL` admits each of them.
///
/// `HORN` is never widened (CHC semantics), and neither is a logic that
/// already names floating point (`*FP*`) or is `ALL` / `ALL_SUPPORTED`. An
/// unset logic stays unset: the solver then reads the content anyway. Callers
/// skip the widening for a logic the user named (`--ay-logic`), which also
/// makes `--ay-logic QF_AUFBV` the way to reproduce the narrow logic.
pub(in crate::codegen_ay) fn upgrade_logic_for_floating_point(
    program: &mut AYProgram,
    uses_floating_point: bool,
) {
    if !uses_floating_point {
        return;
    }
    let widen = program.get_logic().is_some_and(|logic| {
        logic != "HORN" && logic != "ALL" && logic != "ALL_SUPPORTED" && !logic.contains("FP")
    });
    if widen {
        program.set_logic("ALL");
    }
}

fn collect_implicit_bmc_vars(vc: &BmcVc, vars: &mut BTreeMap<String, Sort>) {
    let bound = BTreeSet::new();
    for constraint in &vc.constraints {
        collect_expr_vars(constraint, vars, &bound);
    }
    for violation in &vc.violations {
        collect_expr_vars(&violation.condition, vars, &bound);
    }
    for query in &vc.model_queries {
        collect_expr_vars(query, vars, &bound);
    }
}

fn collect_expr_vars(expr: &Expr, vars: &mut BTreeMap<String, Sort>, bound: &BTreeSet<String>) {
    match expr.value() {
        ExprValue::Var { name } => {
            if !bound.contains(name) {
                vars.entry(name.clone()).or_insert_with(|| expr.sort().clone());
            }
        }
        ExprValue::Forall { vars: quantified, body, triggers }
        | ExprValue::Exists { vars: quantified, body, triggers } => {
            let mut nested_bound = bound.clone();
            for (name, _) in quantified {
                nested_bound.insert(name.clone());
            }
            collect_expr_vars(body, vars, &nested_bound);
            for group in triggers {
                for trigger in group {
                    collect_expr_vars(trigger, vars, &nested_bound);
                }
            }
        }
        _ => {
            for child in expr.children() {
                collect_expr_vars(child, vars, bound);
            }
        }
    }
}

/// Declare every datatype/array/seq sort referenced anywhere in `vc`'s
/// constraint, violation, and model-query expressions — including sorts that
/// appear only as an intermediate node's result sort.
///
/// A single shared `seen` set is threaded across all expressions so a datatype
/// is walked transitively at most once; `program.declare_datatype` additionally
/// dedups by name, so this never double-declares sorts already emitted.
fn declare_intermediate_sorts(program: &mut AYProgram, vc: &BmcVc) {
    let mut seen = BTreeSet::new();
    for constraint in &vc.constraints {
        declare_expr_sorts(program, constraint, &mut seen);
    }
    for violation in &vc.violations {
        declare_expr_sorts(program, &violation.condition, &mut seen);
    }
    for query in &vc.model_queries {
        declare_expr_sorts(program, query, &mut seen);
    }
}

/// Declare the result sort of `expr` and, transitively, of every subexpression.
///
/// `Expr::children()` yields all child nodes, including quantifier bodies /
/// triggers and datatype-constructor arguments, so this visits the entire tree.
fn declare_expr_sorts(program: &mut AYProgram, expr: &Expr, seen: &mut BTreeSet<String>) {
    ensure_sort_declared_inner(program, expr.sort(), seen);
    for child in expr.children() {
        declare_expr_sorts(program, child, seen);
    }
}

fn ensure_sort_declared(program: &mut AYProgram, sort: &Sort) {
    let mut seen = BTreeSet::new();
    ensure_sort_declared_inner(program, sort, &mut seen);
}

fn ensure_sort_declared_inner(program: &mut AYProgram, sort: &Sort, seen: &mut BTreeSet<String>) {
    match sort.inner() {
        SortInner::Array(array) => {
            ensure_sort_declared_inner(program, &array.index_sort, seen);
            ensure_sort_declared_inner(program, &array.element_sort, seen);
        }
        SortInner::Datatype(datatype) => {
            if !seen.insert(datatype.name.clone()) {
                return;
            }
            for constructor in &datatype.constructors {
                for field in &constructor.fields {
                    ensure_sort_declared_inner(program, &field.sort, seen);
                }
            }
            program.declare_datatype(datatype.clone());
        }
        SortInner::Seq(element) => ensure_sort_declared_inner(program, element, seen),
        _ => {}
    }
}

/// Emits a CHC verification condition to a AY program.
///
/// Converts the abstract `ChcVc` to a concrete `AYProgram` in HORN logic
/// for solving by AY/Z3's CHC engine (PDR). The structure is:
///
/// ```text
/// (set-logic HORN)
/// (declare-rel block_0 (State))  ; relation declarations
/// (declare-rel error ())
/// (rule (=> body head))          ; Horn rules
/// (query error)                   ; reachability query
/// ```
///
/// # Arguments
///
/// * `vc` - The CHC verification condition to emit
///
/// # Returns
///
/// A `AYProgram` ready for serialization to SMT-LIB2 (HORN logic).
///
/// REQUIRES: vc.relations contains valid relation declarations
/// REQUIRES: vc.rules contains well-formed Horn rules
/// ENSURES: Output program uses HORN logic
/// ENSURES: Output program contains one declare-rel per relation
/// ENSURES: Output program contains one rule per Horn rule
/// ENSURES: Output program ends with query command if target is set
pub(in crate::codegen_ay) fn emit_chc(vc: &ChcVc) -> AYProgram {
    let mut program = AYProgram::horn();

    // Warn if CHC VC appears empty or malformed
    if vc.rules.is_empty() {
        warn!("emit_chc: ChcVc has no rules - verification will be trivial");
    }
    if vc.query.target.is_none() {
        warn!("emit_chc: ChcVc has no query target - no reachability check will be performed");
    }

    // Emit declarations (Arc-based sorts/datatypes: clone is refcount bump)
    for decl in &vc.decls {
        emit_decl(&mut program, decl);
    }

    // Emit variable declarations (deref Arc<str> to &str, clone Sort)
    for var in vc.vars() {
        program.declare_var(&*var.name, var.sort.clone());
    }

    // Emit relation declarations (clone Arc<str> name + Vec<Sort>)
    for rel in &vc.relations {
        program.declare_rel(rel.name.clone(), rel.arg_sorts.clone());
    }

    // Emit Horn rules (Expr clone is O(1) via Arc)
    for rule in &vc.rules {
        let body_expr = build_rule_body(&rule.body);
        let head_expr = build_relation_app(&rule.head);
        program.rule(head_expr, body_expr);
    }

    // Emit query
    if let Some(ref target) = vc.query.target {
        let query_expr = Expr::var(target.as_str(), bool_sort());
        program.query(query_expr);
    }

    // Part of #1162: Emit cover property declarations and assertions AFTER the
    // query. PDR processes the HORN program up to `(query error)` — anything
    // emitted after the query is not part of the CHC solving but remains in the
    // serialized SMT-LIB file for the driver's secondary SAT check to extract.
    // Placing these before the query caused PDR to treat them as additional
    // HORN constraints, making the CHC problem UNKNOWN for trivial covers.
    for (name, condition) in &vc.cover_assertions {
        let pred = program.declare_const(name, bool_sort());
        program.assert(pred.eq(condition.clone()));
    }

    // Debug: dump generated SMT-LIB (#1889)
    // Part of #2267: use eq_ignore_ascii_case to avoid String allocation from to_lowercase().
    if std::env::var("CHC_DEBUG")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false)
    {
        debug!("=== GENERATED SMT-LIB ===\n{}", program);
        debug!("=== END SMT-LIB ===");
    }

    program
}

/// Programmatic CHC emission entrypoint.
///
/// This exposes the existing HORN SMT-LIB lowering without requiring the
/// caller to go through the compiler's artifact writer.
pub(in crate::codegen_ay) fn emit_chc_program(vc: &ChcVc) -> AYProgram {
    emit_chc(vc)
}

/// Emit a CHC verification condition directly to SMT-LIB2 text.
///
/// This is the string form consumed by the native CHC driver API and avoids
/// coupling callers to `.smt2` files.
pub(in crate::codegen_ay) fn emit_chc_smt2(vc: &ChcVc) -> String {
    emit_chc(vc).to_string()
}

/// Builds an expression for a rule body from a reference.
///
/// The rule body is a conjunction of:
/// 1. An optional relation application (predecessor state)
/// 2. Zero or more constraints
///
/// Expr cloning is O(1) since Expr uses Arc<ExprValue> internally.
#[must_use]
fn build_rule_body(body: &trust_mc_core::chc::RuleBody) -> Expr {
    let mut conjuncts: Vec<Expr> =
        Vec::with_capacity(body.constraints.len() + usize::from(body.relation.is_some()));

    if let Some(ref rel_app) = body.relation {
        conjuncts.push(build_relation_app(rel_app));
    }

    // Clone each constraint — O(1) per Expr due to Arc
    conjuncts.extend(body.constraints.iter().cloned());

    conjuncts.into_iter().reduce(ay_bindings::Expr::and).unwrap_or_else(|| Expr::bool_const(true))
}

/// Builds an expression for a relation application from a reference.
#[must_use]
fn build_relation_app(app: &trust_mc_core::chc::RelationApp) -> Expr {
    if app.args.is_empty() {
        Expr::var(&*app.name, bool_sort())
    } else {
        // Clone the Arc<Vec<Expr>> contents — each Expr clone is O(1) via Arc
        let args: Vec<Expr> = (*app.args).clone();
        Expr::func_app(&*app.name, args)
    }
}
