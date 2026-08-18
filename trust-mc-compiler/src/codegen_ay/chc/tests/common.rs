// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

// Shared imports for all test modules
pub(super) use super::super::super::names;
pub(super) use super::super::super::names::{enum_sort, struct_sort};
pub(super) use super::super::super::test_fixtures::{option_like_struct_sort, point_sort_prefixed};
pub(super) use super::super::ChcConfig;
pub(super) use super::super::codegen_call_coerce::coerce_eq_constraint;
pub(super) use super::super::codegen_call_misc::CallMisc;
pub(super) use super::super::codegen_stmt_store_ref::StmtStoreRef;
pub(super) use super::super::codegen_types::CodegenTypes;
pub(super) use super::super::stubs_option_helpers::OptionHelpers;
pub(super) use super::super::*;
pub(super) use crate::codegen_ay::context::with_test_ay_ctx_for_source;
pub(super) use crate::codegen_ay::stubs::StubKind;
pub(super) use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
pub(super) use ay_bindings::{Expr, ExprValue, SortInner};
pub(super) use rustc_middle::ty::TyCtxt;
pub(super) use rustc_public::CrateDef;
pub(super) use rustc_public::mir::{AggregateKind, Operand, Place};
pub(super) use rustc_public::rustc_internal;
pub(super) use rustc_public::ty::{FnSig, RigidTy, TyKind, UintTy};
pub(super) use std::collections::HashSet;
pub(super) use trust_mc_core::chc::RelationDecl;

// Collection test fixtures
pub(super) use super::super::super::test_fixtures::{
    hashmap_iter_sort, hashset_iter_sort, option_datatype_sort, tuple_sort,
};

/// Helper: Find a function signature by name suffix in the current crate.
pub(super) fn fn_sig_by_suffix(tcx: TyCtxt<'_>, suffix: &str) -> FnSig {
    let matches: Vec<_> = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| {
            let def_id = rustc_internal::internal(tcx, item.def_id());
            let path = tcx.def_path_str(def_id);
            path == suffix || path.ends_with(&format!("::{suffix}"))
        })
        .collect();
    match matches.as_slice() {
        [] => panic!("missing item with suffix '{suffix}'"),
        [single] => {
            let def_id = rustc_internal::internal(tcx, single.def_id());
            let fn_ty = rustc_internal::stable(tcx.type_of(def_id)).value;
            fn_ty.kind().fn_sig().expect("expected function signature").skip_binder()
        }
        many => {
            let names: Vec<_> = many
                .iter()
                .map(|item| {
                    let def_id = rustc_internal::internal(tcx, item.def_id());
                    tcx.def_path_str(def_id)
                })
                .collect();
            panic!("ambiguous suffix '{suffix}': {} matches: {names:?}", many.len());
        }
    }
}

pub(super) fn find_crate_item_by_suffix(tcx: TyCtxt<'_>, suffix: &str) -> rustc_public::CrateItem {
    let matches: Vec<_> = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| {
            let def_id = rustc_internal::internal(tcx, item.def_id());
            let path = tcx.def_path_str(def_id);
            path == suffix || path.ends_with(&format!("::{suffix}"))
        })
        .collect();
    match matches.as_slice() {
        [] => panic!("missing item with suffix '{suffix}'"),
        [single] => *single,
        many => {
            let names: Vec<_> = many
                .iter()
                .map(|item| {
                    let def_id = rustc_internal::internal(tcx, item.def_id());
                    tcx.def_path_str(def_id)
                })
                .collect();
            panic!("ambiguous suffix '{suffix}': {} matches: {names:?}", many.len());
        }
    }
}

pub(super) fn resolve_single_type_generic_instance_by_suffix(
    tcx: TyCtxt<'_>,
    suffix: &str,
    concrete_ty: rustc_public::ty::Ty,
) -> rustc_public::mir::mono::Instance {
    let item = find_crate_item_by_suffix(tcx, suffix);
    let def_id = rustc_internal::internal(tcx, item.def_id());
    let fn_ty = rustc_internal::stable(tcx.type_of(def_id)).value;
    let TyKind::RigidTy(RigidTy::FnDef(fn_def, _)) = fn_ty.kind() else {
        panic!("item '{suffix}' is not a function: {fn_ty:?}");
    };
    rustc_public::mir::mono::Instance::resolve(
        fn_def,
        &rustc_public::ty::GenericArgs(vec![rustc_public::ty::GenericArgKind::Type(concrete_ty)]),
    )
    .expect("single-type generic instance should resolve")
}

/// Generic helper: collect StubKinds from Call terminators using a detection closure.
///
/// Replaces 7 nearly-identical `collect_detected_*_stubs` functions.
/// The closure receives (func, args) from each Call terminator and returns
/// `Option<StubKind>`.
fn collect_stubs_with<F>(body: &rustc_public::mir::Body, mut detect: F) -> Vec<StubKind>
where
    F: FnMut(&rustc_public::mir::Operand, &[rustc_public::mir::Operand]) -> Option<StubKind>,
{
    use rustc_public::mir::TerminatorKind;
    let mut detected = Vec::new();
    for block in &body.blocks {
        if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind
            && let Some(stub_kind) = detect(func, args)
        {
            detected.push(stub_kind);
        }
    }
    detected
}

/// Collect detected BigInt StubKinds from Call terminators.
pub(super) fn collect_detected_bigint_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    collect_stubs_with(body, |func, args| chc_ctx.detect_bigint_stub(func, args))
}

/// Collect detected BigRational StubKinds from Call terminators.
pub(super) fn collect_detected_bigrational_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    collect_stubs_with(body, |func, args| chc_ctx.detect_bigrational_stub(func, args))
}

/// Collect detected HashMap StubKinds from Call terminators.
pub(super) fn collect_detected_hashmap_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    collect_stubs_with(body, |func, args| chc_ctx.detect_hashmap_stub(func, args))
}

/// Collect detected collection predicate StubKinds (Vec/String is_empty).
pub(super) fn collect_detected_collection_predicate_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    collect_stubs_with(body, |func, _| {
        chc_ctx.detect_stub_matching(func, StubKind::is_collection_predicate)
    })
}

/// Collect detected Vec iterator StubKinds (into_iter, iter, iter_mut, next).
pub(super) fn collect_detected_vec_iter_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    collect_stubs_with(body, |func, _| chc_ctx.detect_vec_iter_stub(func))
}

/// Collect detected iterator intrinsic StubKinds (CheckedAddUnsigned, OptionUnwrapUnchecked).
pub(super) fn collect_detected_iterator_intrinsic_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    collect_stubs_with(body, |func, _| chc_ctx.detect_iterator_intrinsic_stub(func))
}

/// Collect detected Result predicate StubKinds (is_ok/is_err).
pub(super) fn collect_detected_result_predicate_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    collect_stubs_with(body, |func, _| {
        chc_ctx.detect_stub_matching(func, StubKind::is_result_predicate)
    })
}

/// Collect detected ptr.add/ptr.write/ptr.read StubKinds from Call terminators.
pub(super) fn collect_detected_ptr_memory_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    collect_stubs_with(body, |func, _| chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory))
}

/// Collect detected pointer utility StubKinds (NonZero/ptr helpers) from calls.
pub(super) fn collect_detected_pointer_utility_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    collect_stubs_with(body, |func, _| {
        chc_ctx.detect_stub_matching(func, StubKind::is_pointer_utility)
    })
}

/// Collect detected mem intrinsic StubKinds (size_of/align_of) from Call terminators.
pub(super) fn collect_detected_mem_intrinsic_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    collect_stubs_with(body, |func, _| {
        chc_ctx.detect_stub_matching(func, StubKind::is_mem_intrinsic)
    })
}

/// Collect detected pointer cast StubKinds from Call terminators.
pub(super) fn collect_detected_ptr_cast_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    collect_stubs_with(body, |func, _| chc_ctx.detect_stub_matching(func, StubKind::is_ptr_cast))
}

/// Collect detected String core StubKinds from Call terminators.
pub(super) fn collect_detected_string_core_stubs<'tcx, 'body>(
    chc_ctx: &ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> Vec<StubKind> {
    collect_stubs_with(body, |func, _| chc_ctx.detect_stub_matching(func, StubKind::is_string_core))
}

/// Shared structural checks for CHC pipeline tests.
/// Verifies: relations count, error relation, bb0 entry, entry rule, rule count,
/// and rule-head referential integrity against declared relations.
///
/// `bb_count` is the total number of MIR basic blocks. After dead block
/// elimination (#3436), error-only blocks (those that cannot reach Return)
/// are excluded from relation declaration. The actual relation count will
/// be: return-reachable blocks + 1 (error). This is always >= 2 (bb0 + error)
/// and always <= bb_count + 1.
pub(super) fn assert_vc_structure(vc: &trust_mc_core::chc::ChcVc, fn_name: &str, bb_count: usize) {
    // 1. Relations: at least entry (bb0) + error; at most all BBs + error.
    // Dead block elimination (#3436) removes error-only blocks, so the count
    // can be less than bb_count.
    //
    // BSEM-18: block-relation count is bounded by `bb_count`; the error family
    // (`error` plus one `error_p{id}` per check site) is excluded from the
    // block bound since it is proportional to the number of checks, not blocks.
    assert!(
        vc.relations.len() >= 2,
        "{fn_name}: expected >= 2 relations (bb0 + error), got {}",
        vc.relations.len()
    );
    let block_relation_count =
        vc.relations.iter().filter(|r| !is_error_head(r.name.as_str())).count();
    assert!(
        block_relation_count <= bb_count,
        "{fn_name}: expected <= {bb_count} block relations, got {block_relation_count}"
    );

    // 2. Error relation must exist
    let has_error = vc.relations.iter().any(|r| r.name == "error");
    assert!(has_error, "{fn_name}: missing 'error' relation");

    // 3. bb0 relation must exist (entry point)
    let has_bb0 = vc.relations.iter().any(|r| r.name.contains("__bb0"));
    assert!(has_bb0, "{fn_name}: missing bb0 relation");

    // 4. Entry rule: body.relation is None, head targets bb0
    let entry_rules: Vec<_> = vc.rules.iter().filter(|r| r.body.relation.is_none()).collect();
    assert!(!entry_rules.is_empty(), "{fn_name}: no entry (init) rule found");
    let has_discharged_straightline_obligation = entry_rules.iter().any(|rule| {
        rule.head.name == "error"
            && rule
                .body
                .constraints
                .iter()
                .any(|constraint| matches!(constraint.value(), ExprValue::BoolConst(false)))
    });
    assert!(
        entry_rules.iter().any(|rule| rule.head.name.contains("__bb0"))
            || has_discharged_straightline_obligation,
        "{fn_name}: entry rules should include a bb0 target, got: {:?}",
        entry_rules.iter().map(|rule| rule.head.name.as_str()).collect::<Vec<_>>()
    );

    // 5. Rules count: at least 1 (the entry rule). Dead block elimination
    // may significantly reduce rule count by excluding error-only block chains.
    assert!(!vc.rules.is_empty(), "{fn_name}: expected at least 1 rule (entry), got 0",);

    // 6. All rule heads must reference declared relations
    let declared: HashSet<_> = vc.relations.iter().map(|r| r.name.as_str()).collect();
    for rule in &vc.rules {
        assert!(
            declared.contains(rule.head.name.as_str()),
            "{fn_name}: rule head '{}' references undeclared relation",
            rule.head.name
        );
    }
}

/// Fail loudly when a MIR probe no longer contains the target pattern.
///
/// Tests that exercise specific CHC code paths must assert this predicate so
/// optimizer-driven MIR changes cannot silently make the test vacuous.
pub(super) fn assert_mir_pattern_found(found: bool, pattern: &str) {
    assert!(
        found,
        "Expected target MIR pattern '{pattern}'. Optimizer may have eliminated it; adjust the probe."
    );
}

// HashMap/HashSet iterator test helpers

pub(super) fn is_selector_named(expr: &Expr, name: &str) -> bool {
    matches!(
        expr.value(),
        ExprValue::DatatypeSelector { selector_name, .. } if selector_name == name
    )
}

pub(super) fn is_keys_pos_select(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::Select { array, index } => {
            is_selector_named(array, "fld_keys") && is_selector_named(index, "fld_pos")
        }
        _ => false,
    }
}

/// DT-free (#3057): membership is select(fld_present, keys[pos]) — plain Bool.
pub(super) fn is_present_key_select(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::Select { array, index } => {
            is_selector_named(array, "fld_present") && is_keys_pos_select(index)
        }
        _ => false,
    }
}

pub(super) fn is_set_key_select(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::Select { array, index } => {
            is_selector_named(array, "fld_set") && is_keys_pos_select(index)
        }
        _ => false,
    }
}

pub(super) fn is_iter_bounds_check(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::BvULt(lhs, rhs) => {
            is_selector_named(lhs, "fld_pos") && is_selector_named(rhs, "fld_len")
        }
        _ => false,
    }
}

/// DT-free (#3057): membership is select(present, keys[pos]) directly.
/// No DatatypeTester/DatatypeSelector wrapper — the fld_present array
/// already returns Bool.
pub(super) fn is_hashmap_is_member(expr: &Expr) -> bool {
    is_present_key_select(expr)
}

pub(super) fn is_hashmap_iter_membership_constraint(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            matches!(else_expr.value(), ExprValue::BoolConst(true))
                && is_iter_bounds_check(cond)
                && then_expr.sort().is_bool()
                && is_hashmap_is_member(then_expr)
        }
        _ => false,
    }
}

pub(super) fn is_hashset_iter_membership_constraint(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::Ite { cond, then_expr, else_expr } => {
            matches!(else_expr.value(), ExprValue::BoolConst(true))
                && is_iter_bounds_check(cond)
                && then_expr.sort().is_bool()
                && is_set_key_select(then_expr)
        }
        _ => false,
    }
}

// =========================================================================
// Vec Store/Select structural predicates (Part of #2854)
// =========================================================================

/// Check if an expression references the Vec `fld_data` backing array.
///
/// In Datatype mode, the array is accessed via `DatatypeSelector { selector_name: "fld_data", .. }`.
/// In projected mode (#2874), it is a `Var` whose name contains "fld_data" or "fld3".
pub(super) fn references_fld_data(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::DatatypeSelector { selector_name, .. } => {
            selector_name == "fld_data" || selector_name == "fld3"
        }
        ExprValue::Var { name } => name.contains("fld_data") || name.contains("fld3"),
        _ => false,
    }
}

/// Check if an expression is a `Store` whose array operand references `fld_data`.
pub(super) fn is_store_on_fld_data(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::Store { array, .. } => {
            references_fld_data(array) || constraint_tree_contains(array, &references_fld_data)
        }
        _ => false,
    }
}

/// Check if an expression is a `Select` whose array operand references `fld_data`.
pub(super) fn is_select_on_fld_data(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::Select { array, .. } => {
            references_fld_data(array) || constraint_tree_contains(array, &references_fld_data)
        }
        _ => false,
    }
}

/// Check if an expression is an `Ite` (used for Option construction in VecPop).
pub(super) fn is_ite(expr: &Expr) -> bool {
    matches!(expr.value(), ExprValue::Ite { .. })
}

// =========================================================================
// Semantic assertion helpers (Part of #2558 — Wave 1)
// =========================================================================

/// Assert that at least one transition rule (non-init, non-error) carries
/// non-trivial semantics — either in body constraints or head arguments.
///
/// A rule is "trivial" when every body constraint is `BoolConst(true)` AND
/// every head argument is a plain `Var`. Simple non-branching functions
/// (single-block, call stubs) legitimately encode semantics in head argument
/// expressions (e.g. `bvadd(a, b)`, field selectors) rather than body
/// constraints. This helper catches both encoding styles.
pub(super) fn assert_has_nontrivial_transition_constraints(
    vc: &trust_mc_core::chc::ChcVc,
    fn_name: &str,
) {
    let has_nontrivial = vc.rules.iter().any(|rule| {
        // Skip init rules (no source relation) and error-head rules
        if rule.body.relation.is_none() || &*rule.head.name == "error" {
            return false;
        }
        // Non-trivial body constraint?
        let body_nontrivial =
            rule.body.constraints.iter().any(|c| !matches!(c.value(), ExprValue::BoolConst(true)));
        // Non-trivial head arg? (anything beyond a plain Var is a computed value)
        let head_nontrivial =
            rule.head.args.iter().any(|a| !matches!(a.value(), ExprValue::Var { .. }));
        body_nontrivial || head_nontrivial
    });
    assert!(
        has_nontrivial,
        "{fn_name}: no transition rule has non-trivial semantics. \
         All rule bodies are vacuously true and all head args are plain variables — \
         codegen may be emitting unconstrained transitions."
    );
}

/// Assert that the VC contains state of the given sort — either as a relation
/// argument sort or as a free variable (`declare-var`) sort.
///
/// After the free-variable encoding migration, state variables may appear as
/// `declare-var` entries (in `vc.vars()`) rather than relation argument sorts.
/// This helper checks both locations so tests are encoding-strategy-agnostic.
///
/// `sort_pred` receives each sort and returns true if it matches.
/// `sort_desc` is a human-readable label for error messages (e.g. "Bool",
/// "bv32").
pub(super) fn assert_relation_has_arg_sort(
    vc: &trust_mc_core::chc::ChcVc,
    fn_name: &str,
    sort_pred: impl Fn(&ay_bindings::Sort) -> bool,
    sort_desc: &str,
) {
    let in_relations = vc.relations.iter().any(|r| r.arg_sorts.iter().any(&sort_pred));
    let in_vars = vc.vars().iter().any(|v| sort_pred(&v.sort));
    assert!(
        in_relations || in_vars,
        "{fn_name}: expected at least one relation with a {sort_desc} argument sort"
    );
}

/// Assert that at least one rule across all rules contains the given
/// expression kind — searching both body constraints and head arguments.
///
/// Call stubs and single-block functions may encode semantics in head
/// argument expressions rather than body constraints. This searches both.
///
/// `expr_pred` receives each `Expr` and returns true on match.
/// `expr_desc` is a human-readable label for error messages (e.g. "bvadd",
/// "Store", "Eq").
pub(super) fn assert_rule_contains_expr_kind(
    vc: &trust_mc_core::chc::ChcVc,
    fn_name: &str,
    expr_pred: impl Fn(&Expr) -> bool,
    expr_desc: &str,
) {
    let found = vc.rules.iter().any(|rule| {
        let in_body = rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &expr_pred));
        let in_head = rule.head.args.iter().any(|a| constraint_tree_contains(a, &expr_pred));
        let in_body_rel =
            rule.body.relation.as_ref().is_some_and(|rel| {
                rel.args.iter().any(|a| constraint_tree_contains(a, &expr_pred))
            });
        in_body || in_head || in_body_rel
    });
    assert!(
        found,
        "{fn_name}: no rule constraint, head arg, or body relation arg contains a {expr_desc} expression. \
         The codegen path may not be emitting the expected constraint form."
    );
}

/// Recursively walk an expression tree and return true if any sub-expression
/// matches `pred`. This allows asserting that a deeply-nested operator (e.g.
/// `bvadd` inside an `Eq` inside an `Ite`) is present.
pub(super) fn constraint_tree_contains(expr: &Expr, pred: &impl Fn(&Expr) -> bool) -> bool {
    if pred(expr) {
        return true;
    }
    let mut stack: Vec<&Expr> = expr_children(expr);
    while let Some(child) = stack.pop() {
        if pred(child) {
            return true;
        }
        stack.extend(expr_children(child));
    }
    false
}

/// Extract binary sub-expression pair, if the expression is a binary operator.
fn expr_children_binary(val: &ExprValue) -> Option<[&Expr; 2]> {
    match val {
        ExprValue::Eq(a, b)
        | ExprValue::BvAdd(a, b)
        | ExprValue::BvSub(a, b)
        | ExprValue::BvMul(a, b)
        | ExprValue::BvUDiv(a, b)
        | ExprValue::BvSDiv(a, b)
        | ExprValue::BvURem(a, b)
        | ExprValue::BvSRem(a, b)
        | ExprValue::BvAnd(a, b)
        | ExprValue::BvOr(a, b)
        | ExprValue::BvXor(a, b)
        | ExprValue::BvShl(a, b)
        | ExprValue::BvLShr(a, b)
        | ExprValue::BvAShr(a, b)
        | ExprValue::BvConcat(a, b)
        | ExprValue::BvULt(a, b)
        | ExprValue::BvULe(a, b)
        | ExprValue::BvUGt(a, b)
        | ExprValue::BvUGe(a, b)
        | ExprValue::BvSLt(a, b)
        | ExprValue::BvSLe(a, b)
        | ExprValue::BvSGt(a, b)
        | ExprValue::BvSGe(a, b)
        | ExprValue::IntAdd(a, b)
        | ExprValue::IntSub(a, b)
        | ExprValue::IntMul(a, b)
        | ExprValue::IntDiv(a, b)
        | ExprValue::IntMod(a, b)
        | ExprValue::IntLt(a, b)
        | ExprValue::IntLe(a, b)
        | ExprValue::IntGt(a, b)
        | ExprValue::IntGe(a, b)
        | ExprValue::RealAdd(a, b)
        | ExprValue::RealSub(a, b)
        | ExprValue::RealMul(a, b)
        | ExprValue::RealDiv(a, b)
        | ExprValue::RealLt(a, b)
        | ExprValue::RealLe(a, b)
        | ExprValue::RealGt(a, b)
        | ExprValue::RealGe(a, b)
        | ExprValue::Implies(a, b)
        | ExprValue::Xor(a, b)
        | ExprValue::BvAddNoOverflowUnsigned(a, b)
        | ExprValue::BvAddNoOverflowSigned(a, b)
        | ExprValue::BvSubNoUnderflowUnsigned(a, b)
        | ExprValue::BvSubNoOverflowSigned(a, b)
        | ExprValue::BvMulNoOverflowUnsigned(a, b)
        | ExprValue::BvMulNoOverflowSigned(a, b)
        | ExprValue::BvSdivNoOverflow(a, b)
        | ExprValue::Select { array: a, index: b } => Some([a, b]),
        _ => None,
    }
}

/// Return the direct child sub-expressions of an `ExprValue`.
pub(super) fn expr_children(expr: &Expr) -> Vec<&Expr> {
    let val = expr.value();
    if let Some([a, b]) = expr_children_binary(val) {
        return vec![a, b];
    }
    match val {
        // Leaf nodes
        ExprValue::BoolConst(_)
        | ExprValue::BitVecConst { .. }
        | ExprValue::IntConst(_)
        | ExprValue::RealConst(_)
        | ExprValue::Var { .. } => vec![],
        // Unary
        ExprValue::Not(e)
        | ExprValue::BvNeg(e)
        | ExprValue::BvNot(e)
        | ExprValue::IntNeg(e)
        | ExprValue::RealNeg(e)
        | ExprValue::Bv2Int(e)
        | ExprValue::IntToReal(e)
        | ExprValue::BvZeroExtend { expr: e, .. }
        | ExprValue::BvSignExtend { expr: e, .. }
        | ExprValue::BvExtract { expr: e, .. }
        | ExprValue::DatatypeSelector { expr: e, .. }
        | ExprValue::DatatypeTester { expr: e, .. }
        | ExprValue::BvNegNoOverflow(e)
        | ExprValue::Int2Bv(e, _)
        | ExprValue::ConstArray { value: e, .. }
        | ExprValue::Forall { body: e, .. }
        | ExprValue::Exists { body: e, .. } => vec![e],
        // Ternary
        ExprValue::Ite { cond, then_expr, else_expr } => vec![cond, then_expr, else_expr],
        ExprValue::Store { array, index, value } => vec![array, index, value],
        // N-ary
        ExprValue::And(es) | ExprValue::Or(es) | ExprValue::Distinct(es) => es.iter().collect(),
        ExprValue::DatatypeConstructor { args, .. } | ExprValue::FuncApp { args, .. } => {
            args.iter().collect()
        }
        // Binary cases handled above; catch remaining
        _ => vec![],
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct MalformedBvSite {
    pub(super) rule_idx: usize,
    pub(super) head_relation: String,
    pub(super) op_kind: &'static str,
    pub(super) child_sorts: Vec<String>,
}

fn malformed_bv_site_detail(expr: &Expr) -> Option<(&'static str, Vec<String>)> {
    match expr.value() {
        ExprValue::BvConcat(high, low)
            if high.sort().bitvec_width().is_none() || low.sort().bitvec_width().is_none() =>
        {
            Some(("concat", vec![format!("{:?}", high.sort()), format!("{:?}", low.sort())]))
        }
        ExprValue::BvExtract { expr: inner, .. } if inner.sort().bitvec_width().is_none() => {
            Some(("extract", vec![format!("{:?}", inner.sort())]))
        }
        _ => None,
    }
}

fn first_malformed_bv_site_in_expr(expr: &Expr) -> Option<(&'static str, Vec<String>)> {
    if let Some(detail) = malformed_bv_site_detail(expr) {
        return Some(detail);
    }
    let mut stack = expr_children(expr);
    while let Some(child) = stack.pop() {
        if let Some(detail) = malformed_bv_site_detail(child) {
            return Some(detail);
        }
        stack.extend(expr_children(child));
    }
    None
}

fn first_malformed_bv_site_in_rule(
    rule_idx: usize,
    rule: &trust_mc_core::chc::Rule,
) -> Option<MalformedBvSite> {
    let head_relation = rule.head.name.to_string();
    for constraint in &rule.body.constraints {
        if let Some((op_kind, child_sorts)) = first_malformed_bv_site_in_expr(constraint) {
            return Some(MalformedBvSite { rule_idx, head_relation, op_kind, child_sorts });
        }
    }
    if let Some(relation) = &rule.body.relation {
        for arg in relation.args.iter() {
            if let Some((op_kind, child_sorts)) = first_malformed_bv_site_in_expr(arg) {
                return Some(MalformedBvSite { rule_idx, head_relation, op_kind, child_sorts });
            }
        }
    }
    for arg in rule.head.args.iter() {
        if let Some((op_kind, child_sorts)) = first_malformed_bv_site_in_expr(arg) {
            return Some(MalformedBvSite { rule_idx, head_relation, op_kind, child_sorts });
        }
    }
    None
}

pub(super) fn first_malformed_bv_site(vc: &trust_mc_core::chc::ChcVc) -> Option<MalformedBvSite> {
    vc.rules
        .iter()
        .enumerate()
        .find_map(|(rule_idx, rule)| first_malformed_bv_site_in_rule(rule_idx, rule))
}

// =========================================================================
// VC rule search helpers — avoid format!("{:?}", vc.rules) memory explosion
// =========================================================================

/// Check if any rule in the VC contains a `Var` whose name includes `needle`.
/// Searches body constraints and head arguments recursively.
///
/// This replaces the anti-pattern `format!("{:?}", vc.rules).contains(name)`
/// which materializes the entire expression tree as a multi-MB heap string.
/// With deeply nested Store/ITE chains (e.g. 13 type arrays × 64-byte window),
/// the Debug output can exceed 100MB per test — a primary OOM vector when
/// multiple tests accumulate these strings.
pub(super) fn vc_rules_contain_var(vc: &trust_mc_core::chc::ChcVc, needle: &str) -> bool {
    vc.rules.iter().any(|rule| {
        let pred = |e: &Expr| matches!(e.value(), ExprValue::Var { name } if name.contains(needle));
        rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
            || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
    })
}

pub(super) fn vc_rules_contain_var_scalarized(
    vc: &trust_mc_core::chc::ChcVc,
    base: &str,
    suffix: &str,
) -> bool {
    vc.rules.iter().any(|rule| {
        let pred = |e: &Expr| {
            matches!(e.value(), ExprValue::Var { name } if name.contains(base) && name.ends_with(suffix))
        };
        rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
            || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
    })
}

pub(super) fn vc_rules_contain_var_out(vc: &trust_mc_core::chc::ChcVc, base: &str) -> bool {
    vc_rules_contain_var_scalarized(vc, base, "__out")
}

pub(super) fn expr_is_obj_valid_false_update(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::Store { array, value, .. } => {
            matches!(array.value(), ExprValue::Var { name, .. } if name == "obj_valid")
                && matches!(value.value(), ExprValue::BoolConst(false))
        }
        ExprValue::Eq(lhs, rhs) => {
            let lhs_is_scalar_out = matches!(lhs.value(), ExprValue::Var { name, .. } if name.starts_with("obj_valid_at_") && name.ends_with("__out"));
            let rhs_is_scalar_out = matches!(rhs.value(), ExprValue::Var { name, .. } if name.starts_with("obj_valid_at_") && name.ends_with("__out"));
            (lhs_is_scalar_out && matches!(rhs.value(), ExprValue::BoolConst(false)))
                || (rhs_is_scalar_out && matches!(lhs.value(), ExprValue::BoolConst(false)))
        }
        _ => false,
    }
}

pub(super) fn vc_contains_obj_valid_false_update(vc: &trust_mc_core::chc::ChcVc) -> bool {
    vc.rules.iter().any(|rule| {
        rule.body
            .constraints
            .iter()
            .any(|constraint| constraint_tree_contains(constraint, &expr_is_obj_valid_false_update))
    })
}

pub(super) fn expr_mentions_obj_size_metadata(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::Select { array, .. } => {
            matches!(array.value(), ExprValue::Var { name, .. } if name == "obj_size")
        }
        ExprValue::Var { name, .. } => name == "obj_size" || name.starts_with("obj_size_at_"),
        _ => false,
    }
}

/// True if `name` heads an error obligation: either the aggregate `error`
/// relation or a per-property `error_p{id}` relation (BSEM-18).
pub(super) fn is_error_head(name: &str) -> bool {
    name == "error" || name.starts_with("error_p")
}

pub(super) fn vc_error_rules_contain_obj_size_metadata(vc: &trust_mc_core::chc::ChcVc) -> bool {
    vc.rules.iter().filter(|r| is_error_head(r.head.name.as_str())).any(|rule| {
        rule.body
            .constraints
            .iter()
            .any(|c| constraint_tree_contains(c, &expr_mentions_obj_size_metadata))
            || rule
                .head
                .args
                .iter()
                .any(|a| constraint_tree_contains(a, &expr_mentions_obj_size_metadata))
    })
}

/// Check if a single CHC rule references a `Var` whose name includes `needle`.
/// Searches body constraints, body relation args, and head arguments.
pub(super) fn rule_contains_var(rule: &trust_mc_core::chc::Rule, needle: &str) -> bool {
    let pred = |e: &Expr| matches!(e.value(), ExprValue::Var { name } if name.contains(needle));
    rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
        || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        || rule
            .body
            .relation
            .as_ref()
            .is_some_and(|rel| rel.args.iter().any(|a| constraint_tree_contains(a, &pred)))
}

/// Check if a single CHC rule contains an expression matching `pred`.
/// Searches body constraints, body relation args, and head arguments.
pub(super) fn rule_contains_expr(
    rule: &trust_mc_core::chc::Rule,
    pred: impl Fn(&Expr) -> bool,
) -> bool {
    rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
        || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        || rule
            .body
            .relation
            .as_ref()
            .is_some_and(|rel| rel.args.iter().any(|a| constraint_tree_contains(a, &pred)))
}

/// Check if any error-targeting rule contains a `Var` whose name includes `needle`.
/// Searches body constraints, body relation args, and head arguments.
pub(super) fn vc_error_rules_contain_var(vc: &trust_mc_core::chc::ChcVc, needle: &str) -> bool {
    vc.rules
        .iter()
        .filter(|r| is_error_head(r.head.name.as_str()))
        .any(|rule| rule_contains_var(rule, needle))
}

/// Check if any constraint across all rules, when serialized to SMT-LIB2,
/// satisfies `pred`. Streams one constraint at a time to avoid collecting
/// all serialized strings into memory simultaneously.
pub(super) fn any_constraint_str(
    vc: &trust_mc_core::chc::ChcVc,
    pred: impl Fn(&str) -> bool,
) -> bool {
    vc.rules.iter().flat_map(|r| r.body.constraints.iter()).any(|c| pred(&c.to_string()))
}

/// Count constraints across all rules whose SMT-LIB2 serialization satisfies `pred`.
/// Streams one constraint at a time.
pub(super) fn count_constraint_str(
    vc: &trust_mc_core::chc::ChcVc,
    pred: impl Fn(&str) -> bool,
) -> usize {
    vc.rules.iter().flat_map(|r| r.body.constraints.iter()).filter(|c| pred(&c.to_string())).count()
}

/// Check if any rule has non-empty body constraints.
pub(super) fn has_any_constraints(vc: &trust_mc_core::chc::ChcVc) -> bool {
    vc.rules.iter().any(|r| !r.body.constraints.is_empty())
}

/// Default timeout (seconds) for AY-backed CHC tests.
pub(super) const Z3_TEST_TIMEOUT_SECS: u64 = 5;

/// Read optional AY timeout override for slower environments.
/// A zero value retains the historical helper's immediate-timeout semantics.
pub(super) fn z3_test_timeout_secs_or(default_secs: u64) -> u64 {
    std::env::var("TRUST_MC_AY_TEST_TIMEOUT_SECS")
        .or_else(|_| std::env::var("TRUST_MC_Z3_TEST_TIMEOUT_SECS"))
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default_secs)
}

pub(super) struct Z3RunOutput {
    pub verdict: String,
    pub stdout: String,
    pub stderr: String,
    pub status_success: bool,
}

fn ay_adaptive_config_with_timeout(timeout_secs: u64) -> ay_chc::AdaptiveConfig {
    let mut config =
        ay_chc::AdaptiveConfig::with_budget(std::time::Duration::from_secs(timeout_secs), false);
    // Use the AdaptivePortfolio route used by trust-mc's CHC integrations, but
    // apply a conservative test-only gate rather than claiming exact config
    // parity: strict_proofs is true here even though the separate
    // integration_ay_runner test helper retains AdaptiveConfig's false default.
    // Any trust-proof fallback therefore degrades to Unknown in this corpus.
    config.strict_proofs = true;
    config
}

fn ay_executor_with_timeout(timeout_secs: u64) -> ay_dpll::Executor {
    let mut executor = ay_dpll::Executor::new();
    executor.set_timeout(Some(std::time::Duration::from_secs(timeout_secs)));
    executor
}

fn spawn_ay_interrupt_timer(
    timeout: std::time::Duration,
    interrupt: std::sync::Arc<std::sync::atomic::AtomicBool>,
) -> (std::sync::mpsc::Sender<()>, std::thread::JoinHandle<()>) {
    let (cancel_tx, cancel_rx) = std::sync::mpsc::channel();
    let timer = std::thread::spawn(move || {
        if matches!(
            cancel_rx.recv_timeout(timeout),
            Err(std::sync::mpsc::RecvTimeoutError::Timeout)
        ) {
            interrupt.store(true, std::sync::atomic::Ordering::Relaxed);
        }
    });
    (cancel_tx, timer)
}

/// Execute AY with SMT-LIB2 input and capture verdict plus full stdout/stderr.
pub(super) fn run_z3_on_smt2_capture_output_with_timeout(
    smt: &str,
    timeout_secs: u64,
) -> Result<Z3RunOutput, String> {
    if smt.contains("(query ") || smt.contains("(rule ") || smt.contains("(declare-rel ") {
        // AdaptiveConfig defines a zero budget as unlimited. Preserve this
        // helper's historical immediate-timeout contract explicitly.
        if timeout_secs == 0 {
            return Ok(ay_run_output("unknown", ""));
        }
        let problem = match ay_chc::ChcParser::parse(smt) {
            Ok(problem) => problem,
            Err(err) => {
                return Ok(ay_run_output("error", &format!("AY CHC parse failed: {err}")));
            }
        };
        return match ay_chc::AdaptivePortfolio::new(
            problem,
            ay_adaptive_config_with_timeout(timeout_secs),
        )
        .solve()
        {
            ay_chc::VerifiedChcResult::Safe(_) => Ok(ay_run_output("unsat", "")),
            ay_chc::VerifiedChcResult::Unsafe(_) => Ok(ay_run_output("sat", "")),
            ay_chc::VerifiedChcResult::Unknown(_) => Ok(ay_run_output("unknown", "")),
            _ => Ok(ay_run_output("unknown", "")),
        };
    }

    let commands = ay_frontend::parse(smt).map_err(|err| format!("AY parse failed: {err}"))?;
    let mut executor = ay_executor_with_timeout(timeout_secs);
    // `Executor::set_timeout` is a per-check budget and AY deliberately extends
    // quantified deadlines to keep deterministic instantiation work load-stable.
    // Preserve the pre-AY helper's overall wall-clock deadline with an
    // independent, cancelable cooperative interrupt timer. AY polls this flag
    // throughout its supported solve paths; an outer process watchdog remains
    // the backstop for any uncooperative code. Capturing the Result before `?`
    // guarantees the timer is canceled and joined on every normal return,
    // including errors.
    let interrupt = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    executor.set_interrupt(std::sync::Arc::clone(&interrupt));
    let (cancel_tx, timer) = spawn_ay_interrupt_timer(
        std::time::Duration::from_secs(timeout_secs),
        std::sync::Arc::clone(&interrupt),
    );
    let outputs = executor.execute_all(&commands);
    let _ = cancel_tx.send(());
    timer.join().expect("AY interrupt timer thread should not panic");
    // Read only after joining: if completion races the deadline, the timer's
    // final decision is visible and the boundary case fails closed.
    let timed_out = interrupt.load(std::sync::atomic::Ordering::Relaxed);
    if timed_out {
        return Ok(ay_run_output("unknown", ""));
    }
    let outputs = outputs.map_err(|err| format!("AY execution failed: {err}"))?;
    let verdict = outputs
        .iter()
        .find_map(|output| {
            let verdict = output.trim();
            matches!(verdict, "sat" | "unsat" | "unknown").then(|| verdict.to_string())
        })
        .unwrap_or_default();
    Ok(Z3RunOutput {
        verdict,
        stdout: outputs.join("\n"),
        stderr: String::new(),
        status_success: true,
    })
}

fn ay_run_output(verdict: &str, stderr: &str) -> Z3RunOutput {
    Z3RunOutput {
        verdict: verdict.to_string(),
        stdout: verdict.to_string(),
        stderr: stderr.to_string(),
        status_success: stderr.is_empty(),
    }
}

/// Execute AY with SMT-LIB2 input and return the first result line.
pub(super) fn run_z3_on_smt2_with_timeout(smt: &str, timeout_secs: u64) -> Result<String, String> {
    let output = run_z3_on_smt2_capture_output_with_timeout(smt, timeout_secs)?;
    if matches!(output.verdict.as_str(), "sat" | "unsat" | "unknown") && output.status_success {
        return Ok(output.verdict);
    }
    if !output.status_success {
        return Err(format!("AY failed. stderr: {}. stdout: {}", output.stderr, output.stdout));
    }
    if output.verdict.is_empty() {
        return Err(format!("AY produced empty output. stderr: {}", output.stderr));
    }
    Ok(output.verdict)
}

/// Assert that AY returns the expected result (custom timeout).
pub(super) fn assert_z3_result_with_timeout(smt: &str, expected: &str, timeout_secs: u64) {
    match run_z3_on_smt2_with_timeout(smt, timeout_secs) {
        Ok(result) => {
            assert_eq!(
                result, expected,
                "Expected AY result '{expected}', got '{result}'. SMT:\n{smt}"
            );
        }
        Err(e) => panic!("AY execution failed: {e}. SMT:\n{smt}"),
    }
}

/// Assert that AY returns the expected result (default timeout).
pub(super) fn assert_z3_result(smt: &str, expected: &str) {
    assert_z3_result_with_timeout(smt, expected, z3_test_timeout_secs_or(Z3_TEST_TIMEOUT_SECS));
}

#[test]
fn ay_test_dpll_timeout_configuration_is_preserved() {
    let executor = ay_executor_with_timeout(11);
    assert_eq!(executor.timeout(), Some(std::time::Duration::from_secs(11)));
}

/// Migration regression control: raw `PdrConfig::{default,production}` at the
/// canonical AY pin returns Unknown for this baseline, while the
/// AdaptivePortfolio route used by trust-mc returns a verified Safe result.
/// Keep the assertion on the shared harness so a future raw-PDR reroute cannot
/// silently recur.
#[test]
fn adaptive_chc_route_regression_control() {
    let smt = r#"
        (set-logic HORN)
        (declare-rel inv (Int))
        (declare-rel done (Int))
        (declare-rel error ())
        (declare-var x Int)
        (declare-var x_next Int)
        (rule (=> (= x 0) (inv x)))
        (rule (=> (and (inv x) (< x 10) (= x_next (+ x 1))) (inv x_next)))
        (rule (=> (and (inv x) (>= x 10)) (done x)))
        (rule (=> (and (done x) (not (= x 10))) error))
        (query error)
    "#;
    let output = run_z3_on_smt2_capture_output_with_timeout(smt, 30)
        .expect("adaptive CHC route should execute");
    assert_eq!(output.verdict, "unsat", "adaptive CHC route must return verified Safe");
}

#[test]
fn ay_test_interrupt_timer_fire_and_cancel_paths() {
    let fired = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let (cancel_tx, timer) =
        spawn_ay_interrupt_timer(std::time::Duration::ZERO, std::sync::Arc::clone(&fired));
    timer.join().expect("zero-duration AY interrupt timer should not panic");
    assert!(fired.load(std::sync::atomic::Ordering::Relaxed));
    drop(cancel_tx);

    let canceled = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let (cancel_tx, timer) = spawn_ay_interrupt_timer(
        std::time::Duration::from_secs(60),
        std::sync::Arc::clone(&canceled),
    );
    cancel_tx.send(()).expect("cancel AY interrupt timer");
    timer.join().expect("canceled AY interrupt timer should not panic");
    assert!(!canceled.load(std::sync::atomic::Ordering::Relaxed));
}

#[test]
fn ay_test_pretriggered_interrupt_is_enforced_by_dpll() {
    let commands = ay_frontend::parse("(set-logic QF_UF)\n(check-sat)\n")
        .expect("parse pretriggered-interrupt fixture");
    let mut executor = ay_dpll::Executor::new();
    executor.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(true)));
    let outputs = executor.execute_all(&commands).expect("execute pretriggered-interrupt fixture");
    assert!(
        outputs.iter().any(|output| output.trim() == "unknown"),
        "pretriggered AY interrupt should return unknown, got {outputs:?}"
    );
}

#[test]
fn ay_test_zero_timeout_is_enforced_by_dpll() {
    let output = run_z3_on_smt2_capture_output_with_timeout("(set-logic QF_UF)\n(check-sat)\n", 0)
        .expect("zero-timeout DPLL execution should return an Unknown verdict");
    assert_eq!(output.verdict, "unknown");
}

#[test]
fn ay_test_zero_timeout_is_enforced_by_adaptive_chc() {
    let smt = r#"
        (set-logic HORN)
        (declare-rel inv (Int))
        (declare-rel error ())
        (declare-var x Int)
        (rule (inv 0))
        (rule (=> (and (inv x) (< x 10)) (inv (+ x 1))))
        (rule (=> (and (inv x) (< x 0)) error))
        (query error)
    "#;
    let output = run_z3_on_smt2_capture_output_with_timeout(smt, 0)
        .expect("zero-timeout adaptive CHC execution should return an Unknown verdict");
    assert_eq!(output.verdict, "unknown");
}

/// Run a test closure on a thread with a 32 MB stack.
///
/// The default 8 MB test-thread stack is insufficient for tests that do full
/// `mir_to_chc` translation of complex sources with nested while-loops and
/// method calls (e.g., the LRA `LinearExpr` fixture). The CHC inline walker
/// recurses through callee bodies, consuming O(depth × frame_size) stack.
///
/// Part of #4145: stack overflow in bootstrap_lra test family.
pub(super) fn join_with_timeout<T>(handle: std::thread::JoinHandle<T>, label: &str) -> T {
    const TIMEOUT: std::time::Duration = std::time::Duration::from_secs(120);
    let start = std::time::Instant::now();
    loop {
        if handle.is_finished() {
            break;
        }
        if start.elapsed() > TIMEOUT {
            panic!("{label}: timed out after {}s (#4282)", TIMEOUT.as_secs());
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
    match handle.join() {
        Ok(val) => val,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

pub(super) fn run_with_large_stack<F: FnOnce() + Send + 'static>(f: F) {
    const STACK_SIZE: usize = 32 * 1024 * 1024; // 32 MB
    let handle = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(f)
        .expect("spawn large-stack thread");
    join_with_timeout(handle, "run_with_large_stack");
}

/// Test adapters for the Wave-5 typed projection entries.
///
/// `ChcCtx::datatype_field_select` / `datatype_field_update` take and return
/// [`crate::codegen_ay::provenance::Val`]: a field of a value is itself a value,
/// and nothing in either function touches memory. The tests below build literal
/// datatype terms, so the tag is justified by the fixture itself; these wrappers
/// only keep the assertions expression-shaped.
pub(super) fn select_field_val(
    container: &Expr,
    field_idx: usize,
    cons_idx: Option<usize>,
) -> Option<Expr> {
    use crate::codegen_ay::provenance::Val;
    ChcCtx::datatype_field_select(&Val::of_value(container.clone()), field_idx, cons_idx)
        .map(Val::into_expr)
}

/// Write-side counterpart of [`select_field_val`].
pub(super) fn update_field_val(
    container: &Expr,
    field_idx: usize,
    cons_idx: Option<usize>,
    new_val: Expr,
) -> Option<Expr> {
    use crate::codegen_ay::provenance::Val;
    ChcCtx::datatype_field_update(
        &Val::of_value(container.clone()),
        field_idx,
        cons_idx,
        Val::of_value(new_val),
    )
    .map(Val::into_expr)
}
