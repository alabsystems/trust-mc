// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-backed bootstrap LRA regression tests for nested array-backed `Rational` stores.
//!
//! Part of #3814, #3766, #134: keep the Tier 3 LRA `LinearExpr` packet off the
//! flattened translation-drop/self-loop fallback lanes.

use super::super::call::inline_alias_writeback::pre_resolve_arg_target_locals;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_fn_inline::CallDispatchFnInline;
use super::super::inline_body::translate_inline_body;
use super::super::inline_field_map::populate_inline_self_field_hints;
use super::common::*;
use rustc_public::mir::{
    Body, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, TyKind};

const BOOTSTRAP_LRA_LINEAR_EXPR_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct Rational {
        num: i64,
        den: i64,
    }

    impl Rational {
        fn zero() -> Self {
            Self { num: 0, den: 1 }
        }

        fn one() -> Self {
            Self { num: 1, den: 1 }
        }

        fn from_i64(v: i64) -> Self {
            Self { num: v, den: 1 }
        }

        fn is_zero(&self) -> bool {
            self.num == 0
        }

        fn negate(&self) -> Self {
            Self { num: -self.num, den: self.den }
        }

        fn add(&self, other: &Self) -> Self {
            let num = self.num * other.den + other.num * self.den;
            let den = self.den * other.den;
            Self::reduce(num, den)
        }

        fn mul(&self, other: &Self) -> Self {
            let num = self.num * other.num;
            let den = self.den * other.den;
            Self::reduce(num, den)
        }

        fn reduce(num: i64, den: i64) -> Self {
            if num == 0 {
                return Self { num: 0, den: 1 };
            }
            let g = gcd(num.unsigned_abs(), den.unsigned_abs()) as i64;
            let sign = if den < 0 { -1 } else { 1 };
            Self { num: sign * num / g, den: sign * den / g }
        }
    }

    fn gcd(mut a: u64, mut b: u64) -> u64 {
        while b != 0 {
            let t = b;
            b = a % b;
            a = t;
        }
        if a == 0 { 1 } else { a }
    }

    #[derive(Clone, Copy)]
    pub struct LinearExpr {
        vars: [u32; 4],
        coeffs: [Rational; 4],
        len: usize,
        constant: Rational,
    }

    impl LinearExpr {
        fn zero() -> Self {
            Self {
                vars: [0; 4],
                coeffs: [Rational::zero(); 4],
                len: 0,
                constant: Rational::zero(),
            }
        }

        fn find(&self, var: u32) -> Option<usize> {
            let mut i = 0;
            while i < self.len {
                if self.vars[i] == var {
                    return Some(i);
                }
                i += 1;
            }
            None
        }

        fn add_term(&mut self, var: u32, coeff: Rational) {
            if coeff.is_zero() {
                return;
            }
            if let Some(pos) = self.find(var) {
                let new_coeff = self.coeffs[pos].add(&coeff);
                if new_coeff.is_zero() {
                    let mut j = pos;
                    while j + 1 < self.len {
                        self.vars[j] = self.vars[j + 1];
                        self.coeffs[j] = self.coeffs[j + 1];
                        j += 1;
                    }
                    self.len -= 1;
                } else {
                    self.coeffs[pos] = new_coeff;
                }
            } else if self.len < 4 {
                self.vars[self.len] = var;
                self.coeffs[self.len] = coeff;
                self.len += 1;
            }
        }

        fn scale(&mut self, factor: &Rational) {
            let mut i = 0;
            while i < self.len {
                self.coeffs[i] = self.coeffs[i].mul(factor);
                i += 1;
            }
            self.constant = self.constant.mul(factor);

            let mut write = 0;
            let mut read = 0;
            while read < self.len {
                if !self.coeffs[read].is_zero() {
                    self.vars[write] = self.vars[read];
                    self.coeffs[write] = self.coeffs[read];
                    write += 1;
                }
                read += 1;
            }
            self.len = write;
        }

        fn negate(&mut self) {
            let mut i = 0;
            while i < self.len {
                self.coeffs[i] = self.coeffs[i].negate();
                i += 1;
            }
            self.constant = self.constant.negate();
        }

        fn coeff_for(&self, var: u32) -> Option<Rational> {
            if let Some(pos) = self.find(var) { Some(self.coeffs[pos]) } else { None }
        }
    }

    pub fn probe_lra_add_term_zero_is_noop(seed: i64) -> i64 {
        let mut expr = LinearExpr::zero();
        let coeff = Rational::from_i64(seed);
        expr.add_term(0, coeff);

        let coeff_before = expr.coeff_for(0).unwrap_or(Rational::zero());
        expr.add_term(0, Rational::zero());
        let coeff_after = expr.coeff_for(0).unwrap_or(Rational::zero());

        coeff_before.num
            + coeff_before.den
            + coeff_after.num
            + coeff_after.den
            + expr.constant.den
    }

    pub fn probe_lra_scale_by_one(seed: i64) -> i64 {
        let mut expr = LinearExpr::zero();
        let coeff = Rational::from_i64(seed);
        expr.add_term(0, coeff);
        expr.constant = Rational::from_i64(42);

        let coeff_before = expr.coeff_for(0).unwrap_or(Rational::zero());
        expr.scale(&Rational::one());
        let coeff_after = expr.coeff_for(0).unwrap_or(Rational::zero());

        coeff_before.num
            + coeff_before.den
            + coeff_after.num
            + coeff_after.den
            + expr.constant.num
            + expr.constant.den
    }

    pub fn probe_lra_double_negation(seed: i64) -> i64 {
        let mut expr = LinearExpr::zero();
        expr.add_term(0, Rational::from_i64(seed));
        expr.constant = Rational::from_i64(17);

        let coeff_before = expr.coeff_for(0).unwrap_or(Rational::zero());
        expr.negate();
        expr.negate();
        let coeff_after = expr.coeff_for(0).unwrap_or(Rational::zero());

        coeff_before.num
            + coeff_before.den
            + coeff_after.num
            + coeff_after.den
            + expr.constant.num
            + expr.constant.den
    }

    pub fn probe_lra_coeff_field_index(expr: LinearExpr, idx: usize) -> i64 {
        let lane = if expr.len == 0 { 0 } else { idx % expr.len };
        let coeff = expr.coeffs[lane];
        coeff.num + coeff.den
    }

    pub fn probe_lra_coeff_field_index_ref(expr: &LinearExpr, idx: usize) -> i64 {
        let lane = if expr.len == 0 { 0 } else { idx % expr.len };
        let coeff = expr.coeffs[lane];
        coeff.num + coeff.den
    }

    pub fn probe_lra_rational_array_index(coeffs: [Rational; 4], idx: usize) -> i64 {
        let lane = idx % 4;
        let coeff = coeffs[lane];
        coeff.num + coeff.den
    }
"#;

const RATIONAL_GUARD_PROBE_FN_NAMES: [&str; 2] =
    ["probe_lra_add_term_zero_is_noop", "probe_lra_scale_by_one"];

/// Minimal source for lightweight field-index tests that only need struct
/// definitions and simple probe functions. Avoids compiling the complex
/// while-loop method bodies (add_term, scale, negate, find) which slow
/// rustc MIR generation significantly.
const BOOTSTRAP_LRA_INDEX_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy, PartialEq, Eq)]
    pub struct Rational {
        num: i64,
        den: i64,
    }

    pub struct LinearExpr {
        coeffs: [Rational; 4],
        vars: [u32; 4],
        constant: Rational,
        len: usize,
    }

    pub fn probe_lra_coeff_field_index(expr: LinearExpr, idx: usize) -> i64 {
        let lane = if expr.len == 0 { 0 } else { idx % expr.len };
        let coeff = expr.coeffs[lane];
        coeff.num + coeff.den
    }

    pub fn probe_lra_coeff_field_index_ref(expr: &LinearExpr, idx: usize) -> i64 {
        let lane = if expr.len == 0 { 0 } else { idx % expr.len };
        let coeff = expr.coeffs[lane];
        coeff.num + coeff.den
    }

    pub fn probe_lra_rational_array_index(coeffs: [Rational; 4], idx: usize) -> i64 {
        let lane = idx % 4;
        let coeff = coeffs[lane];
        coeff.num + coeff.den
    }
"#;

fn reset_bootstrap_lra_metadata() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_constant_translation_drop_count();
    let _ = crate::codegen_ay::take_unsupported_field_projection_count();
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
    let _ = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
}

fn assert_no_bootstrap_lra_translation_drop_metadata(fn_name: &str) {
    let translation_drops = take_translation_drop_by_fn();
    let drop_fallback_reasons = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let place_drop_count = crate::codegen_ay::take_place_translation_drop_count();
    let constant_drop_count = crate::codegen_ay::take_constant_translation_drop_count();
    let field_projection_drop_count = crate::codegen_ay::take_unsupported_field_projection_count();
    let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
    assert_eq!(
        drop_count, 0,
        "{fn_name} should not record translation drops for bootstrap LRA index-bearing reads, drops={translation_drops:?}, sound_fallback_reasons={drop_fallback_reasons:?}, sites={translation_sites:?}, place_count={place_drop_count}, constant_count={constant_drop_count}, field_projection_count={field_projection_drop_count}"
    );
    assert!(
        !translation_sites.contains_key(fn_name),
        "{fn_name} should not record translation-drop site reasons, map={translation_sites:?}"
    );
    assert!(
        !drop_fallback_reasons.contains_key(fn_name),
        "{fn_name} should not record categorized sound-fallback reasons, map={drop_fallback_reasons:?}"
    );
    assert_eq!(
        place_drop_count, 0,
        "{fn_name} should not increment place_translation_drop, count={place_drop_count}"
    );
    assert_eq!(
        constant_drop_count, 0,
        "{fn_name} should not increment const_translation_drop, count={constant_drop_count}"
    );
    assert_eq!(
        field_projection_drop_count, 0,
        "{fn_name} should not increment unsupported_field_projection, count={field_projection_drop_count}"
    );
}

fn inline_budget_note(tcx: TyCtxt<'_>, suffix: &str) -> String {
    let instance = find_instance_by_suffix(tcx, suffix);
    let body = instance.body().expect("function body");
    let effective = crate::codegen_ay::shared::count_effective_blocks(&body);
    let limit = super::super::inline_budget::chc_inline_effective_block_limit(&body, effective);
    format!("{suffix}:effective={effective},limit={limit}")
}

fn with_lra_method_call(
    probe_suffix: &str,
    callee_suffix: &str,
    assertions: impl FnOnce(
        TyCtxt<'_>,
        &mut ChcCtx<'_, '_>,
        &Operand,
        &[Operand],
        &Place,
        usize,
        &RelationApp,
        &[Expr],
        &HashSet<usize>,
        usize,
        &str,
    ) + Send,
) {
    with_test_ay_ctx_for_source(BOOTSTRAP_LRA_LINEAR_EXPR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, probe_suffix);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, probe_suffix, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, func, args, destination, target, callee_path) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                if let TerminatorKind::Call {
                    func, args, destination, target: Some(target), ..
                } = &block.terminator.kind
                {
                    let path = chc_ctx
                        .resolve_callee_path(func)
                        .or_else(|| chc_ctx.resolve_fn_def_name(func))?;
                    path.ends_with(callee_suffix).then(|| {
                        (bb_idx, func.clone(), args.clone(), destination.clone(), *target, path)
                    })
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                panic!("expected {callee_suffix} call terminator in {probe_suffix}")
            });

        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();

        assertions(
            ctx.tcx,
            &mut chc_ctx,
            &func,
            &args,
            &destination,
            target,
            &from_app,
            &stmt_constraints,
            &modified_locals,
            bb_idx,
            &callee_path,
        );
    });
}

fn places_from_operand(op: &Operand) -> Vec<&Place> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => vec![place],
        Operand::Constant(_) => vec![],
    }
}

fn place_is_direct_field_index(
    place: &Place,
    local_idx: usize,
    require_leading_deref: bool,
) -> bool {
    if place.local != local_idx {
        return false;
    }

    let projections: &[ProjectionElem] = if require_leading_deref {
        match place.projection.first() {
            Some(ProjectionElem::Deref) => &place.projection[1..],
            _ => return false,
        }
    } else {
        if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            return false;
        }
        &place.projection
    };

    let mut seen_field = false;
    let mut seen_index = false;
    for proj in projections {
        match proj {
            ProjectionElem::Field(_, _) if !seen_field && !seen_index => seen_field = true,
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                if seen_field && !seen_index =>
            {
                seen_index = true;
            }
            _ => return false,
        }
    }

    seen_field && seen_index
}

fn find_direct_field_index_place(
    body: &Body,
    local_idx: usize,
    require_leading_deref: bool,
) -> Option<Place> {
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(dest, rvalue) = &stmt.kind {
                if place_is_direct_field_index(dest, local_idx, require_leading_deref) {
                    return Some(dest.clone());
                }

                let source_places: Vec<&Place> = match rvalue {
                    Rvalue::Use(op) => places_from_operand(op),
                    Rvalue::Ref(_, _, place)
                    | Rvalue::AddressOf(_, place)
                    | Rvalue::CopyForDeref(place)
                    | Rvalue::Discriminant(place)
                    | Rvalue::Len(place) => vec![place],
                    Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                        let mut places = places_from_operand(lhs);
                        places.extend(places_from_operand(rhs));
                        places
                    }
                    Rvalue::UnaryOp(_, op) | Rvalue::Cast(_, op, _) | Rvalue::Repeat(op, _) => {
                        places_from_operand(op)
                    }
                    _ => vec![],
                };

                for place in source_places {
                    if place_is_direct_field_index(place, local_idx, require_leading_deref) {
                        return Some(place.clone());
                    }
                }
            }
        }
    }

    None
}

fn place_is_direct_index_only(
    place: &Place,
    local_idx: usize,
    require_leading_deref: bool,
) -> bool {
    if place.local != local_idx {
        return false;
    }

    let projections: &[ProjectionElem] = if require_leading_deref {
        match place.projection.first() {
            Some(ProjectionElem::Deref) => &place.projection[1..],
            _ => return false,
        }
    } else {
        if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            return false;
        }
        &place.projection
    };

    let mut seen_index = false;
    for proj in projections {
        match proj {
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } if !seen_index => {
                seen_index = true;
            }
            _ => return false,
        }
    }

    seen_index
}

fn find_direct_index_only_place(
    body: &Body,
    local_idx: usize,
    require_leading_deref: bool,
) -> Option<Place> {
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(dest, rvalue) = &stmt.kind {
                if place_is_direct_index_only(dest, local_idx, require_leading_deref) {
                    return Some(dest.clone());
                }

                let source_places: Vec<&Place> = match rvalue {
                    Rvalue::Use(op) => places_from_operand(op),
                    Rvalue::Ref(_, _, place)
                    | Rvalue::AddressOf(_, place)
                    | Rvalue::CopyForDeref(place)
                    | Rvalue::Discriminant(place)
                    | Rvalue::Len(place) => vec![place],
                    Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                        let mut places = places_from_operand(lhs);
                        places.extend(places_from_operand(rhs));
                        places
                    }
                    Rvalue::UnaryOp(_, op) | Rvalue::Cast(_, op, _) | Rvalue::Repeat(op, _) => {
                        places_from_operand(op)
                    }
                    _ => vec![],
                };

                for place in source_places {
                    if place_is_direct_index_only(place, local_idx, require_leading_deref) {
                        return Some(place.clone());
                    }
                }
            }
        }
    }

    None
}

fn assert_bootstrap_lra_vc_shape(
    vc: &trust_mc_core::chc::ChcVc,
    fn_name: &str,
    body: &rustc_public::mir::Body,
) {
    assert_vc_structure(vc, fn_name, body.blocks.len());
    assert_relation_has_arg_sort(
        vc,
        fn_name,
        ay_bindings::Sort::is_array,
        "Array (LinearExpr nested Rational coeffs backing arrays)",
    );
    assert_relation_has_arg_sort(vc, fn_name, |sort| sort.bitvec_width() == Some(64), "bv64");
    assert_has_nontrivial_transition_constraints(vc, fn_name);
    assert_rule_contains_expr_kind(
        vc,
        fn_name,
        |expr| matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array()),
        "Select(Array, idx)",
    );
    assert_rule_contains_expr_kind(
        vc,
        fn_name,
        |expr| matches!(expr.value(), ExprValue::Store { array, .. } if array.sort().is_array()),
        "Store(Array, idx, val)",
    );
}

#[test]
fn test_bootstrap_lra_linear_expr_packet_has_clean_metadata() {
    // Part of #4282: keep one representative full packet translation on the
    // add_term path. The scale/negate paths are covered below by targeted
    // fn_inline checks without paying for the full loop-heavy body walk.
    run_with_large_stack(|| {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        reset_bootstrap_lra_metadata();

        let fn_name = "probe_lra_add_term_zero_is_noop";
        with_test_ay_ctx_for_source(BOOTSTRAP_LRA_LINEAR_EXPR_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc_skip_tic(ctx.tcx, &body, fn_name, ChcConfig::default());
            assert_bootstrap_lra_vc_shape(&vc, fn_name, &body);
        });

        let fallback_counts = get_chc_fallback_counts();
        let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
        assert!(
            fallback_count <= 4,
            "{fn_name} fallback count should not exceed baseline ceiling (4): \
             got={fallback_count}, map={fallback_counts:?}"
        );
        let translation_drops = take_translation_drop_by_fn();
        let translation_drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
        assert!(
            translation_drop_count <= 40,
            "{fn_name} translation drops should not exceed baseline 40: \
             got={translation_drop_count}, map={translation_drops:?}"
        );
    });
}

#[test]
fn test_bootstrap_lra_local_rational_probes_do_not_route_to_bigrational_or_real_state() {
    // Part of #4282: these guards only need the declared state surface, not a
    // full rule-generation walk. Checking the declared relations keeps coverage
    // on the Rational-vs-BigRational sort boundary without the scale-path cost.
    run_with_large_stack(|| {
        for fn_name in RATIONAL_GUARD_PROBE_FN_NAMES {
            with_test_ay_ctx_for_source(BOOTSTRAP_LRA_LINEAR_EXPR_SOURCE, |ctx| {
                let instance = find_instance_by_suffix(ctx.tcx, fn_name);
                let body = instance.body().expect("function body");
                let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
                let detected = collect_detected_bigrational_stubs(&chc_ctx, &body);
                assert!(
                    detected.is_empty(),
                    "{fn_name} should keep local Rational methods off the BigRational stub lane: \
                     {detected:?}"
                );
                chc_ctx.declare_block_relations();
                assert!(
                    chc_ctx.state_var_mgr.state_vars.iter().all(|(_, sort)| !sort.is_real()),
                    "{fn_name} should not declare Real-sorted state vars for local Rational methods: {:?}",
                    chc_ctx
                        .state_var_mgr
                        .state_vars
                        .iter()
                        .map(|(name, sort)| (name.to_string(), sort.clone()))
                        .collect::<Vec<_>>()
                );
                assert!(
                    chc_ctx
                        .vc
                        .relations
                        .iter()
                        .all(|rel| rel.arg_sorts.iter().all(|sort| !sort.is_real())),
                    "{fn_name} should not declare Real-sorted relation args for local Rational \
                     methods: {:?}",
                    chc_ctx
                        .vc
                        .relations
                        .iter()
                        .map(|rel| rel.arg_sorts.clone())
                        .collect::<Vec<_>>()
                );
            });
        }
    });
}

#[test]
fn test_bootstrap_lra_coeff_field_index_unflattens_selected_rational() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_bootstrap_lra_metadata();

    with_test_ay_ctx_for_source(BOOTSTRAP_LRA_INDEX_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_lra_coeff_field_index");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_lra_coeff_field_index", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let expr_local = 1usize;
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&expr_local),
            "test precondition failed: LinearExpr param local {expr_local} was not flattened"
        );

        let place = find_direct_field_index_place(&body, expr_local, false)
            .expect("probe_lra_coeff_field_index should contain a direct Field+Index read");
        let expr = chc_ctx
            .translate_place_with_modified(&place, &HashSet::new())
            .expect("direct Field+Index read on flattened LinearExpr should translate");

        assert!(
            constraint_tree_contains(
                &expr,
                &|e| matches!(e.value(), ExprValue::Select { array, .. } if array.sort().is_array())
            ),
            "selected coeff should keep the underlying array select in the translated expression"
        );
        assert!(
            expr.sort().is_datatype(),
            "selected coeff should be rebuilt as Rational datatype, got {:?}",
            expr.sort()
        );
    });

    assert_no_bootstrap_lra_translation_drop_metadata("probe_lra_coeff_field_index");
    reset_bootstrap_lra_metadata();
}

#[test]
fn test_bootstrap_lra_deref_field_index_unflattens_selected_rational() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_bootstrap_lra_metadata();

    with_test_ay_ctx_for_source(BOOTSTRAP_LRA_INDEX_PROBE_SOURCE, |ctx| {
        let fn_name = "probe_lra_coeff_field_index_ref";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let expr_ref_local = 1usize;
        let place = find_direct_field_index_place(&body, expr_ref_local, true)
            .expect("probe_lra_coeff_field_index_ref should contain a Deref+Field+Index read");
        let expr = chc_ctx
            .translate_place_with_deref(&place, &HashSet::new())
            .expect("Deref+Field+Index read on &LinearExpr should translate");

        assert!(
            constraint_tree_contains(
                &expr,
                &|e| matches!(e.value(), ExprValue::Select { array, .. } if array.sort().is_array())
            ),
            "Deref+Field+Index read should keep the underlying array select in the translated expression"
        );
        assert!(
            expr.sort().is_datatype(),
            "selected coeff through &LinearExpr should rebuild a Rational datatype, got {:?}",
            expr.sort()
        );
    });

    assert_no_bootstrap_lra_translation_drop_metadata("probe_lra_coeff_field_index_ref");
    reset_bootstrap_lra_metadata();
}

#[test]
fn test_bootstrap_lra_pure_index_unflattens_selected_rational() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_bootstrap_lra_metadata();

    with_test_ay_ctx_for_source(BOOTSTRAP_LRA_INDEX_PROBE_SOURCE, |ctx| {
        let fn_name = "probe_lra_rational_array_index";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let coeffs_local = 1usize;
        assert!(
            !chc_ctx.flatten.flattened_tuple_locals.contains(&coeffs_local),
            "test precondition failed: Rational array param local {coeffs_local} should stay non-flattened"
        );

        let place = find_direct_index_only_place(&body, coeffs_local, false)
            .expect("probe_lra_rational_array_index should contain a direct Index read");
        let expr = chc_ctx
            .translate_place_with_modified(&place, &HashSet::new())
            .expect("direct Index read on Rational array should translate");

        assert!(
            constraint_tree_contains(
                &expr,
                &|e| matches!(e.value(), ExprValue::Select { array, .. } if array.sort().is_array())
            ),
            "pure Index read should keep the underlying array select in the translated expression"
        );
        assert!(
            expr.sort().is_datatype(),
            "selected Rational array element should rebuild a datatype, got {:?}",
            expr.sort()
        );
    });

    // #3830 baseline: place_translation_drop <= 8 (from global CHC encoding
    // of the full probe body, not from the targeted index read above).
    // The index read itself translates correctly (asserted above), but the
    // surrounding while-loop and nested method calls in the probe body still
    // produce fallbacks. Reduce this threshold as encoding improves.
    {
        let place_drop_count = crate::codegen_ay::take_place_translation_drop_count();
        assert!(
            place_drop_count <= 8,
            "probe_lra_rational_array_index: place_translation_drop should not exceed baseline 8, got={place_drop_count}"
        );
    }
    reset_bootstrap_lra_metadata();
}

/// Verify that the CHC inline budget and hint infrastructure are correctly
/// wired for an LRA method call. With bounded loop replay (#3853), the
/// walker can now handle single-header while-loops in inlined method bodies.
/// This test validates:
///   1. Budget computation uses CHC-specific limits (not shared 16-block cap)
///   2. Flattened field hints populate when arg[0] is a flattened struct
///   3. Arguments are translatable for inline dispatch
///   4. translate_inline_body succeeds for loop-bearing bodies within budget
///
/// Part of #3830: hint mechanism + budget fix validation.
/// Part of #3853: bounded loop replay enables precise inline of loop bodies.
fn assert_lra_method_inline_infrastructure(
    probe_suffix: &str,
    callee_suffix: &str,
    budget_suffixes: &[&str],
    expect_within_budget: bool,
) {
    with_lra_method_call(
        probe_suffix,
        callee_suffix,
        |tcx,
         chc_ctx,
         func,
         args,
         destination,
         target,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx,
         callee_path| {
            let budget_notes: Vec<_> =
                budget_suffixes.iter().map(|suffix| inline_budget_note(tcx, suffix)).collect();
            let func_ty = func.ty(chc_ctx.body.locals()).expect("call callee type");
            let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func_ty.kind() else {
                panic!("expected FnDef for {callee_path}, got {func_ty:?}");
            };
            let instance =
                rustc_public::mir::mono::Instance::resolve(def, &substs).expect("callee instance");
            let inline_body = instance.body().expect("callee body");
            let effective = crate::codegen_ay::shared::count_effective_blocks(&inline_body);
            let limit = super::super::inline_budget::chc_inline_effective_block_limit(
                &inline_body,
                effective,
            );
            // Verify budget expectation matches reality.
            assert_eq!(
                effective <= limit,
                expect_within_budget,
                "{callee_path}: effective={effective}, limit={limit}, expected_within={expect_within_budget}, budgets={budget_notes:?}"
            );
            let translated_params: Vec<_> = args
                .iter()
                .map(|arg| chc_ctx.resolve_ref_or_const_referent(arg, modified_locals))
                .collect();
            assert!(
                translated_params.iter().all(Option::is_some),
                "{callee_path} should have translatable inline arguments, params={translated_params:?}, budgets={budget_notes:?}"
            );
            if !expect_within_budget {
                return;
            }
            let params: Vec<_> = translated_params
                .into_iter()
                .collect::<Option<Vec<_>>>()
                .expect("translatable params asserted above");
            let target_opt = Some(target);
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target: &target_opt,
                from_app,
                stmt_constraints,
                modified_locals,
                callee_path: None,
            };
            chc_ctx.mark_inline_field_reads(&inline_body, &params, bb_idx);
            // Part of #3830: verify flattened field hints populate correctly.
            populate_inline_self_field_hints(chc_ctx, &dcx);
            let hints_populated = chc_ctx.inline_self_field_hints.is_some();
            let inline_result = translate_inline_body(
                chc_ctx,
                &inline_body,
                &params,
                bb_idx,
                &std::collections::HashMap::new(),
                Some(instance),
                0,
            );
            chc_ctx.inline_self_field_hints = None;
            // Part of #3830: Verify hints were populated for flattened struct args.
            assert!(
                hints_populated,
                "{callee_path} should populate flattened field hints (#3830), budgets={budget_notes:?}"
            );
            // Part of #3853: with bounded loop replay, translate_inline_body
            // should succeed for single-header loop bodies within budget.
            // When it succeeds, also verify fn_inline dispatch stays precise.
            if inline_result.is_some() {
                assert!(
                    chc_ctx.try_dispatch_call_fn_inline(&dcx),
                    "{callee_path} should stay on direct fn_inline, budgets={budget_notes:?}"
                );
            }
        },
    );
}

#[test]
fn test_bootstrap_lra_add_term_call_is_claimed_by_fn_inline() {
    // Part of #4145: inline body translation on LRA source needs >8 MB stack.
    run_with_large_stack(|| {
        assert_lra_method_inline_infrastructure(
            "probe_lra_add_term_zero_is_noop",
            "LinearExpr::add_term",
            &["LinearExpr::add_term", "LinearExpr::find", "Rational::add", "Rational::is_zero"],
            false, // exceeds budget
        );
    });
}

/// Part of #3889: Inline-specific regression for the live failure surface.
/// `LinearExpr::find` should inline precisely without falling back to an
/// inferable predicate. On current HEAD, the field-map resolver in
/// `field_map_projection.rs` loses the Array sort when resolving
/// `self.vars[i]` through a `&self` reference, causing the walker to bail
/// and `find` to become `P_inf_LinearExpr::find`.
///
/// This test asserts zero inferable predicates from the `add_term` path.
/// It should FAIL until the field-map resolver is fixed to preserve Array
/// sort through Deref+Field+Index chains.
#[test]
fn test_bootstrap_lra_add_term_find_does_not_produce_inferable_predicate() {
    // Part of #4145: full mir_to_chc on loop-bearing LRA source needs >8 MB stack.
    run_with_large_stack(|| {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        reset_bootstrap_lra_metadata();
        let _ = crate::codegen_ay::take_inferable_predicate_count();
        let _ = crate::codegen_ay::take_unhandled_call_by_fn();

        with_test_ay_ctx_for_source(BOOTSTRAP_LRA_LINEAR_EXPR_SOURCE, |ctx| {
            let fn_name = "probe_lra_add_term_zero_is_noop";
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            assert_bootstrap_lra_vc_shape(&vc, fn_name, &body);

            let inferable_decls: Vec<_> = vc
                .decls
                .iter()
                .filter_map(|decl| match decl {
                    trust_mc_core::decl::Decl::Fun { name, .. } if name.starts_with("P_inf_") => {
                        Some(name.clone())
                    }
                    _ => None,
                })
                .collect();

            let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
            let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();

            assert!(
                inferable_count <= 2,
                "{fn_name}: add_term path inferable predicates should be minimal, got {inferable_count}. \
                 inferable_decls={inferable_decls:?}, unhandled={unhandled_calls:?}"
            );
        });

        reset_bootstrap_lra_metadata();
    });
}

#[test]
fn test_bootstrap_lra_scale_call_is_claimed_by_fn_inline() {
    // Part of #4145: inline body translation on LRA source needs >8 MB stack.
    run_with_large_stack(|| {
        assert_lra_method_inline_infrastructure(
            "probe_lra_scale_by_one",
            "LinearExpr::scale",
            &["LinearExpr::scale", "Rational::mul", "Rational::one"],
            true, // within budget
        );
    });
}

#[test]
fn test_bootstrap_lra_scale_call_keeps_receiver_target_resolution() {
    // Part of #4282: exercise the receiver-resolution seam directly rather
    // than translating the whole loop-bearing scale probe body.
    run_with_large_stack(|| {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        reset_bootstrap_lra_metadata();

        with_lra_method_call(
            "probe_lra_scale_by_one",
            "LinearExpr::scale",
            |_tcx,
             chc_ctx,
             func,
             args,
             destination,
             target,
             from_app,
             stmt_constraints,
             modified_locals,
             bb_idx,
             callee_path| {
                let target_opt = Some(target);
                let dcx = DispatchCallContext {
                    bb_idx,
                    func,
                    args,
                    destination,
                    target: &target_opt,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                    callee_path: None,
                };
                let pre_resolved = pre_resolve_arg_target_locals(chc_ctx, &dcx);
                let receiver_local = pre_resolved.get(&1).copied().expect(
                    "scale call receiver should resolve to a caller-side target local before inline walk",
                );
                assert!(
                    chc_ctx.flatten.flattened_tuple_locals.contains(&receiver_local),
                    "{callee_path} should resolve arg0 to the flattened LinearExpr receiver local, \
                     got local {receiver_local}, pre_resolved={pre_resolved:?}"
                );
            },
        );
        assert_no_bootstrap_lra_translation_drop_metadata("probe_lra_scale_by_one");
    });
}

#[test]
fn test_bootstrap_lra_negate_call_is_claimed_by_fn_inline() {
    // Part of #4145: inline body translation on LRA source needs >8 MB stack.
    run_with_large_stack(|| {
        assert_lra_method_inline_infrastructure(
            "probe_lra_double_negation",
            "LinearExpr::negate",
            &["LinearExpr::negate", "Rational::negate"],
            true, // within budget
        );
    });
}
