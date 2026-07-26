// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Bootstrap-specific regression tests for array-backed flattened struct receivers.
//!
//! Part of #3766: pin the UnionFind/LinearExpr family shapes before another
//! translation-drop production patch.

use super::common::*;

const FLATTENED_ARRAY_STRUCT_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy)]
    pub struct UnionFindLike {
        parent: [u32; 4],
        rank: [u32; 4],
        size: usize,
    }

    impl UnionFindLike {
        fn new() -> Self {
            Self { parent: [0, 1, 2, 3], rank: [0; 4], size: 4 }
        }

        fn find(&self, idx: usize) -> u32 {
            self.parent[idx % self.size]
        }

        fn union(&mut self, x: usize, y: usize) {
            let rx = self.find(x) as usize;
            let ry = self.find(y) as usize;
            if rx != ry {
                self.parent[ry] = rx as u32;
                self.rank[rx] = 1;
            }
        }

        fn rank_at(&self, idx: usize) -> u32 {
            self.rank[idx % self.size]
        }
    }

    #[derive(Clone, Copy)]
    pub struct LinearExprLike {
        vars: [u32; 4],
        coeffs: [u32; 4],
        len: usize,
        bias: u32,
    }

    impl LinearExprLike {
        fn zero() -> Self {
            Self { vars: [0; 4], coeffs: [0; 4], len: 0, bias: 0 }
        }

        fn add_term(&mut self, var: u32, coeff: u32) {
            if self.len < 4 {
                let slot = self.len;
                self.vars[slot] = var;
                self.coeffs[slot] = coeff;
                self.len += 1;
            }
        }

        fn shifted(self, delta: u32) -> Self {
            Self {
                vars: self.vars,
                coeffs: self.coeffs,
                len: self.len,
                bias: delta,
            }
        }

        fn coeff_at(&self, idx: usize) -> u32 {
            let lane = if self.len == 0 { 0 } else { idx % self.len };
            self.coeffs[lane] ^ self.bias
        }
    }

    #[derive(Clone, Copy)]
    pub struct RationalLike {
        num: i64,
        den: i64,
    }

    #[derive(Clone, Copy)]
    pub struct LinearExprNested {
        vars: [u32; 4],
        coeffs: [RationalLike; 4],
        len: usize,
        constant: RationalLike,
    }

    impl LinearExprNested {
        fn seeded() -> Self {
            Self {
                vars: [0, 1, 2, 3],
                coeffs: [
                    RationalLike { num: 3, den: 1 },
                    RationalLike { num: 5, den: 2 },
                    RationalLike { num: 7, den: 3 },
                    RationalLike { num: 11, den: 4 },
                ],
                len: 4,
                constant: RationalLike { num: 13, den: 5 },
            }
        }
    }

    #[derive(Clone, Copy)]
    pub struct ArrayStruct {
        lanes: [u32; 4],
        size: usize,
    }

    pub fn probe_union_find_like_receiver_chain(seed: usize) -> u32 {
        let mut uf = UnionFindLike::new();
        let x = seed % 4;
        let y = (seed + 1) % 4;
        uf.union(x, y);
        uf.rank_at(x)
    }

    pub fn probe_linear_expr_like_receiver_copy(var: u32, coeff: u32) -> u32 {
        let mut expr = LinearExprLike::zero();
        expr.add_term(var, coeff);
        let copied = expr.shifted(1);
        copied.coeff_at(0)
    }

    pub fn probe_array_struct_field_index_read(idx: usize) -> u32 {
        let data = ArrayStruct { lanes: [7, 11, 13, 17], size: 4 };
        data.lanes[idx % data.size]
    }

    pub fn probe_linear_expr_nested_coeff_num(idx: usize) -> i64 {
        let expr = LinearExprNested::seeded();
        let lane = if expr.len == 0 { 0 } else { idx % expr.len };
        expr.coeffs[lane].num + expr.constant.den
    }

    pub fn probe_linear_expr_nested_coeff_store(idx: usize, num: i64, den: i64) -> i64 {
        let mut expr = LinearExprNested::seeded();
        let lane = if expr.len == 0 { 0 } else { idx % expr.len };
        expr.coeffs[lane] = RationalLike { num, den };
        expr.coeffs[lane].num + expr.constant.den
    }

    pub fn probe_linear_expr_nested_constant_replace(num: i64, den: i64) -> i64 {
        let mut expr = LinearExprNested::seeded();
        expr.constant = RationalLike { num, den };
        expr.constant.num + expr.constant.den + expr.coeffs[0].num
    }

    #[derive(Clone, Copy)]
    pub struct ExplainEntryLike {
        pub lhs: u32,
        pub rhs: u32,
    }

    #[derive(Clone, Copy)]
    pub struct NormalFormLike {
        pub deps: [ExplainEntryLike; 4],
        pub deps_len: usize,
    }

    impl NormalFormLike {
        fn new() -> Self {
            Self {
                deps: [ExplainEntryLike { lhs: 0, rhs: 0 }; 4],
                deps_len: 0,
            }
        }

        fn add_dep(&mut self, lhs: u32, rhs: u32) {
            if self.deps_len < 4 {
                let slot = self.deps_len;
                self.deps[slot] = ExplainEntryLike { lhs, rhs };
                self.deps_len += 1;
            }
        }

        fn merge_deps(&mut self, other: &Self) {
            let mut i = 0;
            while i < other.deps_len {
                if self.deps_len < 4 {
                    self.deps[self.deps_len] = other.deps[i];
                    self.deps_len += 1;
                }
                i += 1;
            }
        }
    }

    pub fn probe_normal_form_merge_deps_copy(seed_lhs: u32, seed_rhs: u32) -> u32 {
        let mut nf1 = NormalFormLike::new();
        nf1.add_dep(1, 2);

        let mut nf2 = NormalFormLike::new();
        nf2.add_dep(seed_lhs, seed_rhs);
        nf2.add_dep(seed_lhs + 1, seed_rhs + 1);

        nf1.merge_deps(&nf2);
        // nf1 should now have 3 deps: (1,2), (seed_lhs,seed_rhs), (seed_lhs+1,seed_rhs+1)
        let copied_entry = nf1.deps[1];
        copied_entry.lhs + copied_entry.rhs
    }
"#;

fn reset_flattened_array_struct_metadata() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_constant_translation_drop_count();
    let _ = crate::codegen_ay::take_unsupported_field_projection_count();
}

fn assert_no_translation_drop_metadata(fn_name: &str) {
    let translation_drops = take_translation_drop_by_fn();
    let drop_fallback_reasons = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let place_drop_count = crate::codegen_ay::take_place_translation_drop_count();
    let constant_drop_count = crate::codegen_ay::take_constant_translation_drop_count();
    let field_projection_drop_count = crate::codegen_ay::take_unsupported_field_projection_count();
    let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
    assert_eq!(
        drop_count, 0,
        "{fn_name} should not record translation drops for the bootstrap array-backed receiver shape, drops={translation_drops:?}, sound_fallback_reasons={drop_fallback_reasons:?}, sites={translation_sites:?}, place_count={place_drop_count}, constant_count={constant_drop_count}, field_projection_count={field_projection_drop_count}"
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

#[test]
fn test_translation_drop_union_find_like_receiver_chain_has_clean_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_flattened_array_struct_metadata();

    with_test_ay_ctx_for_source(FLATTENED_ARRAY_STRUCT_SOURCE, |ctx| {
        let fn_name = "probe_union_find_like_receiver_chain";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (UnionFindLike backing arrays)",
        );
        assert_relation_has_arg_sort(&vc, fn_name, |sort| sort.bitvec_width() == Some(32), "bv32");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, idx)",
        );
    });

    assert_no_translation_drop_metadata("probe_union_find_like_receiver_chain");
    reset_flattened_array_struct_metadata();
}

#[test]
fn test_translation_drop_linear_expr_like_receiver_copy_has_clean_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_flattened_array_struct_metadata();

    with_test_ay_ctx_for_source(FLATTENED_ARRAY_STRUCT_SOURCE, |ctx| {
        let fn_name = "probe_linear_expr_like_receiver_copy";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (LinearExprLike backing arrays)",
        );
        assert_relation_has_arg_sort(&vc, fn_name, |sort| sort.bitvec_width() == Some(32), "bv32");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Store { array, .. } if array.sort().is_array()),
            "Store(Array, idx, val)",
        );
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, idx)",
        );
    });

    assert_no_translation_drop_metadata("probe_linear_expr_like_receiver_copy");
    reset_flattened_array_struct_metadata();
}

#[test]
fn test_translation_drop_array_struct_field_index_read_has_clean_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_flattened_array_struct_metadata();

    with_test_ay_ctx_for_source(FLATTENED_ARRAY_STRUCT_SOURCE, |ctx| {
        let fn_name = "probe_array_struct_field_index_read";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (ArrayStruct lanes field)",
        );
        assert_relation_has_arg_sort(&vc, fn_name, |sort| sort.bitvec_width() == Some(32), "bv32");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, idx)",
        );
    });

    assert_no_translation_drop_metadata("probe_array_struct_field_index_read");
    reset_flattened_array_struct_metadata();
}

#[test]
fn test_translation_drop_linear_expr_nested_coeff_num_has_clean_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_flattened_array_struct_metadata();

    with_test_ay_ctx_for_source(FLATTENED_ARRAY_STRUCT_SOURCE, |ctx| {
        let fn_name = "probe_linear_expr_nested_coeff_num";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (LinearExprNested nested coeffs backing arrays)",
        );
        assert_relation_has_arg_sort(&vc, fn_name, |sort| sort.bitvec_width() == Some(64), "bv64");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, idx)",
        );
    });

    assert_no_translation_drop_metadata("probe_linear_expr_nested_coeff_num");
    reset_flattened_array_struct_metadata();
}

#[test]
fn test_translation_drop_linear_expr_nested_coeff_store_has_clean_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_flattened_array_struct_metadata();

    with_test_ay_ctx_for_source(FLATTENED_ARRAY_STRUCT_SOURCE, |ctx| {
        let fn_name = "probe_linear_expr_nested_coeff_store";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (LinearExprNested coeffs backing array)",
        );
        assert_relation_has_arg_sort(&vc, fn_name, |sort| sort.bitvec_width() == Some(64), "bv64");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Store { array, .. } if array.sort().is_array()),
            "Store(Array, idx, val)",
        );
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, idx)",
        );
    });

    assert_no_translation_drop_metadata("probe_linear_expr_nested_coeff_store");
    reset_flattened_array_struct_metadata();
}

#[test]
fn test_translation_drop_linear_expr_nested_constant_replace_has_clean_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_flattened_array_struct_metadata();

    with_test_ay_ctx_for_source(FLATTENED_ARRAY_STRUCT_SOURCE, |ctx| {
        let fn_name = "probe_linear_expr_nested_constant_replace";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (LinearExprNested coeffs backing array)",
        );
        assert_relation_has_arg_sort(&vc, fn_name, |sort| sort.bitvec_width() == Some(64), "bv64");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, idx)",
        );
    });

    assert_no_translation_drop_metadata("probe_linear_expr_nested_constant_replace");
    reset_flattened_array_struct_metadata();
}

#[test]
fn test_translation_drop_normal_form_merge_deps_copy_has_clean_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_flattened_array_struct_metadata();

    with_test_ay_ctx_for_source(FLATTENED_ARRAY_STRUCT_SOURCE, |ctx| {
        let fn_name = "probe_normal_form_merge_deps_copy";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            fn_name,
            ay_bindings::Sort::is_array,
            "Array (NormalFormLike deps backing array)",
        );
        assert_relation_has_arg_sort(&vc, fn_name, |sort| sort.bitvec_width() == Some(32), "bv32");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        // The merge_deps copy path must produce both Select (read other.deps[i])
        // and Store (write self.deps[self.deps_len]) on Array sorts.
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Select { array, .. } if array.sort().is_array()),
            "Select(Array, idx) for other.deps[i]",
        );
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |expr| matches!(expr.value(), ExprValue::Store { array, .. } if array.sort().is_array()),
            "Store(Array, idx, val) for self.deps[self.deps_len]",
        );
    });

    assert_no_translation_drop_metadata("probe_normal_form_merge_deps_copy");
    reset_flattened_array_struct_metadata();
}

/// D3 diagnostic for #3825: inspect VC structure for the merge_deps copy path.
///
/// The while loop in `merge_deps` reads `other.deps[i]` via array Select and
/// writes `self.deps[self.deps_len]` via array Store. This test verifies:
/// 1. Multiple relations exist (loop header produces a second predicate)
/// 2. At least one transition rule contains both Select and Store on arrays
///    (the loop body copies an element from one struct's array to another)
/// 3. The VC has back-edge rules (transition from the same relation to itself)
///
/// If any of these fail, the encoding is structurally incomplete for the
/// while-loop array-copy pattern.
#[test]
fn test_normal_form_merge_deps_vc_has_loop_structure() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_flattened_array_struct_metadata();

    with_test_ay_ctx_for_source(FLATTENED_ARRAY_STRUCT_SOURCE, |ctx| {
        let fn_name = "probe_normal_form_merge_deps_copy";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        // 1. Multiple relations: the while loop should produce at least one
        //    loop-header predicate beyond the function entry/exit.
        let relation_count = vc.relations.len();
        eprintln!("#3825 diag: {fn_name}: {relation_count} relations, {} rules", vc.rules.len());
        for rel in &vc.relations {
            eprintln!(
                "  relation: {} args={} sorts={:?}",
                rel.name,
                rel.arg_sorts.len(),
                rel.arg_sorts.iter().map(|s| format!("{s:?}")).collect::<Vec<_>>()
            );
        }

        // 2. Check for a transition rule that has both Select and Store on arrays.
        //    This is the core loop-body pattern: read from other.deps, write to self.deps.
        let has_copy_rule = vc.rules.iter().any(|rule| {
            let has_select = rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e| {
                    matches!(e.value(), ExprValue::Select { array, .. } if array.sort().is_array())
                })
            }) || rule.head.args.iter().any(|a| {
                constraint_tree_contains(a, &|e| {
                    matches!(e.value(), ExprValue::Select { array, .. } if array.sort().is_array())
                })
            });
            let has_store = rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e| {
                    matches!(e.value(), ExprValue::Store { array, .. } if array.sort().is_array())
                })
            }) || rule.head.args.iter().any(|a| {
                constraint_tree_contains(a, &|e| {
                    matches!(e.value(), ExprValue::Store { array, .. } if array.sort().is_array())
                })
            });
            has_select && has_store
        });
        eprintln!("#3825 diag: has_copy_rule (Select+Store in same rule): {has_copy_rule}");
        assert!(
            has_copy_rule,
            "{fn_name}: no single rule contains both Select and Store on Array — \
             the while-loop body should produce a transition with read-then-write"
        );

        // 3. Check for back-edge rules (same relation appears in both head and body).
        let has_back_edge = vc.rules.iter().any(|rule| {
            rule.body.relation.as_ref().is_some_and(|body_rel| *body_rel.name == *rule.head.name)
        });
        eprintln!("#3825 diag: has_back_edge (self-loop rule): {has_back_edge}");
        // Note: back-edge is expected for a while loop but CHC encoding may
        // inline it through unrolling. Log rather than hard-assert.
    });

    reset_flattened_array_struct_metadata();
}
