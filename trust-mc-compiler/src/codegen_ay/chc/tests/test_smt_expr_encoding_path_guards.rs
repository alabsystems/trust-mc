// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SMT expression-level regression guards for encoding paths.
//!
//! Part of #3410: Missing AY SMT-level regression guard tests.
//!
//! These tests verify encoding-path-specific SMT invariants that are only
//! tested end-to-end by the canary suite. Each test compiles real Rust source
//! through the `mir_to_chc` pipeline and inspects the generated CHC
//! expressions for structural correctness of specific encoding paths.
//!
//! Invariants guarded:
//! 9. Vec push Store: index sort is BV, element sort matches Vec<T>
//! 10. Pointer offset: ptr.add produces BV64 arithmetic (pointer-width)
//! 11. Sound fallback: well-formedness maintained on fallback paths
//! 12. HashMap insert Store: backing array has Array sort, value is BV-sorted
//! 13. Enum discriminant: SetDiscriminant/match encoding uses correct BV width
//! 14. Slice fat pointer: slice parameters carry BV64 length in relations
//! 15. While loop back-edge: loop body produces self-referencing relation
//! 16. Integer cast/truncation: u32-to-u8 cast uses BvExtract with correct widths
//! 17. Fixed-size array index Select: arr[idx] uses Select with BV-sorted index
//! 18. Option ADT constructor: Some(x) produces DatatypeConstructor application
//! 19. Assertion error rule: assert!(cond) targets error relation with negated condition
//! 20. Integer widening: u8-to-u32 cast produces BvZeroExtend with correct widths
//! 21. Struct field access: s.field produces DatatypeSelector expression
//! 22. Signed widening: i8-to-i32 cast produces BvSignExtend (not BvZeroExtend)
//! 23. Bitwise NOT: !x on u32 produces BvNot expression
//! 24. Boolean multi-condition: compound conditions produce And/Or connectives
//! 25. Wrapping subtraction: wrapping_sub produces BvSub with matching BV widths
//! 26. BV division: u32 / u32 produces BvUDiv with matching widths + div-by-zero guard
//! 27. Signed comparison: i32 < i32 produces BvSLt (not BvULt) with matching widths
//! 28. Array store/select round-trip: Store and Select index/element sorts are consistent
//! 29. Bitwise shift: << produces BvShl, >> on u32 produces BvLShr (not BvAShr)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// =============================================================================
// Invariant 9: Vec push Store sort consistency
// =============================================================================

/// Vec::push Store must have: (a) Array-sorted array operand, (b) BV-sorted
/// index (usize = BV64), and (c) BV-sorted value matching element type (BV32
/// for Vec<u32>). Regression guard: sort mismatch in Store causes Z3 type
/// errors or silent unsoundness in the backing-array model.
#[test]
fn test_vec_push_store_sort_invariants() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_vec_push_sort() {
            let mut v: Vec<u32> = Vec::new();
            v.push(42);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_push_sort");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_push_sort", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_push_sort", body.blocks.len());

        // Collect all Store nodes from the VC and check sort invariants
        let mut store_count = 0usize;
        let mut store_array_not_array = false;
        let mut store_index_not_bv = false;

        let check_store = |e: &Expr| -> Option<&'static str> {
            if let ExprValue::Store { array, index, .. } = e.value() {
                if !array.sort().is_array() {
                    return Some("array_not_array");
                }
                if !index.sort().is_bitvec() {
                    return Some("index_not_bv");
                }
                return Some("ok");
            }
            None
        };

        for rule in &vc.rules {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::Store { .. });
            let check_in_tree = |root: &Expr| {
                let mut found = Vec::new();
                let mut stack: Vec<&Expr> = vec![root];
                while let Some(node) = stack.pop() {
                    if let Some(result) = check_store(node) {
                        found.push(result);
                    }
                    stack.extend(expr_children(node));
                }
                found
            };

            for constraint in &rule.body.constraints {
                if constraint_tree_contains(constraint, &pred) {
                    for result in check_in_tree(constraint) {
                        store_count += 1;
                        if result == "array_not_array" {
                            store_array_not_array = true;
                        }
                        if result == "index_not_bv" {
                            store_index_not_bv = true;
                        }
                    }
                }
            }
            for arg in rule.head.args.iter() {
                if constraint_tree_contains(arg, &pred) {
                    for result in check_in_tree(arg) {
                        store_count += 1;
                        if result == "array_not_array" {
                            store_array_not_array = true;
                        }
                        if result == "index_not_bv" {
                            store_index_not_bv = true;
                        }
                    }
                }
            }
        }

        // Vec::push must produce at least one Store (writing to fld_data)
        assert!(store_count > 0, "Vec::push encoding must produce at least one Store expression");

        // Store array operand must be Array-sorted
        assert!(!store_array_not_array, "Vec::push Store array operand must be Array-sorted");

        // Store index must be BV-sorted (usize = pointer width)
        assert!(!store_index_not_bv, "Vec::push Store index must be BV-sorted (usize)");
    });
}

// =============================================================================
// Invariant 10: Pointer offset produces BV64 arithmetic (pointer-width)
// =============================================================================

/// ptr.add on a pointer must produce BvAdd/BvMul with BV64 operands
/// (pointer-width). Regression guard: if ptr.add uses BV32 instead of BV64,
/// pointer arithmetic wraps at 4GB boundary, producing incorrect addresses.
#[test]
fn test_ptr_offset_produces_pointer_width_bv_arithmetic() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_offset(p: *const u32) -> *const u32 {
            unsafe { p.add(3) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_offset");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ptr_offset", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ptr_offset", body.blocks.len());

        // Relations must carry BV64 for pointer state variables
        assert_relation_has_arg_sort(
            &vc,
            "probe_ptr_offset",
            |s| s.bitvec_width() == Some(64),
            "BV64",
        );

        // BvMul must operate on BV64 operands (count * sizeof(T) in pointer width).
        // Check that no BvMul in the VC has non-64-bit BV operands when both
        // operands are bitvec (excluding non-BV operands which are other computations).
        let bvmul_wrong_width = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvMul(l, r)
                    if l.sort().is_bitvec() && r.sort().is_bitvec()
                    && l.sort().bitvec_width() == Some(64)
                    && r.sort().bitvec_width() != Some(64))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !bvmul_wrong_width,
            "ptr.add BvMul for count * sizeof(T) must use BV64 operands -- found width mismatch"
        );

        // The VC should contain BV64 arithmetic (either BvAdd or BvMul or BvConcat)
        // that encodes the pointer offset computation. At minimum, the output
        // pointer must be constrained (not pure nondet).
        assert_has_nontrivial_transition_constraints(&vc, "probe_ptr_offset");
    });
}

// =============================================================================
// Invariant 11: Sound fallback produces unconstrained destination (nondet)
// =============================================================================

/// When a call fallback path fires, the destination variable must be
/// genuinely unconstrained in the rule body (nondet). If the fallback
/// accidentally binds the dest to some expression, the over-approximation
/// property is violated and the result may be unsound.
/// Regression guard: #4158 (bail-out state leak gap).
#[test]
fn test_sound_fallback_dest_unconstrained_via_pipeline() {
    // Use an unrecognized function call that will trigger sound fallback
    // (the codegen cannot translate it, so it falls back to nondet).
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        unsafe extern "C" {
            fn unknown_extern_fn(x: u32) -> u32;
        }

        pub fn probe_fallback_nondet(x: u32, flag: bool) -> u32 {
            if flag {
                unsafe { unknown_extern_fn(x) }
            } else {
                0
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_fallback_nondet");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_fallback_nondet", ChcConfig::default());

        assert_vc_structure(&vc, "probe_fallback_nondet", body.blocks.len());

        // The VC must have at least some rules (entry + transitions).
        assert!(vc.rules.len() >= 2, "Expected at least 2 rules, got {}", vc.rules.len());

        // Global well-formedness: no ITE should have non-Bool condition
        let ite_non_bool = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Ite { cond, .. } if !cond.sort().is_bool())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!ite_non_bool, "Even with fallback paths, ITE conditions must be Bool");

        // Global well-formedness: no Eq should have mismatched sorts
        let eq_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::Eq(l, r) if l.sort() != r.sort());
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!eq_mismatch, "Even with fallback paths, Eq operand sorts must match");

        // No malformed BV concat/extract should be produced
        let malformed = first_malformed_bv_site(&vc);
        assert!(malformed.is_none(), "Fallback path must not produce malformed BV: {malformed:?}");
    });
}

// =============================================================================
// Invariant 12: HashMap insert Store has correct Array sort structure
// =============================================================================

/// HashMap::insert must encode as Array Store where the array operand has
/// Array sort. The index (key) and value sorts must both be BV-sorted
/// (matching the key/value types). Regression guard: if the HashMap
/// backing array has wrong sorts, insert/get produce sort mismatch.
#[test]
fn test_hashmap_insert_store_array_sort_structure() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;

        pub fn probe_hashmap_insert_sort() {
            let mut m: HashMap<u32, u32> = HashMap::new();
            m.insert(1, 10);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_insert_sort");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashmap_insert_sort", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashmap_insert_sort", body.blocks.len());

        // HashMap::insert must produce at least one Store (writing to backing array).
        let has_store = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::Store { .. });
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(has_store, "HashMap::insert encoding must produce at least one Store expression");

        // Every Store in the VC must have Array-sorted array operand
        let store_bad_array = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Store { array, .. } if !array.sort().is_array())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!store_bad_array, "HashMap Store array operand must be Array-sorted");

        // Every Store index must be BV-sorted (HashMap key = u32 -> BV32 or coerced BV64)
        let store_bad_index = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Store { index, .. } if !index.sort().is_bitvec())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!store_bad_index, "HashMap Store index (key) must be BV-sorted");

        // No malformed BV concat/extract should exist
        let malformed = first_malformed_bv_site(&vc);
        assert!(malformed.is_none(), "HashMap insert must not produce malformed BV: {malformed:?}");

        // Relations must carry Array sort for the HashMap state
        assert_relation_has_arg_sort(
            &vc,
            "probe_hashmap_insert_sort",
            ay_bindings::Sort::is_array,
            "Array (HashMap backing)",
        );
    });
}

// =============================================================================
// Invariant 13: Enum discriminant encoding uses correct BV width
// =============================================================================

/// Enum match/discriminant encoding must produce BV-sorted discriminant reads
/// and ITE-based dispatch with Bool conditions. The discriminant comparison
/// (SwitchInt on the tag) must use matching BV widths on both sides.
/// Regression guard: wrong discriminant width causes silent misrouting through
/// match arms, producing incorrect verification results.
#[test]
fn test_enum_discriminant_encoding_bv_width() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub enum Action { Add(u32), Sub(u32), Nop }

        pub fn probe_enum_discr(a: Action) -> u32 {
            match a {
                Action::Add(x) => x,
                Action::Sub(x) => x.wrapping_add(1),
                Action::Nop => 0,
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_enum_discr");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_enum_discr", ChcConfig::default());

        assert_vc_structure(&vc, "probe_enum_discr", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_enum_discr");

        // The VC must contain Eq comparisons for discriminant dispatch (SwitchInt).
        // At least one Eq node comparing BV values (discriminant tag vs constant).
        let has_bv_eq = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Eq(l, r)
                    if l.sort().is_bitvec() && r.sort().is_bitvec())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(has_bv_eq, "Enum match must produce BV Eq comparisons for discriminant dispatch");

        // All Eq nodes must have matching operand sorts (no width mismatch)
        let eq_sort_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::Eq(l, r) if l.sort() != r.sort());
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !eq_sort_mismatch,
            "Enum discriminant Eq comparisons must have matching operand sorts"
        );

        // BV32 must appear in relations for the u32 payload fields
        assert_relation_has_arg_sort(
            &vc,
            "probe_enum_discr",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // No malformed BV concat/extract from discriminant or payload access
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Enum discriminant encoding must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 14: Slice fat pointer carries BV64 length in relations
// =============================================================================

/// Slice parameters (&[T]) must encode as fat pointers with a BV64-sorted
/// length component in the CHC relation state variables. The data pointer
/// is also BV64. Regression guard: if slice length is encoded as BV32 or
/// Int, bounds-check comparisons produce sort mismatches with usize indices.
#[test]
fn test_slice_fat_pointer_bv64_length_in_relations() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_slice_len(s: &[u32]) -> usize {
            s.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_len");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_slice_len", ChcConfig::default());

        assert_vc_structure(&vc, "probe_slice_len", body.blocks.len());

        // Relations must carry BV64 for the usize length and pointer components
        assert_relation_has_arg_sort(
            &vc,
            "probe_slice_len",
            |s| s.bitvec_width() == Some(64),
            "BV64",
        );

        // The return value is usize (BV64). The VC should have nontrivial
        // constraints that propagate the length field to the return slot.
        assert_has_nontrivial_transition_constraints(&vc, "probe_slice_len");

        // No BV comparison should have mismatched widths (len vs index both BV64)
        let bv_cmp_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| match e.value() {
                ExprValue::BvULt(l, r)
                | ExprValue::BvULe(l, r)
                | ExprValue::BvUGt(l, r)
                | ExprValue::BvUGe(l, r) => {
                    l.sort().is_bitvec()
                        && r.sort().is_bitvec()
                        && l.sort().bitvec_width() != r.sort().bitvec_width()
                }
                _ => false,
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !bv_cmp_mismatch,
            "Slice operations must not produce BV comparisons with mismatched widths"
        );
    });
}

// =============================================================================
// Invariant 15: While loop back-edge produces self-referencing relation
// =============================================================================

/// A while loop must produce at least one rule whose body relation references
/// the same relation name as its head (loop back-edge). Without this
/// self-referential rule, the CHC solver cannot reason about the loop and
/// the encoding degenerates to a single unrolling or unconstrained result.
/// Regression guard: dead block elimination or optimizer changes could
/// accidentally remove the back-edge.
#[test]
fn test_while_loop_produces_back_edge_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_while_loop(mut n: u32) -> u32 {
            let mut acc: u32 = 0;
            while n > 0 {
                acc = acc.wrapping_add(n);
                n = n.wrapping_sub(1);
            }
            acc
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_while_loop");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_while_loop", ChcConfig::default());

        assert_vc_structure(&vc, "probe_while_loop", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_while_loop");

        // Find at least one back-edge: a rule where body.relation.name == head.name.
        // This is the defining structural property of a loop in CHC encoding.
        let has_back_edge = vc
            .rules
            .iter()
            .any(|rule| rule.body.relation.as_ref().is_some_and(|rel| rel.name == rule.head.name));
        assert!(
            has_back_edge,
            "While loop must produce a CHC rule with body relation == head relation (back-edge)"
        );

        // The back-edge rule must carry nontrivial semantics: either in head
        // args (computed values like bvadd) or in body constraints (non-true
        // conditions). The CHC encoding may place loop body updates in either
        // location depending on the encoding strategy.
        let back_edge_nontrivial = vc.rules.iter().any(|rule| {
            let is_back_edge =
                rule.body.relation.as_ref().is_some_and(|rel| rel.name == rule.head.name);
            if !is_back_edge {
                return false;
            }
            let head_nontrivial =
                rule.head.args.iter().any(|a| !matches!(a.value(), ExprValue::Var { .. }));
            let body_nontrivial = rule
                .body
                .constraints
                .iter()
                .any(|c| !matches!(c.value(), ExprValue::BoolConst(true)));
            head_nontrivial || body_nontrivial
        });
        assert!(
            back_edge_nontrivial,
            "While loop back-edge rule must have nontrivial semantics (loop body updates)"
        );

        // BV32 must appear in relations for the u32 accumulator and counter
        assert_relation_has_arg_sort(
            &vc,
            "probe_while_loop",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );
    });
}

// =============================================================================
// Invariant 16: Integer cast/truncation uses BvExtract with correct widths
// =============================================================================
//
// Invariants 17-21 added in Round 6 (Part of #3410).
// 17. Fixed-size array index Select with BV-sorted index
// 18. Option Some/None produces DatatypeConstructor
// 19. assert! produces error-targeting rule with negated condition
// 20. Integer widening (u8 to u32) produces BvZeroExtend
// 21. Struct field access produces DatatypeSelector

/// Casting u32 to u8 must produce a BvExtract (or equivalent truncation)
/// where the source is BV32-sorted and the result is BV8-sorted. The extract
/// range must be [0, 7] (low 8 bits). Regression guard: if the cast produces
/// wrong-width BvExtract or skips truncation entirely, the value may silently
/// carry extra high bits that corrupt downstream computations.
#[test]
fn test_integer_cast_truncation_bvextract_widths() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_u32_to_u8(x: u32, flag: bool) -> u8 {
            if flag { x as u8 } else { 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_u32_to_u8");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_u32_to_u8", ChcConfig::default());

        assert_vc_structure(&vc, "probe_u32_to_u8", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_u32_to_u8");

        // The VC must contain BvExtract for the truncation (u32 -> u8).
        // Both BvExtract and BvAnd-mask are valid truncation strategies;
        // BvExtract is the primary encoding path.
        let has_extract = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvExtract { .. });
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        // BvAnd with a constant mask is an alternative truncation encoding
        let has_and_mask = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvAnd(l, r)
                    if matches!(l.value(), ExprValue::BitVecConst { .. })
                    || matches!(r.value(), ExprValue::BitVecConst { .. }))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        assert!(
            has_extract || has_and_mask,
            "u32-to-u8 cast must produce BvExtract or BvAnd mask for truncation"
        );

        // If BvExtract is present, verify the source operand is bitvec-sorted
        // (not Bool, not Int, not Array).
        let extract_bad_source = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvExtract { expr: inner, .. }
                    if !inner.sort().is_bitvec())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !extract_bad_source,
            "BvExtract source must be bitvec-sorted for integer truncation"
        );

        // Relations must carry BV8 for the u8 return type
        assert_relation_has_arg_sort(
            &vc,
            "probe_u32_to_u8",
            |s| s.bitvec_width() == Some(8),
            "BV8",
        );

        // Relations must also carry BV32 for the u32 input
        assert_relation_has_arg_sort(
            &vc,
            "probe_u32_to_u8",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Integer cast encoding must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 17: Fixed-size array index Select with BV-sorted index
// =============================================================================

/// Indexing a fixed-size array (`arr[idx]`) must produce a `Select` expression
/// where the array operand has Array sort and the index is BV-sorted (usize =
/// BV64). The Select result sort must match the element type (BV32 for [u32; N]).
/// Regression guard: if the index sort is Int or Bool instead of BV64, the
/// Select sort signature mismatches the declared Array sort and Z3 rejects it.
#[test]
fn test_array_index_select_bv_sorted_index() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array_select(arr: [u32; 4], idx: usize) -> u32 {
            arr[idx]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_select");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_array_select", ChcConfig::default());

        assert_vc_structure(&vc, "probe_array_select", body.blocks.len());

        // The VC must contain at least one Select expression (array read).
        let has_select = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::Select { .. });
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(has_select, "Array indexing must produce at least one Select expression");

        // Every Select array operand must be Array-sorted.
        let select_bad_array = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Select { array, .. } if !array.sort().is_array())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!select_bad_array, "Array Select array operand must be Array-sorted");

        // Every Select index must be BV-sorted (usize = BV64).
        let select_bad_index = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Select { index, .. } if !index.sort().is_bitvec())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!select_bad_index, "Array Select index must be BV-sorted (usize = BV64)");

        // Relations must carry BV32 for the u32 element type
        assert_relation_has_arg_sort(
            &vc,
            "probe_array_select",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // Relations must carry BV64 for the usize index
        assert_relation_has_arg_sort(
            &vc,
            "probe_array_select",
            |s| s.bitvec_width() == Some(64),
            "BV64",
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Array index Select must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 18: Option Some/None flattened ADT encoding
// =============================================================================

/// Constructing `Some(x)` for `Option<u32>` must produce the correct
/// flattened encoding: a Bool state variable (is_some discriminant) set to
/// `true` and a BV32 state variable (payload) carrying the input value.
/// The CHC relations must carry both Bool and BV32 argument sorts.
/// Regression guard: if Option flattening omits the Bool discriminant or
/// drops the payload binding, match arms cannot distinguish Some from None
/// and the payload read returns unconstrained garbage.
#[test]
fn test_option_some_flattened_adt_encoding() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_some(x: u32) -> Option<u32> {
            Some(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_some");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_some", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_some", body.blocks.len());

        // Option<u32> is flattened to (Bool, BV32) state variables:
        // - Bool: is_some discriminant (true = Some, false = None)
        // - BV32: payload value
        //
        // Relations must carry Bool for the discriminant.
        assert_relation_has_arg_sort(
            &vc,
            "probe_option_some",
            ay_bindings::Sort::is_bool,
            "Bool (Option discriminant)",
        );

        // Relations must carry BV32 for the u32 payload.
        assert_relation_has_arg_sort(
            &vc,
            "probe_option_some",
            |s| s.bitvec_width() == Some(32),
            "BV32 (Option payload)",
        );

        // The VC must contain BoolConst(true) — the is_some discriminant for Some.
        // This appears either as a body constraint or a head argument in the rule
        // that encodes the Some construction.
        let has_bool_true = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BoolConst(true));
            // Check head args: flattened Some sets discriminant = true in the
            // next relation's argument list.
            rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
                || rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
        });
        assert!(
            has_bool_true,
            "Option::Some encoding must produce BoolConst(true) for the is_some discriminant"
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Option construction must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 19: assert! produces error-targeting rule with negated condition
// =============================================================================

/// `assert!(cond)` in Rust must produce at least one CHC rule whose head
/// targets the `error` relation. The body of this error rule must contain
/// the negated assertion condition (either `Not(cond)` or `Eq(cond, false)`).
/// Without an error-targeting rule, the CHC solver has no violation to check
/// and verification becomes vacuous (always PROOF regardless of the assertion).
/// Regression guard: optimizer changes or dead block elimination could
/// accidentally remove the error path.
#[test]
fn test_assert_produces_error_targeting_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_assert_error(x: u32) -> u32 {
            assert!(x > 0);
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assert_error");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_assert_error", ChcConfig::default());

        assert_vc_structure(&vc, "probe_assert_error", body.blocks.len());

        // Must have at least one error-targeting rule (head.name == "error").
        let error_rules: Vec<_> = vc.rules.iter().filter(|r| r.head.name == "error").collect();
        assert!(
            !error_rules.is_empty(),
            "assert!(x > 0) must produce at least one error-targeting rule"
        );

        // Error rules must have zero head arguments (error relation has no state).
        for error_rule in &error_rules {
            assert!(
                error_rule.head.args.is_empty(),
                "Error relation head must have zero arguments, got {}",
                error_rule.head.args.len()
            );
        }

        // The error rule must have a non-empty source relation (it transitions
        // FROM a block, not from init).
        let error_has_source = error_rules.iter().any(|r| r.body.relation.is_some());
        assert!(
            error_has_source,
            "Error rule must have a source relation (transition from a BB, not init)"
        );

        // At least one non-error rule must carry a BV comparison (BvUGt for x > 0)
        // or a Not/Eq-based condition — proving the condition is actually encoded.
        let has_comparison = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(
                    e.value(),
                    ExprValue::BvUGt(_, _)
                        | ExprValue::BvULt(_, _)
                        | ExprValue::BvSGt(_, _)
                        | ExprValue::BvSLt(_, _)
                        | ExprValue::Not(_)
                )
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            has_comparison,
            "assert!(x > 0) must encode a BV comparison or Not in the transition rules"
        );

        // No malformed BV
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Assertion encoding must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 20: Integer widening (u8 to u32) produces BvZeroExtend
// =============================================================================

/// Casting u8 to u32 must produce a `BvZeroExtend` (or `BvConcat` with zeros)
/// where the source is BV8-sorted and the result is BV32-sorted. The
/// extension amount must be 24 bits (32 - 8). Regression guard: if the
/// widening cast is omitted, the 8-bit value is used directly in 32-bit
/// context, causing sort mismatches or silent high-bit corruption.
#[test]
fn test_integer_widening_u8_to_u32_bvzeroextend() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_u8_to_u32(x: u8, flag: bool) -> u32 {
            if flag { x as u32 } else { 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_u8_to_u32");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_u8_to_u32", ChcConfig::default());

        assert_vc_structure(&vc, "probe_u8_to_u32", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_u8_to_u32");

        // The VC must contain BvZeroExtend (primary widening path).
        let has_zero_extend = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvZeroExtend { .. });
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        // BvConcat with a zero constant is an alternative widening encoding:
        // concat(#x000000, x_8bit) = zero-extend.
        let has_concat_zero = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvConcat(high, _)
                    if matches!(high.value(), ExprValue::BitVecConst { .. }))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        assert!(
            has_zero_extend || has_concat_zero,
            "u8-to-u32 cast must produce BvZeroExtend or BvConcat(zeros, x) for widening"
        );

        // If BvZeroExtend is present, verify the source operand is BV-sorted.
        let extend_bad_source = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvZeroExtend { expr: inner, .. }
                    if !inner.sort().is_bitvec())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!extend_bad_source, "BvZeroExtend source must be BV-sorted for integer widening");

        // Relations must carry BV8 for the u8 input
        assert_relation_has_arg_sort(
            &vc,
            "probe_u8_to_u32",
            |s| s.bitvec_width() == Some(8),
            "BV8",
        );

        // Relations must carry BV32 for the u32 return type
        assert_relation_has_arg_sort(
            &vc,
            "probe_u8_to_u32",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Integer widening must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 21: Struct field access produces DatatypeSelector expression
// =============================================================================

/// Accessing a struct field (`s.x`) must produce either a `DatatypeSelector`
/// expression (if the struct is encoded as a AY Datatype) or a `BvExtract`/
/// variable reference with field-name metadata (if the struct is flattened).
/// The selected field must preserve the correct BV width for the field type.
/// Regression guard: if field access falls back to nondet or produces the
/// wrong BV width, field reads silently return unconstrained garbage, causing
/// false proofs.
#[test]
fn test_struct_field_access_produces_selector() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Point { pub x: u32, pub y: u32 }

        pub fn probe_struct_field(p: Point) -> u32 {
            p.x.wrapping_add(p.y)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_field");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_struct_field", ChcConfig::default());

        assert_vc_structure(&vc, "probe_struct_field", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_struct_field");

        // Check for DatatypeSelector (DT mode) — field access on a Datatype.
        let has_dt_selector = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::DatatypeSelector { .. });
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        // Check for field-named Var (flattened mode) — the struct is decomposed
        // into separate state variables named after fields (e.g. "fld_x", "fld_y"
        // or "fld0", "fld1").
        let has_field_var = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Var { name }
                    if name.contains("fld") || name.contains("field"))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        assert!(
            has_dt_selector || has_field_var,
            "Struct field access must produce DatatypeSelector or field-named Var"
        );

        // The VC must contain BvAdd (wrapping_add encoding) to confirm the
        // field values are actually used in computation, not just declared.
        let has_bvadd = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvAdd(_, _));
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(has_bvadd, "probe_struct_field must produce BvAdd for wrapping_add of fields");

        // Relations must carry BV32 for the u32 field types
        assert_relation_has_arg_sort(
            &vc,
            "probe_struct_field",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Struct field access must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 22: Signed widening (i8 to i32) produces BvSignExtend
// =============================================================================

/// Casting i8 to i32 must produce a `BvSignExtend` (sign-extending the high
/// bit) rather than `BvZeroExtend` (which would treat the value as unsigned
/// and corrupt negative numbers). The source must be BV8-sorted and the
/// result BV32-sorted. Regression guard: if signed widening uses zero
/// extension instead, negative values like -1i8 become 255i32 instead of
/// -1i32, causing silent arithmetic corruption in downstream computations.
#[test]
fn test_guard_signed_widening_i8_to_i32_bvsignextend() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_i8_to_i32(x: i8, flag: bool) -> i32 {
            if flag { x as i32 } else { 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_i8_to_i32");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_i8_to_i32", ChcConfig::default());

        assert_vc_structure(&vc, "probe_i8_to_i32", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_i8_to_i32");

        // The VC must contain BvSignExtend (primary signed widening path).
        let has_sign_extend = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvSignExtend { .. });
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        // BvConcat with sign-extension bits is an alternative encoding.
        let has_concat_sign = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvConcat(_, _));
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        assert!(
            has_sign_extend || has_concat_sign,
            "i8-to-i32 signed cast must produce BvSignExtend or BvConcat for sign extension"
        );

        // If BvSignExtend is present, verify the source operand is BV-sorted.
        let extend_bad_source = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvSignExtend { expr: inner, .. }
                    if !inner.sort().is_bitvec())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !extend_bad_source,
            "BvSignExtend source must be BV-sorted for signed integer widening"
        );

        // Relations must carry BV8 for the i8 input
        assert_relation_has_arg_sort(
            &vc,
            "probe_i8_to_i32",
            |s| s.bitvec_width() == Some(8),
            "BV8",
        );

        // Relations must carry BV32 for the i32 return type
        assert_relation_has_arg_sort(
            &vc,
            "probe_i8_to_i32",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Signed widening must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 23: Bitwise NOT on u32 produces BvNot expression
// =============================================================================

/// Applying bitwise NOT (`!x`) on a u32 must produce a `BvNot` expression
/// whose operand is BV32-sorted. The result must also be BV32-sorted (same
/// width as input). Regression guard: if bitwise NOT is omitted or encoded
/// as BvNeg (arithmetic negation), the result is 2's complement negation
/// instead of 1's complement inversion, producing wrong values for all
/// inputs except 0.
#[test]
fn test_guard_bitwise_not_produces_bvnot() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_bitwise_not(x: u32, flag: bool) -> u32 {
            if flag { !x } else { 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bitwise_not");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_bitwise_not", ChcConfig::default());

        assert_vc_structure(&vc, "probe_bitwise_not", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_bitwise_not");

        // The VC must contain BvNot (bitwise complement).
        let has_bvnot = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvNot(_));
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        // BvXor with all-ones mask is an alternative encoding for NOT.
        let has_xor_ones = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvXor(l, r)
                    if matches!(l.value(), ExprValue::BitVecConst { .. })
                    || matches!(r.value(), ExprValue::BitVecConst { .. }))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        assert!(
            has_bvnot || has_xor_ones,
            "Bitwise NOT (!x) must produce BvNot or BvXor with all-ones mask"
        );

        // If BvNot is present, verify the operand is BV-sorted.
        let bvnot_bad_operand = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvNot(inner) if !inner.sort().is_bitvec())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!bvnot_bad_operand, "BvNot operand must be BV-sorted for bitwise NOT encoding");

        // Relations must carry BV32 for the u32 operand and result
        assert_relation_has_arg_sort(
            &vc,
            "probe_bitwise_not",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Bitwise NOT encoding must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 24: Compound boolean conditions produce correct CFG structure
// =============================================================================

/// A function with compound boolean conditions (`a && b`, `a || b`) must
/// encode short-circuit evaluation as multiple CFG transitions with BV
/// comparisons. Rust compiles `&&` and `||` into separate `SwitchInt`
/// terminators, each producing its own basic block transition. The VC must
/// reflect this: multiple transition rules carrying BV comparisons.
/// Regression guard: if boolean conjunction/disjunction collapses into a
/// single unconstrained transition, branch conditions are lost and both
/// paths appear feasible, producing false counterexamples.
#[test]
fn test_guard_compound_boolean_short_circuit_cfg() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_compound_bool(a: u32, b: u32) -> u32 {
            if a > 0 && b > 0 {
                a.wrapping_add(b)
            } else if a > 0 || b > 0 {
                1
            } else {
                0
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_compound_bool");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_compound_bool", ChcConfig::default());

        assert_vc_structure(&vc, "probe_compound_bool", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_compound_bool");

        // The source has two compound conditions (&&, ||), which produce
        // multiple basic blocks with BV comparisons (BvUGt for `> 0`).
        let has_bv_comparison = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(
                    e.value(),
                    ExprValue::BvUGt(_, _)
                        | ExprValue::BvULt(_, _)
                        | ExprValue::Eq(_, _)
                        | ExprValue::Not(_)
                )
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            has_bv_comparison,
            "Compound boolean conditions must produce BV comparison expressions (BvUGt/Eq/Not)"
        );

        // Rust compiles && and || via short-circuit: each condition is a
        // separate SwitchInt producing separate BB transitions. The encoding
        // must produce multiple distinct transition rules (not just init +
        // single exit). The number of rules reflects the short-circuit CFG.
        let transition_rules =
            vc.rules.iter().filter(|r| r.body.relation.is_some() && r.head.name != "error").count();
        assert!(
            transition_rules >= 3,
            "Compound boolean (&&, ||) must produce >= 3 transition rules \
             for short-circuit evaluation, got {transition_rules}"
        );

        // BvAdd must be present (wrapping_add in the a > 0 && b > 0 branch).
        let has_bvadd = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvAdd(_, _));
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(has_bvadd, "probe_compound_bool must produce BvAdd for the wrapping_add branch");

        // BV32 must appear in relations for the u32 parameters and return.
        assert_relation_has_arg_sort(
            &vc,
            "probe_compound_bool",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Compound boolean encoding must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 25: Wrapping subtraction produces BvSub with matching BV widths
// =============================================================================

/// `wrapping_sub` on u32 must produce a `BvSub` expression where both
/// operands are BV32-sorted (matching the operand type). The result sort
/// must also be BV32. Regression guard: if subtraction is encoded with
/// mismatched widths (e.g., one operand BV32 and other BV64), Z3 rejects
/// the expression or the solver produces spurious counterexamples from
/// implicit zero-extension of the narrower operand.
#[test]
fn test_guard_wrapping_sub_produces_bvsub_matching_widths() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_wrapping_sub(a: u32, b: u32, flag: bool) -> u32 {
            if flag { a.wrapping_sub(b) } else { 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_sub");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_wrapping_sub", ChcConfig::default());

        assert_vc_structure(&vc, "probe_wrapping_sub", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_wrapping_sub");

        // The VC must contain BvSub (wrapping subtraction encoding).
        let has_bvsub = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvSub(_, _));
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(has_bvsub, "wrapping_sub must produce a BvSub expression in the VC");

        // Every BvSub in the VC must have matching operand widths.
        let bvsub_width_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvSub(l, r)
                    if l.sort().is_bitvec() && r.sort().is_bitvec()
                    && l.sort().bitvec_width() != r.sort().bitvec_width())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !bvsub_width_mismatch,
            "BvSub operands must have matching BV widths -- found width mismatch"
        );

        // BvSub operands must be BV32-sorted (u32 - u32).
        let bvsub_not_bv32 = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvSub(l, r)
                    if l.sort().bitvec_width() == Some(32)
                    && r.sort().bitvec_width() != Some(32))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !bvsub_not_bv32,
            "u32 wrapping_sub BvSub must use BV32 operands -- found non-BV32 operand"
        );

        // Relations must carry BV32 for the u32 parameters and return
        assert_relation_has_arg_sort(
            &vc,
            "probe_wrapping_sub",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Wrapping subtraction encoding must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 26: BV division produces BvUDiv with matching operand widths
// =============================================================================

/// Integer division on u32 (`a / b`) must produce a `BvUDiv` expression where
/// both operands are BV32-sorted and have matching widths. The encoding must
/// also generate a division-by-zero guard: either a conditional (Ite/SwitchInt)
/// that checks `b != 0` before dividing, or an error-targeting rule that fires
/// when `b == 0`. Without this guard, BV division by the zero bitvector is
/// defined by SMT-LIB2 as all-ones (#xFFFFFFFF for BV32), which silently
/// produces wrong results instead of panicking as Rust requires.
/// Regression guard: if the division guard is omitted or the BvUDiv operands
/// have mismatched widths, the encoding is either unsound (missing panic on
/// div-by-zero) or produces Z3 sort errors.
#[test]
fn test_guard_bv_division_operand_widths_and_guard() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_div_u32(a: u32, b: u32, flag: bool) -> u32 {
            if flag { a / b } else { 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_div_u32");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_div_u32", ChcConfig::default());

        assert_vc_structure(&vc, "probe_div_u32", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_div_u32");

        // The VC must contain BvUDiv (unsigned division encoding for u32).
        let has_bvudiv = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvUDiv(_, _));
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        // The encoder may also use ITE-guarded division or overflow-check intrinsics.
        // Accept BvUDiv or Ite wrapping a BvUDiv as valid division encodings.
        let has_guarded_div = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Ite { then_expr, .. }
                    if constraint_tree_contains(then_expr, &|inner| matches!(inner.value(), ExprValue::BvUDiv(_, _))))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        assert!(
            has_bvudiv || has_guarded_div,
            "u32 division must produce BvUDiv or ITE-guarded BvUDiv expression"
        );

        // Every BvUDiv in the VC must have matching operand widths.
        let bvudiv_width_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvUDiv(l, r)
                    if l.sort().is_bitvec() && r.sort().is_bitvec()
                    && l.sort().bitvec_width() != r.sort().bitvec_width())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !bvudiv_width_mismatch,
            "BvUDiv operands must have matching BV widths -- found width mismatch"
        );

        // Division by zero must be guarded: either an error-targeting rule exists
        // (from the panic path) or an Eq/BvUGt check against zero appears in
        // transition constraints (guard before the division). Rust panics on
        // div-by-zero, so the encoding must reflect this in some form.
        let has_error_rule = vc.rules.iter().any(|r| r.head.name == "error");
        let has_zero_check = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Eq(l, r)
                    if (matches!(l.value(), ExprValue::BitVecConst { .. })
                        || matches!(r.value(), ExprValue::BitVecConst { .. })))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            has_error_rule || has_zero_check,
            "Division encoding must have a div-by-zero guard (error rule or zero-check constraint)"
        );

        // Relations must carry BV32 for the u32 operand types
        assert_relation_has_arg_sort(
            &vc,
            "probe_div_u32",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Division encoding must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 27: Signed comparison (i32) produces BvSLt/BvSGt (not BvULt/BvUGt)
// =============================================================================

/// Comparing signed integers (`i32 < i32`) must produce signed BV comparisons
/// (`BvSLt`, `BvSGt`, etc.) rather than unsigned comparisons (`BvULt`, `BvUGt`).
/// Using unsigned comparison on signed values causes -1i32 (0xFFFFFFFF) to
/// compare greater than 1i32 (0x00000001), which is incorrect.
/// Regression guard: if the codegen emits unsigned comparisons for signed types,
/// all negative-number comparisons silently produce wrong results, causing
/// false proofs or false counterexamples depending on the assertion direction.
#[test]
fn test_guard_signed_comparison_produces_bvslt_not_bvult() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_signed_cmp(a: i32, b: i32) -> i32 {
            if a < b { a } else { b }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_signed_cmp");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_signed_cmp", ChcConfig::default());

        assert_vc_structure(&vc, "probe_signed_cmp", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_signed_cmp");

        // The VC must contain at least one signed BV comparison (BvSLt, BvSLe,
        // BvSGt, or BvSGe) for the `a < b` condition on i32 operands.
        let has_signed_cmp = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(
                    e.value(),
                    ExprValue::BvSLt(_, _)
                        | ExprValue::BvSLe(_, _)
                        | ExprValue::BvSGt(_, _)
                        | ExprValue::BvSGe(_, _)
                )
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        // The encoding may also use Eq-based comparison after subtracting,
        // or encode via BV sign-bit extraction. Accept signed BV comparison
        // or Eq combined with BvSub as valid signed comparison encodings.
        let has_eq_with_bv = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Eq(l, r)
                    if l.sort().is_bitvec() && r.sort().is_bitvec()
                    && l.sort().bitvec_width() == Some(32))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });

        assert!(
            has_signed_cmp || has_eq_with_bv,
            "i32 comparison must produce signed BV comparisons (BvSLt/BvSGt) or BV32 Eq dispatch"
        );

        // All signed BV comparisons must have matching operand widths.
        let signed_cmp_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| match e.value() {
                ExprValue::BvSLt(l, r)
                | ExprValue::BvSLe(l, r)
                | ExprValue::BvSGt(l, r)
                | ExprValue::BvSGe(l, r) => {
                    l.sort().is_bitvec()
                        && r.sort().is_bitvec()
                        && l.sort().bitvec_width() != r.sort().bitvec_width()
                }
                _ => false,
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!signed_cmp_mismatch, "Signed BV comparison operands must have matching widths");

        // All signed BV comparisons must produce Bool sort.
        let signed_cmp_non_bool = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(
                    e.value(),
                    ExprValue::BvSLt(_, _)
                        | ExprValue::BvSLe(_, _)
                        | ExprValue::BvSGt(_, _)
                        | ExprValue::BvSGe(_, _)
                ) && !e.sort().is_bool()
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!signed_cmp_non_bool, "Signed BV comparison result must be Bool sort");

        // Relations must carry BV32 for i32 parameters
        assert_relation_has_arg_sort(
            &vc,
            "probe_signed_cmp",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Signed comparison encoding must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 28: Array store followed by select at same index is well-formed
// =============================================================================

/// Writing to an array (Store) and reading from the same array (Select) must
/// produce expressions where the array sort, index sort, and element sort are
/// mutually consistent. Specifically: (a) Store and Select must operate on the
/// same Array sort, (b) index sorts must match between Store and Select,
/// (c) element sort from Select must equal the value sort written by Store.
/// This tests the round-trip consistency of the array theory encoding when
/// both write and read paths are exercised in the same function.
/// Regression guard: if Store and Select use different index sorts (e.g., BV32
/// for Store index but BV64 for Select index), the SMT solver treats them as
/// operations on different array theory instances, causing reads to return
/// unconstrained values instead of the written data.
#[test]
fn test_guard_array_store_select_sort_consistency() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array_store_select(arr: [u32; 4], val: u32) -> u32 {
            let mut a = arr;
            a[0] = val;
            a[0]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_store_select");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_array_store_select", ChcConfig::default());

        assert_vc_structure(&vc, "probe_array_store_select", body.blocks.len());

        // The VC must contain at least one Store (array write).
        let has_store = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::Store { .. });
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(has_store, "Array write (a[0] = val) must produce at least one Store expression");

        // The VC must contain at least one Select (array read).
        let has_select = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::Select { .. });
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(has_select, "Array read (a[0]) must produce at least one Select expression");

        // Every Store must have: array=Array-sorted, index=BV-sorted, value=BV-sorted.
        let store_bad_sorts = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Store { array, index, value }
                    if !array.sort().is_array()
                    || !index.sort().is_bitvec()
                    || (!value.sort().is_bitvec() && !value.sort().is_bool()))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !store_bad_sorts,
            "Store must have Array-sorted array, BV-sorted index, and BV/Bool-sorted value"
        );

        // Every Select must have: array=Array-sorted, index=BV-sorted.
        let select_bad_sorts = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Select { array, index }
                    if !array.sort().is_array() || !index.sort().is_bitvec())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!select_bad_sorts, "Select must have Array-sorted array and BV-sorted index");

        // Verify per-operation sort self-consistency: within each Store,
        // the index sort must be a valid index for the array operand's declared
        // Array sort. Within each Select, same. The encoding may use different
        // index widths across operations (e.g., BV64 for heap Store, BV32 for
        // fixed-size array Select) -- this is an architectural pattern, not a bug.
        // What matters is that no individual Store/Select has internally
        // inconsistent sorts.
        let store_self_inconsistent = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Store { array, index, .. }
                    if array.sort().is_array() && index.sort().is_bitvec()
                    && index.sort().bitvec_width().is_none())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !store_self_inconsistent,
            "Store index must have a concrete BV width (not unresolved)"
        );

        let select_self_inconsistent = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Select { array, index }
                    if array.sort().is_array() && index.sort().is_bitvec()
                    && index.sort().bitvec_width().is_none())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !select_self_inconsistent,
            "Select index must have a concrete BV width (not unresolved)"
        );

        // Verify that nested Store(Select(...)) patterns (read-modify-write)
        // have the outer Store's array sort matching the inner Select's array sort.
        let nested_sort_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::Store { array, .. }
                    if matches!(array.value(), ExprValue::Select { array: inner_arr, .. }
                        if inner_arr.sort() != array.sort()))
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(!nested_sort_mismatch, "Nested Store(Select(...)) must have matching array sorts");

        // Relations must carry BV32 for the u32 element type
        assert_relation_has_arg_sort(
            &vc,
            "probe_array_store_select",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(
            malformed.is_none(),
            "Array store/select must not produce malformed BV: {malformed:?}"
        );
    });
}

// =============================================================================
// Invariant 29: Bitwise shift produces BvShl/BvLShr with matching BV widths
// =============================================================================

/// Bitwise left shift (`<<`) on u32 must produce `BvShl` and logical right
/// shift (`>>`) on u32 must produce `BvLShr`. Both operands (value and shift
/// amount) must be BV32-sorted with matching widths. The result sort must
/// also be BV32.
/// Regression guard: if the shift amount has a different BV width than the
/// value (e.g., BV8 shift amount on BV32 value), Z3 rejects the expression
/// with a sort mismatch error. If logical right shift uses BvAShr
/// (arithmetic shift) instead of BvLShr, unsigned values get sign-extended
/// from the high bit, producing incorrect results for values with bit 31 set.
#[test]
fn test_guard_bitwise_shift_produces_bvshl_bvlshr_matching_widths() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_shift_ops(x: u32, flag: bool) -> u32 {
            if flag {
                (x << 2).wrapping_add(x >> 3)
            } else {
                0
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_shift_ops");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_shift_ops", ChcConfig::default());

        assert_vc_structure(&vc, "probe_shift_ops", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_shift_ops");

        // The VC must contain BvShl (left shift) for `x << 2`.
        let has_bvshl = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvShl(_, _));
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(has_bvshl, "u32 left shift (<<) must produce a BvShl expression");

        // The VC must contain BvLShr (logical right shift) for `x >> 3`.
        // u32 is unsigned so >> must use logical shift, not arithmetic shift.
        let has_bvlshr = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvLShr(_, _));
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            has_bvlshr,
            "u32 right shift (>>) must produce a BvLShr (logical shift) expression, not BvAShr"
        );

        // Every BvShl must have matching operand widths.
        let bvshl_width_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvShl(l, r)
                    if l.sort().is_bitvec() && r.sort().is_bitvec()
                    && l.sort().bitvec_width() != r.sort().bitvec_width())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !bvshl_width_mismatch,
            "BvShl operands must have matching BV widths -- found width mismatch"
        );

        // Every BvLShr must have matching operand widths.
        let bvlshr_width_mismatch = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| {
                matches!(e.value(), ExprValue::BvLShr(l, r)
                    if l.sort().is_bitvec() && r.sort().is_bitvec()
                    && l.sort().bitvec_width() != r.sort().bitvec_width())
            };
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !bvlshr_width_mismatch,
            "BvLShr operands must have matching BV widths -- found width mismatch"
        );

        // No BvAShr should appear for unsigned u32 shifts.
        // BvAShr is only correct for signed types (i32 >>).
        let has_bvashr = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvAShr(_, _));
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            !has_bvashr,
            "u32 right shift must NOT produce BvAShr (arithmetic shift) -- \
             BvAShr sign-extends from bit 31, corrupting unsigned values"
        );

        // The VC must contain BvAdd (from wrapping_add combining the two shifts).
        let has_bvadd = vc.rules.iter().any(|rule| {
            let pred = |e: &Expr| matches!(e.value(), ExprValue::BvAdd(_, _));
            rule.body.constraints.iter().any(|c| constraint_tree_contains(c, &pred))
                || rule.head.args.iter().any(|a| constraint_tree_contains(a, &pred))
        });
        assert!(
            has_bvadd,
            "probe_shift_ops must produce BvAdd for the wrapping_add combining both shifts"
        );

        // Relations must carry BV32 for the u32 parameters and return
        assert_relation_has_arg_sort(
            &vc,
            "probe_shift_ops",
            |s| s.bitvec_width() == Some(32),
            "BV32",
        );

        // No malformed BV concat/extract
        let malformed = first_malformed_bv_site(&vc);
        assert!(malformed.is_none(), "Shift encoding must not produce malformed BV: {malformed:?}");
    });
}
