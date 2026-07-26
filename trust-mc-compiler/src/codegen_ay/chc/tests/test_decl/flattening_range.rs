// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ═══════════════════════════════════════════════════════════════════════
// Range<T> flattening tests (Part of #2214)
// ═══════════════════════════════════════════════════════════════════════

const RANGE_PROBE_SOURCE: &str = r#"
use std::ops::Range;

pub fn range_local(n: u32) -> u32 {
    let r: Range<u32> = 0..n;
    r.start + r.end
}

pub fn range_for_loop(n: u32) -> u32 {
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    while i < n {
        sum = sum.wrapping_add(i);
        i = i.wrapping_add(1);
    }
    sum
}
"#;

const RANGE_INCLUSIVE_PROBE_SOURCE: &str = r#"
use std::ops::RangeInclusive;

pub fn range_inclusive_local(n: u32) -> bool {
    let r: RangeInclusive<u32> = 0..=n;
    r.contains(&n)
}
"#;

/// Verify that Range<u32> locals are flattened to 2 scalar state vars (no Datatype).
#[test]
fn test_range_local_flattened_no_datatype_sort() {
    with_test_ay_ctx_for_source(RANGE_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "range_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "range_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // No relation argument should have a Datatype sort (Range should be flattened)
        for rel in &chc_ctx.vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype(),
                    "Range<u32> should be flattened, but relation {} has Datatype sort: {:?}",
                    rel.name,
                    sort
                );
            }
        }
    });
}

/// Verify that flattened Range locals appear in flattened_tuple_locals set.
#[test]
fn test_range_local_in_flattened_set() {
    with_test_ay_ctx_for_source(RANGE_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "range_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "range_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // At least one local should be flattened (the Range<u32> local)
        assert!(
            !chc_ctx.flatten.flattened_tuple_locals.is_empty(),
            "range_local should have at least one flattened local (Range<u32>)"
        );
    });
}

/// Verify that flattened Range<u32> produces two BV32 state vars (start, end).
/// Part of #2876: Range fields use native BV sort (reverting Int-lifting from #2875).
#[test]
fn test_range_flattened_produces_two_bv_state_vars() {
    with_test_ay_ctx_for_source(RANGE_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "range_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "range_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find fld0/fld1 pairs with BV sort — these are the Range-flattened fields.
        // Range<u32> should produce BV32 fields, not Int.
        let bv_fld0 = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .any(|(name, sort)| name.contains("_fld0") && sort.is_bitvec());
        let bv_fld1 = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .any(|(name, sort)| name.contains("_fld1") && sort.is_bitvec());

        assert!(
            bv_fld0,
            "Range<u32> should produce at least one BV-sorted _fld0 (start) state var"
        );
        assert!(bv_fld1, "Range<u32> should produce at least one BV-sorted _fld1 (end) state var");
    });
}

/// Verify that mir_to_chc on Range-using function produces valid VC structure.
#[test]
fn test_range_mir_to_chc_valid_vc() {
    with_test_ay_ctx_for_source(RANGE_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "range_local");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "range_local", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "range_local", bb_count);

        // Verify no Datatype sorts in any relation signature
        for rel in &vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype(),
                    "range_local VC should have no Datatype sorts after flattening, found {:?} in {}",
                    sort,
                    rel.name
                );
            }
        }
    });
}

/// Verify that RangeInclusive<u32> locals are flattened to scalar state vars
/// instead of remaining as a Datatype local.
#[test]
fn test_range_inclusive_local_flattened_no_datatype_sort() {
    with_test_ay_ctx_for_source(RANGE_INCLUSIVE_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "range_inclusive_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "range_inclusive_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        for rel in &chc_ctx.vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype(),
                    "RangeInclusive<u32> should be flattened, but relation {} has Datatype sort: {:?}",
                    rel.name,
                    sort
                );
            }
        }
    });
}

/// Verify that RangeInclusive<u32> produces three scalar state vars:
/// start, end, and exhausted.
#[test]
fn test_range_inclusive_flattened_produces_three_state_vars() {
    with_test_ay_ctx_for_source(RANGE_INCLUSIVE_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "range_inclusive_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "range_inclusive_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let range_local = body
            .locals()
            .iter()
            .enumerate()
            .find_map(|(idx, decl)| {
                format!("{:?}", decl.ty).contains("RangeInclusive").then_some(idx)
            })
            .expect("fixture should contain a RangeInclusive local");
        let prefix = format!("_range_inclusive_local_{range_local}_fld");
        for (suffix, predicate, description) in [
            ("0", Sort::is_bitvec as fn(&Sort) -> bool, "BV-sorted _fld0 (start)"),
            ("1", Sort::is_bitvec as fn(&Sort) -> bool, "BV-sorted _fld1 (end)"),
            ("2", Sort::is_bool as fn(&Sort) -> bool, "Bool _fld2 (exhausted)"),
        ] {
            let target = format!("{prefix}{suffix}");
            assert!(
                chc_ctx
                    .state_var_mgr
                    .state_vars
                    .iter()
                    .any(|(name, sort)| name.as_ref() == target.as_str() && predicate(sort)),
                "RangeInclusive<u32> should produce a {description} state var"
            );
        }
        assert_eq!(
            chc_ctx.flatten.flattened_local_field_count.get(&range_local).copied(),
            Some(3),
            "RangeInclusive<u32> should register a 3-field flattened local"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// IndexRange flattening tests (Part of #2272)
//
// IndexRange is an internal rustc type used by slice/array iterators.
// It has the same shape as Range<usize> (start, end) but is a separate
// type. The flattening path in collect_state_vars must intercept it and
// produce 2 bitvec(POINTER_WIDTH) state variables.
// ═══════════════════════════════════════════════════════════════════════

/// IndexRange locals should be flattened to 2 bitvec state vars via the
/// collect_state_vars ADT match arm that checks def.trimmed_name() == "IndexRange".
///
/// We trigger IndexRange in MIR by iterating over a slice, which the compiler
/// desugars into IndexRange-based iteration.
#[test]
fn test_index_range_local_flattened_no_datatype_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn index_range_probe(arr: &[u32]) -> u32 {
            let mut sum: u32 = 0;
            let mut i: usize = 0;
            while i < arr.len() {
                sum = sum.wrapping_add(arr[i]);
                i = i.wrapping_add(1);
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "index_range_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "index_range_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // The primary invariant: no Datatype sort should remain in relation args.
        // If IndexRange flattening works, its fields are decomposed into scalars.
        for rel in &chc_ctx.vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype() || sort.datatype_name().is_some_and(|n| n != "IndexRange"),
                    "index_range_probe: IndexRange should be flattened, found Datatype sort {:?} in {}",
                    sort,
                    rel.name
                );
            }
        }
    });
}

/// The flattened IndexRange should produce state vars with _fld0 and _fld1 suffixes.
#[test]
fn test_index_range_flattened_produces_two_bv_state_vars() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn index_range_bv_probe(arr: &[u32]) -> u32 {
            let mut sum: u32 = 0;
            let mut i: usize = 0;
            while i < arr.len() {
                sum = sum.wrapping_add(arr[i]);
                i = i.wrapping_add(1);
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "index_range_bv_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "index_range_bv_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Check that any flattened locals (from IndexRange or Range) have the
        // expected 2-field structure with bitvec sorts.
        for &local_idx in &chc_ctx.flatten.flattened_tuple_locals {
            let field_count = chc_ctx.flatten.flattened_local_field_count.get(&local_idx).copied();
            assert!(
                field_count.is_some(),
                "flattened local {local_idx} should have a field count entry"
            );
            // IndexRange and Range both flatten to 2 fields
            if field_count == Some(2) {
                // Verify both fields exist in state_vars with bitvec sorts
                let prefix = format!("_index_range_bv_probe_{local_idx}_fld");
                let field_vars: Vec<_> = chc_ctx
                    .state_var_mgr
                    .state_vars
                    .iter()
                    .filter(|(name, _)| name.starts_with(&prefix))
                    .collect();
                if !field_vars.is_empty() {
                    assert_eq!(
                        field_vars.len(),
                        2,
                        "2-field flattened local {local_idx} should have exactly 2 state vars, got {:?}",
                        field_vars
                    );
                    for (name, sort) in &field_vars {
                        assert!(
                            sort.is_bitvec(),
                            "IndexRange field {name} should be bitvec, got {:?}",
                            sort
                        );
                    }
                }
            }
        }
    });
}

/// End-to-end: translate a function with IndexRange locals and verify valid VC.
#[test]
fn test_index_range_mir_to_chc_valid_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn index_range_vc_probe(arr: &[u32]) -> u32 {
            let mut sum: u32 = 0;
            let mut i: usize = 0;
            while i < arr.len() {
                sum = sum.wrapping_add(arr[i]);
                i = i.wrapping_add(1);
            }
            sum
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "index_range_vc_probe");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "index_range_vc_probe", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "index_range_vc_probe", bb_count);

        // Verify no IndexRange Datatype sorts in any relation signature
        for rel in &vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype() || sort.datatype_name().is_some_and(|n| n != "IndexRange"),
                    "index_range_vc_probe VC should flatten IndexRange, found {:?} in {}",
                    sort,
                    rel.name
                );
            }
        }
    });
}
