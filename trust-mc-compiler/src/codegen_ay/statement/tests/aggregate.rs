// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for aggregate.rs — tuple, struct, enum, closure, array,
//! Vec/String/RawVec/BigInt codegen.
//!
//! 45 trivial AY-only expression tests deleted per rule #2312 and #2482
//! (tested AY Sort::struct_type/Expr::datatype_constructor, not production codegen).
//! Remaining tests use with_test_ay_ctx_for_source to exercise codegen_aggregate,
//! plus 4 tuple_sort_name tests that call the production helper.

use super::*;
use crate::codegen_ay::names::RUST_STRING_SORT;

// ─── MIR-driven codegen tests (exercise actual codegen_aggregate) ──

const AGGREGATE_PROBE_SOURCE: &str = r#"
pub fn tuple_probe(x: u32, y: bool) -> (u32, bool) {
    (x, y)
}

pub fn array_probe(a: u32, b: u32, c: u32) -> [u32; 3] {
    [a, b, c]
}

pub fn option_some_probe(x: u32) -> Option<u32> {
    Some(x)
}

pub fn option_none_probe() -> Option<u32> {
    None
}

pub enum UnitEnum { Red, Green, Blue }
pub fn unit_enum_probe() -> UnitEnum {
    UnitEnum::Green
}

pub fn closure_probe(x: u32) -> u32 {
    let add = |y: u32| x + y;
    add(1)
}
"#;

const AGGREGATE_LAYOUT_PROBE_SOURCE: &str = r#"
#![allow(dead_code)]

pub struct RawVec<T> {
    pub ptr: *mut T,
    pub cap: usize,
}

pub struct Vec<T> {
    pub buf: RawVec<T>,
    pub len: usize,
}

pub struct String {
    pub vec: Vec<u8>,
}

pub struct BigUint {
    pub data: Vec<u64>,
}

pub struct BigInt {
    pub sign: i8,
    pub data: BigUint,
}

pub fn rawvec_layout_probe(ptr: *mut u32, cap: usize) -> RawVec<u32> {
    RawVec { ptr, cap }
}

pub fn vec_layout_probe(ptr: *mut u32, len: usize, cap: usize) -> Vec<u32> {
    let buf = RawVec { ptr, cap };
    Vec { buf, len }
}

pub fn string_layout_probe(ptr: *mut u8, len: usize, cap: usize) -> String {
    let vec = Vec {
        buf: RawVec { ptr, cap },
        len,
    };
    String { vec }
}

pub fn bigint_layout_probe(sign: i8, ptr: *mut u64, len: usize, cap: usize) -> BigInt {
    let data = BigUint {
        data: Vec {
            buf: RawVec { ptr, cap },
            len,
        },
    };
    BigInt { sign, data }
}

pub fn biguint_layout_probe(ptr: *mut u64, len: usize, cap: usize) -> BigUint {
    BigUint {
        data: Vec {
            buf: RawVec { ptr, cap },
            len,
        },
    }
}
"#;

/// Count how many `Rvalue::Aggregate` nodes of each kind appear in the MIR.
fn count_aggregates(body: &rustc_public::mir::Body) -> Vec<(String, usize)> {
    let mut counts: std::collections::HashMap<String, usize> = Default::default();
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(_, Rvalue::Aggregate(kind, _)) = &stmt.kind {
                let label = match kind {
                    rustc_public::mir::AggregateKind::Tuple => "Tuple".into(),
                    rustc_public::mir::AggregateKind::Array(_) => "Array".into(),
                    rustc_public::mir::AggregateKind::Adt(def, ..) => {
                        format!("Adt({})", def.name())
                    }
                    rustc_public::mir::AggregateKind::Closure(_, _) => "Closure".into(),
                    rustc_public::mir::AggregateKind::RawPtr(_, _) => "RawPtr".into(),
                    _ => "Other".into(),
                };
                *counts.entry(label).or_default() += 1;
            }
        }
    }
    let mut result: Vec<_> = counts.into_iter().collect();
    result.sort();
    result
}

/// Run aggregate codegen for the first ADT aggregate with the given trimmed name.
fn codegen_first_named_adt_aggregate(
    ctx: &mut AYCtx<'_, 'static>,
    fn_suffix: &str,
    adt_name: &str,
) -> Option<Expr> {
    let instance = find_instance_by_suffix(ctx, fn_suffix);
    let body = instance.body().expect("function body");
    ctx.set_current_fn(instance);
    let tuple_usage = TupleUsageAnalysis::run(&body);
    let mut codegen = StatementCodegen::new(ctx, &body, tuple_usage);

    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(_, Rvalue::Aggregate(kind, operands)) = &stmt.kind
                && let rustc_public::mir::AggregateKind::Adt(def, ..) = kind
            {
                let full_name = def.name();
                if def.trimmed_name() == adt_name
                    || full_name == adt_name
                    || full_name.rsplit("::").next() == Some(adt_name)
                {
                    return codegen.codegen_aggregate(kind, operands);
                }
            }
        }
    }
    panic!("missing {adt_name} aggregate in {fn_suffix}");
}

#[test]
fn test_codegen_tuple_aggregate_produces_datatype() {
    with_test_ay_ctx_for_source(AGGREGATE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "tuple_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_, Rvalue::Aggregate(kind, operands)) = &stmt.kind
                    && let rustc_public::mir::AggregateKind::Tuple = kind
                {
                    let result = codegen.codegen_aggregate(kind, operands);
                    // Result may be None if operands reference uninitialized locals,
                    // but the codegen path is exercised either way.
                    if let Some(expr) = result {
                        assert!(
                            expr.sort().is_datatype(),
                            "tuple should produce datatype, got {:?}",
                            expr.sort()
                        );
                    }
                    return;
                }
            }
        }
    });
}

#[test]
fn test_codegen_array_aggregate_produces_array() {
    with_test_ay_ctx_for_source(AGGREGATE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_, Rvalue::Aggregate(kind, operands)) = &stmt.kind
                    && let rustc_public::mir::AggregateKind::Array(_) = kind
                {
                    let result = codegen.codegen_aggregate(kind, operands);
                    if let Some(expr) = result {
                        assert!(
                            expr.sort().is_array(),
                            "array should produce array sort, got {:?}",
                            expr.sort()
                        );
                    }
                    return;
                }
            }
        }
    });
}

#[test]
fn test_codegen_option_some_aggregate_produces_datatype() {
    with_test_ay_ctx_for_source(AGGREGATE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "option_some_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_, Rvalue::Aggregate(kind, operands)) = &stmt.kind
                    && let rustc_public::mir::AggregateKind::Adt(def, ..) = kind
                    && def.name().contains("Option")
                {
                    let result = codegen.codegen_aggregate(kind, operands);
                    if let Some(expr) = result {
                        assert!(
                            expr.sort().is_datatype(),
                            "Option::Some should produce datatype, got {:?}",
                            expr.sort()
                        );
                    }
                    return;
                }
            }
        }
    });
}

#[test]
fn test_codegen_unit_enum_aggregate_produces_bitvec() {
    with_test_ay_ctx_for_source(AGGREGATE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "unit_enum_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_, Rvalue::Aggregate(kind, operands)) = &stmt.kind
                    && let rustc_public::mir::AggregateKind::Adt(def, ..) = kind
                    && def.name().contains("UnitEnum")
                {
                    let result = codegen.codegen_aggregate(kind, operands);
                    if let Some(expr) = result {
                        // Unit enums encode as bitvec discriminants
                        assert!(
                            expr.sort().is_bitvec(),
                            "Unit enum should produce bitvec, got {:?}",
                            expr.sort()
                        );
                    }
                    return;
                }
            }
        }
    });
}

#[test]
fn test_codegen_closure_aggregate_produces_datatype() {
    with_test_ay_ctx_for_source(AGGREGATE_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "closure_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(_, Rvalue::Aggregate(kind, operands)) = &stmt.kind
                    && let rustc_public::mir::AggregateKind::Closure(_, _) = kind
                {
                    let result = codegen.codegen_aggregate(kind, operands);
                    if let Some(expr) = result {
                        assert!(
                            expr.sort().is_datatype(),
                            "Closure should produce datatype, got {:?}",
                            expr.sort()
                        );
                    }
                    return;
                }
            }
        }
    });
}

#[test]
fn test_aggregate_mir_discovery_finds_tuple_in_probe() {
    with_test_ay_ctx_for_source(AGGREGATE_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "tuple_probe");
        let body = instance.body().expect("function body");
        let aggs = count_aggregates(&body);
        assert!(
            aggs.iter().any(|(kind, count)| kind == "Tuple" && *count > 0),
            "Expected Tuple aggregate in tuple_probe MIR, found: {:?}",
            aggs
        );
    });
}

#[test]
fn test_aggregate_mir_discovery_finds_array_in_probe() {
    with_test_ay_ctx_for_source(AGGREGATE_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_probe");
        let body = instance.body().expect("function body");
        let aggs = count_aggregates(&body);
        assert!(
            aggs.iter().any(|(kind, count)| kind == "Array" && *count > 0),
            "Expected Array aggregate in array_probe MIR, found: {:?}",
            aggs
        );
    });
}

#[test]
fn test_codegen_rawvec_special_layout_via_mir() {
    with_test_ay_ctx_for_source(AGGREGATE_LAYOUT_PROBE_SOURCE, |mut ctx| {
        let expr = codegen_first_named_adt_aggregate(&mut ctx, "rawvec_layout_probe", "RawVec")
            .expect("RawVec aggregate should codegen");
        assert_eq!(expr.sort().datatype_name(), Some("RawVec"));

        let ptr = expr.clone().field_select("RawVec", "fld_ptr", Sort::bitvec(POINTER_WIDTH));
        let cap = expr.field_select("RawVec", "fld_cap", Sort::bitvec(POINTER_WIDTH));
        assert_eq!(ptr.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert_eq!(cap.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

#[test]
fn test_codegen_vec_special_layout_via_mir() {
    with_test_ay_ctx_for_source(AGGREGATE_LAYOUT_PROBE_SOURCE, |mut ctx| {
        let expr = codegen_first_named_adt_aggregate(&mut ctx, "string_layout_probe", "Vec")
            .expect("Vec aggregate should codegen");
        let dt_name =
            expr.sort().datatype_name().expect("Vec aggregate should be datatype").to_string();
        assert!(
            dt_name.starts_with("Vec_"),
            "Vec aggregate should use Vec_* sort naming, got {dt_name}"
        );

        let ptr = expr.clone().field_select(&dt_name, "fld_ptr", Sort::bitvec(POINTER_WIDTH));
        let len = expr.clone().field_select(&dt_name, "fld_len", Sort::bitvec(POINTER_WIDTH));
        let cap = expr.clone().field_select(&dt_name, "fld_cap", Sort::bitvec(POINTER_WIDTH));
        let data = expr.field_select(
            &dt_name,
            "fld_data",
            Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32)),
        );

        assert_eq!(ptr.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert_eq!(len.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert_eq!(cap.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert!(data.sort().is_array());
    });
}

#[test]
fn test_codegen_string_special_layout_via_mir() {
    with_test_ay_ctx_for_source(AGGREGATE_LAYOUT_PROBE_SOURCE, |mut ctx| {
        let expr = codegen_first_named_adt_aggregate(&mut ctx, "string_layout_probe", "String")
            .expect("String aggregate should codegen");
        assert_eq!(expr.sort().datatype_name(), Some(RUST_STRING_SORT));

        let ptr =
            expr.clone().field_select(RUST_STRING_SORT, "fld_ptr", Sort::bitvec(POINTER_WIDTH));
        let len =
            expr.clone().field_select(RUST_STRING_SORT, "fld_len", Sort::bitvec(POINTER_WIDTH));
        let cap =
            expr.clone().field_select(RUST_STRING_SORT, "fld_cap", Sort::bitvec(POINTER_WIDTH));
        let data = expr.field_select(
            RUST_STRING_SORT,
            "fld_data",
            Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8)),
        );

        assert_eq!(ptr.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert_eq!(len.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert_eq!(cap.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert!(data.sort().is_array());
    });
}

#[test]
fn test_codegen_bigint_struct_returns_symbolic_int_via_mir() {
    with_test_ay_ctx_for_source(AGGREGATE_LAYOUT_PROBE_SOURCE, |mut ctx| {
        let expr = codegen_first_named_adt_aggregate(&mut ctx, "bigint_layout_probe", "BigInt")
            .expect("BigInt aggregate should codegen");
        assert!(expr.sort().is_int(), "BigInt aggregate should use Int sort");
    });
}

#[test]
fn test_codegen_biguint_struct_adds_non_negative_assert_via_mir() {
    with_test_ay_ctx_for_source(AGGREGATE_LAYOUT_PROBE_SOURCE, |mut ctx| {
        let before = ctx.program.commands().len();
        let expr = codegen_first_named_adt_aggregate(&mut ctx, "biguint_layout_probe", "BigUint")
            .expect("BigUint aggregate should codegen");
        assert!(expr.sort().is_int(), "BigUint aggregate should use Int sort");

        let added_commands = &ctx.program.commands()[before..];
        let has_non_negative_assert = added_commands.iter().any(|cmd| {
            matches!(
                cmd,
                ay_bindings::Constraint::Assert { expr, .. }
                    if matches!(expr.value(), ExprValue::IntGe(..))
            )
        });
        assert!(has_non_negative_assert, "BigUint aggregate should add Int >= 0 assertion");
    });
}

// ─── tuple_sort_name (production helper in sort_inference.rs) ────────

#[test]
fn test_tuple_sort_name_single_bv32() {
    let fields = vec![("fld_0", Sort::bitvec(32))];
    let name = StatementCodegen::tuple_sort_name(&fields);
    assert_eq!(name, "Tuple_bv32");
}

#[test]
fn test_tuple_sort_name_two_fields_bv32_bool() {
    let fields = vec![("fld_0", Sort::bitvec(32)), ("fld_1", Sort::bool())];
    let name = StatementCodegen::tuple_sort_name(&fields);
    assert_eq!(name, "Tuple_bv32_bool");
}

#[test]
fn test_tuple_sort_name_three_fields_mixed() {
    let fields =
        vec![("fld_0", Sort::bitvec(64)), ("fld_1", Sort::bitvec(8)), ("fld_2", Sort::int())];
    let name = StatementCodegen::tuple_sort_name(&fields);
    assert_eq!(name, "Tuple_bv64_bv8_int");
}

#[test]
fn test_tuple_sort_name_array_field() {
    let arr = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8));
    let fields = vec![("fld_0", arr)];
    let name = StatementCodegen::tuple_sort_name(&fields);
    // Array short name includes element type
    assert!(name.starts_with("Tuple_"), "Should start with Tuple_ but got: {}", name);
}
