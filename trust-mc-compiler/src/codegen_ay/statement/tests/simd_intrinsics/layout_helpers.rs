// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD layout and helper-function tests.
//!
//! Split from the SIMD intrinsic monolith per #3759.

use super::*;

fn assert_array_backed_lane_stores(rebuilt: &Expr, elements: &[Expr]) {
    let ExprValue::DatatypeConstructor { args, .. } = rebuilt.value() else {
        panic!("rebuilt SIMD should be a datatype constructor");
    };
    assert_eq!(args.len(), 1, "U32x4 constructor should have exactly one array field");

    let mut stores = Vec::new();
    let mut cursor = args[0].clone();
    while let ExprValue::Store { array, index, value } = cursor.value() {
        stores.push((index.clone(), value.clone()));
        cursor = array.clone();
    }
    stores.reverse();
    assert_eq!(
        stores.len(),
        elements.len(),
        "constructor should store exactly one value per SIMD lane"
    );

    for (lane, (index, value)) in stores.iter().enumerate() {
        match index.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, POINTER_WIDTH, "lane index should be POINTER_WIDTH-wide");
                assert_eq!(*value, BigInt::from(lane as u64), "wrong lane index stored");
            }
            other => panic!("expected bitvector lane index, got {other:?}"),
        }
        assert_eq!(
            value, &elements[lane],
            "stored lane value should match extracted element at lane {lane}"
        );
    }
}

#[test]
fn test_simd_layout_array_based_u32x4() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let arg_ty = body.arg_locals()[0].ty;
        let layout = codegen.simd_layout(arg_ty).expect("U32x4 should have a SIMD layout");
        assert_eq!(layout.lane_count(), 4, "U32x4 has 4 lanes");
        assert_eq!(layout.elem_width(), Some(32), "U32x4 elements are 32-bit");
    });
}

#[test]
fn test_simd_layout_signed_i32x4() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "shift_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let arg_ty = body.arg_locals()[0].ty;
        let layout = codegen.simd_layout(arg_ty).expect("I32x4 should have a SIMD layout");
        assert_eq!(layout.lane_count(), 4);
        assert_eq!(layout.elem_width(), Some(32));
    });
}

#[test]
fn test_simd_layout_u8x4() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "cast_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let arg_ty = body.arg_locals()[0].ty;
        let layout = codegen.simd_layout(arg_ty).expect("U8x4 should have a SIMD layout");
        assert_eq!(layout.lane_count(), 4);
        assert_eq!(layout.elem_width(), Some(8), "U8x4 elements are 8-bit");
    });
}

#[test]
fn test_simd_element_is_signed() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let u32x4_ty = body.arg_locals()[0].ty;
        assert!(!codegen.simd_element_is_signed(u32x4_ty), "U32x4 elements should be unsigned");
    });
}

#[test]
fn test_simd_element_is_signed_i32x4() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "shift_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let i32x4_ty = body.arg_locals()[0].ty;
        assert!(codegen.simd_element_is_signed(i32x4_ty), "I32x4 elements should be signed");
    });
}

#[test]
fn test_simd_layout_non_simd_returns_none() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "reduce_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let ret_ty = body.ret_local().ty;
        let layout = codegen.simd_layout(ret_ty);
        assert!(layout.is_none(), "u32 should not have a SIMD layout");
    });
}

#[test]
fn test_simd_extract_elements_produces_4_elements() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let arg_ty = body.arg_locals()[0].ty;
        let layout = codegen.simd_layout(arg_ty).expect("U32x4 layout");
        let arg_expr = codegen.codegen_operand(&local_operand(1)).expect("arg 1 expr");

        let elements = codegen
            .simd_extract_elements(&arg_expr, &layout)
            .expect("should extract elements from U32x4");
        assert_eq!(elements.len(), 4, "U32x4 should have 4 elements");
        for (i, elem) in elements.iter().enumerate() {
            assert_eq!(elem.sort().bitvec_width(), Some(32), "element {i} should be 32-bit bitvec");
        }
    });
}

#[test]
fn test_simd_construct_expr_roundtrip_u32x4() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let simd_ty = body.arg_locals()[0].ty;
        let layout = codegen.simd_layout(simd_ty).expect("U32x4 layout");
        let arg_expr = codegen.codegen_operand(&local_operand(1)).expect("arg 1 expr");
        let elements = codegen.simd_extract_elements(&arg_expr, &layout).expect("extract elements");

        let rebuilt = codegen
            .simd_construct_expr(elements.clone(), &layout, simd_ty)
            .expect("should reconstruct U32x4 from extracted elements");
        assert_eq!(rebuilt.sort(), arg_expr.sort(), "rebuilt SIMD expression should keep type");
        assert_array_backed_lane_stores(&rebuilt, &elements);
    });
}

#[test]
fn test_simd_construct_expr_rejects_short_array_lane_list() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bitwise_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let simd_ty = body.arg_locals()[0].ty;
        let layout = codegen.simd_layout(simd_ty).expect("U32x4 layout");
        let arg_expr = codegen.codegen_operand(&local_operand(1)).expect("arg 1 expr");
        let mut elements =
            codegen.simd_extract_elements(&arg_expr, &layout).expect("extract elements");
        elements.pop();

        let rebuilt = codegen.simd_construct_expr(elements, &layout, simd_ty);
        assert!(rebuilt.is_none(), "constructor should reject incorrect lane count");
    });
}

#[test]
fn test_simd_layout_multifield_u32x2() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "multifield_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let simd_ty = body.arg_locals()[0].ty;
        let layout = codegen.simd_layout(simd_ty).expect("U32x2 should infer MultiField layout");
        assert_eq!(layout.lane_count(), 2, "U32x2 should have two lanes");
        assert_eq!(layout.elem_width(), Some(32), "U32x2 elements should be 32-bit");
    });
}

#[test]
fn test_simd_layout_multifield_mixed_width_rejected() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "mixed_multifield_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let simd_ty = body.arg_locals()[0].ty;
        let layout = codegen.simd_layout(simd_ty);
        assert!(
            layout.is_none(),
            "Mixedx2(u32, u16) should be rejected because lanes have different sorts"
        );
    });
}

#[test]
fn test_simd_multifield_roundtrip_u32x2() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "multifield_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let simd_ty = body.arg_locals()[0].ty;
        let layout = codegen.simd_layout(simd_ty).expect("U32x2 layout");
        let arg_expr = codegen.codegen_operand(&local_operand(1)).expect("arg 1 expression");
        let elements = codegen.simd_extract_elements(&arg_expr, &layout).expect("extract lanes");
        assert_eq!(elements.len(), 2, "U32x2 should extract exactly 2 lanes");
        assert!(elements.iter().all(|elem| elem.sort().bitvec_width() == Some(32)));

        let rebuilt =
            codegen.simd_construct_expr(elements.clone(), &layout, simd_ty).expect("rebuild U32x2");
        let ExprValue::DatatypeConstructor { args, .. } = rebuilt.value() else {
            panic!("rebuilt U32x2 should be a datatype constructor");
        };
        assert_eq!(args.len(), 2, "U32x2 constructor should have two scalar lane fields");
        assert_eq!(args[0], elements[0], "lane 0 should be preserved by reconstruction");
        assert_eq!(args[1], elements[1], "lane 1 should be preserved by reconstruction");
    });
}

#[test]
fn test_simd_multifield_construct_rejects_short_lane_list() {
    with_test_ay_ctx_for_source(SIMD_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "multifield_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_arg_locals(&mut codegen, &body);

        let simd_ty = body.arg_locals()[0].ty;
        let layout = codegen.simd_layout(simd_ty).expect("U32x2 layout");
        let arg_expr = codegen.codegen_operand(&local_operand(1)).expect("arg 1 expression");
        let mut elements =
            codegen.simd_extract_elements(&arg_expr, &layout).expect("extract lanes");
        elements.pop();

        let rebuilt = codegen.simd_construct_expr(elements, &layout, simd_ty);
        assert!(rebuilt.is_none(), "constructor should reject missing MultiField lane");
    });
}
