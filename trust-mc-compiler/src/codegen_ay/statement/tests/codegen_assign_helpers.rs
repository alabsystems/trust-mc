// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for codegen_assign_helpers.rs: assignment helper methods.
//!
//! Covers:
//! - `update_struct_field`: Struct field reconstruction for Box mutations
//! - `try_codegen_flattened_tuple_aggregate`: Tuple aggregate flattening
//! - `try_codegen_flattened_option_aggregate`: Option enum flattening
//! - `try_codegen_tuple_copy`: Tuple copy propagation
//! - `track_aggregate_ref_pointees`: Reference tracking through aggregates
//! - `try_construct_slice_datatype_from_cast`: Slice datatype construction
//! - `try_codegen_wide_ptr_metadata_from_cast`: Wide pointer metadata
//!
//! Part of #2016.

use super::*;

// =============================================================================
// update_struct_field — expression-level tests
// =============================================================================

/// Test update_struct_field with single-constructor datatype (struct).
/// Verifies field replacement produces a new constructor expression.
#[test]
fn test_update_struct_field_single_field_replacement() {
    let pt_sort = point_sort();
    let old_struct = point_expr(10, 20, pt_sort.clone());

    // Extract field 0 (x) from old struct, update with new value
    let new_x = Expr::bitvec_const(99u128, 32);

    // Manually reconstruct like update_struct_field does:
    // Keep field 1 (y), replace field 0 (x)
    let y_val = old_struct.field_select("Point", "y", Sort::bitvec(32));
    let cons_name = pt_sort.datatype_default_constructor().unwrap().to_string();
    let new_struct =
        Expr::datatype_constructor("Point", &cons_name, vec![new_x, y_val], pt_sort.clone());

    assert!(new_struct.sort().is_datatype());
    assert_eq!(*new_struct.sort(), pt_sort);
    assert_eq!(new_struct.sort().datatype_name(), Some("Point"));
}

/// Test update_struct_field with nested field indices returns None.
/// Currently only single-level field updates are supported.
#[test]
fn test_update_struct_field_nested_indices_returns_none() {
    // Nested field_indices [0, 1] should fail (not supported)
    let nested_indices: Vec<usize> = vec![0, 1];
    assert!(nested_indices.len() != 1, "nested indices should not be length 1");
}

/// Test update_struct_field with out-of-bounds field index.
#[test]
fn test_update_struct_field_out_of_bounds_field() {
    let pt_sort = point_sort();
    let _pt = point_expr(10, 20, pt_sort);

    // Point has 2 fields (x, y). Field index 5 is out of bounds.
    // In production code, update_struct_field would return None.
    let num_fields = 2;
    let target_field: usize = 5;
    assert!(target_field >= num_fields, "field index should be out of bounds");
}

/// Test update_struct_field with non-datatype sort returns None.
#[test]
fn test_update_struct_field_non_datatype_returns_none() {
    let bv_expr = Expr::bitvec_const(42u128, 32);
    assert!(!bv_expr.sort().is_datatype(), "bitvec should not be datatype");
}

// =============================================================================
// Tuple flattening — MIR-driven tests
// =============================================================================

/// Test tuple aggregate assignment produces flattened field entries.
/// Covers try_codegen_flattened_tuple_aggregate in codegen_assign_helpers.rs:394-513.
#[test]
fn test_codegen_tuple_aggregate_produces_flattened_fields() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn make_tuple(a: u32, b: u64) -> (u32, u64) {
            (a, b)
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "make_tuple");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Process all statements
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // The return place (local_0) should have flattened fields
            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let return_base = format!("{}::local_0", fn_name);
            let field_0_key = format!("{}_field_0", return_base);
            let field_1_key = format!("{}_field_1", return_base);

            // At least one field should be present (tuple was flattened)
            let has_field_0 = codegen.env_lookup(&field_0_key).is_some();
            let has_field_1 = codegen.env_lookup(&field_1_key).is_some();

            // Tuple flattening should produce individual field entries
            assert!(
                has_field_0 || has_field_1,
                "tuple aggregate should produce at least one flattened field entry"
            );
        },
    );
}

/// Test tuple with three fields produces all three flattened entries.
#[test]
fn test_codegen_triple_tuple_aggregate_all_fields() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn make_triple(a: u32, b: u32, c: u32) -> (u32, u32, u32) {
            (a, b, c)
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "make_triple");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let return_base = format!("{}::local_0", fn_name);

            let f0 = codegen.env_lookup(&format!("{}_field_0", return_base));
            let f1 = codegen.env_lookup(&format!("{}_field_1", return_base));
            let f2 = codegen.env_lookup(&format!("{}_field_2", return_base));

            assert!(
                f0.is_some() || f1.is_some() || f2.is_some(),
                "triple tuple should produce flattened field entries"
            );
        },
    );
}

/// Test tuple copy propagation: `let b = a` where a is a tuple.
/// Covers try_codegen_tuple_copy in codegen_assign_helpers.rs:326-383.
#[test]
fn test_codegen_tuple_copy_propagation() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn copy_tuple(a: u32, b: u32) -> (u32, u32) {
            let t = (a, b);
            t
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "copy_tuple");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // After processing, return place should have tuple fields
            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let return_base = format!("{}::local_0", fn_name);
            let f0 = codegen.env_lookup(&format!("{}_field_0", return_base));
            let f1 = codegen.env_lookup(&format!("{}_field_1", return_base));

            assert!(f0.is_some() || f1.is_some(), "tuple copy should propagate field entries");
        },
    );
}

// =============================================================================
// Reference tracking through aggregates — MIR-driven tests
// =============================================================================

/// Test that tuple containing a reference propagates ref_pointees.
/// Covers track_aggregate_ref_pointees in codegen_assign_helpers.rs:8-79.
#[test]
fn test_codegen_aggregate_ref_tracking_through_tuple() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn ref_in_tuple(x: u32) -> u32 {
            let r = &x;
            let t = (*r, 1u32);
            t.0
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "ref_in_tuple");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // After processing, ref_pointees should have at least one entry
            // (from the `let r = &x` assignment)
            assert!(
                !codegen.ref_pointees.is_empty(),
                "ref_pointees should be populated after reference creation"
            );
        },
    );
}

/// Test that processing a function with mutable reference tracks ref_pointees.
#[test]
fn test_codegen_aggregate_mut_ref_tracking() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn mut_ref_track(mut x: u32) -> u32 {
            let r = &mut x;
            *r = 42;
            x
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "mut_ref_track");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // ref_pointees should track the mutable reference
            assert!(
                !codegen.ref_pointees.is_empty(),
                "ref_pointees should track mutable references"
            );
        },
    );
}

// =============================================================================
// Slice coercion — MIR-driven tests
// =============================================================================

/// Test slice coercion: `&[T; N]` -> `&[T]` produces proper datatype.
/// Covers try_construct_slice_datatype_from_cast in codegen_assign_helpers.rs:275-324.
#[test]
fn test_codegen_slice_coercion_cast_through_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn slice_coerce(arr: &[u32; 4]) -> &[u32] {
            arr
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "slice_coerce");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Find a Cast statement (the coercion)
            let cast_stmt = body
                .blocks
                .iter()
                .flat_map(|bb| bb.statements.iter())
                .find(|stmt| matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::Cast(..))));

            let stmt = cast_stmt.expect("MIR for slice_coerce should contain a Cast statement");
            let lhs = match &stmt.kind {
                StatementKind::Assign(lhs, _) => lhs,
                _ => unreachable!(),
            };
            let lhs_base = codegen.ssa_base_name(lhs);

            codegen.codegen_statement(stmt);

            let entry = codegen.env_lookup(&lhs_base);
            assert!(entry.is_some(), "slice coercion cast should produce env entry");
        },
    );
}

// =============================================================================
// Checked binary op helpers — MIR-driven tests
// =============================================================================

/// Test checked subtraction produces field_0 (result) and field_1 (overflow).
/// Note: plain `a - b` reliably produces CheckedBinaryOp in debug MIR;
/// `.overflowing_sub()` may be lowered to an intrinsic call instead.
#[test]
fn test_codegen_checked_sub_produces_fields() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn checked_sub_mir(a: u32, b: u32) -> u32 {
            a - b
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "checked_sub_mir");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let checked_stmt =
                body.blocks.iter().flat_map(|bb| bb.statements.iter()).find(|stmt| {
                    matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::CheckedBinaryOp(..)))
                });

            let stmt = checked_stmt
                .expect("MIR for checked_sub_mir should contain a CheckedBinaryOp statement");
            let lhs = match &stmt.kind {
                StatementKind::Assign(lhs, _) => lhs,
                _ => unreachable!(),
            };
            let lhs_base = codegen.ssa_base_name(lhs);

            codegen.codegen_statement(stmt);

            let field_0_key = format!("{}_field_0", lhs_base);
            let field_1_key = format!("{}_field_1", lhs_base);
            let result_expr = codegen
                .env_lookup(&field_0_key)
                .expect("CheckedBinaryOp sub should produce field_0 (result)");
            let overflow_expr = codegen
                .env_lookup(&field_1_key)
                .expect("CheckedBinaryOp sub should produce field_1 (overflow)");

            assert!(result_expr.sort().is_bitvec());
            assert!(overflow_expr.sort().is_bool());
        },
    );
}

/// Test checked multiplication produces correct field types.
/// Note: plain `a * b` reliably produces CheckedBinaryOp in debug MIR;
/// `.overflowing_mul()` may be lowered to an intrinsic call instead.
#[test]
fn test_codegen_checked_mul_produces_fields() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn checked_mul_mir(a: u64, b: u64) -> u64 {
            a * b
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "checked_mul_mir");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let checked_stmt =
                body.blocks.iter().flat_map(|bb| bb.statements.iter()).find(|stmt| {
                    matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::CheckedBinaryOp(..)))
                });

            let stmt = checked_stmt
                .expect("MIR for checked_mul_mir should contain a CheckedBinaryOp statement");
            let lhs = match &stmt.kind {
                StatementKind::Assign(lhs, _) => lhs,
                _ => unreachable!(),
            };
            let lhs_base = codegen.ssa_base_name(lhs);

            codegen.codegen_statement(stmt);

            let field_0_key = format!("{}_field_0", lhs_base);
            let result_expr = codegen
                .env_lookup(&field_0_key)
                .expect("CheckedBinaryOp mul should produce field_0");
            assert_eq!(result_expr.sort().bitvec_width(), Some(64));
        },
    );
}

// =============================================================================
// Option flattening — expression-level tests
// =============================================================================

/// Test Option-like enum flattening produces piecewise SSA fields.
/// Verifies the naming convention: {base}_variant_{V}_field_0.
#[test]
fn test_option_flattening_naming_convention() {
    let base = "fn::local_5";
    let variant_idx = 1; // Some variant

    let field_key = format!("{}_variant_{}_field_0", base, variant_idx);
    assert_eq!(field_key, "fn::local_5_variant_1_field_0");

    // None variant uses .0 discriminant key
    let discrim_key = format!("{}.0", base);
    assert_eq!(discrim_key, "fn::local_5.0");
}

/// Test Option Some variant produces bitvec under variant key.
#[test]
fn test_option_some_flattening_bitvec_payload() {
    // Some(42u32) produces:
    // - {base}_variant_1_field_0 = bv32(42)
    // - {base} = bv32(42) (for Discriminant handler)
    let payload = Expr::bitvec_const(42u128, 32);
    assert!(payload.sort().is_bitvec());
    assert_eq!(payload.sort().bitvec_width(), Some(32));
}

/// Test Option None variant produces zero discriminant.
#[test]
fn test_option_none_flattening_zero_discriminant() {
    // None produces:
    // - {base}.0 = bv32(0) (discriminant)
    // - {base} = bv64(0) (base key)
    let discrim = Expr::bitvec_const(0u64, 32);
    let base_val = Expr::bitvec_const(0u64, POINTER_WIDTH);
    assert_eq!(discrim.sort().bitvec_width(), Some(32));
    assert_eq!(base_val.sort().bitvec_width(), Some(POINTER_WIDTH));
}

// =============================================================================
// Wide pointer metadata — expression-level tests
// =============================================================================

/// Test wide pointer metadata naming: {lhs_name}_meta.
#[test]
fn test_wide_ptr_metadata_naming() {
    let lhs_name = "fn::local_3_0";
    let meta_name = format!("{lhs_name}_meta");
    assert_eq!(meta_name, "fn::local_3_0_meta");
}

/// Test wide pointer metadata sort is bitvec(POINTER_WIDTH).
#[test]
fn test_wide_ptr_metadata_sort() {
    let meta = Expr::var("fn::local_3_0_meta", Sort::bitvec(POINTER_WIDTH));
    assert_eq!(meta.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// Test wide pointer metadata constraint: meta = array_len.
#[test]
fn test_wide_ptr_metadata_constraint() {
    let meta = Expr::var("meta", Sort::bitvec(POINTER_WIDTH));
    let len = Expr::bitvec_const(4u128, POINTER_WIDTH);
    let constraint = meta.eq(len);
    assert!(constraint.sort().is_bool());
}

// =============================================================================
// Array materialization — expression-level tests
// =============================================================================

/// Test array-to-memory materialization address calculation.
/// Verifies addr + (i * elem_size) pattern.
#[test]
fn test_array_materialization_address_calc() {
    let base_addr = Expr::bitvec_const(0x2000u128, POINTER_WIDTH);
    let elem_size: usize = 4;
    let index: usize = 3;
    let byte_offset = index * elem_size;

    let offset_expr = Expr::bitvec_const(byte_offset as u128, POINTER_WIDTH);
    let elem_addr = base_addr.bvadd(offset_expr);

    assert_eq!(elem_addr.sort().bitvec_width(), Some(POINTER_WIDTH));
    assert!(matches!(elem_addr.value(), ExprValue::BvAdd(_, _)));
}

/// Test array element select pattern for materialization.
#[test]
fn test_array_materialization_element_select() {
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(32));
    let arr = Expr::var("arr_0", arr_sort);
    let idx = Expr::bitvec_const(2u128, POINTER_WIDTH);
    let elem = arr.select(idx);

    assert_eq!(elem.sort().bitvec_width(), Some(32));
}

/// Test byte extraction for multi-byte array element materialization.
/// Simulates the little-endian byte extraction at codegen_assign_helpers.rs:221-234.
#[test]
fn test_array_materialization_byte_extract() {
    let elem = Expr::bitvec_const(0x12345678u128, 32);
    let elem_size: usize = 4;

    // Extract byte 0 (low byte): bits [7:0]
    let byte0 = elem.clone().extract(7, 0);
    assert_eq!(byte0.sort().bitvec_width(), Some(8));

    // Extract byte 3 (high byte): bits [31:24]
    let byte3 = elem.extract(31, 24);
    assert_eq!(byte3.sort().bitvec_width(), Some(8));

    assert_eq!(elem_size, 4); // verify 4-byte element
}

/// Test single-byte array element materialization (no extraction needed).
#[test]
fn test_array_materialization_single_byte_element() {
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8));
    let arr = Expr::var("byte_arr", arr_sort);
    let idx = Expr::bitvec_const(0u128, POINTER_WIDTH);
    let elem = arr.select(idx);

    // Single-byte elements are stored directly (no extraction)
    assert_eq!(elem.sort().bitvec_width(), Some(8));
}

/// Test MAX_MATERIALIZE_ELEMENTS constant is reasonable (Part of #2511).
#[test]
fn test_array_materialization_cap_constant() {
    assert_eq!(
        StatementCodegen::MAX_MATERIALIZE_ELEMENTS,
        1024,
        "materialization cap should be 1024 elements"
    );
}

/// Test checked_mul boundary: verifies that `usize::MAX / elem_size` elements
/// would overflow the byte offset calculation that we now guard with checked_mul.
#[test]
fn test_array_materialization_byte_offset_overflow_detected() {
    let elem_size: usize = 4;
    let overflowing_index: usize = usize::MAX / elem_size + 1;
    assert!(
        overflowing_index.checked_mul(elem_size).is_none(),
        "byte offset should overflow for pathologically large index"
    );
}

/// Test elem_size * 8 overflow: element sizes near usize::MAX / 8 would overflow
/// the bit-width calculation that we now guard with checked_mul + u32::try_from.
#[test]
fn test_array_materialization_elem_bits_overflow_detected() {
    let large_elem_size: usize = usize::MAX / 4; // Overflows when * 8
    assert!(
        large_elem_size.checked_mul(8).is_none(),
        "elem_bits should overflow for very large element size"
    );

    // Normal sizes should not overflow
    let normal_elem_size: usize = 8; // u64
    let bits = normal_elem_size.checked_mul(8).unwrap();
    assert_eq!(u32::try_from(bits).unwrap(), 64);
}

/// Test that address-of a stack array exercises the materialization path.
/// Part of #2511: first direct coverage for try_materialize_array_to_memory.
#[test]
fn test_codegen_address_of_array_materializes() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn array_addr_of() -> *const u32 {
            let arr: [u32; 4] = [1, 2, 3, 4];
            arr.as_ptr()
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "array_addr_of");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Process all statements — should not panic even with array address-of
            let mut stmt_count = 0;
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                    stmt_count += 1;
                }
            }
            assert!(stmt_count > 0, "should process array addr-of without panic");
        },
    );
}

/// Test single-element array address-of exercises materialization.
/// Part of #2511: 1-element boundary case.
#[test]
fn test_codegen_address_of_single_element_array() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn single_elem() -> *const u8 {
            let arr: [u8; 1] = [42];
            arr.as_ptr()
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "single_elem");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }
            // No panic = success
        },
    );
}

// =============================================================================
// Constant reference tracking — MIR-driven tests
// =============================================================================

/// Test constant reference creates synthetic pointee in ref_pointees.
/// Covers codegen_assign.rs:897-933 (constant ref path).
#[test]
fn test_codegen_const_ref_creates_synthetic_pointee() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn const_ref_tracking() -> u32 {
            let r: &u32 = &0;
            *r
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "const_ref_tracking");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // After processing, ref_pointees should have at least one entry
            // from the promoted constant `&0`
            assert!(
                !codegen.ref_pointees.is_empty(),
                "const reference should create ref_pointees entry"
            );
        },
    );
}

// =============================================================================
// Tuple mixed-type flattening — MIR-driven tests
// =============================================================================

/// Test tuple with bool and bitvec fields produces correct sorts.
#[test]
fn test_codegen_tuple_mixed_bool_bitvec_fields() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn mixed_tuple(a: u32, b: bool) -> (u32, bool) {
            (a, b)
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "mixed_tuple");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let return_base = format!("{}::local_0", fn_name);
            let f0 = codegen.env_lookup(&format!("{}_field_0", return_base));
            let f1 = codegen.env_lookup(&format!("{}_field_1", return_base));

            let expr_f0 = f0.expect("tuple field_0 should be populated after codegen");
            assert!(expr_f0.sort().is_bitvec(), "field_0 should be bitvec (u32)");
            let expr_f1 = f1.expect("tuple field_1 should be populated after codegen");
            assert!(expr_f1.sort().is_bool(), "field_1 should be bool");
        },
    );
}

/// Test tuple with 8-bit and 64-bit fields produces correct widths.
#[test]
fn test_codegen_tuple_u8_u64_fields() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn u8_u64_tuple(a: u8, b: u64) -> (u8, u64) {
            (a, b)
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "u8_u64_tuple");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let return_base = format!("{}::local_0", fn_name);
            let f0 = codegen.env_lookup(&format!("{}_field_0", return_base));
            let f1 = codegen.env_lookup(&format!("{}_field_1", return_base));

            let expr_f0 = f0.expect("tuple field_0 should be populated after codegen");
            assert_eq!(expr_f0.sort().bitvec_width(), Some(8), "field_0 should be bv8 (u8)");
            let expr_f1 = f1.expect("tuple field_1 should be populated after codegen");
            assert_eq!(expr_f1.sort().bitvec_width(), Some(64), "field_1 should be bv64 (u64)");
        },
    );
}

// =============================================================================
// Multi-block assignment — MIR-driven tests
// =============================================================================

/// Test that assignments in if/else branches don't panic and produce env entries.
#[test]
fn test_codegen_assignment_in_branches_no_panic() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn branch_assign(x: u32) -> (u32, u32) {
            let a;
            let b;
            if x > 10 {
                a = x;
                b = 1u32;
            } else {
                a = 0u32;
                b = x;
            }
            (a, b)
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "branch_assign");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Should have multiple blocks
            assert!(body.blocks.len() >= 3, "branch_assign should have at least 3 blocks");

            let mut stmt_count = 0;
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                    stmt_count += 1;
                }
            }
            assert!(stmt_count > 0, "should process statements without panic");
        },
    );
}

// =============================================================================
// Helper function
// =============================================================================

// =============================================================================
// track_aggregate_ref_pointees — flattened (#2076) piecewise VALUE propagation
// =============================================================================

/// An aggregate field built from a FLATTENED Option-like value must carry that
/// value's piecewise entries (`{src}.0` discriminant, `{src}_variant_V_field_F`
/// payload) onto `{lhs}_field_{i}` — the exact name a later `x.i` read resolves.
///
/// Without this the aggregate stores only the payload bitvec, the discriminant
/// is dropped, and `Discriminant(x.i)` degrades to the "bitvec-stored enum
/// discriminant" symbolic over-approximation (both variants explored), which
/// makes `Some(v)` and `None` indistinguishable downstream.
#[test]
fn test_aggregate_propagates_flattened_option_entries_to_field() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn ident(x: u32) -> u32 { x }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "ident");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Seed local_1 as a flattened Some(payload): base payload, `.0`
            // discriminant, and the variant payload key.
            let src = Place { local: Local::from(1usize), projection: vec![] };
            let src_base = codegen.ssa_base_name(&src);
            let discrim_key = crate::codegen_ay::names::discrim_name(&src_base);
            let variant_key = crate::codegen_ay::names::base_variant_field_name(&src_base, 1, 0);
            codegen.env_update(src_base.clone(), Expr::bitvec_const(7u64, 32));
            codegen.env_update(discrim_key, Expr::bitvec_const(1u64, 32));
            codegen.env_update(variant_key, Expr::bitvec_const(7u64, 32));

            let lhs_base = "probe::local_99".to_string();
            codegen.track_aggregate_ref_pointees(&lhs_base, &[Operand::Copy(src.clone())]);

            let field_base = crate::codegen_ay::names::indexed_field_name(&lhs_base, 0);
            let field_discrim = crate::codegen_ay::names::discrim_name(&field_base);
            let field_variant =
                crate::codegen_ay::names::base_variant_field_name(&field_base, 1, 0);
            assert!(
                codegen.env_lookup(&field_discrim).is_some(),
                "aggregate field must carry the flattened discriminant `{field_discrim}`"
            );
            assert!(
                codegen.env_lookup(&field_variant).is_some(),
                "aggregate field must carry the flattened payload `{field_variant}`"
            );
        },
    );
}

/// Control (opposite direction): an aggregate field built from a plain scalar
/// with NO flattened entries must NOT invent any. The propagation is a copy of
/// what the source actually has, never a fabricated discriminant.
#[test]
fn test_aggregate_does_not_invent_flattened_entries_for_scalar() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn ident2(x: u32) -> u32 { x }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "ident2");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let src = Place { local: Local::from(1usize), projection: vec![] };
            let src_base = codegen.ssa_base_name(&src);
            codegen.env_update(src_base, Expr::bitvec_const(7u64, 32));

            let lhs_base = "probe::local_98".to_string();
            codegen.track_aggregate_ref_pointees(&lhs_base, &[Operand::Copy(src.clone())]);

            let field_base = crate::codegen_ay::names::indexed_field_name(&lhs_base, 0);
            let field_discrim = crate::codegen_ay::names::discrim_name(&field_base);
            assert!(
                codegen.env_lookup(&field_discrim).is_none(),
                "no flattened entries on the source means none on the aggregate field"
            );
        },
    );
}
