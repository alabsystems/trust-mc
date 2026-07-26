// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Allocation, layout, and NonNull helper tests.
//
// Extracted from regression.rs per #1734.

use super::*;

// Unit tests for allocation codegen functions (Part of #1320)
// =============================================================================

const ALLOC_MIR_PROBE_SOURCE: &str = r#"
use core::alloc::Layout;

pub fn alloc_probe(size: usize, align: usize, ptr: *mut u8) -> *mut u8 {
    if size > align { ptr } else { core::ptr::null_mut() }
}

pub fn layout_probe(layout: Layout, size: usize, align: usize) -> usize {
    layout.size().wrapping_add(size).wrapping_add(align)
}

pub fn option_probe(ptr: *mut u8, len: usize, opt: Option<*mut u8>) -> *mut u8 {
    match opt {
        Some(p) if len > 0 => p,
        _ => ptr,
    }
}

pub fn bool_probe(flag: bool) -> bool {
    !flag
}
"#;

fn seed_alloc_arg_locals(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    body: &rustc_public::mir::Body,
) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let place = local_place(local_idx);
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("alloc_arg_{local_idx}"), sort));
        }
    }
}

#[test]
fn test_codegen_alloc_dealloc_realloc_mir_paths() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_arg_locals(&mut codegen, &body);

        let destination = local_place(0);

        assert_eq!(
            codegen.codegen_rust_alloc(
                &[local_operand(1), local_operand(2)],
                &destination,
                Some(11)
            ),
            Some(11)
        );
        assert_eq!(
            codegen.codegen_rust_alloc_zeroed(
                &[local_operand(1), local_operand(2)],
                &destination,
                Some(12)
            ),
            Some(12)
        );
        assert_eq!(
            codegen.codegen_rust_dealloc(
                &[local_operand(3), local_operand(1), local_operand(2)],
                Some(13)
            ),
            Some(13)
        );
        assert_eq!(
            codegen.codegen_rust_realloc(
                &[local_operand(3), local_operand(1), local_operand(2), local_operand(1)],
                &destination,
                Some(14)
            ),
            Some(14)
        );

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert_eq!(assigned.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

#[test]
fn test_codegen_layout_helpers_mir_paths() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "layout_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_arg_locals(&mut codegen, &body);

        let layout_base = codegen.ssa_base_name(&local_place(1));
        let layout_expr = codegen.create_layout_struct(
            Expr::bitvec_const(64, POINTER_WIDTH),
            Expr::bitvec_const(8, POINTER_WIDTH),
        );
        codegen.env_update(layout_base, layout_expr);

        let destination = local_place(0);
        assert_eq!(
            codegen.codegen_layout_size(&[local_operand(1)], &destination, Some(21)),
            Some(21)
        );
        assert_eq!(
            codegen.codegen_layout_align(&[local_operand(1)], &destination, Some(22)),
            Some(22)
        );
        assert_eq!(
            codegen.codegen_layout_from_size_align_unchecked(
                &[local_operand(2), local_operand(3)],
                &destination,
                Some(23)
            ),
            Some(23)
        );
        assert_eq!(
            codegen.codegen_layout_dangling(&[local_operand(1)], &destination, Some(24)),
            Some(24)
        );

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert_eq!(assigned.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

#[test]
fn test_codegen_layout_is_size_align_valid_sets_bool_destination() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_arg_locals(&mut codegen, &body);

        let destination = local_place(0);
        assert_eq!(codegen.codegen_layout_is_size_align_valid(&destination, Some(31)), Some(31));

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert!(assigned.sort().is_bool());
    });
}

#[test]
fn test_codegen_nonnull_option_try_branch_and_allocator_paths() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "option_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_arg_locals(&mut codegen, &body);

        let option_base = codegen.ssa_base_name(&local_place(3));
        codegen.env_update(option_base, Expr::bitvec_const(0x2200, POINTER_WIDTH));

        let destination = local_place(0);
        assert_eq!(
            codegen.codegen_nonnull_new(&[local_operand(1)], &destination, Some(41)),
            Some(41)
        );
        assert_eq!(
            codegen.codegen_nonnull_slice_from_raw_parts(
                &[local_operand(1), local_operand(2)],
                &destination,
                Some(42)
            ),
            Some(42)
        );
        assert_eq!(
            codegen.codegen_option_ok_or(&[local_operand(3)], &destination, Some(43)),
            Some(43)
        );
        assert_eq!(
            codegen.codegen_nonnull_as_nonnull_ptr(&[local_operand(1)], &destination, Some(44)),
            Some(44)
        );
        assert_eq!(
            codegen.codegen_try_branch(&[local_operand(1)], &destination, Some(45)),
            Some(45)
        );

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert_eq!(assigned.sort().bitvec_width(), Some(POINTER_WIDTH));
    });

    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "layout_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_arg_locals(&mut codegen, &body);

        let layout_base = codegen.ssa_base_name(&local_place(1));
        let layout_expr = codegen.create_layout_struct(
            Expr::bitvec_const(32, POINTER_WIDTH),
            Expr::bitvec_const(8, POINTER_WIDTH),
        );
        codegen.env_update(layout_base, layout_expr);

        let destination = local_place(0);
        assert_eq!(
            codegen.codegen_allocator_allocate(
                &[local_operand(2), local_operand(1)],
                &destination,
                Some(46)
            ),
            Some(46)
        );

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert_eq!(assigned.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}
// Trivial expression-pattern-only tests removed per org rule (#2312):
// "Tests that only construct library types and assert their properties are
// trivial." Deleted: test_heap_alloc_returns_pointer_width,
// test_alloc_size_align_width, test_realloc_fresh_pointer,
// test_dealloc_pointer_pattern, test_layout_struct_sort,
// test_layout_size_extraction. Production-path coverage retained in
// MIR-backed tests above.

/// Test Layout::dangling extracts alignment from Layout self argument (#3412).
/// For align=16, dangling pointer should be 16 (not hardcoded 0x8).
#[test]
fn test_layout_dangling_uses_layout_alignment() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "layout_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_arg_locals(&mut codegen, &body);

        // Create Layout with align=16 (e.g., repr(align(16)) struct)
        let layout_base = codegen.ssa_base_name(&local_place(1));
        let layout_expr = codegen.create_layout_struct(
            Expr::bitvec_const(32, POINTER_WIDTH),
            Expr::bitvec_const(16, POINTER_WIDTH),
        );
        codegen.env_update(layout_base, layout_expr);

        let destination = local_place(0);
        let result = codegen.codegen_layout_dangling(&[local_operand(1)], &destination, Some(24));
        assert_eq!(result, Some(24));

        // bind_ssa_result stores an SSA Var in env; verify sort is pointer-width
        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base).expect("destination assigned");
        assert_eq!(
            assigned.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "dangling pointer must be pointer-width bitvec"
        );
    });
}

/// Test Layout::dangling with no args falls back to 0x8 (defensive).
#[test]
fn test_layout_dangling_no_args_fallback() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "layout_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let destination = local_place(0);
        let result = codegen.codegen_layout_dangling(&[], &destination, Some(25));
        assert_eq!(result, Some(25), "dangling with empty args should still succeed");

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base).expect("destination assigned");
        assert_eq!(assigned.sort().bitvec_width(), Some(POINTER_WIDTH));
    });
}

#[test]
fn test_layout_dangling_extra_checks_invalidates_provenance() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        ctx.config.extra_pointer_checks = true;
        let instance = find_instance_by_suffix(&ctx, "layout_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_arg_locals(&mut codegen, &body);

        let layout_base = codegen.ssa_base_name(&local_place(1));
        let layout_expr = codegen.create_layout_struct(
            Expr::bitvec_const(32, POINTER_WIDTH),
            Expr::bitvec_const(16, POINTER_WIDTH),
        );
        codegen.env_update(layout_base, layout_expr);

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let destination = local_place(0);
        let result = codegen.codegen_layout_dangling(&[local_operand(1)], &destination, Some(24));
        assert_eq!(result, Some(24));

        let rendered_constraints = codegen.ctx.bmc_vc.constraints[constraints_before..]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            rendered_constraints.contains("false"),
            "extra-pointer-checks Layout::dangling should store false into obj_valid: {rendered_constraints}"
        );
    });
}

// Additional trivial expression-pattern tests removed per #2312:
// test_layout_is_valid_constraints, test_layout_from_size_align,
// test_coerce_zero_extend_small, test_coerce_truncate_large,
// test_fallback_ptr_constant, test_nonnull_new_wraps_ptr,
// test_nonnull_slice_returns_data_ptr, test_allocator_allocate_returns_ptr,
// test_try_branch_success_value, test_layout_align_default,
// test_option_ok_or_extracts_value, test_nonnull_as_nonnull_ptr_extracts_data,
// test_nonnull_as_nonnull_ptr_raw_bitvec.
// Production-path coverage retained in MIR-backed tests above.

// =============================================================================
// Layout::array_with_type tests (alloc.rs:682-721)
// =============================================================================

/// Test codegen_layout_array_with_type computes correct layout.
#[test]
fn test_codegen_layout_array_with_type_returns_target() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_arg_locals(&mut codegen, &body);

        let destination = local_place(0);
        // Layout::array::<u32>(count) with elem_size=4, elem_align=4
        let result = codegen.codegen_layout_array_with_type(
            &[local_operand(1)],
            &destination,
            Some(50),
            4, // elem_size
            4, // elem_align
        );
        assert_eq!(result, Some(50));

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base);
        assert!(assigned.is_some(), "layout array should assign to destination");
    });
}

/// Test codegen_layout_array_with_type with empty args uses default count.
#[test]
fn test_codegen_layout_array_with_type_no_args() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let destination = local_place(0);
        let result = codegen.codegen_layout_array_with_type(
            &[],
            &destination,
            Some(51),
            8, // elem_size
            8, // elem_align
        );
        assert_eq!(result, Some(51));
    });
}

// =============================================================================
// Pointer arithmetic tests (alloc.rs:725-783)
// =============================================================================

/// Test codegen_ptr_add returns pointer-width result.
#[test]
fn test_codegen_ptr_add_returns_target() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_arg_locals(&mut codegen, &body);

        let destination = local_place(0);
        // ptr_add(ptr, count) - args: ptr (local 3), count (local 1)
        let result =
            codegen.codegen_ptr_add(&[local_operand(3), local_operand(1)], &destination, Some(60));
        assert_eq!(result, Some(60));

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base);
        assert!(assigned.is_some(), "ptr_add should assign to destination");
        if let Some(expr) = assigned {
            assert_eq!(expr.sort().bitvec_width(), Some(POINTER_WIDTH));
        }
    });
}

/// Test codegen_ptr_add with insufficient args returns fallback.
#[test]
fn test_codegen_ptr_add_insufficient_args() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let destination = local_place(0);
        // Only 1 arg instead of 2
        let result = codegen.codegen_ptr_add(&[local_operand(1)], &destination, Some(61));
        assert_eq!(result, None, "ptr_add with insufficient args must fail-closed (#2497)");
    });
}

// =============================================================================
// Pointer read/write tests (alloc.rs:787-884)
// =============================================================================

/// Test codegen_ptr_read returns symbolic value.
#[test]
fn test_codegen_ptr_read_returns_target() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_arg_locals(&mut codegen, &body);

        let destination = local_place(0);
        let result = codegen.codegen_ptr_read(&[local_operand(3)], &destination, Some(70));
        assert_eq!(result, Some(70));

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base);
        assert!(assigned.is_some(), "ptr_read should assign symbolic value to destination");
    });
}

/// Test codegen_ptr_read with no args still returns target.
#[test]
fn test_codegen_ptr_read_no_args() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let destination = local_place(0);
        let result = codegen.codegen_ptr_read(&[], &destination, Some(71));
        assert_eq!(result, Some(71));
    });
}

/// Test codegen_ptr_write returns target (store not modeled).
#[test]
fn test_codegen_ptr_write_returns_target() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_arg_locals(&mut codegen, &body);

        // ptr_write(ptr, value) - args: ptr (local 3), value (local 1)
        let result = codegen.codegen_ptr_write(&[local_operand(3), local_operand(1)], Some(80));
        assert_eq!(result, Some(80));
    });
}

/// Test codegen_ptr_write with insufficient args fails closed (#2721).
#[test]
fn test_codegen_ptr_write_insufficient_args() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result = codegen.codegen_ptr_write(&[], Some(81));
        assert_eq!(result, None, "insufficient args must fail-closed (#2721)");
    });
}

// =============================================================================
// Edge case tests — empty args and dealloc calling conventions
// =============================================================================

/// Test codegen_rust_alloc with empty args returns None.
#[test]
fn test_codegen_rust_alloc_empty_args() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let destination = local_place(0);
        let result = codegen.codegen_rust_alloc(&[], &destination, Some(90));
        assert_eq!(result, None);
    });
}

/// Test codegen_rust_dealloc with empty args returns None.
#[test]
fn test_codegen_rust_dealloc_empty_args() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result = codegen.codegen_rust_dealloc(&[], Some(91));
        assert_eq!(result, None);
    });
}

/// Test codegen_rust_realloc with fewer than 4 args returns None.
#[test]
fn test_codegen_rust_realloc_insufficient_args() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let destination = local_place(0);
        let result = codegen.codegen_rust_realloc(
            &[local_operand(1), local_operand(2)],
            &destination,
            Some(92),
        );
        assert_eq!(result, None);
    });
}

/// Test codegen_rust_dealloc with only ptr arg uses defaults for size/align.
#[test]
fn test_codegen_rust_dealloc_ptr_only() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_arg_locals(&mut codegen, &body);

        // Only ptr arg (local 3 is *mut u8 in alloc_probe)
        let result = codegen.codegen_rust_dealloc(&[local_operand(3)], Some(93));
        assert_eq!(result, Some(93));
    });
}

// =============================================================================
// try_extract_layout_fields — direct unit tests
// =============================================================================

/// Test try_extract_layout_fields with a proper Layout datatype expression.
/// This tests the production function directly (not just expression patterns).
#[test]
fn test_try_extract_layout_fields_layout_datatype() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Construct a proper Layout datatype with both fld_size and fld_align
        let layout_sort = struct_sort(
            "Layout",
            [("fld_size", Sort::bitvec(POINTER_WIDTH)), ("fld_align", Sort::bitvec(POINTER_WIDTH))],
        );
        let layout_expr = Expr::var("test_layout", layout_sort);

        let result = codegen.try_extract_layout_fields(&layout_expr);
        assert!(result.is_some(), "Layout datatype should be recognized");

        let (size, align) = result.expect("Layout fields");
        assert_eq!(
            size.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "extracted size should be pointer-width bitvec"
        );
        assert!(
            matches!(size.value(), ExprValue::DatatypeSelector { .. }),
            "size should be a field selector expression"
        );
        assert_eq!(
            align.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "extracted align should be pointer-width bitvec"
        );
        assert!(
            matches!(align.value(), ExprValue::DatatypeSelector { .. }),
            "align should be a field selector expression (not hardcoded constant)"
        );
    });
}

/// Test try_extract_layout_fields rejects non-Layout datatypes.
#[test]
fn test_try_extract_layout_fields_non_layout_datatype() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // A datatype that is NOT Layout
        let other_sort = struct_sort("Point", [("x", Sort::bitvec(32)), ("y", Sort::bitvec(32))]);
        let other_expr = Expr::var("test_point", other_sort);

        let result = codegen.try_extract_layout_fields(&other_expr);
        assert!(result.is_none(), "non-Layout datatype should return None");
    });
}

/// Test try_extract_layout_fields rejects plain bitvec (not a datatype).
#[test]
fn test_try_extract_layout_fields_bitvec() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bv_expr = Expr::bitvec_const(64u64, POINTER_WIDTH);
        let result = codegen.try_extract_layout_fields(&bv_expr);
        assert!(result.is_none(), "bitvec should return None (not a datatype)");
    });
}

/// Round-trip: create_layout_struct -> try_extract_layout_fields preserves values.
/// Concrete Layout: #3007 extraction returns BitVecConst args (not selectors).
#[test]
fn test_layout_roundtrip_create_then_extract() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let size_val = Expr::bitvec_const(64u64, POINTER_WIDTH);
        let align_val = Expr::bitvec_const(4u64, POINTER_WIDTH);
        let layout = codegen.create_layout_struct(size_val, align_val);

        // Layout should be a Datatype, not a bare bitvec
        assert!(layout.sort().is_datatype(), "create_layout_struct must return Datatype");
        assert_eq!(layout.sort().datatype_name(), Some("Layout"));

        // Extract and verify both fields are recovered
        let (size, align) = codegen
            .try_extract_layout_fields(&layout)
            .expect("Layout Datatype should be extractable");

        assert_eq!(size.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert!(matches!(size.value(), ExprValue::BitVecConst { .. }));
        assert_eq!(align.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert!(matches!(align.value(), ExprValue::BitVecConst { .. }));
    });
}

// =============================================================================
// coerce_to_ptr_width — expression shape assertions
// =============================================================================

/// Test coerce_to_ptr_width with exact width is identity — no wrapping.
#[test]
fn test_coerce_to_ptr_width_exact() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let exact = Expr::bitvec_const(42u128, POINTER_WIDTH);
        let result = codegen.coerce_to_ptr_width(exact);
        assert_eq!(result.sort().bitvec_width(), Some(POINTER_WIDTH));
        // Exact width: returned as-is, no zero_extend or extract wrapper
        assert!(
            matches!(result.value(), ExprValue::BitVecConst { .. }),
            "exact-width should pass through unchanged"
        );
    });
}

/// Test coerce_to_ptr_width with smaller width zero-extends.
#[test]
fn test_coerce_to_ptr_width_small() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let small = Expr::bitvec_const(42u128, 32);
        let result = codegen.coerce_to_ptr_width(small);
        assert_eq!(result.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert!(
            matches!(result.value(), ExprValue::BvZeroExtend { .. }),
            "smaller width should be zero-extended"
        );
    });
}

/// Test coerce_to_ptr_width with larger width truncates via extract.
#[test]
fn test_coerce_to_ptr_width_large() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let large = Expr::bitvec_const(42u128, 128);
        let result = codegen.coerce_to_ptr_width(large);
        assert_eq!(result.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert!(
            matches!(result.value(), ExprValue::BvExtract { .. }),
            "larger width should be truncated via extract"
        );
    });
}

/// Test coerce_to_ptr_width with non-bitvec (bool) returns FALLBACK_PTR.
#[test]
fn test_coerce_to_ptr_width_non_bitvec() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dt = Expr::var("x", Sort::bool());
        let result = codegen.coerce_to_ptr_width(dt);
        assert_eq!(result.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert!(
            matches!(result.value(), ExprValue::BitVecConst { .. }),
            "non-bitvec should return FALLBACK_PTR constant"
        );
    });
}

/// Test coerce_to_ptr_width with datatype sort returns FALLBACK_PTR.
#[test]
fn test_coerce_to_ptr_width_datatype() {
    with_test_ay_ctx_for_source(ALLOC_MIR_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let dt_sort = struct_sort("Pair", [("a", Sort::bitvec(32)), ("b", Sort::bitvec(32))]);
        let dt_expr = Expr::var("pair", dt_sort);
        let result = codegen.coerce_to_ptr_width(dt_expr);
        assert_eq!(result.sort().bitvec_width(), Some(POINTER_WIDTH));
        assert!(
            matches!(result.value(), ExprValue::BitVecConst { .. }),
            "datatype sort should return FALLBACK_PTR constant"
        );
    });
}
