// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for alloc.rs — codegen_rust_alloc, codegen_rust_alloc_zeroed,
//! codegen_rust_dealloc, codegen_rust_realloc, coerce_to_ptr_width.
//!
//! Part of proof_coverage phase: alloc.rs (288 LOC) had zero dedicated tests.

use super::*;

// ─── MIR probe source ───────────────────────────────────────────────────

const ALLOC_PROBE: &str = r#"
pub fn alloc_probe(size: usize, align: usize) -> *mut u8 {
    if size > 0 { align as *mut u8 } else { core::ptr::null_mut() }
}
"#;

const ALLOC_LAYOUT_FALLBACK_PROBE: &str = r#"
use core::alloc::Layout;

pub fn layout_probe(layout: Layout, size: usize, align: usize) -> usize {
    layout.size().wrapping_add(size).wrapping_add(align)
}

pub fn bool_probe(flag: bool) -> bool {
    !flag
}
"#;

fn seed_alloc_args(codegen: &mut StatementCodegen<'_, '_, '_>, body: &rustc_public::mir::Body) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let place = local_place(local_idx);
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("alloc_arg_{local_idx}"), sort));
        }
    }
}

fn invalid_deref_operand(local_idx: usize) -> Operand {
    Operand::Copy(Place { local: Local::from(local_idx), projection: vec![ProjectionElem::Deref] })
}

// ─── codegen_rust_alloc ─────────────────────────────────────────────────

#[test]
fn test_rust_alloc_with_args_returns_target_and_assigns_ptr() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_args(&mut codegen, &body);

        let destination = local_place(0);
        let result = codegen.codegen_rust_alloc(
            &[local_operand(1), local_operand(2)],
            &destination,
            Some(10),
        );
        assert_eq!(result, Some(10), "should return target block");

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert_eq!(
            assigned.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "alloc result should be pointer-width bitvec"
        );
    });
}

#[test]
fn test_rust_alloc_empty_args_returns_none() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let destination = local_place(0);
        let result = codegen.codegen_rust_alloc(&[], &destination, Some(11));
        assert_eq!(result, None, "empty args should return None (guard)");
    });
}

#[test]
fn test_rust_alloc_operand_codegen_failure_uses_symbolic_size_2455() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let destination = local_place(0);
        let bad_size = invalid_deref_operand(1);
        let result = codegen.codegen_rust_alloc(&[bad_size], &destination, Some(12));
        assert_eq!(result, Some(12), "symbolic-size fallback path should stay translatable");

        let new_constraints = &codegen.ctx.bmc_vc.constraints[constraints_before..];
        let rendered_constraints: Vec<String> =
            new_constraints.iter().map(ToString::to_string).collect();
        assert!(
            rendered_constraints.iter().any(|constraint| constraint.contains("alloc_size_")),
            "expected symbolic alloc_size_* fallback in emitted constraints, got {rendered_constraints:?}"
        );
    });
}

#[test]
fn test_codegen_layout_size_non_layout_arg_uses_symbolic_fallback_2455() {
    with_test_ay_ctx_for_source(ALLOC_LAYOUT_FALLBACK_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_args(&mut codegen, &body);

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let destination = local_place(0);
        assert_eq!(
            codegen.codegen_layout_size(&[local_operand(1)], &destination, Some(32)),
            Some(32)
        );

        let new_constraints = &codegen.ctx.bmc_vc.constraints[constraints_before..];
        let rendered_constraints: Vec<String> =
            new_constraints.iter().map(ToString::to_string).collect();
        assert!(
            rendered_constraints.iter().any(|constraint| constraint.contains("layout_size_")),
            "expected symbolic layout_size_* fallback in emitted constraints, got {rendered_constraints:?}"
        );
    });
}

#[test]
fn test_codegen_layout_align_non_layout_arg_uses_symbolic_fallback_2455() {
    with_test_ay_ctx_for_source(ALLOC_LAYOUT_FALLBACK_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "bool_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_args(&mut codegen, &body);

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let destination = local_place(0);
        assert_eq!(
            codegen.codegen_layout_align(&[local_operand(1)], &destination, Some(33)),
            Some(33)
        );

        let new_constraints = &codegen.ctx.bmc_vc.constraints[constraints_before..];
        let rendered_constraints: Vec<String> =
            new_constraints.iter().map(ToString::to_string).collect();
        assert!(
            rendered_constraints.iter().any(|constraint| constraint.contains("layout_align_")),
            "expected symbolic layout_align_* fallback in emitted constraints, got {rendered_constraints:?}"
        );
    });
}

#[test]
fn test_codegen_layout_from_size_align_unchecked_size_failure_uses_symbolic_2455() {
    with_test_ay_ctx_for_source(ALLOC_LAYOUT_FALLBACK_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "layout_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_args(&mut codegen, &body);

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let bad_size = invalid_deref_operand(2);
        let destination = local_place(1);
        assert_eq!(
            codegen.codegen_layout_from_size_align_unchecked(
                &[bad_size, local_operand(3)],
                &destination,
                Some(34)
            ),
            Some(34)
        );

        let new_constraints = &codegen.ctx.bmc_vc.constraints[constraints_before..];
        let rendered_constraints: Vec<String> =
            new_constraints.iter().map(ToString::to_string).collect();
        assert!(
            rendered_constraints.iter().any(|constraint| constraint.contains("layout_unc_size_")),
            "expected symbolic layout_unc_size_* fallback in emitted constraints, got {rendered_constraints:?}"
        );
    });
}

// ─── codegen_rust_alloc_zeroed ──────────────────────────────────────────

#[test]
fn test_rust_alloc_zeroed_delegates_to_alloc() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_args(&mut codegen, &body);

        let destination = local_place(0);
        let result = codegen.codegen_rust_alloc_zeroed(
            &[local_operand(1), local_operand(2)],
            &destination,
            Some(20),
        );
        assert_eq!(result, Some(20), "alloc_zeroed should return target block");

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert_eq!(
            assigned.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "alloc_zeroed result should be pointer-width bitvec"
        );
    });
}

// ─── codegen_rust_dealloc ───────────────────────────────────────────────

#[test]
fn test_rust_dealloc_three_arg_form_returns_target() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_args(&mut codegen, &body);

        // __rust_dealloc(ptr, size, align) — 3 args, first two locals are size/align
        // but codegen_rust_dealloc treats arg[0] as ptr, arg[1] as size, arg[2] as align
        let result = codegen.codegen_rust_dealloc(
            &[local_operand(1), local_operand(1), local_operand(2)],
            Some(30),
        );
        assert_eq!(result, Some(30), "dealloc should return target block");
    });
}

#[test]
fn test_rust_dealloc_empty_args_returns_none() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let result = codegen.codegen_rust_dealloc(&[], Some(31));
        assert_eq!(result, None, "empty args should return None (guard)");
    });
}

#[test]
fn test_rust_dealloc_single_arg_uses_defaults() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_args(&mut codegen, &body);

        // Only ptr provided — exercises the else branch at lines 122-124
        let result = codegen.codegen_rust_dealloc(&[local_operand(1)], Some(32));
        assert_eq!(result, Some(32), "single-arg dealloc should return target");
    });
}

// ─── codegen_rust_realloc ───────────────────────────────────────────────

#[test]
fn test_rust_realloc_with_four_args_returns_target_and_assigns_ptr() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_args(&mut codegen, &body);

        let destination = local_place(0);
        // __rust_realloc(ptr, old_size, align, new_size) — reuse locals for 4 args
        let result = codegen.codegen_rust_realloc(
            &[local_operand(1), local_operand(1), local_operand(2), local_operand(1)],
            &destination,
            Some(40),
        );
        assert_eq!(result, Some(40), "realloc should return target block");

        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base).expect("destination should be assigned");
        assert_eq!(
            assigned.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "realloc result should be pointer-width bitvec"
        );
    });
}

#[test]
fn test_rust_realloc_align_failure_still_invalidates_old_ptr_3723() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        seed_alloc_args(&mut codegen, &body);

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        let destination = local_place(0);
        // __rust_realloc(ptr, old_size, BAD_ALIGN, new_size)
        // arg[2] is a deref that will fail codegen, forcing symbolic align fallback
        let result = codegen.codegen_rust_realloc(
            &[local_operand(1), local_operand(1), invalid_deref_operand(2), local_operand(1)],
            &destination,
            Some(42),
        );
        assert_eq!(result, Some(42), "realloc with failed align should still return target");

        // Destination must be assigned (heap_realloc ran, not early-returned)
        let dest_base = codegen.ssa_base_name(&destination);
        let assigned = codegen.env_lookup(&dest_base).expect(
            "destination should be assigned — heap_realloc must run even when align fails (#3723)",
        );
        assert_eq!(
            assigned.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "realloc result should be pointer-width bitvec"
        );

        // Verify heap_realloc ran (not early-returned): old_ptr must be invalidated
        // via a heap_dealloc_valid FREED-bit store. The align parameter is unused
        // by the heap model (_align in heap_alloc), so realloc_align_* won't appear
        // in constraints — the key invariant is that deallocation happened.
        // The liveness range is `(_ BitVec 1)`, so freed is `#b0` — see
        // `AYCtx::heap_valid_bit` for why it is not `Bool`.
        let new_constraints = &codegen.ctx.bmc_vc.constraints[constraints_before..];
        let rendered: Vec<String> = new_constraints.iter().map(ToString::to_string).collect();
        let rendered_constraints = rendered.join("\n");
        assert!(
            rendered_constraints.contains("heap_dealloc_valid")
                && rendered_constraints.contains("#b0"),
            "expected realloc constraints to invalidate old obj_valid via a heap_dealloc_valid freed-bit store, got {rendered_constraints}"
        );
    });
}

#[test]
fn test_rust_realloc_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let destination = local_place(0);
        // Only 2 args when 4 needed
        let result = codegen.codegen_rust_realloc(
            &[local_operand(1), local_operand(1)],
            &destination,
            Some(41),
        );
        assert_eq!(result, None, "insufficient args should return None");
    });
}

// ─── coerce_to_ptr_width ────────────────────────────────────────────────

#[test]
fn test_coerce_to_ptr_width_exact_width_is_noop() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let expr = Expr::bitvec_const(42u64, POINTER_WIDTH);
        let result = codegen.coerce_to_ptr_width(expr.clone());
        assert_eq!(
            result.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "exact-width should pass through unchanged"
        );
        // Value should be preserved
        assert_eq!(result.to_string(), expr.to_string());
    });
}

#[test]
fn test_coerce_to_ptr_width_narrow_zero_extends() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let narrow = Expr::bitvec_const(255u64, 8);
        let result = codegen.coerce_to_ptr_width(narrow);
        assert_eq!(
            result.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "narrow bitvec should be zero-extended to POINTER_WIDTH"
        );
    });
}

#[test]
fn test_coerce_to_ptr_width_wide_truncates() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let wide = Expr::bitvec_const(0u128, 128);
        let result = codegen.coerce_to_ptr_width(wide);
        assert_eq!(
            result.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "wide bitvec should be truncated to POINTER_WIDTH"
        );
    });
}

#[test]
fn test_coerce_to_ptr_width_non_bitvec_returns_fallback() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "alloc_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let bool_expr = Expr::bool_const(true);
        let result = codegen.coerce_to_ptr_width(bool_expr);
        assert_eq!(
            result.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "non-bitvec should return FALLBACK_PTR (pointer-width bitvec)"
        );
        // Should be FALLBACK_PTR (0x1000)
        match result.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, POINTER_WIDTH);
                assert_eq!(*value, 0x1000u64.into(), "fallback should be FALLBACK_PTR (0x1000)");
            }
            other => panic!("expected BitVecConst fallback, got {other:?}"),
        }
    });
}
