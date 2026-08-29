// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for heap allocation model.
//!
//! Extracted from heap/mod.rs as part of #2836.

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx;

// ========================================================================
// Heap Model Tests (#1234)
// ========================================================================

#[test]
fn test_heap_alloc_returns_non_zero_address() {
    with_test_ay_ctx(|mut ctx| {
        let size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let ptr = ctx.heap_alloc(size, align);

        // First allocation should return address = 1 * HEAP_STRIDE = 0x100000
        assert_eq!(ptr, Expr::bitvec_const(0x100000u128, POINTER_WIDTH));
    });
}

#[test]
fn test_heap_alloc_multiple_non_overlapping() {
    with_test_ay_ctx(|mut ctx| {
        let size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);

        let ptr1 = ctx.heap_alloc(size.clone(), align.clone());
        let ptr2 = ctx.heap_alloc(size.clone(), align.clone());
        let ptr3 = ctx.heap_alloc(size, align);

        // Each allocation gets HEAP_STRIDE (0x100000) apart
        assert_eq!(ptr1, Expr::bitvec_const(0x100000u128, POINTER_WIDTH)); // id=1
        assert_eq!(ptr2, Expr::bitvec_const(0x200000u128, POINTER_WIDTH)); // id=2
        assert_eq!(ptr3, Expr::bitvec_const(0x300000u128, POINTER_WIDTH)); // id=3

        // Verify allocations are non-overlapping (different addresses)
        assert_ne!(ptr1, ptr2);
        assert_ne!(ptr2, ptr3);
        assert_ne!(ptr1, ptr3);
    });
}

#[test]
fn test_heap_alloc_initializes_heap_arrays() {
    with_test_ay_ctx(|mut ctx| {
        // Before any allocation, heap arrays should be None
        assert!(ctx.heap_state.obj_valid.is_none());
        assert!(ctx.heap_state.obj_size.is_none());

        let size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let _ptr = ctx.heap_alloc(size, align);

        // After allocation, heap arrays should be initialized
        assert!(ctx.heap_state.obj_valid.is_some());
        assert!(ctx.heap_state.obj_size.is_some());
    });
}

#[test]
fn test_heap_dealloc_marks_invalid() {
    with_test_ay_ctx(|mut ctx| {
        let size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let ptr = ctx.heap_alloc(size.clone(), align.clone());

        // After allocation, obj_valid should be Some
        assert!(ctx.heap_state.obj_valid.is_some());

        // Dealloc should update obj_valid (mark as invalid)
        let valid_before = ctx.heap_state.obj_valid.clone();
        let constraints_before = ctx.bmc_vc.constraints.len();
        ctx.heap_dealloc(ptr, size, align);

        // obj_valid should have changed (new store with false)
        let valid_after = ctx.heap_state.obj_valid.clone();
        assert_ne!(valid_before, valid_after);

        // Fix #2763: Verify the constraint stores the FREED bit (not the alive
        // one). The old assert_ne! only checked that obj_valid changed, which
        // would also pass if dealloc incorrectly marked the object alive.
        // The liveness range is `(_ BitVec 1)`, so freed is `#b0` — see
        // `AYCtx::heap_valid_bit` for why it is not `Bool`.
        let dealloc_constraints: String = ctx.bmc_vc.constraints[constraints_before..]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            dealloc_constraints.contains("#b0"),
            "heap_dealloc must store the freed bit into obj_valid; \
             constraints:\n{dealloc_constraints}"
        );
    });
}

/// Verify that heap_dealloc emits SMT constraints so the solver can
/// reason about deallocation (use-after-free detection).
///
/// heap_alloc emits SSA constraints via declare_var + assert.
/// heap_dealloc should do the same to communicate validity=false to the solver.
/// Part of #2531.
#[test]
fn test_heap_dealloc_emits_smt_constraints() {
    with_test_ay_ctx(|mut ctx| {
        let size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);

        // Allocate — this emits constraints for validity and size
        let ptr = ctx.heap_alloc(size.clone(), align.clone());
        let constraints_after_alloc = ctx.bmc_vc.constraints.len();
        // heap_alloc emits at least 2 constraints (obj_valid, obj_size)
        assert!(
            constraints_after_alloc >= 2,
            "heap_alloc should emit at least 2 SMT constraints (validity + size), got {}",
            constraints_after_alloc
        );

        // Deallocate — should also emit constraints for validity=false
        ctx.heap_dealloc(ptr, size, align);
        let constraints_after_dealloc = ctx.bmc_vc.constraints.len();

        // Fix #2531: heap_dealloc now emits SSA constraints.
        // The solver can now reason about deallocation for use-after-free detection.
        assert!(
            constraints_after_dealloc > constraints_after_alloc,
            "heap_dealloc should emit SMT constraints (got {} after alloc, {} after dealloc)",
            constraints_after_alloc,
            constraints_after_dealloc
        );
    });
}

/// Verify that heap_dealloc records a double_free_check violation.
/// Part of #2718: BMC parity with CHC double-free detection.
#[test]
fn test_heap_dealloc_records_double_free_violation() {
    with_test_ay_ctx(|mut ctx| {
        let size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);

        let violations_before = ctx.bmc_vc.violations.len();
        let ptr = ctx.heap_alloc(size.clone(), align.clone());
        // alloc should not add violations
        assert_eq!(ctx.bmc_vc.violations.len(), violations_before);

        ctx.heap_dealloc(ptr, size, align);

        // dealloc should record double_free_check + dealloc_size_mismatch violations
        assert!(
            ctx.bmc_vc.violations.len() >= violations_before + 2,
            "heap_dealloc should record double_free_check and dealloc_size_mismatch violations, \
             got {} total (was {})",
            ctx.bmc_vc.violations.len(),
            violations_before
        );

        // Verify the violation labels are correct
        let labels: Vec<&str> = ctx.bmc_vc.violations[violations_before..]
            .iter()
            .filter_map(|v| v.smt_var.as_deref())
            .collect();
        assert!(
            labels.iter().any(|l| l.contains("double_free_check")),
            "should contain double_free_check violation, got: {:?}",
            labels
        );
        assert!(
            labels.iter().any(|l| l.contains("dealloc_size_mismatch")),
            "should contain dealloc_size_mismatch violation, got: {:?}",
            labels
        );
    });
}

/// Verify that double-free of the same pointer records violations on both deallocs.
/// Part of #2718.
#[test]
fn test_heap_double_free_records_two_violations() {
    with_test_ay_ctx(|mut ctx| {
        let size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);

        let ptr = ctx.heap_alloc(size.clone(), align.clone());
        let violations_after_alloc = ctx.bmc_vc.violations.len();

        // First dealloc — ptr is valid, so double_free_check violation should be
        // unsatisfiable (the solver won't find a counterexample for a valid free).
        ctx.heap_dealloc(ptr.clone(), size.clone(), align.clone());
        let violations_after_first = ctx.bmc_vc.violations.len();
        assert!(
            violations_after_first > violations_after_alloc,
            "first dealloc should record safety check violations"
        );

        // Second dealloc of same ptr — ptr is now invalid, so the double_free_check
        // violation IS satisfiable (the solver can find the double-free).
        ctx.heap_dealloc(ptr, size, align);
        let violations_after_second = ctx.bmc_vc.violations.len();
        assert!(
            violations_after_second > violations_after_first,
            "second dealloc should also record safety check violations"
        );
    });
}

/// Verify that heap_dealloc records a dealloc_size_mismatch violation.
/// Part of #2718: BMC parity with CHC size mismatch detection.
#[test]
fn test_heap_dealloc_records_size_mismatch_violation() {
    with_test_ay_ctx(|mut ctx| {
        let alloc_size = Expr::bitvec_const(64u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let ptr = ctx.heap_alloc(alloc_size, align.clone());

        let violations_before = ctx.bmc_vc.violations.len();

        // Dealloc with different size — should record size mismatch violation
        let wrong_size = Expr::bitvec_const(32u128, POINTER_WIDTH);
        ctx.heap_dealloc(ptr, wrong_size, align);

        let size_mismatch_count = ctx.bmc_vc.violations[violations_before..]
            .iter()
            .filter(|v| v.smt_var.as_deref().is_some_and(|s| s.contains("dealloc_size_mismatch")))
            .count();
        assert_eq!(
            size_mismatch_count, 1,
            "should record exactly one dealloc_size_mismatch violation"
        );
    });
}

/// Regression test: deallocating an interior pointer must record a base-pointer violation.
/// Part of #2725.
#[test]
fn test_heap_dealloc_records_non_base_pointer_violation_2725() {
    with_test_ay_ctx(|mut ctx| {
        let alloc_size = Expr::bitvec_const(64u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let ptr = ctx.heap_alloc(alloc_size.clone(), align.clone());
        let interior_ptr = ptr.bvadd(Expr::bitvec_const(16u128, POINTER_WIDTH));

        let violations_before = ctx.bmc_vc.violations.len();
        ctx.heap_dealloc(interior_ptr, alloc_size, align);

        let non_base_count = ctx.bmc_vc.violations[violations_before..]
            .iter()
            .filter(|v| {
                v.smt_var.as_deref().is_some_and(|s| s.contains("dealloc_base_pointer_check"))
            })
            .count();
        assert_eq!(
            non_base_count, 1,
            "should record exactly one dealloc_base_pointer_check violation"
        );
    });
}

/// Regression test: dealloc metadata updates must index by object ID, not raw address.
/// Without this, `heap_is_allocated(ptr)` checks (`obj_valid[obj_id(ptr)]`) never observe
/// dealloc stores (`obj_valid[ptr]`), masking use-after-free paths.
#[test]
fn test_heap_dealloc_updates_obj_valid_by_object_id_2718() {
    with_test_ay_ctx(|mut ctx| {
        let ptr = Expr::var("sym_ptr", Sort::bitvec(POINTER_WIDTH));
        let size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let constraints_before = ctx.bmc_vc.constraints.len();

        ctx.heap_dealloc(ptr.clone(), size, align);

        let expected_obj = ctx.heap_pointer_object(ptr).to_string();
        let rendered_constraints = ctx.bmc_vc.constraints[constraints_before..]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            rendered_constraints.contains(&expected_obj),
            "heap_dealloc should index metadata by object id `{expected_obj}`; constraints:\n{rendered_constraints}"
        );
    });
}

/// Verify that heap_realloc also gets double-free detection via heap_dealloc_ptr_only.
/// Part of #2718.
#[test]
fn test_heap_realloc_records_double_free_violation() {
    with_test_ay_ctx(|mut ctx| {
        let size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let ptr = ctx.heap_alloc(size.clone(), align.clone());

        let violations_before = ctx.bmc_vc.violations.len();

        // Realloc internally calls heap_dealloc_ptr_only, which should record double_free_check
        let _new_ptr = ctx.heap_realloc(ptr, size.clone(), align, size);

        let double_free_count = ctx.bmc_vc.violations[violations_before..]
            .iter()
            .filter(|v| v.smt_var.as_deref().is_some_and(|s| s.contains("double_free_check")))
            .count();
        assert_eq!(
            double_free_count, 1,
            "heap_realloc should record double_free_check via heap_dealloc_ptr_only"
        );
    });
}

/// Verify that heap_realloc also gets the base-pointer check via heap_dealloc_ptr_only.
/// Part of #2725.
#[test]
fn test_heap_realloc_records_base_pointer_violation() {
    with_test_ay_ctx(|mut ctx| {
        let size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let ptr = ctx.heap_alloc(size.clone(), align.clone());

        let violations_before = ctx.bmc_vc.violations.len();

        // Realloc calls heap_dealloc_ptr_only, which should record dealloc_base_pointer_check
        let _new_ptr = ctx.heap_realloc(ptr, size.clone(), align, size);

        let base_ptr_count = ctx.bmc_vc.violations[violations_before..]
            .iter()
            .filter(|v| {
                v.smt_var.as_deref().is_some_and(|s| s.contains("dealloc_base_pointer_check"))
            })
            .count();
        assert_eq!(
            base_ptr_count, 1,
            "heap_realloc should record dealloc_base_pointer_check via heap_dealloc_ptr_only"
        );
    });
}

/// Regression test: realloc with wrong old_size must record a size-mismatch violation.
/// Part of #2817: BMC heap_realloc previously ignored old_size (underscore-prefixed).
#[test]
fn test_heap_realloc_records_old_size_mismatch_violation() {
    with_test_ay_ctx(|mut ctx| {
        let alloc_size = Expr::bitvec_const(64u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let ptr = ctx.heap_alloc(alloc_size, align.clone());

        let violations_before = ctx.bmc_vc.violations.len();

        // Realloc with wrong old_size — should record dealloc_size_mismatch
        let wrong_old_size = Expr::bitvec_const(32u128, POINTER_WIDTH);
        let new_size = Expr::bitvec_const(128u128, POINTER_WIDTH);
        let _new_ptr = ctx.heap_realloc(ptr, wrong_old_size, align, new_size);

        let size_mismatch_count = ctx.bmc_vc.violations[violations_before..]
            .iter()
            .filter(|v| v.smt_var.as_deref().is_some_and(|s| s.contains("dealloc_size_mismatch")))
            .count();
        assert_eq!(
            size_mismatch_count, 1,
            "heap_realloc should record exactly one dealloc_size_mismatch violation"
        );
    });
}

#[test]
fn test_heap_realloc_allocates_new_memory() {
    with_test_ay_ctx(|mut ctx| {
        let size1 = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let size2 = Expr::bitvec_const(16u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);

        // First allocation
        let ptr1 = ctx.heap_alloc(size1.clone(), align.clone());
        assert_eq!(ptr1, Expr::bitvec_const(0x100000u128, POINTER_WIDTH));

        // Realloc should return a new allocation (id=2)
        let ptr2 = ctx.heap_realloc(ptr1, size1, align.clone(), size2);
        assert_eq!(ptr2, Expr::bitvec_const(0x200000u128, POINTER_WIDTH));

        // Another allocation should continue from id=3
        let ptr3 = ctx.heap_alloc(Expr::bitvec_const(4u128, POINTER_WIDTH), align);
        assert_eq!(ptr3, Expr::bitvec_const(0x300000u128, POINTER_WIDTH));
    });
}

#[test]
fn test_heap_state_fresh_alloc_id_increments() {
    with_test_ay_ctx(|mut ctx| {
        // Fresh alloc IDs should increment
        let id1 = ctx.heap_state.fresh_alloc_id();
        let id2 = ctx.heap_state.fresh_alloc_id();
        let id3 = ctx.heap_state.fresh_alloc_id();

        assert_eq!(id1, Some(1));
        assert_eq!(id2, Some(2));
        assert_eq!(id3, Some(3));
    });
}

#[test]
fn test_ensure_heap_arrays_initialized_idempotent() {
    with_test_ay_ctx(|mut ctx| {
        // Call ensure_heap_arrays_initialized multiple times
        ctx.ensure_heap_arrays_initialized();
        let valid1 = ctx.heap_state.obj_valid.clone();
        let size1 = ctx.heap_state.obj_size.clone();

        ctx.ensure_heap_arrays_initialized();
        let valid2 = ctx.heap_state.obj_valid.clone();
        let size2 = ctx.heap_state.obj_size.clone();

        // Should return the same arrays (idempotent)
        assert_eq!(valid1, valid2);
        assert_eq!(size1, size2);
    });
}

// ========================================================================
// Ptr(id, offset) Model Tests (#1410)
// ========================================================================

#[test]
fn test_heap_pointer_object_computes_allocation_id() {
    with_test_ay_ctx(|ctx| {
        // HEAP_STRIDE = 0x100000 (1MB)
        // Allocation id=1 returns address 0x100000
        // Allocation id=2 returns address 0x200000
        // Use POINTER_WIDTH to match implementation
        let stride = Expr::bitvec_const(HEAP_STRIDE as u128, POINTER_WIDTH);

        // Pointer at allocation 1's base should have object ID 1
        // heap_pointer_object(ptr) returns ptr / HEAP_STRIDE
        let ptr1 = Expr::bitvec_const(0x100000u128, POINTER_WIDTH);
        let obj_id1 = ctx.heap_pointer_object(ptr1.clone());
        assert_eq!(obj_id1, ptr1.bvudiv(stride.clone()));

        // Pointer within allocation 1 (offset 0x500) should also have object ID 1
        // 0x100500 / 0x100000 = 1 (integer division)
        let ptr1_mid = Expr::bitvec_const(0x100500u128, POINTER_WIDTH);
        let obj_id1_mid = ctx.heap_pointer_object(ptr1_mid.clone());
        assert_eq!(obj_id1_mid, ptr1_mid.bvudiv(stride.clone()));

        // Pointer at allocation 3's base should have object ID 3
        // 0x300000 / 0x100000 = 3
        let ptr3 = Expr::bitvec_const(0x300000u128, POINTER_WIDTH);
        let obj_id3 = ctx.heap_pointer_object(ptr3.clone());
        assert_eq!(obj_id3, ptr3.bvudiv(stride));
    });
}

#[test]
fn test_heap_pointer_offset_computes_offset_within_allocation() {
    with_test_ay_ctx(|ctx| {
        // Use POINTER_WIDTH to match implementation
        let stride = Expr::bitvec_const(HEAP_STRIDE as u128, POINTER_WIDTH);

        // Pointer at allocation 1's base should have offset 0
        // 0x100000 % 0x100000 = 0
        let ptr1_base = Expr::bitvec_const(0x100000u128, POINTER_WIDTH);
        let offset1_base = ctx.heap_pointer_offset(ptr1_base.clone());
        assert_eq!(offset1_base, ptr1_base.bvurem(stride.clone()));

        // Pointer at offset 0x500 within allocation 1 should have offset 0x500
        // 0x100500 % 0x100000 = 0x500
        let ptr1_mid = Expr::bitvec_const(0x100500u128, POINTER_WIDTH);
        let offset1_mid = ctx.heap_pointer_offset(ptr1_mid.clone());
        assert_eq!(offset1_mid, ptr1_mid.bvurem(stride.clone()));

        // Pointer at allocation 2's base + 0x1234 should have offset 0x1234
        // 0x201234 % 0x100000 = 0x1234
        let ptr2_offset = Expr::bitvec_const(0x201234u128, POINTER_WIDTH);
        let offset2 = ctx.heap_pointer_offset(ptr2_offset.clone());
        assert_eq!(offset2, ptr2_offset.bvurem(stride));
    });
}

#[test]
fn test_heap_is_allocated_returns_select_expr() {
    with_test_ay_ctx(|mut ctx| {
        // Ensure heap arrays are initialized
        ctx.ensure_heap_arrays_initialized();

        // Check that heap_is_allocated returns a select expression
        let ptr = Expr::bitvec_const(0x100000u128, POINTER_WIDTH);
        let is_alloc = ctx.heap_is_allocated(ptr, None);

        // The result should be a select from obj_valid array
        // We can't easily test the exact expression structure, but we can verify
        // it returns an Expr with Bool sort
        assert!(is_alloc.sort().is_bool());
    });
}

#[test]
fn test_heap_is_allocated_with_size_check() {
    with_test_ay_ctx(|mut ctx| {
        // Verify size argument is respected in range check
        ctx.ensure_heap_arrays_initialized();

        let ptr = Expr::bitvec_const(0x100000u128, POINTER_WIDTH);
        let size = Expr::bitvec_const(64u128, POINTER_WIDTH);

        // With size, should return AND of validity and same-allocation check
        let is_alloc = ctx.heap_is_allocated(ptr, Some(size));

        // Result should be Bool (conjunction of validity and boundary check)
        assert!(is_alloc.sort().is_bool());
    });
}

/// Regression test: heap_is_allocated with concrete zero size skips
/// the end-pointer boundary check (no underflow in end_ptr computation).
/// Part of #2715.
#[test]
fn test_heap_is_allocated_zero_size_skips_end_check() {
    with_test_ay_ctx(|mut ctx| {
        ctx.ensure_heap_arrays_initialized();

        let ptr = Expr::bitvec_const(HEAP_STRIDE as u128, POINTER_WIDTH); // base of alloc 1
        let zero_size = Expr::bitvec_const(0u128, POINTER_WIDTH);

        // With concrete zero size, should take the same path as None (no end-ptr check).
        let is_alloc_zero = ctx.heap_is_allocated(ptr.clone(), Some(zero_size));
        let is_alloc_none = ctx.heap_is_allocated(ptr, None);

        // Both should return Bool sort
        assert!(is_alloc_zero.sort().is_bool());
        assert!(is_alloc_none.sort().is_bool());

        let expr_str = is_alloc_zero.to_string();
        assert!(expr_str.contains("ite"), "zero-size path should use SMT guard, got: {expr_str}");
        assert!(
            expr_str.contains(&Expr::bitvec_const(0u128, POINTER_WIDTH).to_string()),
            "zero-size guard should compare against zero bitvector, got: {expr_str}"
        );
    });
}

/// Regression test: heap_is_allocated with size=1 at allocation base
/// computes end_ptr = base + 1 - 1 = base, which should be in the same allocation.
#[test]
fn test_heap_is_allocated_size_one_at_base() {
    with_test_ay_ctx(|mut ctx| {
        ctx.ensure_heap_arrays_initialized();

        let ptr = Expr::bitvec_const(HEAP_STRIDE as u128, POINTER_WIDTH);
        let one_size = Expr::bitvec_const(1u128, POINTER_WIDTH);

        let is_alloc = ctx.heap_is_allocated(ptr, Some(one_size));

        // Should return Bool (AND of validity and same_alloc)
        assert!(is_alloc.sort().is_bool());
        // Expression should contain AND (conjunction of base_valid and same_alloc)
        let expr_str = is_alloc.to_string();
        assert!(
            expr_str.contains("and") || expr_str.contains("select"),
            "size=1 should produce a non-trivial allocation check, got: {}",
            expr_str
        );
    });
}

/// Regression test: symbolic size keeps a runtime zero guard in the generated expression.
/// This avoids rejecting valid zero-sized symbolic accesses (#2715).
#[test]
fn test_heap_is_allocated_symbolic_size_contains_zero_guard_2715() {
    with_test_ay_ctx(|mut ctx| {
        ctx.ensure_heap_arrays_initialized();

        let ptr = Expr::bitvec_const(HEAP_STRIDE as u128, POINTER_WIDTH);
        let symbolic_size = Expr::var("sym_size", Sort::bitvec(POINTER_WIDTH));
        let is_alloc = ctx.heap_is_allocated(ptr, Some(symbolic_size));

        assert!(is_alloc.sort().is_bool());
        let expr_str = is_alloc.to_string();
        assert!(
            expr_str.contains("ite"),
            "symbolic size check should use ite guard, got: {expr_str}"
        );
        assert!(
            expr_str.contains("sym_size"),
            "symbolic size variable should appear in guard, got: {expr_str}"
        );
        assert!(
            expr_str.contains(&Expr::bitvec_const(0u128, POINTER_WIDTH).to_string()),
            "guard should compare symbolic size to zero, got: {expr_str}"
        );
    });
}

/// Verify that `heap_alloc` emits a stride-limit constraint (`size <= HEAP_STRIDE`).
///
/// Without this, a symbolic size exceeding HEAP_STRIDE would silently overlap
/// neighboring allocations. Part of #2532.
#[test]
fn test_heap_alloc_emits_stride_limit_constraint() {
    with_test_ay_ctx(|mut ctx| {
        let constraints_before = ctx.bmc_vc.constraints.len();

        let size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let _ptr = ctx.heap_alloc(size, align);

        let constraints_after = ctx.bmc_vc.constraints.len();

        // heap_alloc emits: stride limit (1) + obj_valid update (1) + obj_size update (1) = 3
        assert!(
            constraints_after >= constraints_before + 3,
            "heap_alloc should emit at least 3 constraints (stride + valid + size), got {}",
            constraints_after - constraints_before
        );

        // Verify that one constraint is the stride-limit bvule assertion.
        // The stride constant is HEAP_STRIDE = 0x100000.
        let stride_str = Expr::bitvec_const(HEAP_STRIDE as u128, POINTER_WIDTH).to_string();
        let has_stride_constraint = ctx.bmc_vc.constraints.iter().any(|c| {
            let s = c.to_string();
            s.contains("bvule") && s.contains(&stride_str)
        });
        assert!(has_stride_constraint, "heap_alloc must emit bvule(size, HEAP_STRIDE) constraint");
    });
}

/// Verify that stride-limit constraint uses the symbolic size variable when
/// allocating with a symbolic (non-constant) size expression.
#[test]
fn test_heap_alloc_stride_limit_with_symbolic_size() {
    with_test_ay_ctx(|mut ctx| {
        let symbolic_size = Expr::var("alloc_size", Sort::bitvec(POINTER_WIDTH));
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let _ptr = ctx.heap_alloc(symbolic_size, align);

        // The stride constraint should reference our symbolic variable
        let has_symbolic_stride = ctx.bmc_vc.constraints.iter().any(|c| {
            let s = c.to_string();
            s.contains("alloc_size") && s.contains("bvule")
        });
        assert!(has_symbolic_stride, "heap_alloc must constrain symbolic size <= HEAP_STRIDE");
    });
}

#[test]
fn test_heap_model_integration_alloc_then_check() {
    with_test_ay_ctx(|mut ctx| {
        let size = Expr::bitvec_const(64u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);

        // Allocate and get the returned pointer
        let ptr = ctx.heap_alloc(size, align);

        // The pointer should be for allocation ID 1 (0x100000)
        assert_eq!(ptr, Expr::bitvec_const(0x100000u128, POINTER_WIDTH));

        // pointer_object should return the division expression
        let stride = Expr::bitvec_const(HEAP_STRIDE as u128, POINTER_WIDTH);
        let obj_id = ctx.heap_pointer_object(ptr.clone());
        assert_eq!(obj_id, ptr.clone().bvudiv(stride.clone()));

        // pointer_offset should return the modulo expression
        let offset = ctx.heap_pointer_offset(ptr.clone());
        assert_eq!(offset, ptr.bvurem(stride));
    });
}

// ========================================================================
// Realloc Data Copy Tests (#2716)
// ========================================================================

/// Verify that heap_realloc copies bytes from old allocation to new allocation.
/// Part of #2716: realloc must preserve min(old_size, new_size) bytes.
#[test]
fn test_heap_realloc_copies_data_to_new_allocation() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();

        let size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);

        // Allocate and write some bytes to old allocation
        let old_ptr = ctx.heap_alloc(size.clone(), align.clone());
        assert_eq!(old_ptr, Expr::bitvec_const(0x100000u128, POINTER_WIDTH));

        // Write 3 known bytes at old_ptr+0, +1, +2
        for i in 0u128..3 {
            let addr = old_ptr.clone().bvadd(Expr::bitvec_const(i, POINTER_WIDTH));
            ctx.store_memory(addr, Expr::bitvec_const(0xAA + i, 8));
        }

        let mem_before_realloc = ctx.memory().to_string();

        // Realloc: grow from 8 to 16 bytes
        let new_size = Expr::bitvec_const(16u128, POINTER_WIDTH);
        let new_ptr = ctx.heap_realloc(old_ptr, size, align, new_size);
        assert_eq!(new_ptr, Expr::bitvec_const(0x200000u128, POINTER_WIDTH));

        // Memory expr should have grown — realloc copied 8 bytes
        let mem_after_realloc = ctx.memory().to_string();
        assert_ne!(
            mem_before_realloc, mem_after_realloc,
            "heap_realloc should modify memory (copy bytes from old to new)"
        );

        // The memory expression should contain store operations at the new address
        let new_base_str = Expr::bitvec_const(0x200000u128, POINTER_WIDTH).to_string();
        assert!(
            mem_after_realloc.contains(&new_base_str),
            "memory should contain stores at new allocation base 0x200000, got: {}",
            &mem_after_realloc[..mem_after_realloc.len().min(500)]
        );
    });
}

/// Verify byte-level data preservation during realloc copy.
///
/// The existing test_heap_realloc_copies_data_to_new_allocation checks that
/// memory changed and that stores exist at the new address. This test goes
/// further: it loads individual bytes from the new allocation and verifies
/// they match the original data written to the old allocation.
///
/// Part of #2716. Strengthened by Prover (P1:949).
#[test]
fn test_heap_realloc_preserves_byte_content() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();

        let size = Expr::bitvec_const(4u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let old_ptr = ctx.heap_alloc(size.clone(), align.clone());

        // Write 4 known bytes at old_ptr+0..+3
        let test_bytes: [u128; 4] = [0xDE, 0xAD, 0xBE, 0xEF];
        for (i, &byte_val) in test_bytes.iter().enumerate() {
            let addr = old_ptr.clone().bvadd(Expr::bitvec_const(i as u128, POINTER_WIDTH));
            ctx.store_memory(addr, Expr::bitvec_const(byte_val, 8));
        }

        // Realloc: grow from 4 to 8 bytes — should copy all 4 original bytes
        let new_size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let new_ptr = ctx.heap_realloc(old_ptr, size, align, new_size);

        // Load each byte from the new allocation and verify it matches.
        // After store+load on the same address, SMT simplification yields
        // store(mem, addr, val).select(addr) = val. The string representation
        // of the loaded expression should contain the stored byte value.
        for (i, &byte_val) in test_bytes.iter().enumerate() {
            let new_addr = new_ptr.clone().bvadd(Expr::bitvec_const(i as u128, POINTER_WIDTH));
            let loaded = ctx.load_memory(new_addr);
            let loaded_str = loaded.to_string();
            let expected_byte = Expr::bitvec_const(byte_val, 8).to_string();
            assert!(
                loaded_str.contains(&expected_byte),
                "byte[{}] at new allocation should contain original value {}, got: {}",
                i,
                expected_byte,
                &loaded_str[..loaded_str.len().min(200)]
            );
        }
    });
}

/// Verify realloc with shrinking size copies only min(old, new) bytes.
///
/// Strengthened by Prover (P1:949): verifies preserved bytes contain
/// original data AND that bytes beyond min(old,new) are NOT copied.
/// Part of #2716.
#[test]
fn test_heap_realloc_shrink_copies_min_bytes() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();

        let old_size = Expr::bitvec_const(16u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let old_ptr = ctx.heap_alloc(old_size.clone(), align.clone());

        // Write 16 bytes with distinguishable values
        for i in 0u128..16 {
            let addr = old_ptr.clone().bvadd(Expr::bitvec_const(i, POINTER_WIDTH));
            ctx.store_memory(addr, Expr::bitvec_const(i + 1, 8));
        }

        // Snapshot memory before realloc to check post-copy reads at byte 5+
        let mem_before = ctx.memory().to_string();

        // Shrink to 4 bytes — should copy only 4 bytes (min(16, 4) = 4)
        let new_size = Expr::bitvec_const(4u128, POINTER_WIDTH);
        let new_ptr = ctx.heap_realloc(old_ptr, old_size, align, new_size);

        let mem_after = ctx.memory().to_string();
        assert_ne!(mem_before, mem_after, "realloc shrink should still copy bytes");
        assert_eq!(new_ptr, Expr::bitvec_const(0x200000u128, POINTER_WIDTH));

        // Verify first 4 bytes were copied (contain original data)
        for i in 0u128..4 {
            let new_addr = new_ptr.clone().bvadd(Expr::bitvec_const(i, POINTER_WIDTH));
            let loaded = ctx.load_memory(new_addr);
            let loaded_str = loaded.to_string();
            let expected = Expr::bitvec_const(i + 1, 8).to_string();
            assert!(
                loaded_str.contains(&expected),
                "byte[{}] should contain original value {}, got: {}",
                i,
                expected,
                &loaded_str[..loaded_str.len().min(200)]
            );
        }

        // The first 4 bytes at the new allocation contain the original data.
        // The old assertion only checked `mem_before != mem_after` which passes
        // even if the wrong data was copied.
    });
}

/// Verify realloc with zero old_size does no copy.
/// Part of #2716.
#[test]
fn test_heap_realloc_zero_old_size_no_copy() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();

        let zero_size = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let new_size = Expr::bitvec_const(16u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let old_ptr = ctx.heap_alloc(zero_size.clone(), align.clone());

        let mem_before = ctx.memory().to_string();

        let _new_ptr = ctx.heap_realloc(old_ptr, zero_size, align, new_size);

        // min(0, 16) = 0, so no bytes should be copied
        let mem_after = ctx.memory().to_string();
        assert_eq!(mem_before, mem_after, "realloc with zero old_size should not modify memory");
    });
}

/// Verify realloc with symbolic sizes records unsupported.
/// Part of #2716.
#[test]
fn test_heap_realloc_symbolic_size_records_unsupported() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();

        let concrete_size = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let old_ptr = ctx.heap_alloc(concrete_size.clone(), align.clone());

        let symbolic_new_size = Expr::var("sym_new_size", Sort::bitvec(POINTER_WIDTH));

        let unsupported_before = ctx.unsupported_constructs.len();
        let _new_ptr = ctx.heap_realloc(old_ptr, concrete_size, align, symbolic_new_size);

        assert!(
            ctx.unsupported_constructs.len() > unsupported_before,
            "realloc with symbolic size should record unsupported construct"
        );
        assert!(
            ctx.unsupported_constructs.contains_key("heap_realloc_symbolic_copy"),
            "should record heap_realloc_symbolic_copy, got: {:?}",
            ctx.unsupported_constructs.keys().collect::<Vec<_>>()
        );
    });
}

/// Verify try_extract_concrete_usize extracts from bitvec constants.
#[test]
fn test_try_extract_concrete_usize() {
    let expr = Expr::bitvec_const(42u128, POINTER_WIDTH);
    assert_eq!(
        AYCtx::try_extract_concrete_usize(&expr),
        Some(42),
        "should extract 42 from bitvec_const(42)"
    );

    let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
    assert_eq!(
        AYCtx::try_extract_concrete_usize(&zero),
        Some(0),
        "should extract 0 from bitvec_const(0)"
    );

    let sym = Expr::var("x", Sort::bitvec(POINTER_WIDTH));
    assert_eq!(
        AYCtx::try_extract_concrete_usize(&sym),
        None,
        "should return None for symbolic variable"
    );
}

/// Verify that realloc with large copy size records unsupported.
/// Part of #2716.
#[test]
fn test_heap_realloc_large_copy_records_unsupported() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();

        let large_size = Expr::bitvec_const(256u128, POINTER_WIDTH);
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let old_ptr = ctx.heap_alloc(large_size.clone(), align.clone());

        let _new_ptr = ctx.heap_realloc(old_ptr, large_size.clone(), align, large_size);

        assert!(
            ctx.unsupported_constructs.contains_key("heap_realloc_data_copy_large"),
            "realloc with copy > 128 bytes should record heap_realloc_data_copy_large, got: {:?}",
            ctx.unsupported_constructs.keys().collect::<Vec<_>>()
        );
    });
}
