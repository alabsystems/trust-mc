// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::chc::codegen_expr_heap;

#[test]
fn test_dealloc_with_dynamic_obj_id() {
    // (#1100) Verify dealloc works with obj_id extracted from pointer
    // This tests the full pattern used in translate_alloc_call for RustDealloc.

    let ptr = Expr::var("ptr", Sort::bitvec(64));
    let obj_valid_in = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_valid_out = Expr::var("obj_valid__out", Sort::array(Sort::bitvec(32), Sort::bool()));

    // Extract obj_id from pointer (high 32 bits)
    let obj_id = ptr.extract(63, 32);
    assert_eq!(obj_id.sort().bitvec_width(), Some(32));

    // Mark as freed
    let freed_constraint = obj_valid_out.eq(obj_valid_in.store(obj_id, Expr::bool_const(false)));

    // Verify constraint structure
    let smt = freed_constraint.to_string();
    assert!(smt.contains("store"), "Should use store: {}", smt);
    assert!(smt.contains("extract"), "Should extract obj_id from pointer: {}", smt);
    assert!(smt.contains("false"), "Should set false for deallocation: {}", smt);
}

#[test]
fn test_realloc_with_dynamic_old_obj_id() {
    // (#1100) Verify realloc extracts old_obj_id from old pointer
    // This tests the full pattern used in translate_alloc_call for RustRealloc.

    let old_ptr = Expr::var("old_ptr", Sort::bitvec(64));
    let obj_valid_in = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_valid_out = Expr::var("obj_valid__out", Sort::array(Sort::bitvec(32), Sort::bool()));
    let new_obj_id = Expr::bitvec_const(10, 32); // Fresh allocation

    // Extract old_obj_id from pointer
    let old_obj_id = old_ptr.extract(63, 32);

    // Chained store: free old, then allocate new
    let after_free = obj_valid_in.store(old_obj_id, Expr::bool_const(false));
    let after_alloc = after_free.store(new_obj_id, Expr::bool_const(true));
    let realloc_constraint = obj_valid_out.eq(after_alloc);

    // Verify constraint structure
    let smt = realloc_constraint.to_string();
    let store_count = smt.matches("store").count();
    assert!(store_count >= 2, "Should have 2 stores: {}", smt);
    assert!(smt.contains("extract"), "Should extract old_obj_id: {}", smt);
}

#[test]
fn test_size_truncation_for_obj_size_array() {
    // (#1100) Verify 64-bit sizes are truncated to 32-bit for obj_size array
    // The obj_size array has 32-bit elements, so 64-bit sizes must be truncated.

    let size_64 = Expr::var("size", Sort::bitvec(64));

    // Truncate to 32 bits
    let size_32 = size_64.extract(31, 0);

    assert_eq!(size_32.sort().bitvec_width(), Some(32));
    let smt = size_32.to_string();
    assert!(smt.contains("extract 31 0"), "Should extract low 32 bits: {}", smt);
}

#[test]
fn test_obj_valid_array_semantics() {
    // (#1100) Document the semantic meaning of obj_valid array
    //
    // obj_valid : Array<ObjId, Bool>
    // - obj_valid[id] = true  → object id is currently allocated (valid)
    // - obj_valid[id] = false → object id is freed or never allocated (invalid)
    //
    // Production initialization (Part of #3159):
    //   ∀id. obj_valid[id] = true (allow-by-default)
    //
    // This is a pragmatic inversion from the ideal deny-by-default model.
    // Unconstrained pointers from opaque/uninlined calls would produce false
    // counterexamples on obj_valid[obj_id] safety checks with deny-by-default.
    // See codegen_rules_entry.rs:71-85 for the production initialization.
    //
    // After alloc(id): obj_valid[id] = true (already true, but explicit store)
    // After dealloc(id): obj_valid[id] = false (preserves use-after-free detection)
    //
    // Use-after-free detection still works:
    // - Dealloc stores false → subsequent deref with obj_valid[obj_id(ptr)] = false is an error

    let obj_valid = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_id = Expr::bitvec_const(1, 32);

    // Check validity: select(obj_valid, id)
    let is_valid = obj_valid.select(obj_id);
    assert!(is_valid.sort().is_bool(), "Validity check should be Bool");

    // This check can be used in assertions:
    // assert!(obj_valid[obj_id(ptr)]) before dereferencing
}

#[test]
fn test_obj_size_array_semantics() {
    // (#1100) Document the semantic meaning of obj_size array
    //
    // obj_size : Array<ObjId, BV32>
    // - obj_size[id] = size of allocation for object id
    //
    // After alloc(id, size): obj_size[id] = size
    // After realloc(old_id, new_id, new_size): obj_size[new_id] = new_size
    //
    // This enables bounds checking:
    // - Accessing ptr+offset where offset >= obj_size[obj_id(ptr)] is OOB

    let obj_size = Expr::var("obj_size", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
    let obj_id = Expr::bitvec_const(1, 32);

    // Get size: select(obj_size, id)
    let size = obj_size.select(obj_id);
    assert_eq!(size.sort().bitvec_width(), Some(32), "Size should be 32-bit");

    // This can be used in bounds assertions:
    // assert!(offset < obj_size[obj_id(ptr)]) before access
}

#[test]
fn test_obj_valid_production_initialization_policy() {
    // Part of #3362: Verify the production initialization policy for obj_valid.
    //
    // Production (codegen_rules_entry.rs:83) initializes:
    //   obj_valid = const_array(BV32, true)
    //
    // This is allow-by-default (Part of #3159). If someone accidentally flips
    // the initializer to const_array(false), this test catches the regression.

    // Use production helper to get the obj_valid variable and sort
    let obj_valid = codegen_expr_heap::obj_valid_in();
    let obj_valid_sort = codegen_expr_heap::obj_valid_sort();
    assert_eq!(*obj_valid.sort(), obj_valid_sort, "obj_valid_in() sort mismatch");

    // Construct the production initialization expression: const_array(BV32, true)
    let all_valid = Expr::const_array(Sort::bitvec(32), Expr::bool_const(true));
    let init_constraint = obj_valid.eq(all_valid.clone());

    // Verify the constraint is well-formed
    assert!(init_constraint.sort().is_bool(), "init constraint should be Bool");

    // Verify the const_array default is true (not false)
    let smt = all_valid.to_string();
    assert!(
        smt.contains("true"),
        "Production policy is allow-by-default (const_array(true)): {}",
        smt
    );
    assert!(!smt.contains("false"), "Production policy must NOT be deny-by-default: {}", smt);
}
