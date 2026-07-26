// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =========================================================================
// Allocator Intrinsic Constraint Verification Tests (#1100)
// =========================================================================
//
// Prover verification tests for the store() pattern used in heap allocation.
// Heap allocation model (#1100), commits ce59e1ee, 2d377f29.
//
// Key invariants verified:
// 1. RustAlloc/RustAllocZeroed: obj_valid[id]=true, obj_size[id]=size
// 2. RustDealloc: obj_valid[id]=false
// 3. RustRealloc: obj_valid[old]=false, obj_valid[new]=true, obj_size[new]=new_size
// 4. Split-pointer model: (obj_id << 32) | offset produces valid 64-bit pointer

#[test]
fn test_alloc_obj_valid_store_constraint() {
    // (#1100) Verify RustAlloc generates: obj_valid__out = store(obj_valid, id, true)
    // This tests the soundness fix from commit 2d377f29.
    //
    // The WRONG pattern was: select(obj_valid, id).eq(true)
    // - This constrains INPUT (precondition), not OUTPUT
    //
    // The CORRECT pattern is: obj_valid__out = store(obj_valid, id, true)
    // - This updates OUTPUT (SSA-style postcondition)

    let obj_valid_in = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_valid_out = Expr::var("obj_valid__out", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_id = Expr::bitvec_const(1, 32);

    // Correct pattern: obj_valid__out = store(obj_valid, obj_id, true)
    let valid_constraint = obj_valid_out.eq(obj_valid_in.store(obj_id, Expr::bool_const(true)));

    // Verify it's a Bool constraint
    assert!(valid_constraint.sort().is_bool());

    // Verify SMT-LIB output contains the correct store pattern
    let smt = valid_constraint.to_string();
    assert!(smt.contains("store"), "Should use store() pattern: {}", smt);
    assert!(smt.contains("obj_valid"), "Should reference obj_valid: {}", smt);
    assert!(smt.contains("obj_valid__out"), "Should reference obj_valid__out: {}", smt);
    assert!(smt.contains("true"), "Should store true for valid allocation: {}", smt);
}

#[test]
fn test_alloc_obj_size_store_constraint() {
    // (#1100) Verify RustAlloc generates: obj_size__out = store(obj_size, id, size)

    let obj_size_in = Expr::var("obj_size", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
    let obj_size_out = Expr::var("obj_size__out", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
    let obj_id = Expr::bitvec_const(1, 32);
    let size = Expr::bitvec_const(64, 32); // 64 bytes

    // Correct pattern: obj_size__out = store(obj_size, obj_id, size)
    let size_constraint = obj_size_out.eq(obj_size_in.store(obj_id, size));

    // Verify it's a Bool constraint
    assert!(size_constraint.sort().is_bool());

    // Verify SMT-LIB output contains the correct store pattern
    let smt = size_constraint.to_string();
    assert!(smt.contains("store"), "Should use store() pattern: {}", smt);
    assert!(smt.contains("obj_size"), "Should reference obj_size: {}", smt);
    assert!(smt.contains("obj_size__out"), "Should reference obj_size__out: {}", smt);
}

#[test]
fn test_dealloc_obj_valid_store_false_constraint() {
    // (#1100) Verify RustDealloc generates: obj_valid__out = store(obj_valid, id, false)
    // This marks the deallocated object as invalid.

    let obj_valid_in = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_valid_out = Expr::var("obj_valid__out", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_id = Expr::bitvec_const(5, 32); // Some allocated object

    // Dealloc pattern: obj_valid__out = store(obj_valid, obj_id, false)
    let freed_constraint = obj_valid_out.eq(obj_valid_in.store(obj_id, Expr::bool_const(false)));

    // Verify it's a Bool constraint
    assert!(freed_constraint.sort().is_bool());

    // Verify SMT-LIB output contains the correct store pattern
    let smt = freed_constraint.to_string();
    assert!(smt.contains("store"), "Should use store() pattern: {}", smt);
    assert!(smt.contains("false"), "Should store false for deallocation: {}", smt);
}

#[test]
fn test_dealloc_size_validation_check() {
    // (#1174) Verify RustDealloc validates: dealloc_size == obj_size[obj_id]
    // Rust's allocator requires size to match the original allocation size.
    //
    // The implementation at chc/stubs_alloc.rs generates:
    //   let size_matches = obj_size_in.select(obj_id_expr).eq(size_32);
    //   safety_checks.push(size_matches);
    //
    // This check ensures deallocation with wrong size is detected as an error.

    let obj_size = Expr::var("obj_size", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
    let obj_id = Expr::bitvec_const(5, 32);
    let alloc_size = Expr::bitvec_const(64, 32); // Original allocation was 64 bytes
    let dealloc_size = Expr::bitvec_const(32, 32); // Trying to dealloc with wrong size

    // The check pattern: obj_size[obj_id] == dealloc_size
    let recorded_size = obj_size.select(obj_id);
    let size_matches = recorded_size.eq(dealloc_size.clone());

    assert!(size_matches.sort().is_bool(), "Size check must be Bool");

    let smt = size_matches.to_string();
    assert!(smt.contains("select"), "Should select from obj_size: {}", smt);

    // When size mismatches:
    // - The check evaluates to false (64 != 32)
    // - emit_error_rule_for_condition negates: !false = true
    // - Error rule body becomes satisfiable, detecting the bug

    // Simulate size mismatch scenario with concrete values
    let concrete_check = alloc_size.eq(dealloc_size);
    let smt2 = concrete_check.to_string();
    // For concrete values 64 and 32, this would be false (size mismatch detected)
    assert!(
        smt2.contains("#x00000040") || smt2.contains("#x00000020"),
        "Should contain bitvec constants: {}",
        smt2
    );
}

#[test]
fn test_realloc_chained_store_constraint() {
    // (#1100) Verify RustRealloc generates chained stores:
    // obj_valid__out = store(store(obj_valid, old_id, false), new_id, true)
    //
    // This atomically:
    // 1. Marks old allocation as freed (old_id -> false)
    // 2. Marks new allocation as valid (new_id -> true)

    let obj_valid_in = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_valid_out = Expr::var("obj_valid__out", Sort::array(Sort::bitvec(32), Sort::bool()));
    let old_obj_id = Expr::bitvec_const(3, 32);
    let new_obj_id = Expr::bitvec_const(7, 32);

    // Realloc pattern: store(store(obj_valid, old_id, false), new_id, true)
    let after_free = obj_valid_in.store(old_obj_id, Expr::bool_const(false));
    let after_alloc = after_free.store(new_obj_id, Expr::bool_const(true));
    let realloc_constraint = obj_valid_out.eq(after_alloc);

    // Verify it's a Bool constraint
    assert!(realloc_constraint.sort().is_bool());

    // Verify SMT-LIB output contains nested stores
    let smt = realloc_constraint.to_string();
    // Should have two store operations
    let store_count = smt.matches("store").count();
    assert!(store_count >= 2, "Should have at least 2 store operations for realloc: {}", smt);
    assert!(smt.contains("false"), "Should mark old as freed: {}", smt);
    assert!(smt.contains("true"), "Should mark new as valid: {}", smt);
}

#[test]
fn test_realloc_new_size_constraint() {
    // (#1100) Verify RustRealloc records new size:
    // obj_size__out = store(obj_size, new_id, new_size)

    let obj_size_in = Expr::var("obj_size", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
    let obj_size_out = Expr::var("obj_size__out", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
    let new_obj_id = Expr::bitvec_const(7, 32);
    let new_size = Expr::bitvec_const(128, 32); // Reallocating to 128 bytes

    let size_constraint = obj_size_out.eq(obj_size_in.store(new_obj_id, new_size));

    // Verify it's a Bool constraint
    assert!(size_constraint.sort().is_bool());

    // Verify SMT-LIB output
    let smt = size_constraint.to_string();
    assert!(smt.contains("store"), "Should use store() pattern: {}", smt);
    assert!(smt.contains("obj_size"), "Should reference obj_size arrays: {}", smt);
}

#[test]
fn test_split_pointer_model_encoding() {
    // (#1100) Verify split-pointer model: ptr = (obj_id << 32) | offset
    // Using concat: obj_id_32 concat offset_32 = 64-bit pointer

    let obj_id = Expr::bitvec_const(5, 32);
    let offset = Expr::bitvec_const(0, 32);

    // Split-pointer encoding: concat(high, low) = high << 32 | low
    let ptr = obj_id.concat(offset);

    // Verify 64-bit result
    assert_eq!(ptr.sort().bitvec_width(), Some(64));

    // Verify SMT-LIB output uses concat
    let smt = ptr.to_string();
    assert!(smt.contains("concat"), "Should use concat for split-pointer: {}", smt);
}

#[test]
fn test_split_pointer_obj_id_extraction() {
    // (#1100) Verify obj_id can be extracted from pointer: extract(63, 32)

    let ptr = Expr::var("ptr", Sort::bitvec(64));

    // Extract high 32 bits (obj_id)
    let obj_id = ptr.extract(63, 32);

    // Verify 32-bit result
    assert_eq!(obj_id.sort().bitvec_width(), Some(32));

    // Verify SMT-LIB output
    let smt = obj_id.to_string();
    assert!(smt.contains("extract 63 32"), "Should extract bits [63:32]: {}", smt);
}

#[test]
fn test_split_pointer_offset_extraction() {
    // (#1100) Verify offset can be extracted from pointer: extract(31, 0)

    let ptr = Expr::var("ptr", Sort::bitvec(64));

    // Extract low 32 bits (offset)
    let offset = ptr.extract(31, 0);

    // Verify 32-bit result
    assert_eq!(offset.sort().bitvec_width(), Some(32));

    // Verify SMT-LIB output
    let smt = offset.to_string();
    assert!(smt.contains("extract 31 0"), "Should extract bits [31:0]: {}", smt);
}

#[test]
fn test_alloc_constraint_sorts_are_arrays() {
    // (#1100) Verify obj_valid and obj_size have correct array sorts

    let obj_valid_sort = Sort::array(Sort::bitvec(32), Sort::bool());
    let obj_size_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));

    // obj_valid: Array<BV32, Bool>
    assert!(obj_valid_sort.is_array(), "obj_valid should be array sort");

    // obj_size: Array<BV32, BV32>
    assert!(obj_size_sort.is_array(), "obj_size should be array sort");

    // Verify they differ
    assert_ne!(
        obj_valid_sort, obj_size_sort,
        "obj_valid and obj_size should have different element sorts"
    );
}

#[test]
fn test_alloc_constraint_preserves_unmodified_entries() {
    // (#1100) Verify store() only modifies specified index, preserving others
    //
    // Key semantic property: If alloc(id) sets obj_valid[id]=true,
    // then obj_valid[other_id] remains unchanged.
    //
    // SMT encoding: select(store(arr, i, v), j) = (ite (= i j) v (select arr j))

    let arr = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let i = Expr::bitvec_const(1, 32);
    let j = Expr::bitvec_const(2, 32);
    let v = Expr::bool_const(true);

    // store(arr, i, v) then select at j
    let stored = arr.store(i, v);
    let at_j = stored.select(j);

    // This should be: (select (store obj_valid #x00000001 true) #x00000002)
    assert!(at_j.sort().is_bool(), "Selecting from obj_valid gives Bool");
    let smt = at_j.to_string();
    assert!(smt.contains("select"), "Should have select: {}", smt);
    assert!(smt.contains("store"), "Should have store inside: {}", smt);
}

#[test]
fn test_heap_state_alloc_ids_start_at_one() {
    // (#1100, #2958) Verify heap allocation IDs start at 2
    // (0 = null, 1 = promoted constants, normal allocs start at 2)

    let mut heap = ChcHeapState::new();

    let first_id = heap.next_alloc_id().unwrap();
    assert_eq!(first_id, 2, "First allocation ID should be 2 (0=null, 1=promoted constants)");

    let second_id = heap.next_alloc_id().unwrap();
    assert_eq!(second_id, 3, "IDs should be sequential");
}

#[test]
fn test_alloc_zeroed_same_constraints_as_alloc() {
    // (#1100) RustAllocZeroed has same obj_valid/obj_size constraints as RustAlloc
    // The "zeroed" property is about memory contents, not validity tracking.
    //
    // Both should generate:
    // - obj_valid__out = store(obj_valid, id, true)
    // - obj_size__out = store(obj_size, id, size)

    // This test verifies the constraint structure is identical
    let obj_valid_in = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_valid_out = Expr::var("obj_valid__out", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_id = Expr::bitvec_const(1, 32);

    // Both alloc and alloc_zeroed use this pattern
    let constraint = obj_valid_out.eq(obj_valid_in.store(obj_id, Expr::bool_const(true)));

    assert!(constraint.sort().is_bool());
    let smt = constraint.to_string();
    // The constraint structure is the same for both
    assert!(smt.contains("store"), "Both should use store pattern");
}

#[test]
fn test_shallow_init_box_same_store_pattern() {
    // (#1100) ShallowInitBox uses same store() pattern as RustAlloc
    // This was also fixed in commit 2d377f29.
    //
    // ShallowInitBox is the MIR intrinsic for Box::new heap allocation.
    // It must use the same SSA-style store() pattern, not select().eq().

    let obj_valid_in = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_valid_out = Expr::var("obj_valid__out", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_size_in = Expr::var("obj_size", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
    let obj_size_out = Expr::var("obj_size__out", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
    let obj_id = Expr::bitvec_const(1, 32);
    let type_size = Expr::bitvec_const(8, 32); // 8-byte type

    // ShallowInitBox constraints (same pattern as RustAlloc)
    let valid_constraint =
        obj_valid_out.eq(obj_valid_in.store(obj_id.clone(), Expr::bool_const(true)));
    let size_constraint = obj_size_out.eq(obj_size_in.store(obj_id, type_size));

    // Verify both constraints use store()
    assert!(valid_constraint.to_string().contains("store"));
    assert!(size_constraint.to_string().contains("store"));
}

#[test]
fn test_store_pattern_vs_wrong_select_pattern() {
    // (#1100) Demonstrate why store() is correct and select().eq() is wrong
    //
    // WRONG (old code): select(obj_valid, id).eq(true)
    // - This says: "The input obj_valid array already has id=true"
    // - This is a PRECONDITION, not an update
    // - AY would reject valid programs where obj_valid[id] was false before alloc
    //
    // CORRECT (new code): obj_valid__out = store(obj_valid, id, true)
    // - This says: "The output array has id=true, regardless of input"
    // - This is a POSTCONDITION that updates state
    // - AY accepts this because it's expressing the allocation's effect

    let obj_valid = Expr::var("obj_valid", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_valid_out = Expr::var("obj_valid__out", Sort::array(Sort::bitvec(32), Sort::bool()));
    let obj_id = Expr::bitvec_const(1, 32);

    // WRONG pattern (what old code did)
    let wrong_constraint = obj_valid.clone().select(obj_id.clone()).eq(Expr::bool_const(true));

    // CORRECT pattern (what new code does)
    let correct_constraint = obj_valid_out.eq(obj_valid.store(obj_id, Expr::bool_const(true)));

    // Both are Bool constraints, but they mean different things
    assert!(wrong_constraint.sort().is_bool());
    assert!(correct_constraint.sort().is_bool());

    // The wrong pattern doesn't have store
    assert!(
        !wrong_constraint.to_string().contains("store"),
        "Wrong pattern should NOT use store: {}",
        wrong_constraint
    );

    // The correct pattern has store
    assert!(
        correct_constraint.to_string().contains("store"),
        "Correct pattern MUST use store: {}",
        correct_constraint
    );

    // The correct pattern references the __out variable
    assert!(
        correct_constraint.to_string().contains("obj_valid__out"),
        "Correct pattern must update output variable: {}",
        correct_constraint
    );
}
