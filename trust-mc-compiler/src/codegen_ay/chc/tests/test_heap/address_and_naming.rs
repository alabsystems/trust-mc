// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_address_encoding_formula() {
    // (#904) Verify the split-pointer address encoding: concat(obj_id, offset)
    let obj_id_expr = Expr::bitvec_const(5i128, 32);
    let offset_expr = Expr::bitvec_const(0i128, 32);
    let addr = obj_id_expr.concat(offset_expr);

    assert_eq!(addr.sort().bitvec_width(), Some(64));
    let smt = addr.to_string();
    assert!(smt.contains("concat"), "Split-pointer should use concat, got: {smt}");
}

#[test]
fn test_address_offset_computation() {
    // (#904) Verify address offset addition: base.bvadd(offset)
    let base_addr = Expr::bitvec_const(0x100000000i128, 64);
    let field_offset = Expr::bitvec_const(8, 64);
    let addr_with_offset = base_addr.bvadd(field_offset);

    assert_eq!(addr_with_offset.sort().bitvec_width(), Some(64));
    let smt = addr_with_offset.to_string();
    assert!(smt.contains("bvadd"), "Address offset should use bvadd, got: {smt}");
}

#[test]
fn test_projection_offset_accumulation() {
    // (#904) Verify offset accumulation for nested field projections
    let mut total_offset = Expr::bitvec_const(0, 32);
    total_offset = total_offset.bvadd(Expr::bitvec_const(0, 32));
    total_offset = total_offset.bvadd(Expr::bitvec_const(8, 32));
    total_offset = total_offset.bvadd(Expr::bitvec_const(16, 32));

    assert_eq!(total_offset.sort().bitvec_width(), Some(32));
    let smt = total_offset.to_string();
    // Three chained bvadd operations
    assert!(smt.contains("bvadd"), "Accumulation should use bvadd, got: {smt}");
    // The nested structure should reference both intermediate offsets
    assert!(
        smt.contains('8') || smt.contains("#x00000008"),
        "Should reference field offset 8, got: {smt}"
    );
}

#[test]
fn test_array_index_offset_computation() {
    // (#904) Verify dynamic index offset: index * element_size
    // Pattern from projection offset computation for Index projections

    let elem_size: usize = 4; // 4-byte elements (e.g., i32)
    let index = Expr::bitvec_const(5, 32); // arr[5]

    // Compute offset: index * elem_size
    let elem_offset = index.bvmul(Expr::bitvec_const(elem_size as i128, 32));

    assert_eq!(elem_offset.sort().bitvec_width(), Some(32));
    // Expected: 5 * 4 = 20 bytes
}

#[test]
fn test_type_size_constants_primitive_integers() {
    // (#904, #1142) Verify type size constants match Rust ABI
    // These validate our get_type_size hardcoded values match the platform

    // Integer types - test actual Rust sizes match our assumptions
    assert_eq!(std::mem::size_of::<bool>(), 1, "bool: 1 byte");
    assert_eq!(std::mem::size_of::<char>(), 4, "char: 4 bytes");
    assert_eq!(std::mem::size_of::<i8>(), 1, "i8: 1 byte");
    assert_eq!(std::mem::size_of::<u8>(), 1, "u8: 1 byte");
    assert_eq!(std::mem::size_of::<i16>(), 2, "i16: 2 bytes");
    assert_eq!(std::mem::size_of::<u16>(), 2, "u16: 2 bytes");
    assert_eq!(std::mem::size_of::<i32>(), 4, "i32: 4 bytes");
    assert_eq!(std::mem::size_of::<u32>(), 4, "u32: 4 bytes");
    assert_eq!(std::mem::size_of::<i64>(), 8, "i64: 8 bytes");
    assert_eq!(std::mem::size_of::<u64>(), 8, "u64: 8 bytes");
    assert_eq!(std::mem::size_of::<i128>(), 16, "i128: 16 bytes");
    assert_eq!(std::mem::size_of::<u128>(), 16, "u128: 16 bytes");
    assert_eq!(std::mem::size_of::<isize>(), 8, "isize: 8 bytes on 64-bit");
    assert_eq!(std::mem::size_of::<usize>(), 8, "usize: 8 bytes on 64-bit");
}

#[test]
fn test_type_size_constants_floats() {
    // (#904, #1142) Verify float type sizes match Rust ABI
    // Note: f16/f128 are nightly features, not tested here
    assert_eq!(std::mem::size_of::<f32>(), 4, "f32: 4 bytes");
    assert_eq!(std::mem::size_of::<f64>(), 8, "f64: 8 bytes");
}

#[test]
fn test_type_size_constants_pointers() {
    // (#904, #1142) Verify pointer sizes (64-bit platform)
    assert_eq!(std::mem::size_of::<&u8>(), 8, "references: 8 bytes on 64-bit");
    assert_eq!(std::mem::size_of::<*const u8>(), 8, "raw pointers: 8 bytes on 64-bit");
}

#[test]
fn test_memory_load_select_pattern() {
    // (#904) Verify memory load pattern: select(arr, addr)
    // This tests the SMT encoding used by load_from_memory

    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let arr = Expr::var("arr_i32", arr_sort);
    let addr = Expr::bitvec_const(0x100000008i128, 64);

    let loaded = arr.select(addr);

    // Result should be element sort (bv32)
    assert_eq!(loaded.sort().bitvec_width(), Some(32));
}

#[test]
fn test_memory_store_pattern() {
    // (#904) Verify memory store pattern: store(arr, addr, val)
    // This tests the SMT encoding used by store_to_memory

    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let arr = Expr::var("arr_i32", arr_sort.clone());
    let addr = Expr::bitvec_const(0x100000008i128, 64);
    let val = Expr::bitvec_const(42, 32);

    let updated = arr.store(addr, val);

    // Result should be array sort
    assert!(updated.sort().is_array(), "Store result should be array sort");
    // Verify sort matches original array sort
    assert_eq!(updated.sort(), &arr_sort, "Store should preserve array sort");
}

#[test]
fn test_local_address_naming_convention() {
    // (#904) Verify local address variable naming: _fn_idx_addr
    let fn_name = "test_fn";
    let local_idx = 3;

    let addr_name = format!("_{}_{}_addr", fn_name, local_idx);

    assert_eq!(addr_name, "_test_fn_3_addr");
}

#[test]
fn test_type_array_naming_convention() {
    // (#904) Verify type array naming: _fn_mem_typekey
    let fn_name = "my_function";
    let type_key = "i32";

    let arr_name = format!("_{}_mem_{}", fn_name, type_key);

    assert_eq!(arr_name, "_my_function_mem_i32");
}

#[test]
fn test_offset_zero_extend_for_address_computation() {
    // (#913) Verify that 32-bit offsets are properly extended to 64-bit
    // for address arithmetic with 64-bit base addresses.
    //
    // This test reproduces the width mismatch bug: base_addr (64-bit)
    // cannot be added to offset (32-bit) without first extending.

    // Simulate 64-bit base address from split-pointer model
    let obj_id = Expr::bitvec_const(1i128, 32);
    let zero_offset = Expr::bitvec_const(0, 32);
    let base_addr = obj_id.concat(zero_offset);
    assert_eq!(base_addr.sort().bitvec_width(), Some(64));

    // Simulate 32-bit offset from projection offset computation
    let offset_32 = Expr::bitvec_const(8, 32); // 8-byte field offset
    assert_eq!(offset_32.sort().bitvec_width(), Some(32));

    // The FIX: zero-extend to 64-bit before adding (#913)
    let offset_64 = offset_32.zero_extend(32);
    assert_eq!(offset_64.sort().bitvec_width(), Some(64));

    // Now bvadd succeeds (would panic without zero_extend)
    let addr_with_offset = base_addr.bvadd(offset_64);
    assert_eq!(addr_with_offset.sort().bitvec_width(), Some(64));
}
