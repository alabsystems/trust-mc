// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for memory model.
//!
//! Extracted from memory/mod.rs as part of #2836.

use crate::codegen_ay::context::with_test_ay_ctx;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::{Expr, Sort};
use std::panic::{AssertUnwindSafe, catch_unwind};

// =========================================================================
// init_memory
// =========================================================================

#[test]
fn test_init_memory_creates_symbolic_array() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let mem = ctx.memory().clone();
        assert!(mem.sort().is_array(), "memory should be an array sort");
        assert_eq!(mem, Expr::var("memory", Sort::memory()));
    });
}

#[test]
fn test_init_memory_idempotent() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let mem1 = ctx.memory().clone();
        ctx.init_memory(); // second call should be no-op
        let mem2 = ctx.memory().clone();
        assert_eq!(mem1, mem2, "double init should not change memory");
    });
}

#[test]
fn test_memory_panics_before_init() {
    with_test_ay_ctx(|ctx| {
        let result = catch_unwind(AssertUnwindSafe(|| ctx.memory()));
        assert!(result.is_err(), "memory() before init_memory() should panic");
    });
}

// =========================================================================
// store_memory / load_memory roundtrip
// =========================================================================

#[test]
fn test_store_load_single_byte() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(100u128, POINTER_WIDTH);
        let val = Expr::bitvec_const(0x42u128, 8);
        ctx.store_memory(addr.clone(), val);
        let loaded = ctx.load_memory(addr);
        // loaded is select(store(memory, addr, 0x42), addr) which simplifies
        // structurally but we verify the sort is correct
        assert_eq!(
            loaded.sort().bitvec_width(),
            Some(8),
            "load from byte-addressed memory should return 8-bit value"
        );
    });
}

#[test]
fn test_store_memory_coerces_narrow_addr() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let mem_before = ctx.memory().clone();
        // 32-bit address should be coerced to POINTER_WIDTH
        let narrow_addr = Expr::bitvec_const(5u128, 32);
        let val = Expr::bitvec_const(0xFFu128, 8);
        ctx.store_memory(narrow_addr, val);
        let mem_after = ctx.memory().clone();
        assert_ne!(
            mem_before, mem_after,
            "store with narrow (32-bit) address should still update memory array"
        );
    });
}

// =========================================================================
// load_memory_bytes
// =========================================================================

#[test]
fn test_load_memory_bytes_zero_returns_1bit_marker() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let result = ctx.load_memory_bytes(addr, 0);
        assert_eq!(result, Expr::bitvec_const(0, 1), "0-byte load should return 1-bit zero marker");
    });
}

#[test]
fn test_load_memory_bytes_one_is_single_select() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let single = ctx.load_memory_bytes(addr.clone(), 1);
        let direct = ctx.load_memory(addr);
        assert_eq!(single, direct, "1-byte load should be equivalent to single load_memory");
    });
}

#[test]
fn test_load_memory_bytes_multi_has_correct_width() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let four_bytes = ctx.load_memory_bytes(addr.clone(), 4);
        assert_eq!(
            four_bytes.sort().bitvec_width(),
            Some(32),
            "4-byte load should produce 32-bit bitvector"
        );

        let eight_bytes = ctx.load_memory_bytes(addr, 8);
        assert_eq!(
            eight_bytes.sort().bitvec_width(),
            Some(64),
            "8-byte load should produce 64-bit bitvector"
        );
    });
}

// =========================================================================
// store_memory_bytes — bitvec paths
// =========================================================================

#[test]
fn test_store_memory_bytes_single_byte() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let mem_before = ctx.memory().clone();
        let addr = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let val = Expr::bitvec_const(0xABu128, 8);
        ctx.store_memory_bytes(addr, val);
        let mem_after = ctx.memory().clone();
        assert_ne!(mem_before, mem_after, "single-byte store should update memory");
    });
}

#[test]
fn test_store_memory_bytes_multi_byte_little_endian() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let val = Expr::bitvec_const(0x1234u128, 16);
        let mem_before = ctx.memory().clone();
        ctx.store_memory_bytes(addr, val);
        let mem_after = ctx.memory().clone();
        assert_ne!(mem_before, mem_after, "store should update memory array");
    });
}

#[test]
fn test_store_memory_bytes_sub_byte_value_zero_extends() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let mem_before = ctx.memory().clone();
        // 3-bit value should be zero-extended to 8 bits (1 byte)
        let val = Expr::bitvec_const(5u128, 3);
        ctx.store_memory_bytes(addr, val);
        let mem_after = ctx.memory().clone();
        assert_ne!(
            mem_before, mem_after,
            "store of sub-byte (3-bit) value should update memory after zero-extension"
        );
    });
}

// =========================================================================
// store_memory_bytes — Bool path
// =========================================================================

#[test]
fn test_store_memory_bytes_bool_true_becomes_ite() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let bool_val = Expr::bool_const(true);
        let mem_before = ctx.memory().clone();
        ctx.store_memory_bytes(addr, bool_val);
        let mem_after = ctx.memory().clone();
        assert_ne!(mem_before, mem_after, "bool store should update memory");
    });
}

#[test]
fn test_store_memory_bytes_bool_false_becomes_ite() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let bool_val = Expr::bool_const(false);
        let mem_before = ctx.memory().clone();
        ctx.store_memory_bytes(addr, bool_val);
        let mem_after = ctx.memory().clone();
        assert_ne!(mem_before, mem_after, "bool(false) store should update memory");
    });
}

// =========================================================================
// store_memory_bytes — Int/Array/Datatype symbolic path
// =========================================================================

#[test]
fn test_store_memory_bytes_int_sort_tracks_symbolically() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let int_val = Expr::int_const(42);
        let mem_before = ctx.memory().clone();
        ctx.store_memory_bytes(addr, int_val);
        // Int values are tracked symbolically — memory array is NOT updated
        let mem_after = ctx.memory().clone();
        assert_eq!(
            mem_before, mem_after,
            "Int sort should be stored symbolically, not in byte memory"
        );
    });
}

#[test]
fn test_store_memory_bytes_array_sort_tracks_symbolically() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8));
        let arr_val = ctx.declare_var("test_arr", arr_sort);
        let mem_before = ctx.memory().clone();
        ctx.store_memory_bytes(addr, arr_val);
        let mem_after = ctx.memory().clone();
        assert_eq!(
            mem_before, mem_after,
            "Array sort should be stored symbolically, not in byte memory"
        );
    });
}

#[test]
fn test_load_symbolic_memory_value_roundtrips_non_bitvec_store() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(11u128, POINTER_WIDTH);
        let other_addr = Expr::bitvec_const(12u128, POINTER_WIDTH);
        ctx.store_memory_bytes(addr.clone(), Expr::int_const(123));

        let recovered = ctx
            .load_symbolic_memory_value(addr)
            .expect("symbolic store must be recoverable at the same address");
        assert!(recovered.sort().is_int(), "recovered symbolic value should preserve Int sort");
        assert!(
            ctx.load_symbolic_memory_value(other_addr).is_none(),
            "different address must not recover symbolic value"
        );
    });
}

#[test]
fn test_load_memory_bytes_panics_after_symbolic_store_same_addr() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(7u128, POINTER_WIDTH);
        ctx.store_memory_bytes(addr.clone(), Expr::int_const(123));

        let result = catch_unwind(AssertUnwindSafe(|| ctx.load_memory_bytes(addr, 8)));
        assert!(
            result.is_err(),
            "loading bytes from addr with prior symbolic Int store must fail closed"
        );
    });
}

#[test]
fn test_load_memory_bytes_after_symbolic_store_different_addr_is_allowed() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let sym_addr = Expr::bitvec_const(7u128, POINTER_WIDTH);
        let other_addr = Expr::bitvec_const(8u128, POINTER_WIDTH);
        ctx.store_memory_bytes(sym_addr, Expr::int_const(123));

        let result = catch_unwind(AssertUnwindSafe(|| ctx.load_memory_bytes(other_addr, 4)));
        assert!(result.is_ok(), "load at unrelated addr should not panic");
        let loaded = result.expect("load should succeed for unrelated addr");
        assert_eq!(loaded.sort().bitvec_width(), Some(32), "4-byte load should be 32-bit");
    });
}

// =========================================================================
// load_memory — fail-closed guard for symbolic stores (#2599)
// =========================================================================

/// Regression test: load_memory (single byte) must panic at an address
/// that was previously written with a non-bitvec symbolic store.
/// This closes the gap where codegen_copy.rs called load_memory directly,
/// bypassing the load_memory_bytes guard. Part of #2599.
#[test]
fn test_load_memory_panics_after_symbolic_store_same_addr() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let addr = Expr::bitvec_const(42u128, POINTER_WIDTH);
        ctx.store_memory_bytes(addr.clone(), Expr::int_const(999));

        let result = catch_unwind(AssertUnwindSafe(|| ctx.load_memory(addr)));
        assert!(
            result.is_err(),
            "load_memory at addr with prior symbolic Int store must fail closed"
        );
    });
}

#[test]
fn test_load_memory_allowed_after_symbolic_store_different_addr() {
    with_test_ay_ctx(|mut ctx| {
        ctx.init_memory();
        let sym_addr = Expr::bitvec_const(42u128, POINTER_WIDTH);
        let other_addr = Expr::bitvec_const(43u128, POINTER_WIDTH);
        ctx.store_memory_bytes(sym_addr, Expr::int_const(999));

        let result = catch_unwind(AssertUnwindSafe(|| ctx.load_memory(other_addr)));
        assert!(result.is_ok(), "load_memory at unrelated addr should not panic");
    });
}

// =========================================================================
// Combined original mega-test (preserved for regression)
// =========================================================================

#[test]
fn test_memory_load_store_semantics() {
    with_test_ay_ctx(|mut ctx| {
        let addr0 = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let addr1 = Expr::bitvec_const(1u128, POINTER_WIDTH);
        let offset0 = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let offset1 = Expr::bitvec_const(1u128, POINTER_WIDTH);
        let offset2 = Expr::bitvec_const(2u128, POINTER_WIDTH);

        let uninit = catch_unwind(AssertUnwindSafe(|| ctx.memory()));
        assert!(uninit.is_err(), "memory access before init should panic");

        ctx.init_memory();
        let mem0 = ctx.memory().clone();
        assert_eq!(mem0, Expr::var("memory", Sort::memory()));

        let byte0 = Expr::bitvec_const(0xABu128, 8);
        let expected_mem1 = mem0.store(addr0.clone(), byte0.clone());
        ctx.store_memory(addr0.clone(), byte0);
        assert_eq!(ctx.memory(), &expected_mem1);

        let load0 = ctx.load_memory(addr0.clone());
        assert_eq!(load0, expected_mem1.clone().select(addr0.clone()));

        let byte1 = Expr::bitvec_const(0xCDu128, 8);
        let expected_mem2 = expected_mem1.store(addr1.clone(), byte1.clone());
        ctx.store_memory(addr1.clone(), byte1);
        assert_eq!(ctx.memory(), &expected_mem2);

        let zero = ctx.load_memory_bytes(addr0.clone(), 0);
        assert_eq!(zero, Expr::bitvec_const(0, 1));

        let single = ctx.load_memory_bytes(addr0.clone(), 1);
        assert_eq!(single, expected_mem2.clone().select(addr0.clone()));

        let multi = ctx.load_memory_bytes(addr0.clone(), 3);
        let expected_multi = expected_mem2.clone().select(addr0.clone().bvadd(offset2)).concat(
            expected_mem2
                .clone()
                .select(addr0.clone().bvadd(offset1.clone()))
                .concat(expected_mem2.clone().select(addr0.clone())),
        );
        assert_eq!(multi, expected_multi);

        let value = Expr::bitvec_const(0x1122u128, 16);
        let expected_mem3 = expected_mem2
            .store(addr0.clone().bvadd(offset0.clone()), value.clone().extract(7, 0))
            .store(addr0.clone().bvadd(offset1.clone()), value.extract(15, 8));
        ctx.store_memory_bytes(addr0.clone(), Expr::bitvec_const(0x1122u128, 16));
        assert_eq!(ctx.memory(), &expected_mem3);

        let tiny = Expr::bitvec_const(1u128, 1);
        let expected_mem4 = expected_mem3
            .store(addr1.clone().bvadd(offset0.clone()), tiny.clone().zero_extend(7).extract(7, 0));
        ctx.store_memory_bytes(addr1.clone(), tiny);
        assert_eq!(ctx.memory(), &expected_mem4);

        let nine_bit = Expr::bitvec_const(0x101u128, 9);
        let nine_extended = nine_bit.clone().zero_extend(7);
        let expected_mem5 = expected_mem4
            .store(addr0.clone().bvadd(offset0), nine_extended.clone().extract(7, 0))
            .store(addr0.clone().bvadd(offset1), nine_extended.extract(15, 8));
        ctx.store_memory_bytes(addr0.clone(), nine_bit);
        assert_eq!(ctx.memory(), &expected_mem5);

        // #923: Bool values are converted to bitvec(8) via ITE - test the conversion
        // true -> ite(true, 1, 0), false -> ite(false, 1, 0) (Part of #744)
        let bool_true = Expr::bool_const(true);
        let bool_true_as_bv = Expr::ite(
            bool_true.clone(),
            Expr::bitvec_const(1u128, 8),
            Expr::bitvec_const(0u128, 8),
        );
        let expected_mem_bool = expected_mem5.store(addr0.clone(), bool_true_as_bv);
        ctx.store_memory_bytes(addr0, bool_true);
        assert_eq!(ctx.memory(), &expected_mem_bool);

        // Also test false
        let bool_false = Expr::bool_const(false);
        let bool_false_as_bv = Expr::ite(
            bool_false.clone(),
            Expr::bitvec_const(1u128, 8),
            Expr::bitvec_const(0u128, 8),
        );
        let expected_mem_bool2 = expected_mem_bool.store(addr1.clone(), bool_false_as_bv);
        ctx.store_memory_bytes(addr1, bool_false);
        assert_eq!(ctx.memory(), &expected_mem_bool2);
    });
}
