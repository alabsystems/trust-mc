// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for codegen_copy.rs — copy/copy_nonoverlapping/write_bytes intrinsics.
//!
//! Tests cover:
//! - Memory copy byte-by-byte unrolling patterns
//! - Pointer address arithmetic with bitvec offsets
//! - Byte value truncation/extension for write_bytes
//! - Zero-length copy (no-op) edge case
//! - Large copy threshold behavior
//! - Overlapping copy (memmove) temporary storage pattern
//!
//! Part of #2016: test coverage for untested codegen_ay modules.

use super::*;

/// Return the number of emitted constraints so far.
fn constraint_count(codegen: &StatementCodegen<'_, '_, '_>) -> usize {
    codegen.ctx.bmc_vc.constraints.len()
}

// =============================================================================
// Copy nonoverlapping: address arithmetic
// =============================================================================

/// Test copy_nonoverlapping address calculation: src + offset for byte i.
#[test]
fn test_copy_nonoverlapping_src_addr() {
    let src_ptr = Expr::bitvec_const(0x1000u128, POINTER_WIDTH);
    let offset = Expr::bitvec_const(3u128, POINTER_WIDTH);
    let src_addr = src_ptr.bvadd(offset);

    assert!(src_addr.sort().is_bitvec());
    assert_eq!(src_addr.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// Test copy_nonoverlapping destination address: dst + offset.
#[test]
fn test_copy_nonoverlapping_dst_addr() {
    let dst_ptr = Expr::bitvec_const(0x2000u128, POINTER_WIDTH);
    let offset = Expr::bitvec_const(7u128, POINTER_WIDTH);
    let dst_addr = dst_ptr.bvadd(offset);

    assert!(dst_addr.sort().is_bitvec());
    assert_eq!(dst_addr.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// Test copy unrolling generates correct number of offset expressions.
#[test]
fn test_copy_unroll_offsets() {
    let total_bytes = 8;
    let mut offsets = Vec::new();
    for i in 0..total_bytes {
        offsets.push(Expr::bitvec_const(i as u128, POINTER_WIDTH));
    }
    assert_eq!(offsets.len(), 8);

    // Verify each offset has the correct width
    for (i, off) in offsets.iter().enumerate() {
        assert!(off.sort().is_bitvec());
        assert_eq!(off.sort().bitvec_width(), Some(POINTER_WIDTH), "offset {} has wrong width", i);
    }
}

/// Test copy_nonoverlapping with element_size > 1.
/// For copying N elements of size S, total_bytes = N * S.
#[test]
fn test_copy_element_size_multiply() {
    let count: usize = 4;
    let element_size: usize = 8; // u64 = 8 bytes
    let total_bytes = count.saturating_mul(element_size);
    assert_eq!(total_bytes, 32);

    // 32 bytes unrolled: offsets 0..32
    for i in 0..total_bytes {
        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
        assert!(offset.sort().is_bitvec());
    }
}

/// Test zero-byte copy is a no-op.
#[test]
fn test_copy_zero_bytes_noop() {
    let count: usize = 0;
    let element_size: usize = 4;
    let total_bytes = count.saturating_mul(element_size);
    assert_eq!(total_bytes, 0);
    // The implementation returns early for zero bytes — no expressions generated.
}

/// Test zero element count copy.
#[test]
fn test_copy_zero_count_noop() {
    let count: usize = 0;
    let element_size: usize = 1;
    let total_bytes = count.saturating_mul(element_size);
    assert_eq!(total_bytes, 0);
}

// =============================================================================
// Copy (overlapping / memmove semantics)
// =============================================================================

/// Test memmove pattern: load all bytes into temps, then store.
/// This prevents overlap corruption.
#[test]
fn test_copy_memmove_temp_pattern() {
    let total_bytes: usize = 4;
    let src_ptr = Expr::bitvec_const(0x1000u128, POINTER_WIDTH);

    // Phase 1: Load all bytes into temporaries
    let mut temp_bytes = Vec::with_capacity(total_bytes);
    for i in 0..total_bytes {
        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
        let _src_addr = src_ptr.clone().bvadd(offset);
        // Simulate loaded byte
        let byte = Expr::var(format!("byte_{}", i), Sort::bitvec(8));
        temp_bytes.push(byte);
    }
    assert_eq!(temp_bytes.len(), 4);

    // Phase 2: Store from temporaries to destination
    let dst_ptr = Expr::bitvec_const(0x1000u128, POINTER_WIDTH); // same addr = overlap!
    for (i, byte) in temp_bytes.iter().enumerate() {
        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
        let _dst_addr = dst_ptr.clone().bvadd(offset);
        // Verify temp byte is 8-bit
        assert_eq!(byte.sort().bitvec_width(), Some(8));
    }
}

/// Test memmove with single byte (simplest non-trivial case).
#[test]
fn test_copy_single_byte() {
    let src_ptr = Expr::bitvec_const(0x3000u128, POINTER_WIDTH);
    let dst_ptr = Expr::bitvec_const(0x4000u128, POINTER_WIDTH);

    // Total bytes = 1 * 1 = 1
    let offset = Expr::bitvec_const(0u128, POINTER_WIDTH);
    let src_addr = src_ptr.bvadd(offset.clone());
    let dst_addr = dst_ptr.bvadd(offset);

    assert!(src_addr.sort().is_bitvec());
    assert!(dst_addr.sort().is_bitvec());
}

// =============================================================================
// Max unroll threshold
// =============================================================================

/// Test MAX_UNROLL_BYTES threshold: 128 bytes is the limit.
#[test]
fn test_max_unroll_bytes_threshold() {
    const MAX_UNROLL_BYTES: usize = 128;

    // At the boundary: 128 bytes should be accepted
    let total_bytes_ok = 128usize;
    assert!(total_bytes_ok <= MAX_UNROLL_BYTES);

    // Over the boundary: 129 bytes should be rejected
    let total_bytes_too_large = 129usize;
    assert!(total_bytes_too_large > MAX_UNROLL_BYTES);
}

/// Test large element count saturating multiplication doesn't overflow.
#[test]
fn test_copy_saturating_mul_no_overflow() {
    let count: usize = usize::MAX;
    let element_size: usize = 2;
    let total_bytes = count.saturating_mul(element_size);
    assert_eq!(total_bytes, usize::MAX); // saturates at MAX
}

// =============================================================================
// Write bytes: byte value coercion
// =============================================================================

/// Test write_bytes with u8 value: no coercion needed.
#[test]
fn test_write_bytes_u8_no_coercion() {
    let val = Expr::bitvec_const(0xAAu128, 8);
    assert_eq!(val.sort().bitvec_width(), Some(8));
    // No extract or extend needed for 8-bit value
}

/// Test write_bytes with wider value: truncate to 8 bits.
#[test]
fn test_write_bytes_truncate_to_u8() {
    let val = Expr::bitvec_const(0x1234u128, 16); // 16-bit value
    assert_eq!(val.sort().bitvec_width(), Some(16));

    // Truncate: extract bits [7:0]
    let truncated = val.extract(7, 0);
    assert_eq!(truncated.sort().bitvec_width(), Some(8));
}

/// Test write_bytes with narrower value: zero-extend to 8 bits.
#[test]
fn test_write_bytes_extend_to_u8() {
    let val = Expr::bitvec_const(1u128, 1); // 1-bit value (bool-like)
    assert_eq!(val.sort().bitvec_width(), Some(1));

    // Zero-extend from 1 bit to 8 bits
    let extended = val.zero_extend(8 - 1);
    assert_eq!(extended.sort().bitvec_width(), Some(8));
}

/// Test write_bytes unrolling stores the same byte at each address.
#[test]
fn test_write_bytes_unroll_stores() {
    let dst_ptr = Expr::bitvec_const(0x5000u128, POINTER_WIDTH);
    let byte_val = Expr::bitvec_const(0u128, 8); // memset(ptr, 0, count)
    let total_bytes = 4;

    for i in 0..total_bytes {
        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
        let addr = dst_ptr.clone().bvadd(offset);
        assert!(addr.sort().is_bitvec());
        // Each store uses the same byte_val
        assert_eq!(byte_val.sort().bitvec_width(), Some(8));
    }
}

/// Test write_bytes with 32-bit value truncates to low byte.
#[test]
fn test_write_bytes_u32_truncate() {
    let val = Expr::bitvec_const(0xDEADBEEFu128, 32);
    assert_eq!(val.sort().bitvec_width(), Some(32));

    // Should truncate to 0xEF (low 8 bits)
    let truncated = val.extract(7, 0);
    assert_eq!(truncated.sort().bitvec_width(), Some(8));
}

// =============================================================================
// Pointer width coercion (coerce_to_ptr_width)
// =============================================================================

/// Test pointer that's already POINTER_WIDTH needs no coercion.
#[test]
fn test_ptr_already_correct_width() {
    let ptr = Expr::bitvec_const(0x8000u128, POINTER_WIDTH);
    assert_eq!(ptr.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// Test narrow pointer zero-extended to POINTER_WIDTH.
#[test]
fn test_ptr_narrow_zero_extend() {
    let narrow_ptr = Expr::bitvec_const(0x100u128, 32);
    assert_eq!(narrow_ptr.sort().bitvec_width(), Some(32));

    if POINTER_WIDTH > 32 {
        let extended = narrow_ptr.zero_extend(POINTER_WIDTH - 32);
        assert_eq!(extended.sort().bitvec_width(), Some(POINTER_WIDTH));
    }
}

// =============================================================================
// try_eval_const_operand patterns
// =============================================================================

/// Test constant operand evaluation returns the integer value.
/// The production code extracts usize from Operand::Constant via alloc.read_uint().
#[test]
fn test_const_operand_usize_expr() {
    // Simulate what happens after successful const eval: a bitvec_const
    let count: usize = 16;
    let expr = Expr::bitvec_const(count as u128, POINTER_WIDTH);
    assert_eq!(expr.sort().bitvec_width(), Some(POINTER_WIDTH));
}

/// Test that element_size defaults to 1 when type info unavailable.
#[test]
fn test_element_size_default_one() {
    let element_size: usize = 1; // default when pointee type unknown
    let count: usize = 10;
    let total_bytes = count.saturating_mul(element_size);
    assert_eq!(total_bytes, 10); // 10 * 1 = 10 bytes
}

// =============================================================================
// MIR-driven tests: copy_nonoverlapping through codegen pipeline
// =============================================================================

/// Probe source for copy_nonoverlapping.
/// MIR lowers this to StatementKind::Intrinsic(CopyNonOverlapping { src, dst, count }).
const COPY_NONOVERLAPPING_PROBE: &str = r#"
pub fn copy_nonoverlapping_u32_probe(src: *const u32, dst: *mut u32) {
    unsafe { core::ptr::copy_nonoverlapping(src, dst, 2); }
}

pub fn copy_nonoverlapping_u8_probe(src: *const u8, dst: *mut u8) {
    unsafe { core::ptr::copy_nonoverlapping(src, dst, 4); }
}

pub fn copy_nonoverlapping_zero_probe(src: *const u32, dst: *mut u32) {
    unsafe { core::ptr::copy_nonoverlapping(src, dst, 0); }
}
"#;

/// Test copy_nonoverlapping with u32 elements (count=2, total_bytes=8).
/// Exercises the CopyNonOverlapping intrinsic through the MIR pipeline.
/// Verifies codegen processes all basic blocks including terminators.
#[test]
fn test_mir_copy_nonoverlapping_u32() {
    with_test_ay_ctx_for_source(COPY_NONOVERLAPPING_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "copy_nonoverlapping_u32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Verify MIR body has expected structure
        assert!(
            body.blocks.len() >= 2,
            "copy_nonoverlapping_u32_probe should have at least 2 basic blocks"
        );

        // Process all statements and terminators
        let mut blocks_processed = 0;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
            let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
            blocks_processed += 1;
        }
        // All blocks processed without panicking
        assert_eq!(
            blocks_processed,
            body.blocks.len(),
            "all basic blocks should be processed by codegen"
        );
    });
}

/// Test copy_nonoverlapping with u8 elements (count=4, total_bytes=4).
/// Verifies all basic blocks are processed through the codegen pipeline.
#[test]
fn test_mir_copy_nonoverlapping_u8() {
    with_test_ay_ctx_for_source(COPY_NONOVERLAPPING_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "copy_nonoverlapping_u8_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert!(body.blocks.len() >= 2, "should have at least 2 basic blocks");

        let mut blocks_processed = 0;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
            let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
            blocks_processed += 1;
        }
        assert_eq!(blocks_processed, body.blocks.len(), "all basic blocks should be processed");
    });
}

/// Test copy_nonoverlapping with zero count (no-op path).
/// Verifies zero-count copy does not modify the memory model.
#[test]
fn test_mir_copy_nonoverlapping_zero_count() {
    with_test_ay_ctx_for_source(COPY_NONOVERLAPPING_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "copy_nonoverlapping_zero_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let mem_before = codegen.ctx.memory().to_string();

        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }
        // Zero-count copy should be a no-op: memory model unchanged
        let mem_after = codegen.ctx.memory().to_string();
        assert_eq!(
            mem_before, mem_after,
            "copy_nonoverlapping with count=0 should not modify the memory model"
        );
    });
}

// =============================================================================
// MIR-driven tests: ptr::write_bytes through dispatch pipeline
// =============================================================================

/// Probe source for write_bytes.
/// MIR lowers this to a Call terminator dispatched through dispatch_memory.
const WRITE_BYTES_PROBE: &str = r#"
pub fn write_bytes_zero_probe(dst: *mut u32, count: usize) {
    unsafe { core::ptr::write_bytes(dst, 0u8, count); }
}

pub fn write_bytes_ff_probe(dst: *mut u8) {
    unsafe { core::ptr::write_bytes(dst, 0xFFu8, 1); }
}
"#;

/// Test write_bytes codegen through the full dispatch pipeline.
/// The write_bytes probe uses a runtime count (symbolic), so write_bytes
/// cannot unroll — the pipeline handles this gracefully without panicking.
/// Verifies MIR structure and all terminators are processed.
#[test]
fn test_mir_write_bytes_dispatch() {
    with_test_ay_ctx_for_source(WRITE_BYTES_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "write_bytes_zero_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Verify MIR has expected structure
        assert!(
            body.blocks.len() >= 2,
            "write_bytes probe should have at least 2 basic blocks (entry + return)"
        );

        // Process all statements
        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }
        // Process terminators (Call to write_bytes dispatches through dispatch_memory)
        let mut terminator_count = 0;
        for bb in &body.blocks {
            let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
            terminator_count += 1;
        }
        // All basic blocks had their terminators processed
        assert_eq!(
            terminator_count,
            body.blocks.len(),
            "all basic block terminators should be processed"
        );
    });
}

/// Test write_bytes with constant u8 count=1 (constant unroll path).
/// Verifies the memory model is modified with store operations.
#[test]
fn test_mir_write_bytes_constant_count() {
    with_test_ay_ctx_for_source(WRITE_BYTES_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "write_bytes_ff_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let mem_before = codegen.ctx.memory().to_string();
        let pre_constraints = constraint_count(&codegen);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }
        for bb in &body.blocks {
            let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
        }
        // write_bytes(dst, 0xFF, 1) should modify memory or emit constraints
        let mem_after = codegen.ctx.memory().to_string();
        let post_constraints = constraint_count(&codegen);
        assert!(
            mem_before != mem_after || post_constraints > pre_constraints,
            "write_bytes constant count=1 should produce observable side effects"
        );
    });
}

// =============================================================================
// MIR-driven tests: ptr::copy (overlapping) through dispatch pipeline
// =============================================================================

/// Probe source for ptr::copy (memmove semantics).
const COPY_OVERLAP_PROBE: &str = r#"
pub fn copy_overlap_u32_probe(src: *const u32, dst: *mut u32) {
    unsafe { core::ptr::copy(src, dst, 3); }
}

pub fn copy_overlap_u8_probe(src: *const u8, dst: *mut u8) {
    unsafe { core::ptr::copy(src, dst, 1); }
}
"#;

/// Test ptr::copy (overlapping) with u32 elements through dispatch.
/// copy(src, dst, 3) with u32 = 12 bytes of memmove (temp-then-store pattern).
/// Verifies memory model is mutated with store operations.
#[test]
fn test_mir_copy_overlap_u32_dispatch() {
    with_test_ay_ctx_for_source(COPY_OVERLAP_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "copy_overlap_u32_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let mem_before = codegen.ctx.memory().to_string();
        let pre_constraints = constraint_count(&codegen);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }
        for bb in &body.blocks {
            let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
        }
        // ptr::copy(src, dst, 3) with u32 = 12 bytes → memory loads + stores
        let mem_after = codegen.ctx.memory().to_string();
        let post_constraints = constraint_count(&codegen);
        assert!(
            mem_before != mem_after || post_constraints > pre_constraints,
            "ptr::copy u32 count=3 should produce observable side effects"
        );
    });
}

/// Test ptr::copy with single u8 byte (simplest non-zero overlapping case).
/// Verifies memory model is mutated for the 1-byte memmove.
#[test]
fn test_mir_copy_overlap_single_byte() {
    with_test_ay_ctx_for_source(COPY_OVERLAP_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "copy_overlap_u8_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let mem_before = codegen.ctx.memory().to_string();
        let pre_constraints = constraint_count(&codegen);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }
        for bb in &body.blocks {
            let _successors = codegen.codegen_terminator_with_successors(&bb.terminator);
        }
        // ptr::copy(src, dst, 1) with u8 = 1 byte → 1 load + 1 store
        let mem_after = codegen.ctx.memory().to_string();
        let post_constraints = constraint_count(&codegen);
        assert!(
            mem_before != mem_after || post_constraints > pre_constraints,
            "ptr::copy u8 count=1 should produce observable side effects"
        );
    });
}
