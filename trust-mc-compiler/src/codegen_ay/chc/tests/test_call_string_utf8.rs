// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unit tests for the concrete byte-slice resolution helpers used by
//! the StrFromUtf8 stub (CHC encoding). Full integration tests are
//! via compiletest harnesses (boxslice1, boxslice2).
//!
//! Note: `std::str::from_utf8` is typically inlined by the Rust compiler,
//! so MIR-level stub detection tests don't work for it. Instead we test
//! the extraction helpers directly and rely on compiletest for end-to-end.

#![allow(clippy::unwrap_used)]

use super::common::*;

/// `try_extract_raw_bytes_from_backing_utf8` should extract concrete bytes
/// from a AY Store chain built over a ConstArray base.
#[test]
fn test_extract_raw_bytes_from_store_chain() {
    // Build: (const-array 0) [0 := 65] [1 := 122]  (i.e., "Az")
    let base = Expr::const_array(Sort::bitvec(POINTER_WIDTH), Expr::bitvec_const(0u64, 8));
    let data = base
        .store(Expr::bitvec_const(0u64, POINTER_WIDTH), Expr::bitvec_const(65u64, 8))
        .store(Expr::bitvec_const(1u64, POINTER_WIDTH), Expr::bitvec_const(122u64, 8));
    let offset = Expr::bitvec_const(0u64, POINTER_WIDTH);

    let bytes = ChcCtx::try_extract_raw_bytes_from_backing_utf8(&data, &offset, 2);
    assert_eq!(bytes, Some(vec![65u8, 122u8]));
}

/// When the Store chain has an offset, bytes should be extracted relative
/// to the base offset.
#[test]
fn test_extract_raw_bytes_with_offset() {
    let base = Expr::const_array(Sort::bitvec(POINTER_WIDTH), Expr::bitvec_const(0u64, 8));
    let data = base
        .store(Expr::bitvec_const(4u64, POINTER_WIDTH), Expr::bitvec_const(72u64, 8))
        .store(Expr::bitvec_const(5u64, POINTER_WIDTH), Expr::bitvec_const(105u64, 8));
    let offset = Expr::bitvec_const(4u64, POINTER_WIDTH);

    let bytes = ChcCtx::try_extract_raw_bytes_from_backing_utf8(&data, &offset, 2);
    assert_eq!(bytes, Some(vec![72u8, 105u8])); // "Hi"
}

/// When the Store chain is backed by a Var (not ConstArray) and not all
/// positions are covered, extraction should return None.
#[test]
fn test_extract_raw_bytes_incomplete_returns_none() {
    let var =
        Expr::var("symbolic_array", Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8)));
    // Only one byte written, but we need 2
    let data = var.store(Expr::bitvec_const(0u64, POINTER_WIDTH), Expr::bitvec_const(65u64, 8));
    let offset = Expr::bitvec_const(0u64, POINTER_WIDTH);

    let bytes = ChcCtx::try_extract_raw_bytes_from_backing_utf8(&data, &offset, 2);
    assert_eq!(bytes, None);
}

/// `extract_const_usize_from_expr_utf8` should extract the value from a
/// BV const expression.
#[test]
fn test_extract_const_usize() {
    let expr = Expr::bitvec_const(42u64, POINTER_WIDTH);
    assert_eq!(ChcCtx::extract_const_usize_from_expr_utf8(&expr), Some(42));

    let symbolic = Expr::var("x", Sort::bitvec(POINTER_WIDTH));
    assert_eq!(ChcCtx::extract_const_usize_from_expr_utf8(&symbolic), None);
}
