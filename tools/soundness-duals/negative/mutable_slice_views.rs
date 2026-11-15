// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a slice view (`s[..]`, `s[a..b]`, `s[..b]`, `s[a..]`) written through, or over
// elements with interior mutability.
//
// Found while pinning the slice-view fixes of m3/soundness-fixes-2 (2026-09-12). The BMC
// index stubs lower a view to a reference to a COPY of the referent. Measured on bundle
// e18dbf853 (BMC): every `&mut` view written through (`full[0] = 9`, `sub[1] = 9`,
// `copy_from_slice`, `iter_mut`) and every view over `Cell` / atomic elements set through
// the other alias verified its *_must_fail SUCCESSFUL and failed its *_safe twin with
// [AY:CTREX_CAT:Genuine]. On edec8fd8a (acdd6604e, 4cea1b249) every view that is not a
// shared reference to Freeze elements is demoted in both lanes (EncodingGap /
// OverApproximation), and the shared Freeze views keep exact contents and length.
//
// KNOWN RED (adversarial review, 2026-09-13): `frozen_range_view_read_*` is red in BMC on
// edec8fd8a and on main 31793ccc3 — `&source[1..3]` is backed by the SOURCE array
// unshifted (statement/slice.rs, try_codegen_subslice_range_ref), so `sub[0]` reads
// `lhs[0]`: the must-fail verified SUCCESSFUL and the safe twin FAILED Genuine. Pinned in
// the manifest as known_red; negative/subslice_offsets.rs carries the full shape set.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

use std::cell::Cell;
use std::sync::atomic::{AtomicU8, Ordering};

#[kani::proof]
fn full_view_write_safe() {
    let mut lhs = [1u8, 2];
    {
        let source: &mut [u8] = &mut lhs;
        let full: &mut [u8] = &mut source[..];
        full[0] = 9;
    }
    assert!(lhs[0] == 9 && lhs[1] == 2);
}

#[kani::proof]
fn full_view_write_must_fail() {
    let mut lhs = [1u8, 2];
    {
        let source: &mut [u8] = &mut lhs;
        let full: &mut [u8] = &mut source[..];
        full[0] = 9;
    }
    assert!(lhs[0] == 1);
}

#[kani::proof]
fn array_full_view_write_safe() {
    let mut lhs = [1u8, 2];
    {
        let full: &mut [u8] = &mut lhs[..];
        full[0] = 9;
    }
    assert!(lhs[0] == 9);
}

#[kani::proof]
fn array_full_view_write_must_fail() {
    let mut lhs = [1u8, 2];
    {
        let full: &mut [u8] = &mut lhs[..];
        full[0] = 9;
    }
    assert!(lhs[0] == 1);
}

#[kani::proof]
fn range_view_write_safe() {
    let mut lhs = [1u8, 2, 3];
    {
        let source: &mut [u8] = &mut lhs;
        let sub: &mut [u8] = &mut source[1..3];
        sub[1] = 9;
    }
    assert!(lhs[2] == 9 && lhs[1] == 2);
}

#[kani::proof]
fn range_view_write_must_fail() {
    let mut lhs = [1u8, 2, 3];
    {
        let source: &mut [u8] = &mut lhs;
        let sub: &mut [u8] = &mut source[1..3];
        sub[1] = 9;
    }
    assert!(lhs[2] == 3);
}

#[kani::proof]
fn range_to_view_write_safe() {
    let mut lhs = [1u8, 2, 3];
    {
        let source: &mut [u8] = &mut lhs;
        let sub: &mut [u8] = &mut source[..2];
        sub[1] = 9;
    }
    assert!(lhs[1] == 9);
}

#[kani::proof]
fn range_to_view_write_must_fail() {
    let mut lhs = [1u8, 2, 3];
    {
        let source: &mut [u8] = &mut lhs;
        let sub: &mut [u8] = &mut source[..2];
        sub[1] = 9;
    }
    assert!(lhs[1] == 2);
}

#[kani::proof]
fn range_from_view_write_safe() {
    let mut lhs = [1u8, 2, 3];
    {
        let source: &mut [u8] = &mut lhs;
        let sub: &mut [u8] = &mut source[1..];
        sub[1] = 9;
    }
    assert!(lhs[2] == 9);
}

#[kani::proof]
fn range_from_view_write_must_fail() {
    let mut lhs = [1u8, 2, 3];
    {
        let source: &mut [u8] = &mut lhs;
        let sub: &mut [u8] = &mut source[1..];
        sub[1] = 9;
    }
    assert!(lhs[2] == 3);
}

#[kani::proof]
fn full_view_copy_from_slice_safe() {
    let mut buf = [0u8; 3];
    let src = [4u8, 5, 6];
    buf[..].copy_from_slice(&src);
    assert!(buf[2] == 6);
}

#[kani::proof]
fn full_view_copy_from_slice_must_fail() {
    let mut buf = [0u8; 3];
    let src = [4u8, 5, 6];
    buf[..].copy_from_slice(&src);
    assert!(buf[2] == 0);
}

#[kani::proof]
fn full_view_iter_mut_safe() {
    let mut buf = [0u8; 2];
    for b in buf[..].iter_mut() {
        *b = 7;
    }
    assert!(buf[1] == 7);
}

#[kani::proof]
fn full_view_iter_mut_must_fail() {
    let mut buf = [0u8; 2];
    for b in buf[..].iter_mut() {
        *b = 7;
    }
    assert!(buf[1] == 0);
}

#[kani::proof]
fn full_view_cell_set_through_view_safe() {
    let lhs = [Cell::new(1u8), Cell::new(2u8)];
    let source: &[Cell<u8>] = &lhs;
    let full: &[Cell<u8>] = &source[..];
    full[0].set(7);
    assert!(lhs[0].get() == 7);
}

#[kani::proof]
fn full_view_cell_set_through_view_must_fail() {
    let lhs = [Cell::new(1u8), Cell::new(2u8)];
    let source: &[Cell<u8>] = &lhs;
    let full: &[Cell<u8>] = &source[..];
    full[0].set(7);
    assert!(lhs[0].get() == 1);
}

#[kani::proof]
fn full_view_atomic_store_after_view_safe() {
    let lhs = [AtomicU8::new(1), AtomicU8::new(2)];
    let source: &[AtomicU8] = &lhs;
    let full: &[AtomicU8] = &source[..];
    lhs[0].store(7, Ordering::SeqCst);
    assert!(full[0].load(Ordering::SeqCst) == 7);
}

#[kani::proof]
fn full_view_atomic_store_after_view_must_fail() {
    let lhs = [AtomicU8::new(1), AtomicU8::new(2)];
    let source: &[AtomicU8] = &lhs;
    let full: &[AtomicU8] = &source[..];
    lhs[0].store(7, Ordering::SeqCst);
    assert!(full[0].load(Ordering::SeqCst) == 1);
}

#[kani::proof]
fn range_view_cell_set_after_view_safe() {
    let lhs = [Cell::new(1u8), Cell::new(2u8), Cell::new(3u8)];
    let source: &[Cell<u8>] = &lhs;
    let sub: &[Cell<u8>] = &source[1..3];
    lhs[1].set(7);
    assert!(sub[0].get() == 7);
}

#[kani::proof]
fn range_view_cell_set_after_view_must_fail() {
    let lhs = [Cell::new(1u8), Cell::new(2u8), Cell::new(3u8)];
    let source: &[Cell<u8>] = &lhs;
    let sub: &[Cell<u8>] = &source[1..3];
    lhs[1].set(7);
    assert!(sub[0].get() == 2);
}

#[kani::proof]
fn range_to_view_cell_set_after_view_safe() {
    let lhs = [Cell::new(1u8), Cell::new(2u8), Cell::new(3u8)];
    let source: &[Cell<u8>] = &lhs;
    let sub: &[Cell<u8>] = &source[..2];
    lhs[1].set(7);
    assert!(sub[1].get() == 7);
}

#[kani::proof]
fn range_to_view_cell_set_after_view_must_fail() {
    let lhs = [Cell::new(1u8), Cell::new(2u8), Cell::new(3u8)];
    let source: &[Cell<u8>] = &lhs;
    let sub: &[Cell<u8>] = &source[..2];
    lhs[1].set(7);
    assert!(sub[1].get() == 2);
}

#[kani::proof]
fn range_from_view_cell_set_after_view_safe() {
    let lhs = [Cell::new(1u8), Cell::new(2u8), Cell::new(3u8)];
    let source: &[Cell<u8>] = &lhs;
    let sub: &[Cell<u8>] = &source[1..];
    lhs[1].set(7);
    assert!(sub[0].get() == 7);
}

#[kani::proof]
fn range_from_view_cell_set_after_view_must_fail() {
    let lhs = [Cell::new(1u8), Cell::new(2u8), Cell::new(3u8)];
    let source: &[Cell<u8>] = &lhs;
    let sub: &[Cell<u8>] = &source[1..];
    lhs[1].set(7);
    assert!(sub[0].get() == 2);
}

#[kani::proof]
fn range_from_view_cell_set_through_view_safe() {
    let lhs = [Cell::new(1u8), Cell::new(2u8), Cell::new(3u8)];
    let source: &[Cell<u8>] = &lhs;
    let sub: &[Cell<u8>] = &source[1..];
    sub[0].set(7);
    assert!(lhs[1].get() == 7);
}

#[kani::proof]
fn range_from_view_cell_set_through_view_must_fail() {
    let lhs = [Cell::new(1u8), Cell::new(2u8), Cell::new(3u8)];
    let source: &[Cell<u8>] = &lhs;
    let sub: &[Cell<u8>] = &source[1..];
    sub[0].set(7);
    assert!(lhs[1].get() == 2);
}

#[kani::proof]
fn frozen_full_view_read_safe() {
    let lhs = [1u8, 2, 3];
    let source: &[u8] = &lhs;
    let full: &[u8] = &source[..];
    assert!(full.len() == 3 && full[1] == 2);
}

#[kani::proof]
fn frozen_full_view_read_must_fail() {
    let lhs = [1u8, 2, 3];
    let source: &[u8] = &lhs;
    let full: &[u8] = &source[..];
    assert!(full[1] == 3);
}

#[kani::proof]
fn frozen_range_view_read_safe() {
    let lhs = [1u8, 2, 3];
    let source: &[u8] = &lhs;
    let sub: &[u8] = &source[1..3];
    assert!(sub.len() == 2 && sub[0] == 2 && sub[1] == 3);
}

#[kani::proof]
fn frozen_range_view_read_must_fail() {
    let lhs = [1u8, 2, 3];
    let source: &[u8] = &lhs;
    let sub: &[u8] = &source[1..3];
    assert!(sub[0] == 1);
}
