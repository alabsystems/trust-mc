// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a `Vec`'s capacity after it grows
//! (walker fail-closed review, round 2 of the repair after the merge with
//! main's Rule D, 2026-10-15, findings 2 and 3).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-15;
//! `--default-unwind 11` for the loops of c2b and c2x): the `_safe` rows are
//! SUCCESSFUL and the `_bug` rows FAILED (`assertion failed: v.capacity() ==
//! ..`), every one measured.
//!
//! MECHANISM UNDER TEST. std's `RawVec` grows by `grow_amortized`,
//! `max(2 * cap, len + additional, MIN_NON_ZERO_CAP)` with a minimum of 8 for
//! a 1-byte element, 4 up to 1024 bytes and 1 above, on every path that
//! reserves (`push`, `insert`, `extend_from_slice`, `extend` from a range,
//! `resize`, `append`, `reserve`), and by `grow_exact`, `len + additional`,
//! on `reserve_exact`. Both lanes modelled every growth as `max(cap, len +
//! additional)` (the BMC lane's `push` and `insert` as `cap + 1`), so
//! `Vec::<u8>::new(); v.push(1); v.capacity() == 1` verified clean where Kani
//! fails and `v.capacity() == 8`, which Kani proves, failed certified Genuine,
//! on main too; the branch's exact range extend had made `extend(0u8..3);
//! v.capacity() == 3` verify where main had matched. Both lanes now state
//! `RawVec`'s rules (`shared/vec_capacity.rs`; CHC `vec_reserved_cap`, BMC
//! `bmc_vec_reserved_cap`), and a growth whose element size or steps the
//! model does not know is a fresh capacity of at least the length, a sound
//! havoc.
//!
//! The `c3` rows: a `collect` over a `vec::IntoIter` may reuse the source's
//! buffer and keep its capacity (`SpecFromIter for IntoIter`); the CHC
//! collect model set the capacity to the length, so `capacity() == 1` of a
//! collected `Vec::with_capacity(10)` holding one element verified clean
//! where Kani fails (on main too). That capacity is now a fresh value of at
//! least the length, a sound havoc (`collected_vec_cap`).
//!
//! Lane scope: both.
//!
//! Run: trust-mc-driver -Z unstable-options --harness-timeout=30s [--ay-chc] vec_capacity_growth_dual.rs

#[kani::proof]
fn c1a_push_u8_cap1_bug() {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    assert!(v.capacity() == 1);
}

#[kani::proof]
fn c1b_push_u8_cap8_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn c1c_extend_u8_cap8_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..3);
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn c1d_extend_slice_u8_cap3_bug() {
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&[1u8, 2, 3]);
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn c1e_with_capacity_push_past_bug() {
    let mut v: Vec<u32> = Vec::with_capacity(2);
    v.push(1);
    v.push(2);
    v.push(3);
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn c1f_reserve_exact_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.reserve_exact(3);
    v.extend(0u8..3);
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn x2i_capacity_eq3_bug() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..3);
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn x2j_capacity_ge_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.extend(0u8..3);
    assert!(v.capacity() >= 3);
}

#[kani::proof]
fn x2k_with_capacity_kept_safe() {
    let mut v: Vec<u8> = Vec::with_capacity(10);
    v.extend(0u8..3);
    assert!(v.capacity() == 10 && v.len() == 3);
}

#[kani::proof]
fn x2u_capacity_u32_eq3_bug() {
    let mut v: Vec<u32> = Vec::new();
    v.extend(0u32..3);
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn c2a_push_twice_u8_cap8_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn c2b_push_nine_u8_cap16_safe() {
    let mut v: Vec<u8> = Vec::new();
    for i in 0..9u8 {
        v.push(i);
    }
    assert!(v.capacity() == 16);
}

#[kani::proof]
fn c2c_push_u64_cap4_safe() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1);
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn c2d_push_u64_cap1_bug() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1);
    assert!(v.capacity() == 1);
}

#[kani::proof]
fn c2e_push_big_cap1_safe() {
    let mut v: Vec<[u8; 2048]> = Vec::new();
    v.push([0u8; 2048]);
    assert!(v.capacity() == 1);
}

#[kani::proof]
fn c2f_vec_literal_push_cap6_safe() {
    let mut v: Vec<u8> = vec![1, 2, 3];
    v.push(4);
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn c2g_vec_literal_push_cap4_bug() {
    let mut v: Vec<u8> = vec![1, 2, 3];
    v.push(4);
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn c2h_with_capacity_exact_safe() {
    let v: Vec<u32> = Vec::with_capacity(3);
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn c2i_reserve_u8_cap8_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.reserve(3);
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn c2j_reserve_u8_cap3_bug() {
    let mut v: Vec<u8> = Vec::new();
    v.reserve(3);
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn c2k_reserve_exact_u8_cap3_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.reserve_exact(3);
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn c2l_extend_slice_20_cap20_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(&[7u8; 20]);
    assert!(v.capacity() == 20);
}

#[kani::proof]
fn c2m_insert_u32_cap4_safe() {
    let mut v: Vec<u32> = Vec::new();
    v.insert(0, 5);
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn c2n_insert_u32_cap1_bug() {
    let mut v: Vec<u32> = Vec::new();
    v.insert(0, 5);
    assert!(v.capacity() == 1);
}

#[kani::proof]
fn c2o_resize_u8_cap8_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.resize(3, 0);
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn c2p_resize_u8_cap3_bug() {
    let mut v: Vec<u8> = Vec::new();
    v.resize(3, 0);
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn c2q_append_u8_cap8_safe() {
    let mut v: Vec<u8> = Vec::new();
    let mut w: Vec<u8> = vec![1, 2];
    v.append(&mut w);
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn c2r_with_capacity_push_within_safe() {
    let mut v: Vec<u32> = Vec::with_capacity(3);
    v.push(1);
    v.push(2);
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn c2s_with_capacity_push_past_cap6_safe() {
    let mut v: Vec<u32> = Vec::with_capacity(3);
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    assert!(v.capacity() == 6);
}

#[kani::proof]
fn c2t_string_push_cap8_safe() {
    let mut s = String::new();
    s.push('a');
    assert!(s.capacity() == 8);
}

#[kani::proof]
fn c2u_string_push_cap1_bug() {
    let mut s = String::new();
    s.push('a');
    assert!(s.capacity() == 1);
}

#[kani::proof]
fn c2v_string_push_str_cap8_safe() {
    let mut s = String::new();
    s.push_str("abc");
    assert!(s.capacity() == 8);
}

#[kani::proof]
fn c2w_string_push_str_cap3_bug() {
    let mut s = String::new();
    s.push_str("abc");
    assert!(s.capacity() == 3);
}

#[kani::proof]
fn c2x_sym_push_count_cap_ge_len_safe() {
    let n: u8 = kani::any();
    kani::assume(n <= 3);
    let mut v: Vec<u8> = Vec::new();
    for i in 0..n {
        v.push(i);
    }
    assert!(v.capacity() >= v.len());
}

#[kani::proof]
fn c2y_set_len_within_grown_cap_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    unsafe { v.set_len(5) };
    assert!(v.len() == 5);
}

#[kani::proof]
fn c2z_zst_cap_max_safe() {
    let v: Vec<()> = Vec::new();
    assert!(v.capacity() == usize::MAX);
}

#[kani::proof]
fn c3a_into_iter_collect_keeps_cap_bug() {
    let mut v: Vec<u8> = Vec::with_capacity(10);
    v.push(1);
    let w: Vec<u8> = v.into_iter().collect();
    assert!(w.capacity() == 1);
}

#[kani::proof]
fn c3b_into_iter_collect_keeps_cap_safe() {
    let mut v: Vec<u8> = Vec::with_capacity(10);
    v.push(1);
    let w: Vec<u8> = v.into_iter().collect();
    assert!(w.capacity() == 10);
}
