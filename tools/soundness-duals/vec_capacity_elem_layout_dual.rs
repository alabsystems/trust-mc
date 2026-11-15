// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a `Vec`'s capacity read from its
//! element's own layout, the capacity `clone` and `split_off` allocate, and
//! `split_off`'s bounds panic (walker fail-closed review, round 3 of the repair
//! after the merge with main's Rule D, 2026-10-15, findings 1 and 2).
//!
//! Oracle (per harness, the corpus-rev Kani at ~/tmc-measure/kani-src,
//! measured 2026-10-15): the `_safe` rows are SUCCESSFUL and the `_bug` rows
//! FAILED, every one measured.
//!
//! MECHANISM UNDER TEST. Finding 1: the capacity model (`vec_reserved_cap`,
//! the zero-sized checks of `capacity()` and `set_len`) read the element's
//! size through the heap model's `get_type_size`, which strips `Cell`,
//! `RefCell`, `Mutex`, `RwLock` and their guards first: `RefCell<()>` (8
//! bytes) read as zero-sized, so `capacity()` was `usize::MAX`; `RefCell<u8>`
//! (16 bytes) and `Mutex<u8>` (8) read as 1 byte, so one push gave 8 where std
//! gives 4; `RefCell<[u8; 1020]>` (1028 bytes) read as 1020, so it gave 4
//! where std gives 1. Round 2 of the repair introduced it: CHC missed bugs
//! (p1b, p4b, p4f, p4h, co, cv) and certified false certificates (p1u, p4a,
//! p4e, cu) where main had matched. Both lanes now read the element's own
//! layout (`shared/vec_capacity.rs`, `vec_elem_layout_size`).
//!
//! Finding 2: `clone` allocates exactly the length (`to_vec_in`), and
//! `split_off(at)` returns `Vec::with_capacity_in(len - at)` and panics when
//! `at > len`. The CHC lane copied the source's capacity into a clone and
//! left `split_off`'s result capacity stale; it assumed `at <= len` away and
//! wrote neither Vec's fields; the BMC lane copied the capacity too. On main
//! as well: missed bugs (p1h, cb on both lanes; cl) and certified false
//! certificates (p1g, p1k, ca, cg, ci, cm, cz). Both lanes now give a clone
//! its length as capacity; CHC `split_off` writes both Vecs' fields, states
//! the panic, and leaves the returned elements a fresh array under an
//! identified sound havoc (`vec_split_off_elements_unmodelled`).
//!
//! Lane scope: both.
//!
//! Run: trust-mc-driver -Z unstable-options --harness-timeout=30s [--ay-chc] vec_capacity_elem_layout_dual.rs

use std::cell::{Cell, RefCell, UnsafeCell};
use std::mem::{ManuallyDrop, MaybeUninit};
use std::sync::{Mutex, RwLock};

#[kani::proof]
fn p1a_refcell_u8_push_cap4_safe() {
    // size_of::<RefCell<u8>>() == 16: min_non_zero_cap 4.
    let mut v: Vec<RefCell<u8>> = Vec::new();
    v.push(RefCell::new(1));
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn p1b_refcell_u8_push_cap8_bug() {
    let mut v: Vec<RefCell<u8>> = Vec::new();
    v.push(RefCell::new(1));
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn p1c_cell_u8_push_cap8_safe() {
    let mut v: Vec<Cell<u8>> = Vec::new();
    v.push(Cell::new(1));
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn p1d_refcell_reserve_cap4_safe() {
    let mut v: Vec<RefCell<u8>> = Vec::new();
    v.reserve(1);
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn p1e_box_u8_push_cap4_safe() {
    let mut v: Vec<Box<u8>> = Vec::new();
    v.push(Box::new(1));
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn p1f_clone_then_push_cap8_safe() {
    // clone allocates exactly len (3); push: grow_amortized(3, 1) = max(6, 4, 8) = 8.
    let v = vec![1u8, 2, 3];
    let mut w = v.clone();
    w.push(4);
    assert!(w.capacity() == 8);
}

#[kani::proof]
fn p1g_clone_cap_eq_len_safe() {
    let mut v: Vec<u8> = Vec::with_capacity(10);
    v.push(1);
    v.push(2);
    let w = v.clone();
    assert!(w.capacity() == 2);
}

#[kani::proof]
fn p1h_clone_cap_eq_10_bug() {
    let mut v: Vec<u8> = Vec::with_capacity(10);
    v.push(1);
    v.push(2);
    let w = v.clone();
    assert!(w.capacity() == 10);
}

#[kani::proof]
fn p1i_shrink_to_fit_cap_safe() {
    let mut v: Vec<u8> = Vec::with_capacity(10);
    v.push(1);
    v.push(2);
    v.shrink_to_fit();
    assert!(v.capacity() == 2);
}

#[kani::proof]
fn p1j_shrink_to_fit_cap10_bug() {
    let mut v: Vec<u8> = Vec::with_capacity(10);
    v.push(1);
    v.push(2);
    v.shrink_to_fit();
    assert!(v.capacity() == 10);
}

#[kani::proof]
fn p1k_split_off_other_cap_safe() {
    // split_off(1): other = with_capacity(len - at) = 2; self keeps 8.
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    let w = v.split_off(1);
    assert!(w.capacity() == 2);
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn p1l_split_off_other_cap8_bug() {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    let w = v.split_off(1);
    assert!(w.capacity() == 8);
}

#[kani::proof]
fn p1m_extend_filter_cap8_safe() {
    // extend from a non-TrustedLen iterator: extend_desugared, reserve(lower + 1).
    let mut v: Vec<u8> = Vec::new();
    v.extend([1u8, 2, 3].iter().copied().filter(|x| *x > 1));
    assert!(v.len() == 2);
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn p1n_extend_filter_cap2_bug() {
    let mut v: Vec<u8> = Vec::new();
    v.extend([1u8, 2, 3].iter().copied().filter(|x| *x > 1));
    assert!(v.capacity() == 2);
}

#[kani::proof]
fn p1o_extend_from_within_cap8_safe() {
    let mut v: Vec<u8> = vec![1, 2, 3];
    v.extend_from_within(..);
    // reserve(3) from cap 3: max(6, 6, 8) = 8.
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn p1p_extend_from_within_cap6_bug() {
    let mut v: Vec<u8> = vec![1, 2, 3];
    v.extend_from_within(..);
    assert!(v.capacity() == 6);
}

#[kani::proof]
fn p1q_truncate_keeps_cap_safe() {
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    v.truncate(1);
    v.clear();
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn p1r_from_array_push_cap_safe() {
    // Vec::from([u16; 3]) has cap 3; push: max(6, 4, 4) = 6.
    let mut v = Vec::from([1u16, 2, 3]);
    v.push(4);
    assert!(v.capacity() == 6);
}

#[kani::proof]
fn p1s_big_elem_push_cap1_safe() {
    let mut v: Vec<[u8; 1025]> = Vec::new();
    v.push([0u8; 1025]);
    assert!(v.capacity() == 1);
}

#[kani::proof]
fn p1t_elem_1024_push_cap4_safe() {
    let mut v: Vec<[u8; 1024]> = Vec::new();
    v.push([0u8; 1024]);
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn p1u_refcell_big_push_cap1_safe() {
    // size_of::<RefCell<[u8; 1020]>>() == 1028 > 1024: min 1.
    let mut v: Vec<RefCell<[u8; 1020]>> = Vec::new();
    v.push(RefCell::new([0u8; 1020]));
    assert!(v.capacity() == 1);
}

#[kani::proof]
fn p1v_insert_into_refcell_cap4_safe() {
    let mut v: Vec<RefCell<u8>> = Vec::new();
    v.insert(0, RefCell::new(1));
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn p1w_resize_refcell_cap4_safe() {
    let mut v: Vec<RefCell<u8>> = Vec::new();
    v.resize(1, RefCell::new(1));
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn p4a_refcell_unit_new_cap0_safe() {
    let v: Vec<RefCell<()>> = Vec::new();
    assert!(v.capacity() == 0);
}

#[kani::proof]
fn p4b_refcell_unit_new_cap_max_bug() {
    let v: Vec<RefCell<()>> = Vec::new();
    assert!(v.capacity() == usize::MAX);
}

#[kani::proof]
fn p4c_refcell_unit_push_cap4_safe() {
    let mut v: Vec<RefCell<()>> = Vec::new();
    v.push(RefCell::new(()));
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn p4d_cell_unit_new_cap_max_safe() {
    // Cell<()> IS zero-sized.
    let v: Vec<Cell<()>> = Vec::new();
    assert!(v.capacity() == usize::MAX);
}

#[kani::proof]
fn p4e_refcell_unit_with_capacity_safe() {
    let v: Vec<RefCell<()>> = Vec::with_capacity(3);
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn p4f_refcell_unit_with_capacity_max_bug() {
    let v: Vec<RefCell<()>> = Vec::with_capacity(3);
    assert!(v.capacity() == usize::MAX);
}

#[kani::proof]
fn p4g_refcell_u8_with_cap_push_past_safe() {
    // with_capacity(1), second push: grow_amortized(1, 1) = max(2, 2, 4) = 4.
    let mut v: Vec<RefCell<u8>> = Vec::with_capacity(1);
    v.push(RefCell::new(1));
    v.push(RefCell::new(2));
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn p4h_refcell_u8_with_cap_push_past_bug() {
    let mut v: Vec<RefCell<u8>> = Vec::with_capacity(1);
    v.push(RefCell::new(1));
    v.push(RefCell::new(2));
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn ca_clone_empty_with_cap_safe() {
    let v: Vec<u16> = Vec::with_capacity(5);
    let w = v.clone();
    assert!(w.capacity() == 0);
    assert!(v.capacity() == 5);
}

#[kani::proof]
fn cb_clone_empty_with_cap_bug() {
    let v: Vec<u16> = Vec::with_capacity(5);
    let w = v.clone();
    assert!(w.capacity() == 5);
}

#[kani::proof]
fn cc_clone_pushed_u32_safe() {
    // push from empty: cap 4; clone allocates exactly len 1.
    let mut v: Vec<u32> = Vec::new();
    v.push(7);
    let w = v.clone();
    assert!(w.capacity() == 1);
    assert!(w.len() == 1);
    assert!(w[0] == 7);
}

#[kani::proof]
fn cd_clone_pushed_u32_bug() {
    let mut v: Vec<u32> = Vec::new();
    v.push(7);
    let w = v.clone();
    assert!(w.capacity() == 4);
}

#[kani::proof]
fn ce_clone_source_cap_kept_safe() {
    let mut v: Vec<u8> = Vec::with_capacity(10);
    v.push(1);
    let _w = v.clone();
    assert!(v.capacity() == 10);
}

#[kani::proof]
fn cf_clone_vec_literal_safe() {
    let v = vec![1u8, 2, 3];
    let w = v.clone();
    assert!(w.capacity() == 3);
}

#[kani::proof]
fn cg_split_off_zero_safe() {
    // split_off(0): other = with_capacity(len), self keeps its capacity.
    let mut v: Vec<u8> = Vec::with_capacity(10);
    v.push(1);
    v.push(2);
    v.push(3);
    let w = v.split_off(0);
    assert!(w.capacity() == 3);
    assert!(v.capacity() == 10);
    assert!(v.len() == 0);
    assert!(w.len() == 3);
}

#[kani::proof]
fn ch_split_off_zero_cap_bug() {
    let mut v: Vec<u8> = Vec::with_capacity(10);
    v.push(1);
    v.push(2);
    v.push(3);
    let w = v.split_off(0);
    assert!(w.capacity() == 10);
}

#[kani::proof]
fn ci_split_off_at_len_safe() {
    let mut v: Vec<u8> = Vec::with_capacity(4);
    v.push(1);
    v.push(2);
    let w = v.split_off(2);
    assert!(w.capacity() == 0);
    assert!(w.len() == 0);
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn cj_split_off_self_cap_bug() {
    let mut v: Vec<u8> = Vec::with_capacity(4);
    v.push(1);
    v.push(2);
    let _w = v.split_off(1);
    assert!(v.capacity() == 1);
}

#[kani::proof]
fn ck_split_off_past_len_bug() {
    // at > len panics.
    let mut v: Vec<u8> = Vec::new();
    v.push(1);
    v.push(2);
    let w = v.split_off(3);
    assert!(w.len() == 0);
}

#[kani::proof]
fn cl_split_off_sym_at_bug() {
    let mut v = vec![1u8, 2];
    let at: usize = kani::any();
    kani::assume(at <= 3);
    let w = v.split_off(at);
    assert!(v.len() + w.len() == 2);
}

#[kani::proof]
fn cm_split_off_sym_at_safe() {
    let mut v = vec![1u8, 2];
    let at: usize = kani::any();
    kani::assume(at <= 2);
    let w = v.split_off(at);
    assert!(v.len() + w.len() == 2);
    assert!(w.capacity() == 2 - at);
}

#[kani::proof]
fn cn_mutex_u8_push_cap4_safe() {
    // size_of::<Mutex<u8>>() == 8 on Linux: min_non_zero_cap 4.
    let mut v: Vec<Mutex<u8>> = Vec::new();
    v.push(Mutex::new(1));
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn co_mutex_u8_push_cap8_bug() {
    let mut v: Vec<Mutex<u8>> = Vec::new();
    v.push(Mutex::new(1));
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn cp_rwlock_u8_push_cap4_safe() {
    let mut v: Vec<RwLock<u8>> = Vec::new();
    v.push(RwLock::new(1));
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn cq_maybeuninit_u8_push_cap8_safe() {
    // MaybeUninit<u8> is 1 byte.
    let mut v: Vec<MaybeUninit<u8>> = Vec::new();
    v.push(MaybeUninit::new(1));
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn cr_manuallydrop_u32_push_cap4_safe() {
    let mut v: Vec<ManuallyDrop<u32>> = Vec::new();
    v.push(ManuallyDrop::new(1));
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn cs_unsafecell_u8_push_cap8_safe() {
    let mut v: Vec<UnsafeCell<u8>> = Vec::new();
    v.push(UnsafeCell::new(1));
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn ct_cell_unit_push_cap_max_safe() {
    // Cell<()> is zero-sized: capacity usize::MAX.
    let mut v: Vec<Cell<()>> = Vec::new();
    v.push(Cell::new(()));
    assert!(v.capacity() == usize::MAX);
}

#[kani::proof]
fn cu_mutex_unit_new_cap0_safe() {
    // Mutex<()> is not zero-sized.
    let v: Vec<Mutex<()>> = Vec::new();
    assert!(v.capacity() == 0);
}

#[kani::proof]
fn cv_mutex_unit_new_cap_max_bug() {
    let v: Vec<Mutex<()>> = Vec::new();
    assert!(v.capacity() == usize::MAX);
}

#[kani::proof]
fn cw_to_vec_cap_safe() {
    let a = [1u8, 2, 3];
    let v = a.to_vec();
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn cx_to_vec_cap_bug() {
    let a = [1u8, 2, 3];
    let v = a.to_vec();
    assert!(v.capacity() == 8);
}

#[kani::proof]
fn cy_clone_then_set_len_reads_len_safe() {
    // the clone has capacity 2; Kani does not check set_len's precondition.
    let mut v: Vec<u8> = Vec::with_capacity(10);
    v.push(1);
    v.push(2);
    let mut w = v.clone();
    unsafe { w.set_len(3) };
    assert!(w.len() == 3);
}

#[kani::proof]
fn cz_clone_then_push_regrow_safe() {
    // clone cap 2, push: grow_amortized(2, 1) = max(4, 3, 8) = 8.
    let mut v: Vec<u8> = Vec::with_capacity(10);
    v.push(1);
    v.push(2);
    let mut w = v.clone();
    w.push(3);
    assert!(w.capacity() == 8);
}

#[kani::proof]
fn da_split_off_self_index_past_at_bug() {
    let mut v = vec![1u8, 2, 3];
    let _w = v.split_off(1);
    assert!(v[1] == 2);
}

#[kani::proof]
fn db_split_off_self_index_safe() {
    let mut v = vec![1u8, 2, 3];
    let _w = v.split_off(2);
    assert!(v[1] == 2);
    assert!(v.len() == 2);
}

#[kani::proof]
fn dc_split_off_other_data_safe() {
    let mut v = vec![1u8, 2, 3];
    let w = v.split_off(1);
    assert!(w[0] == 2);
    assert!(w[1] == 3);
}

#[kani::proof]
fn dd_split_off_other_data_bug() {
    let mut v = vec![1u8, 2, 3];
    let w = v.split_off(1);
    assert!(w[0] == 1);
}

#[kani::proof]
fn de_split_off_other_index_past_len_bug() {
    let mut v = vec![1u8, 2, 3];
    let w = v.split_off(1);
    assert!(w[2] == 0);
}

#[kani::proof]
fn df_split_off_other_len_safe() {
    let mut v: Vec<u32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    let w = v.split_off(3);
    assert!(w.len() == 1);
    assert!(v.len() == 3);
    assert!(w.capacity() == 1);
    assert!(v.capacity() == 4);
}

#[kani::proof]
fn dg_split_off_then_push_other_safe() {
    // other has capacity 1; push: grow_amortized(1, 1) = max(2, 2, 8) = 8.
    let mut v = vec![1u8, 2];
    let mut w = v.split_off(1);
    w.push(9);
    assert!(w.capacity() == 8);
    assert!(w.len() == 2);
}

#[kani::proof]
fn dh_split_off_sym_value_kept_safe() {
    let x: u8 = kani::any();
    let mut v = vec![x, 7];
    let _w = v.split_off(1);
    assert!(v[0] == x);
}
