// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle: corpus-rev Kani (/home/ayates/tmc-measure/kani-src), run on this file
// (see the manifest entry): the expectation of every row is Kani's verdict,
// except where Kani's own modes disagree (rows named `*_failclosed_*`), which
// fail closed: a `safe_` one expects Kani's SUCCESSFUL and is a known-red false
// failure (never a certified counterexample; decision C7, 2026-10-14), a `bug_`
// one FAILED (never a proof).
//
// WHY THIS FILE EXISTS: wrapping pointer steps against Kani's object range
// (heap/stack_address.rs). A wrapping step keeps the pointer's object (Rust's
// provenance, Kani's object bits) and moves its offset T from the object's base
// mod 2^64. T in [0, 2^48) is Kani's object range: the stepped pointer's
// address, equality and order are the same in every mode Kani uses. Outside it
// the pointer is FAR: a dereference is outside its object, and its address,
// order, `offset_from` and an equality its low 48 bits decide are fail-closed,
// because Kani answers them with a 48-bit wrap under a symbolic count and with
// 64-bit offsets under a literal one (measured 2026-10-02).
//
// The first review of the sixth round of fix/chc-false-certificates
// (2026-10-02; main edc662a62, the fifth round's bundle e6b61a573b2f) measured:
// - windows centered on each base put the landing edge at 2^47, so a step of
//   2^47 to 2^48 - 8 bytes was marked as landed and given a fixed wrong
//   address: `q.addr() == p.addr() + k` certified false, its negation proved
//   (finding 1, the `*_2p47` rows; `safe_cast_diff_2p47` and
//   `safe_int_ptr_eq_2p47` were certified false on main too);
// - a step into a window no object owned took that window as its object, so
//   the way back was marked as landed: `p + k - k != p` proved for k == 2^62
//   (finding 2, the `*_far_*` rows);
// - the fifth round sided with Rust where Kani's modes disagree
//   (finding 7, the `*_failclosed_*` rows);
// - map_addr tag round trips did not compile inside the driver's budget
//   (finding 8, the `*_tag_*` rows);
// - a heap pointer moved by a wrapping step was dereferenced with neither lane
//   nor bound checked when its lane was symbolic (finding 4, the `*_heap_*` and
//   `*_vec_*` rows; the same on main).

#![allow(clippy::all)]

struct W {
    p: *const u8,
}

// A far constant step whose window looks like another object's mark, and back.
const K: usize = 0x8003_0000_0000_0000;

#[kani::proof]
fn safe_addr_diff_2p47_range() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k >= (1usize << 47) && k < (1usize << 48) - 8);
    assert!(p.wrapping_byte_add(k).addr().wrapping_sub(p.addr()) == k);
}

#[kani::proof]
#[kani::should_panic]
fn sp_addr_diff_2p47_range() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k >= (1usize << 47) && k < (1usize << 48) - 8);
    assert!(p.wrapping_byte_add(k).addr().wrapping_sub(p.addr()) == k);
}

#[kani::proof]
fn bug_addr_diff_2p47() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    assert!(p.wrapping_byte_add(k).addr().wrapping_sub(p.addr()) != k);
}

#[kani::proof]
fn safe_adjacent_addr_2p47() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let r = p.wrapping_byte_add(k - 1);
    let s = p.wrapping_byte_add(k);
    assert!(r.addr() + 1 == s.addr());
}

#[kani::proof]
fn bug_adjacent_addr_2p47() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let r = p.wrapping_byte_add(k - 1);
    let s = p.wrapping_byte_add(k);
    assert!(r.addr() + 1 != s.addr());
}

#[kani::proof]
fn bug_heap_addr_diff_2p47() {
    let b = Box::new([1u8; 4]);
    let p = b.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    assert!(p.wrapping_byte_add(k).addr().wrapping_sub(p.addr()) != k);
}

#[kani::proof]
fn bug_cast_diff_2p47() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.wrapping_byte_add(k);
    assert!((q as usize).wrapping_sub(p as usize) != k);
}

#[kani::proof]
fn safe_cast_diff_2p47() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.wrapping_byte_add(k);
    assert!((q as usize).wrapping_sub(p as usize) == k);
}

#[kani::proof]
#[kani::should_panic]
fn sp_cast_diff_2p47() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.wrapping_byte_add(k);
    assert!((q as usize).wrapping_sub(p as usize) == k);
}

#[kani::proof]
fn bug_heap_deref_2p47() {
    let b = Box::new([1u8; 4]);
    let p = b.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.wrapping_byte_add(k);
    assert!(unsafe { *q } == 1);
}

#[kani::proof]
fn bug_field_deref_2p47() {
    let a = [1u8; 4];
    let w = W { p: a.as_ptr() };
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = w.p.wrapping_byte_add(k);
    assert!(unsafe { *q } == 1);
}

#[kani::proof]
fn safe_int_ptr_eq_2p47() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.wrapping_byte_add(k);
    let r = (p as usize + k) as *const u8;
    assert!(q == r);
}

#[kani::proof]
#[kani::should_panic]
fn sp_int_ptr_eq_2p47() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.wrapping_byte_add(k);
    let r = (p as usize + k) as *const u8;
    assert!(q == r);
}

#[kani::proof]
fn safe_with_addr_2p47() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.with_addr(p.addr() + k);
    assert!(q.addr() == p.addr() + k);
}

#[kani::proof]
#[kani::should_panic]
fn sp_with_addr_2p47() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.with_addr(p.addr() + k);
    assert!(q.addr() == p.addr() + k);
}

#[kani::proof]
fn bug_with_addr_2p47() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.with_addr(p.addr() + k);
    assert!(q.addr() != p.addr() + k);
}

#[kani::proof]
fn safe_map_addr_2p47() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.map_addr(|x| x + k);
    assert!(q.addr() == p.addr() + k);
}

#[kani::proof]
fn safe_cross_edge_small_const() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == (1usize << 47) - 8);
    let p1 = p.wrapping_byte_add(k);
    let q = p1.wrapping_byte_add(16);
    assert!(q.addr() == p.addr() + k + 16);
}

#[kani::proof]
fn bug_cross_edge_small_const() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == (1usize << 47) - 8);
    let p1 = p.wrapping_byte_add(k);
    let q = p1.wrapping_byte_add(16);
    assert!(q.addr() != p.addr() + k + 16);
}

#[kani::proof]
fn safe_order_landed_vs_next() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.wrapping_byte_add(k);
    // q stays p's provenance; its address is p's plus 2^47.
    assert!(q.addr() - p.addr() == k);
    let _ = b;
}

#[kani::proof]
fn safe_edge_roundtrip_deref() {
    let a = [1u8, 2, 3, 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
    assert!(unsafe { *q } == 1);
}

#[kani::proof]
fn bug_edge_step_reach() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.wrapping_byte_add(k);
    let _ = q.addr();
    assert!(false);
}

#[kani::proof]
fn bug_edge_range_addr_diff_ne() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k >= (1usize << 47) && k < (1usize << 48) - 8);
    assert!(p.wrapping_byte_add(k).addr().wrapping_sub(p.addr()) != k);
}

#[kani::proof]
fn safe_noprov_edge_addr() {
    let p = core::ptr::without_provenance::<u8>(0x1000);
    let k: usize = kani::any();
    kani::assume(k >= (1usize << 47) && k < (1usize << 47) + 16);
    assert!(p.wrapping_byte_add(k).addr() == 0x1000 + k);
}

#[kani::proof]
#[kani::should_panic]
fn sp_noprov_edge_addr() {
    let p = core::ptr::without_provenance::<u8>(0x1000);
    let k: usize = kani::any();
    kani::assume(k >= (1usize << 47) && k < (1usize << 47) + 16);
    assert!(p.wrapping_byte_add(k).addr() == 0x1000 + k);
}

#[kani::proof]
fn bug_noprov_edge_addr() {
    let p = core::ptr::without_provenance::<u8>(0x1000);
    let k: usize = kani::any();
    kani::assume(k >= (1usize << 47) && k < (1usize << 47) + 16);
    assert!(p.wrapping_byte_add(k).addr() != 0x1000 + k);
}

#[kani::proof]
fn safe_mid_edge_addr() {
    let a = [1u8; 16];
    let p = a.as_ptr().wrapping_add(8);
    let k: usize = kani::any();
    kani::assume(k == (1usize << 47) - 4);
    let q = p.wrapping_byte_add(k);
    assert!(q.addr() == p.addr() + k);
}

#[kani::proof]
#[kani::should_panic]
fn sp_mid_edge_addr() {
    let a = [1u8; 16];
    let p = a.as_ptr().wrapping_add(8);
    let k: usize = kani::any();
    kani::assume(k == (1usize << 47) - 4);
    let q = p.wrapping_byte_add(k);
    assert!(q.addr() == p.addr() + k);
}

#[kani::proof]
fn bug_mid_edge_addr() {
    let a = [1u8; 16];
    let p = a.as_ptr().wrapping_add(8);
    let k: usize = kani::any();
    kani::assume(k == (1usize << 47) - 4);
    let q = p.wrapping_byte_add(k);
    assert!(q.addr() != p.addr() + k);
}

#[kani::proof]
fn bug_far_roundtrip_ne() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
    assert!(q != p);
}

#[kani::proof]
fn bug_far_roundtrip_addr_ne() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
    assert!(q.addr() != p.addr());
}

#[kani::proof]
fn safe_far_roundtrip_addr_eq() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
    assert!(q.addr() == p.addr());
}

#[kani::proof]
#[kani::should_panic]
fn sp_far_roundtrip_addr_eq() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
    assert!(q.addr() == p.addr());
}

#[kani::proof]
fn safe_far_roundtrip_deref() {
    let a = [1u8, 2, 3, 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
    assert!(unsafe { *q } == 1);
}

#[kani::proof]
#[kani::should_panic]
fn sp_far_roundtrip_deref() {
    let a = [1u8, 2, 3, 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
    assert!(unsafe { *q } == 1);
}

#[kani::proof]
fn bug_far_const_roundtrip_ne() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_add(K).wrapping_byte_sub(K);
    assert!(q != p);
}

#[kani::proof]
fn safe_far_const_roundtrip_eq() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_add(K).wrapping_byte_sub(K);
    assert!(q == p);
}

#[kani::proof]
#[kani::should_panic]
fn sp_far_const_roundtrip_eq() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_add(K).wrapping_byte_sub(K);
    assert!(q == p);
}

#[kani::proof]
fn bug_far_const_roundtrip_addr_ne() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_add(K).wrapping_byte_sub(K);
    assert!(q.addr() != p.addr());
}

#[kani::proof]
fn bug_heap_far_roundtrip_ne() {
    let b = Box::new([1u8; 4]);
    let p = b.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
    assert!(q != p);
}

#[kani::proof]
fn bug_far_roundtrip_reach() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
    let _ = q;
    assert!(false);
}

#[kani::proof]
fn bug_far_const_roundtrip_reach() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    const K: usize = 0x8003_0000_0000_0000;
    let q = p.wrapping_byte_add(K).wrapping_byte_sub(K);
    let _ = q;
    assert!(false);
}

#[kani::proof]
fn bug_far_range_roundtrip_ne() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k >= (1usize << 61) && k < (1usize << 62));
    let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
    assert!(q != p);
}

#[kani::proof]
fn safe_noprov_far_roundtrip_addr() {
    let p = core::ptr::without_provenance::<u8>(0x1000);
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    assert!(p.wrapping_byte_add(k).wrapping_byte_sub(k).addr() == 0x1000);
}

#[kani::proof]
#[kani::should_panic]
fn sp_noprov_far_roundtrip_addr() {
    let p = core::ptr::without_provenance::<u8>(0x1000);
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    assert!(p.wrapping_byte_add(k).wrapping_byte_sub(k).addr() == 0x1000);
}

#[kani::proof]
fn bug_noprov_far_roundtrip_addr() {
    let p = core::ptr::without_provenance::<u8>(0x1000);
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    assert!(p.wrapping_byte_add(k).wrapping_byte_sub(k).addr() != 0x1000);
}

#[kani::proof]
fn bug_far_roundtrip_heap_addr_ne() {
    let b = Box::new([1u8; 4]);
    let p = b.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 3usize << 60);
    let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
    assert!(q.addr() != p.addr());
}

#[kani::proof]
fn safe_far_step_ne_other() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    assert!(a.as_ptr().wrapping_byte_add(k) != b.as_ptr());
}

#[kani::proof]
#[kani::should_panic]
fn sp_far_step_ne_other() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    assert!(a.as_ptr().wrapping_byte_add(k) != b.as_ptr());
}

#[kani::proof]
fn safe_far_step_eq_same_count() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 48);
    assert!(p.wrapping_byte_add(1usize << 48) == p.wrapping_byte_add(k));
}

#[kani::proof]
#[kani::should_panic]
fn sp_far_step_eq_same_count() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 48);
    assert!(p.wrapping_byte_add(1usize << 48) == p.wrapping_byte_add(k));
}

#[kani::proof]
fn safe_back_one_eq_same_count() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1);
    assert!(p.wrapping_byte_sub(1) == p.wrapping_byte_sub(k));
}

#[kani::proof]
fn safe_failclosed_sym_eq_2p48() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 48);
    assert!(p.wrapping_byte_add(k) == p);
}

#[kani::proof]
fn bug_failclosed_sym_ne_nonzero() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k != 0);
    assert!(p.wrapping_byte_add(k) != p);
}

#[kani::proof]
fn safe_failclosed_sym_addr_2p48() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 48);
    assert!(p.wrapping_byte_add(k).addr() == p.addr());
}

#[kani::proof]
fn bug_failclosed_sym_two_steps_eq() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    let j: usize = kani::any();
    assert!(p.wrapping_byte_add(k) != p.wrapping_byte_add(j) || k == j);
}

#[kani::proof]
fn safe_failclosed_sym_two_steps_eq_mod48() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    let j: usize = kani::any();
    assert!(p.wrapping_byte_add(k) != p.wrapping_byte_add(j) || (k.wrapping_sub(j) & ((1usize<<48)-1)) == 0);
}

#[kani::proof]
fn safe_failclosed_sym_addr_ne_other_obj() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    assert!(a.as_ptr().wrapping_byte_add(k).addr() != b.as_ptr().addr());
}

#[kani::proof]
fn bug_failclosed_sym_neg_step_addr_below() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k > 0 && k < 16);
    assert!(p.wrapping_byte_sub(k).addr() < p.addr());
}

#[kani::proof]
fn safe_failclosed_sym_step_cmp_lt_other() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    let p = a.as_ptr().wrapping_byte_add(k);
    let q = b.as_ptr();
    assert!(p.addr() >> 48 != q.addr() >> 48);
}

#[kani::proof]
fn bug_failclosed_eq_after_2p48() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    assert!(p.wrapping_byte_add(1usize << 48) == p);
}

#[kani::proof]
fn safe_failclosed_addr_eq_after_2p48() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    assert!(p.wrapping_byte_add(1usize << 48).addr() == p.addr());
}

#[kani::proof]
fn safe_failclosed_addr_top_bits_kept() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    assert!(p.wrapping_byte_add(k).addr() >> 48 == p.addr() >> 48);
}

#[kani::proof]
fn bug_failclosed_wrapping_sub_one_addr() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_sub(1);
    assert!(q.addr() == p.addr() - 1);
}

#[kani::proof]
fn safe_failclosed_cast_2p48() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 48);
    assert!(p.wrapping_byte_add(k) as usize == p as usize);
}

#[kani::proof]
fn bug_failclosed_cast_neg1() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1);
    assert!(p.wrapping_byte_sub(k) as usize == (p as usize) - 1);
}

#[kani::proof]
fn bug_failclosed_addr_neg1() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1);
    assert!(p.wrapping_byte_sub(k).addr() == p.addr() - 1);
}

#[kani::proof]
fn bug_failclosed_addr_diff_2p62() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    let q = p.wrapping_byte_add(k);
    assert!(q.addr() - p.addr() == 1usize << 62);
}

#[kani::proof]
fn safe_failclosed_without_ub_local() {
    let v = [0u128; 10];
    let v_0: *const u128 = &v[0];
    let high_offset = usize::MAX / (size_of::<u128>() * 4);
    let v_wrap: *const u128 = v_0.wrapping_add(high_offset);
    let wrapped_offset = (v_wrap.addr() - v_0.addr()) / size_of::<u128>();
    assert_eq!(high_offset, wrapped_offset);
}

#[kani::proof]
fn safe_failclosed_offset_from_far() {
    let a = [5u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 48);
    let q = p.wrapping_byte_add(k);
    let d = unsafe { q.offset_from(p) };
    assert!(d == 0 || d != 0);
}

#[kani::proof]
fn bug_failclosed_offset_from_neg1() {
    let a = [5u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_sub(1);
    let d = unsafe { q.offset_from(p) };
    assert!(d == -1);
}

#[kani::proof]
fn bug_failclosed_high_tag_roundtrip_eq() {
    let x = 5u64;
    let p = &x as *const u64;
    let tagged = p.map_addr(|a| a | (0x5Ausize << 56));
    let untagged = tagged.map_addr(|a| a & !(0xFFusize << 56));
    assert!(untagged == p);
}

#[kani::proof]
fn safe_failclosed_high_tag_roundtrip_ne() {
    let x = 5u64;
    let p = &x as *const u64;
    let tagged = p.map_addr(|a| a | (0x5Ausize << 56));
    let untagged = tagged.map_addr(|a| a & !(0xFFusize << 56));
    assert!(untagged != p);
}

#[kani::proof]
fn bug_failclosed_high_tag_roundtrip_deref() {
    let x = 5u64;
    let p = &x as *const u64;
    let tagged = p.map_addr(|a| a | (0x5Ausize << 56));
    let untagged = tagged.map_addr(|a| a & !(0xFFusize << 56));
    assert!(unsafe { *untagged } == 5);
}

#[kani::proof]
fn bug_failclosed_high_tag_roundtrip_deref_value() {
    let x = 5u64;
    let p = &x as *const u64;
    let tagged = p.map_addr(|a| a | (0x5Ausize << 56));
    let untagged = tagged.map_addr(|a| a & !(0xFFusize << 56));
    assert!(unsafe { *untagged } == 6);
}

#[kani::proof]
fn bug_failclosed_two_half_steps_ne() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 47);
    let q = p.wrapping_byte_add(k).wrapping_byte_add(k);
    assert!(q != p);
}

#[kani::proof]
fn safe_low_tag_roundtrip_heap() {
    let p = Box::into_raw(Box::new(5u64));
    let tagged = p.map_addr(|a| a | 1);
    let untagged = tagged.map_addr(|a| a & !1);
    assert!(unsafe { *untagged } == 5);
    unsafe { drop(Box::from_raw(untagged)) };
}

#[kani::proof]
#[kani::should_panic]
fn sp_low_tag_roundtrip_heap() {
    let p = Box::into_raw(Box::new(5u64));
    let tagged = p.map_addr(|a| a | 1);
    let untagged = tagged.map_addr(|a| a & !1);
    assert!(unsafe { *untagged } == 5);
    unsafe { drop(Box::from_raw(untagged)) };
}

#[kani::proof]
fn bug_low_tag_roundtrip_heap() {
    let p = Box::into_raw(Box::new(5u64));
    let tagged = p.map_addr(|a| a | 1);
    let untagged = tagged.map_addr(|a| a & !1);
    assert!(unsafe { *untagged } == 6);
    unsafe { drop(Box::from_raw(untagged)) };
}

#[kani::proof]
fn safe_low_tag_roundtrip_stack() {
    let x = 5u64;
    let p = &x as *const u64;
    let tagged = p.map_addr(|a| a | 2);
    assert!(tagged.addr() & 3 == 2);
    let untagged = tagged.map_addr(|a| a & !3);
    assert!(untagged == p);
    assert!(unsafe { *untagged } == 5);
}

#[kani::proof]
fn bug_heap_small_oob() {
    let b = Box::new([1u8; 4]);
    let p = b.as_ptr();
    let k: usize = kani::any();
    kani::assume(k >= 4 && k < 1000);
    let q = p.wrapping_add(k);
    let _v = unsafe { *q };
}

#[kani::proof]
fn bug_vec_small_oob() {
    let v = vec![1u8; 4];
    let p = v.as_ptr();
    let k: usize = kani::any();
    kani::assume(k >= 4 && k < 1000);
    let q = p.wrapping_add(k);
    let _v = unsafe { *q };
}

#[kani::proof]
fn bug_heap_sym_small_oob_value() {
    let b = Box::new([1u8; 4]);
    let k: usize = kani::any();
    kani::assume(k >= 4 && k < 1000);
    let v = unsafe { *b.as_ptr().wrapping_add(k) };
    assert!(v == v);
}

#[kani::proof]
fn bug_vec_sym_small_oob_value() {
    let v = vec![1u8; 4];
    let k: usize = kani::any();
    kani::assume(k >= 4 && k < 1000);
    let x = unsafe { *v.as_ptr().wrapping_add(k) };
    assert!(x == x);
}

#[kani::proof]
fn safe_heap_sym_in_bounds() {
    let b = Box::new([1u8; 4]);
    let k: usize = kani::any();
    kani::assume(k < 4);
    let v = unsafe { *b.as_ptr().wrapping_add(k) };
    assert!(v == 1);
}

#[kani::proof]
fn bug_heap_2p48_deref() {
    let a = Box::new(1u8);
    let b = Box::new(2u8);
    let k: usize = kani::any();
    kani::assume(k == 1usize << 48);
    let v = unsafe { *(&*a as *const u8).wrapping_byte_add(k) };
    assert!(v == 1 || v == 2 || *b == 2);
}

#[kani::proof]
fn bug_heap_2p48_range_deref() {
    let a = Box::new([1u8; 4]);
    let _b = Box::new([2u8; 4]);
    let k: usize = kani::any();
    kani::assume(k >= (1usize << 48) && k < (1usize << 48) + 4);
    let v = unsafe { *(a.as_ptr()).wrapping_byte_add(k) };
    assert!(v == v);
}

#[kani::proof]
fn bug_heap_far_roundtrip_write() {
    let mut b = Box::new([1u8; 4]);
    let p = b.as_mut_ptr();
    let k: usize = kani::any();
    kani::assume(k == 1usize << 62);
    let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
    unsafe { *q = 7 };
    assert!(b[0] == 1);
}
