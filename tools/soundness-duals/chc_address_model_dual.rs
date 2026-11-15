// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS, every `safe_` harness is SUCCESSFUL, and every `sp_`
// harness (`#[kani::should_panic]` over a program that never panics) FAILS.
//
// WHY THIS FILE EXISTS: pointer ADDRESSES as integers (heap/stack_address.rs).
// A pointer term is its (object, offset) identity; only address-taken stack
// locals whose address the body observes get a nondeterministic base, and
// `base + offset` is their address. The third review of
// fix/chc-false-certificates (2026-09-27; main c22e1022e and the branch bundle
// bb9a5efcfb57, ay 22db3bcc1, chc, 30 s) measured, on both bundles:
// - `addr()` counted only as a COMPARISON's operand, so a lone `(&y).addr()`
//   left `y` untracked, and its identity term equalled `&x as usize` for a
//   solver-chosen base of `x`: safe_cast_vs_addr_distinct FAILED certified
//   Genuine and sp_cast_vs_addr_distinct passed; the same through a transmute
//   of a pointer array (safe_array_transmute_observed) and a heap pointer,
//   which never has a base (safe_heap_vs_stack_addr);
// - `with_addr(self, a)` read the pointer at `a` from whichever allocation
//   holds it, losing `self`'s provenance: bug_with_addr_other_object and
//   bug_with_addr_past_end clean proofs where Kani reports a dereference
//   outside the object.
// `addr` / `expose_provenance` / `with_addr` / `map_addr` now observe each
// pointer they receive, an aggregate transmute of pointers into integers
// observes them, an untracked object's identity range is disjoint from every
// tracked base, and `with_addr` is `self.wrapping_byte_offset(a - self.addr())`.
// The fourth review (2026-09-28) replaced the identity-range fact with address
// regions (every object its own 2^48-byte region, as in Kani) and moved the
// wrapping step onto the address view; see the section below.

use std::mem::transmute;

#[kani::proof]
fn safe_cast_vs_addr_distinct() {
    let x = 1u8;
    let y = 2u8;
    let ax = &x as *const u8 as usize;
    let ay = (&y as *const u8).addr();
    assert!(ax != ay);
}

#[kani::proof]
fn bug_cast_vs_addr_equal() {
    let x = 1u8;
    let y = 2u8;
    let ax = &x as *const u8 as usize;
    let ay = (&y as *const u8).addr();
    assert!(ax == ay);
}

#[kani::proof]
fn safe_addr_vs_transmute() {
    let x = 1u8;
    let y = 2u8;
    let ax = (&x as *const u8).addr();
    let ty: usize = unsafe { transmute(&y as *const u8) };
    assert!(ax != ty);
}

#[kani::proof]
fn safe_array_transmute_observed() {
    let x = 5u8;
    let y = 6u8;
    let a: [*const u8; 2] = [&x, &y];
    let b: [usize; 2] = unsafe { transmute(a) };
    assert!(b[0] == &x as *const u8 as usize);
    assert!(b[1] != b[0]);
}

#[kani::proof]
fn safe_heap_vs_stack_addr() {
    let x = 1u8;
    let b = Box::new(2u8);
    let ax = &x as *const u8 as usize;
    let ab = (&*b as *const u8).addr();
    assert!(ax != ab);
}

#[kani::proof]
fn safe_cast_vs_addr_same() {
    let x = 1u8;
    let p = &x as *const u8;
    assert!(p.addr() == p as usize);
}

#[kani::proof]
fn safe_with_addr_inner() {
    let a = [1u8, 2, 3, 4];
    let p = a.as_ptr();
    let q = p.with_addr(p.addr() + 2);
    assert!(unsafe { *q } == 3);
}

#[kani::proof]
fn bug_with_addr_other_object() {
    let a = [1u8, 2, 3, 4];
    let b = [9u8, 9, 9, 9];
    let p = a.as_ptr();
    let q = p.with_addr(b.as_ptr().addr());
    let v = unsafe { *q };
    assert!(v == 9 || v != 9);
}

#[kani::proof]
fn bug_with_addr_past_end() {
    let a = [1u8, 2, 3, 4];
    let p = a.as_ptr();
    let q = p.with_addr(p.addr() + 4);
    let v = unsafe { *q };
    assert!(v == 0 || v != 0);
}

// A heap buffer of no recorded size and a pointer loaded through a join: the
// layout fact is the untracked object's identity SLOT, which needs no size and
// reads no heap metadata. The first cut read `obj_size` for a lane that is not a
// constant (safe_join_ptr_vs_stack went from a proof on main to Unknown) and
// left the fact out wherever the body read no heap metadata (the vec![7u8; 3]
// and with_capacity rows stayed false certificates, as on main).
#[kani::proof]
fn safe_join_ptr_vs_stack() {
    let x = 1u8;
    let y = 2u8;
    let z = 3u8;
    let b: bool = kani::any();
    let p: *const u8 = if b { &y } else { &z };
    let ax = &x as *const u8 as usize;
    assert!(p as usize != ax);
}

#[kani::proof]
fn bug_join_ptr_vs_stack() {
    let x = 1u8;
    let y = 2u8;
    let b: bool = kani::any();
    let p: *const u8 = if b { &y } else { &x };
    let ax = &x as *const u8 as usize;
    assert!(p as usize != ax);
}

#[kani::proof]
fn safe_from_elem_vs_stack() {
    let x = 1u8;
    let v = vec![7u8; 3];
    assert!(v.as_ptr() as usize != &x as *const u8 as usize);
}

#[kani::proof]
fn safe_with_capacity_vs_stack() {
    let x = 1u8;
    let mut v: Vec<u8> = Vec::with_capacity(2);
    v.push(5);
    assert!(v.as_ptr() as usize != &x as *const u8 as usize);
}

#[kani::proof]
fn safe_vec_literal_vs_stack() {
    let x = 1u8;
    let v = vec![2u8, 3];
    assert!((&x as *const u8 as usize) != v.as_ptr().addr());
}

#[kani::proof]
fn bug_vec_literal_vs_stack() {
    let x = 1u8;
    let v = vec![2u8, 3];
    assert!((&x as *const u8 as usize) == v.as_ptr().addr());
}

// ---- should_panic twins: each body never panics ----

#[kani::proof]
#[kani::should_panic]
fn sp_cast_vs_addr_distinct() {
    let x = 1u8;
    let y = 2u8;
    let ax = &x as *const u8 as usize;
    let ay = (&y as *const u8).addr();
    assert!(ax != ay);
}

#[kani::proof]
#[kani::should_panic]
fn sp_heap_vs_stack_addr() {
    let x = 1u8;
    let b = Box::new(2u8);
    let ax = &x as *const u8 as usize;
    let ab = (&*b as *const u8).addr();
    assert!(ax != ab);
}

#[kani::proof]
#[kani::should_panic]
fn sp_array_transmute_observed() {
    let x = 5u8;
    let y = 6u8;
    let a: [*const u8; 2] = [&x, &y];
    let b: [usize; 2] = unsafe { transmute(a) };
    assert!(b[0] == &x as *const u8 as usize);
    assert!(b[1] != b[0]);
}

#[kani::proof]
#[kani::should_panic]
fn sp_join_ptr_vs_stack() {
    let x = 1u8;
    let y = 2u8;
    let z = 3u8;
    let b: bool = kani::any();
    let p: *const u8 = if b { &y } else { &z };
    let ax = &x as *const u8 as usize;
    assert!(p as usize != ax);
}

#[kani::proof]
#[kani::should_panic]
fn sp_from_elem_vs_stack() {
    let x = 1u8;
    let v = vec![7u8; 3];
    assert!(v.as_ptr() as usize != &x as *const u8 as usize);
}

#[kani::proof]
#[kani::should_panic]
fn sp_with_capacity_vs_stack() {
    let x = 1u8;
    let mut v: Vec<u8> = Vec::with_capacity(2);
    v.push(5);
    assert!(v.as_ptr() as usize != &x as *const u8 as usize);
}

#[kani::proof]
#[kani::should_panic]
fn sp_vec_literal_vs_stack() {
    let x = 1u8;
    let v = vec![2u8, 3];
    assert!((&x as *const u8 as usize) != v.as_ptr().addr());
}

// ---- steps of 2^32 bytes and more, and addresses across objects ----
//
// Fourth review of fix/chc-false-certificates (2026-09-28), on main c22e1022e
// and the third-review branch alike:
// - a wrapping step was mod 2^64 on the identity term, whose object id sits
//   right above the 32-bit offset, so a step of 2^32 bytes carried into the NEXT
//   object: bug_wrapping_2p32_deref and its heap, backward and element-count
//   variants were clean proofs where Kani reports a pointer outside object
//   bounds, and safe_ptr_ne_after_2p32 / safe_heap_ptr_ne_after_2p32 certified
//   Genuine counterexamples. The step now moves the ADDRESS VIEW
//   `object << 48 | offset48` (pointer_step.rs), whose carries stay in the
//   lane's high offset bits below 2^48; an access through such a lane is
//   outside every object; a constant step that can reach another object's
//   lane (about 2^48 or more) fails closed.
// - an untracked object's address was its identity term, 2^32 apart from the
//   next one, and a tracked base could sit anywhere disjoint from the other
//   bases: `heap - 1`, `heap + 2^32`, `&x + 1 == heap`, `heap_a + 2^32 ==
//   heap_b`, two adjacent locals and a local at a constant address all
//   certified Genuine counterexamples Kani refutes. Every object now has its
//   own 2^48-byte region (Kani's layout): an untracked object the region of
//   its id, a tracked local a free region (heap/stack_address.rs).

#[kani::proof]
fn bug_wrapping_2p32_deref() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let p = a.as_ptr().wrapping_byte_add(1usize << 32);
    let v = unsafe { *p };
    assert!(v == 1 || v == 2 || v == b[0]);
}

#[kani::proof]
fn bug_wrapping_2p32_neg_deref() {
    let b = [2u8; 4];
    let a = [1u8; 4];
    let p = a.as_ptr().wrapping_byte_sub(1usize << 32);
    let v = unsafe { *p };
    assert!(v == 1 || v == 2 || v == b[0]);
}

#[kani::proof]
fn bug_heap_2p32_deref() {
    let a = Box::new(1u8);
    let b = Box::new(2u8);
    let p = (&*a as *const u8).wrapping_byte_add(1usize << 32);
    let v = unsafe { *p };
    assert!(v == 1 || v == 2 || v == *b);
}

#[kani::proof]
fn bug_heap_2p32_neg_deref() {
    let b = Box::new(2u8);
    let a = Box::new(1u8);
    let p = (&*a as *const u8).wrapping_byte_sub(1usize << 32);
    let v = unsafe { *p };
    assert!(v == 1 || v == 2 || v == *b);
}

#[kani::proof]
fn bug_wrapping_add_elems_2p32_deref() {
    let a = [1u32; 4];
    let b = [2u32; 4];
    let p = a.as_ptr().wrapping_add(1usize << 30);
    let v = unsafe { *p };
    assert!(v == 1 || v == 2 || v == b[0]);
}

#[kani::proof]
fn bug_with_addr_2p32_deref() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let p = a.as_ptr();
    let q = p.with_addr(p.addr() + (1usize << 32));
    let v = unsafe { *q };
    assert!(v == 1 || v == 2 || v == b[0]);
}

#[kani::proof]
fn bug_wrapping_2p48_deref() {
    let a = [1u8; 4];
    let p = a.as_ptr().wrapping_byte_add(1usize << 48);
    let v = unsafe { *p };
    assert!(v == 1 || v != 1);
}

#[kani::proof]
fn safe_ptr_ne_after_2p32() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let p = a.as_ptr().wrapping_byte_add(1usize << 32);
    assert!(p != b.as_ptr());
}

#[kani::proof]
fn safe_heap_ptr_ne_after_2p32() {
    let a = Box::new(1u8);
    let b = Box::new(2u8);
    let p = (&*a as *const u8).wrapping_byte_add(1usize << 32);
    assert!(p != &*b as *const u8);
}

#[kani::proof]
fn safe_ptr_ne_after_2p48() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let p = a.as_ptr().wrapping_byte_add(1usize << 48);
    assert!(p != b.as_ptr());
}

#[kani::proof]
fn safe_wrap_2p32_roundtrip() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_add(1usize << 32).wrapping_byte_sub(1usize << 32);
    assert!(q == p);
    assert!(unsafe { *q } == 1);
}

#[kani::proof]
fn safe_wrap_2p32_ne_self() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_add(1usize << 32);
    assert!(q != p);
}

#[kani::proof]
fn safe_wrap_2p32_addr_heap() {
    let a = Box::new(1u8);
    let p = &*a as *const u8;
    let q = p.wrapping_byte_add(1usize << 32);
    assert!(q.addr() == p.addr().wrapping_add(1usize << 32));
}

#[kani::proof]
fn bug_wrap_2p32_addr_heap() {
    let a = Box::new(1u8);
    let p = &*a as *const u8;
    let q = p.wrapping_byte_add(1usize << 32);
    assert!(q.addr() == p.addr());
}

#[kani::proof]
fn safe_wrap_2p32_addr_stack() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_add(1usize << 32);
    assert!(q as usize == (p as usize).wrapping_add(1usize << 32));
}

#[kani::proof]
fn safe_without_provenance_big_addr() {
    let p: *const u8 = core::ptr::without_provenance(1usize << 40);
    assert!(p.addr() == 1usize << 40);
}

#[kani::proof]
fn safe_null_wrapping_big_addr() {
    let p: *const u8 = core::ptr::null::<u8>().wrapping_add(1usize << 40);
    assert!(p as usize == 1usize << 40);
}

#[kani::proof]
fn safe_int_cast_big_addr() {
    let p = (1usize << 40) as *const u8;
    assert!(p as usize == 1usize << 40);
}

#[kani::proof]
fn safe_heap_minus1_vs_stack() {
    let b = Box::new(1u8);
    let x = 2u8;
    let hb = (&*b as *const u8 as usize).wrapping_sub(1);
    let sx = &x as *const u8 as usize;
    assert!(hb != sx);
}

#[kani::proof]
fn safe_heap_plus_2p32_vs_stack() {
    let b = Box::new(1u8);
    let x = 2u8;
    let hb = (&*b as *const u8 as usize).wrapping_add(1usize << 32);
    let sx = &x as *const u8 as usize;
    assert!(hb != sx);
}

#[kani::proof]
fn safe_stack_end_vs_heap_start() {
    let b = Box::new(1u8);
    let x = 2u8;
    let hb = &*b as *const u8 as usize;
    let sx = &x as *const u8 as usize;
    assert!(sx + 1 != hb);
}

#[kani::proof]
fn safe_heap_plus_2p32_vs_heap() {
    let a = Box::new(1u8);
    let b = Box::new(2u8);
    let ha = &*a as *const u8 as usize;
    let hb = &*b as *const u8 as usize;
    assert!(ha.wrapping_add(1usize << 32) != hb);
}

#[kani::proof]
fn safe_heap_minus_2p32_vs_heap() {
    let a = Box::new(1u8);
    let b = Box::new(2u8);
    let ha = &*a as *const u8 as usize;
    let hb = &*b as *const u8 as usize;
    assert!(hb.wrapping_sub(1usize << 32) != ha);
}

#[kani::proof]
fn safe_stack_not_adjacent() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let pa = &a as *const [u8; 4] as usize;
    let pb = &b as *const [u8; 4] as usize;
    assert!(pa + 4 != pb && pb + 4 != pa);
}

#[kani::proof]
fn safe_stack_not_constant_addr() {
    let x = 0u8;
    assert!(&x as *const u8 as usize != 0x1000);
}

#[kani::proof]
fn safe_int_roundtrip_with_stack() {
    let x = 0u8;
    let _b = &x as *const u8 as usize;
    let n: usize = kani::any();
    let p = n as *const u8;
    assert!(p as usize == n);
}

#[kani::proof]
fn bug_int_roundtrip_with_stack() {
    let x = 0u8;
    let _b = &x as *const u8 as usize;
    let n: usize = kani::any();
    let p = n as *const u8;
    assert!(p as usize != n);
}

#[kani::proof]
fn bug_int_near_stack() {
    let x = 0u8;
    let n: usize = kani::any();
    let p = n as *const u8;
    assert!(p as usize != (&x as *const u8 as usize).wrapping_add(1000));
}

#[kani::proof]
#[kani::should_panic]
fn sp_ptr_ne_after_2p32() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let p = a.as_ptr().wrapping_byte_add(1usize << 32);
    assert!(p != b.as_ptr());
}

#[kani::proof]
#[kani::should_panic]
fn sp_heap_ptr_ne_after_2p32() {
    let a = Box::new(1u8);
    let b = Box::new(2u8);
    let p = (&*a as *const u8).wrapping_byte_add(1usize << 32);
    assert!(p != &*b as *const u8);
}

#[kani::proof]
#[kani::should_panic]
fn sp_wrap_2p32_addr_stack() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_add(1usize << 32);
    assert!(q as usize == (p as usize).wrapping_add(1usize << 32));
}

#[kani::proof]
#[kani::should_panic]
fn sp_heap_minus1_vs_stack() {
    let b = Box::new(1u8);
    let x = 2u8;
    let hb = (&*b as *const u8 as usize).wrapping_sub(1);
    let sx = &x as *const u8 as usize;
    assert!(hb != sx);
}

#[kani::proof]
#[kani::should_panic]
fn sp_heap_plus_2p32_vs_stack() {
    let b = Box::new(1u8);
    let x = 2u8;
    let hb = (&*b as *const u8 as usize).wrapping_add(1usize << 32);
    let sx = &x as *const u8 as usize;
    assert!(hb != sx);
}

#[kani::proof]
#[kani::should_panic]
fn sp_stack_end_vs_heap_start() {
    let b = Box::new(1u8);
    let x = 2u8;
    let hb = &*b as *const u8 as usize;
    let sx = &x as *const u8 as usize;
    assert!(sx + 1 != hb);
}

#[kani::proof]
#[kani::should_panic]
fn sp_heap_plus_2p32_vs_heap() {
    let a = Box::new(1u8);
    let b = Box::new(2u8);
    let ha = &*a as *const u8 as usize;
    let hb = &*b as *const u8 as usize;
    assert!(ha.wrapping_add(1usize << 32) != hb);
}

#[kani::proof]
#[kani::should_panic]
fn sp_stack_not_adjacent() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let pa = &a as *const [u8; 4] as usize;
    let pb = &b as *const [u8; 4] as usize;
    assert!(pa + 4 != pb && pb + 4 != pa);
}

#[kani::proof]
#[kani::should_panic]
fn sp_stack_not_constant_addr() {
    let x = 0u8;
    assert!(&x as *const u8 as usize != 0x1000);
}

#[kani::proof]
#[kani::should_panic]
fn sp_int_roundtrip_with_stack() {
    let x = 0u8;
    let _b = &x as *const u8 as usize;
    let n: usize = kani::any();
    let p = n as *const u8;
    assert!(p as usize == n);
}

// Wrapping steps that leave their object (fifth round of
// fix/chc-false-certificates, 2026-10-01; sixth round, 2026-10-02). The address
// arithmetic of a wrapping step carried a pointer into the 2^48-byte window of
// ANOTHER object, where the identity with that address was that object's
// pointer: a count the solver picks refuted `a.as_ptr().wrapping_byte_add(k) !=
// b.as_ptr()` (the three rows below were known red, false certificates on main
// and the fourth round), and a dereference after a step of 2^48 read `b` in
// bounds. A wrapping step now keeps its object and moves its offset from the
// object's base mod 2^64 (Rust's provenance, Kani's object bits); an offset
// outside [0, 2^48), Kani's object range, makes the pointer far: a dereference
// is outside its object and it equals no pointer of another object. Its
// address, order, `offset_from` and an equality its low 48 bits decide are
// fail-closed observations, because Kani answers them with a 48-bit wrap under
// a symbolic count and with 64-bit offsets under a literal one: the address
// rows `safe_sym_step_addr_ne_other_object`, `safe_sym_step_region_ne_other`
// and `safe_const_back_one_as_usize` fail closed, known-red false failures under
// decision C7 (chc_wrapping_object_range_dual.rs
// pins the other shapes). The fifth round's centered windows and landed marks
// are gone (see that file).
#[kani::proof]
fn safe_sym_step_ne_other_object() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    assert!(a.as_ptr().wrapping_byte_add(k) != b.as_ptr());
}

#[kani::proof]
fn safe_sym_step_ne_other_heap_object() {
    let a = Box::new(1u8);
    let b = Box::new(2u8);
    let k: usize = kani::any();
    assert!((&*a as *const u8).wrapping_byte_add(k) != &*b as *const u8);
}

#[kani::proof]
fn safe_sym_step_addr_ne_other_object() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    assert!(a.as_ptr().wrapping_byte_add(k).addr() != b.as_ptr().addr());
}

#[kani::proof]
#[kani::should_panic]
fn sp_sym_step_ne_other_object() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    assert!(a.as_ptr().wrapping_byte_add(k) != b.as_ptr());
}

#[kani::proof]
#[kani::should_panic]
fn sp_sym_step_addr_ne_other_object() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    assert!(a.as_ptr().wrapping_byte_add(k).addr() != b.as_ptr().addr());
}

#[kani::proof]
fn safe_sym_step_from_middle_ne_other() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    assert!(a.as_ptr().wrapping_byte_add(2).wrapping_byte_add(k) != b.as_ptr().wrapping_byte_add(1));
}

#[kani::proof]
#[kani::should_panic]
fn sp_sym_step_from_middle_ne_other() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    assert!(a.as_ptr().wrapping_byte_add(2).wrapping_byte_add(k) != b.as_ptr().wrapping_byte_add(1));
}

#[kani::proof]
fn safe_sym_step_region_ne_other() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    let p = a.as_ptr().wrapping_byte_add(k);
    assert!(p.addr() >> 48 != b.as_ptr().addr() >> 48);
}

#[kani::proof]
#[kani::should_panic]
fn sp_sym_step_region_ne_other() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    let p = a.as_ptr().wrapping_byte_add(k);
    assert!(p.addr() >> 48 != b.as_ptr().addr() >> 48);
}

#[kani::proof]
fn bug_sym_step_eq_same_object() {
    let a = [1u8; 4];
    let k: usize = kani::any();
    assert!(a.as_ptr().wrapping_byte_add(k) != a.as_ptr().wrapping_byte_add(2));
}

#[kani::proof]
fn bug_sym_step_2p48_deref_next_object() {
    let a = [1u8; 4];
    let b = [2u8; 4];
    let k: usize = kani::any();
    kani::assume(k == 1usize << 48);
    let v = unsafe { *a.as_ptr().wrapping_byte_add(k) };
    assert!(v == 1 || v == 2 || b[0] == 2);
}

#[kani::proof]
fn bug_sym_step_back_2p48_deref_prev_object() {
    let b = [2u8; 4];
    let a = [1u8; 4];
    let k: usize = kani::any();
    kani::assume(k == 1usize << 48);
    let v = unsafe { *a.as_ptr().wrapping_byte_sub(k) };
    assert!(v == 1 || v == 2 || b[0] == 2);
}

#[kani::proof]
fn bug_sym_step_2p32_range_deref() {
    let a = [1u8; 4];
    let k: usize = kani::any();
    kani::assume(k >= (1usize << 32) && k < (1usize << 32) + 4);
    let v = unsafe { *a.as_ptr().wrapping_byte_add(k) };
    assert!(v == v);
}

#[kani::proof]
fn bug_sym_step_2p48_range_deref() {
    let a = [1u8; 4];
    let k: usize = kani::any();
    kani::assume(k >= (1usize << 48) && k < (1usize << 48) + 4);
    let v = unsafe { *a.as_ptr().wrapping_byte_add(k) };
    assert!(v == v);
}

#[kani::proof]
fn bug_sym_step_addr_diff_is_k() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    assert!(p.wrapping_byte_add(k).addr().wrapping_sub(p.addr()) == k);
}

#[kani::proof]
fn bug_sym_two_steps_eq() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    let j: usize = kani::any();
    assert!(p.wrapping_byte_add(k) != p.wrapping_byte_add(j) || k == j);
}

#[kani::proof]
fn safe_const_back_one_vs_other_far() {
    let b = [2u8; 4];
    let a = [1u8; 4];
    assert!(a.as_ptr().wrapping_byte_sub(1) != b.as_ptr().wrapping_byte_add((1usize << 48) - 1));
}

#[kani::proof]
#[kani::should_panic]
fn sp_const_back_one_vs_other_far() {
    let b = [2u8; 4];
    let a = [1u8; 4];
    assert!(a.as_ptr().wrapping_byte_sub(1) != b.as_ptr().wrapping_byte_add((1usize << 48) - 1));
}

#[kani::proof]
fn safe_const_back_one_as_usize() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    assert!(p.wrapping_byte_sub(1) as usize == (p as usize) - 1);
}

#[kani::proof]
fn safe_const_back_one_and_forward() {
    let a = [1u8, 2, 3, 4];
    let p = a.as_ptr();
    let q = p.wrapping_byte_sub(1).wrapping_byte_add(1);
    assert!(q == p);
    assert!(unsafe { *q } == 1);
}

// Round trips through a far pointer come back exactly: the step's offset is
// accumulated along the pointer's definition chain (the fifth round read a
// free bit here and failed them closed).
#[kani::proof]
fn safe_sym_roundtrip_eq() {
    let a = [1u8; 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    assert!(p.wrapping_byte_add(k).wrapping_byte_sub(k) == p);
}

#[kani::proof]
fn safe_sym_roundtrip_deref() {
    let a = [1u8, 2, 3, 4];
    let p = a.as_ptr();
    let k: usize = kani::any();
    assert!(unsafe { *p.wrapping_byte_add(k).wrapping_byte_sub(k) } == 1);
}
