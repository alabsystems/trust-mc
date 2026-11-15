// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a store through a reference loaded out of a
//! reference-typed (or raw-pointer) field of a struct: `*h.p = 7` with
//! `h = HM { n, p: &mut *bx }`.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-26):
//!   bug_heap_direct            -> FAILED ('assertion failed: *bx != 7')
//!   safe_heap_direct           -> SUCCESSFUL
//!   bug_heap_helper            -> FAILED ('assertion failed: *bx != 7')
//!   safe_heap_helper           -> SUCCESSFUL
//!   safe_heap_helper_slot_kept -> SUCCESSFUL
//!   bug_stack_helper           -> FAILED ('assertion failed: x != 7'; control)
//!   safe_stack_helper          -> SUCCESSFUL (control)
//!   bug_heap_raw_field         -> FAILED ('assertion failed: *bx != 7')
//!   safe_heap_raw_field        -> SUCCESSFUL
//!   bug_heap_reborrow_helper   -> FAILED ('assertion failed: *bx != 7')
//!   safe_heap_reborrow_helper  -> SUCCESSFUL
//!   bug_heap_nested            -> FAILED ('assertion failed: *bx != 7')
//!   safe_heap_nested           -> SUCCESSFUL
//!   bug_heap_closure           -> FAILED ('assertion failed: *bx != 7')
//!   safe_heap_closure          -> SUCCESSFUL
//!   bug_usize_write_into_field -> FAILED ('assertion failed: *y != 7')
//!   safe_usize_write_into_field -> SUCCESSFUL
//!   bug_copy_whole_over_owner  -> FAILED ('assertion failed: *y != 7')
//!   safe_copy_whole_over_owner -> SUCCESSFUL
//!   bug_shared_cast_write_into_field  -> FAILED ('assertion failed: *y != 7')
//!   safe_shared_cast_write_into_field -> SUCCESSFUL
//!   bug_union_other_field_rebinds  -> FAILED ('assertion failed: *y != 7')
//!   safe_union_other_field_rebinds -> SUCCESSFUL
//!   bug_copy_pointer_into_field    -> FAILED ('assertion failed: *y != 7')
//!   safe_copy_pointer_into_field   -> SUCCESSFUL
//!   bug_whole_store_through_raw_owner  -> FAILED ('assertion failed: *y != 7')
//!   safe_whole_store_through_raw_owner -> SUCCESSFUL
//!   bug_bytes_write_into_field     -> FAILED ('assertion failed: *y != 7')
//!   safe_usize_write_no_reborrow   -> SUCCESSFUL
//!   bug_copy_owner_after_untyped   -> FAILED ('assertion failed: *y != 7')
//!   safe_copy_owner_after_untyped  -> SUCCESSFUL
//!   bug_copy_owner_after_memcpy    -> FAILED ('assertion failed: *y != 7')
//!   safe_copy_owner_after_memcpy   -> SUCCESSFUL
//!   bug_copy_owner_after_untyped_stack  -> FAILED ('assertion failed: z != 7')
//!   safe_copy_owner_after_untyped_stack -> SUCCESSFUL
//!   bug_source_local_rewritten     -> FAILED ('assertion failed: *y != 7')
//!   safe_source_local_rewritten    -> SUCCESSFUL
//!   bug_source_local_memcpy        -> FAILED ('assertion failed: *y != 7')
//!   safe_source_local_memcpy       -> SUCCESSFUL
//!   bug_source_swapped             -> FAILED ('assertion failed: *y != 7')
//!   safe_source_swapped            -> SUCCESSFUL
//!   bug_source_rewritten_shared_owner_ref  -> FAILED ('assertion failed: *y != 7')
//!   safe_source_rewritten_shared_owner_ref -> SUCCESSFUL
//!   bug_source_zeroed_null_deref   -> FAILED (null pointer dereference)
//!   bug_source_transmuted_from_usize  -> FAILED ('assertion failed: *y != 7')
//!   safe_source_transmuted_from_usize -> SUCCESSFUL
//!
//! MECHANISM (pre-existing on main, fixed on fix/chc-lost-writes). Pass 1.5
//! of the ref-target collection (`DerefProjectedCopy`) records
//! `_t = copy (*_r).p` as the PLACE `h.p` ("value-of"), while every
//! consumer of `ref_targets` reads an edge as "points at". When `p` is itself
//! a pointer, `_t` points at `*h.p`, not at the slot `h.p`. Pass 2.5 repairs
//! the edge only when the aggregate's field was built from a pointer with an
//! edge of its own (`&mut x` of a stack local); a heap referent (`&mut *bx`)
//! has none, so the edge stayed, and the store `*_t = 7` wrote 7 into the
//! POINTER field `h.p`. The heap referent kept its value: every bug_heap row
//! except the closure and nested ones was SUCCESSFUL clean on main, and their
//! safe twins were FAILED Genuine (false certificates). The same edge put a
//! modifies-frame check on the slot inside the footprint instead of on the
//! heap referent outside it (modifies_frame_call_arg_escape_dual.rs).
//!
//! The fix drops every value-of edge onto a pointer-typed field
//! (`drop_pointer_field_value_of_edges`), so `_t` resolves through the pointer
//! value it holds, and the store's provenance walks follow the operand the
//! aggregate's field was built from (`pointer_field_value_source`), which
//! names the heap allocation: the store is placed exactly. The closure and
//! nested rows fail closed on both bundles (a deref store through an
//! unresolved referent); their safe twins are known-red false failures.
//!
//! UNTYPED REBINDING (review of fix/chc-lost-writes, 2026-09-27). The first
//! version of the fix trusted the aggregate's operand as the field's value
//! after any write the pointer-store guards do not see: a `usize` store
//! through a pointer cast from `addr_of_mut!(h.p)`, or a byte copy over the
//! owner (`ptr::copy_nonoverlapping(&h2, &mut h, 1)`). The store `*r.p = 7`
//! was then placed on the old referent `*bx`: both safe rows below were
//! certified Genuine, and both bug rows verified SUCCESSFUL clean on the
//! baseline and the first fix alike. The operand is now trusted only when no
//! pointer that may address the owner's bytes is cast, passed to a call,
//! captured, or used to store into the pointer field
//! (`stmt/codegen_stmt_store/pointer_field_escape.rs`); otherwise the store
//! through `r.p` is unresolved and fails closed. A pointer cast from a SHARED
//! borrow of the owner is followed too (the write through it is undefined
//! behaviour, but the oracle executes it), and a union owner is always
//! refused (its fields overlap). The safe rows are known-red false failures.
//! The last six rows (review follow-up 2, 2026-09-27) promote the rest of the
//! rebinding writers the review named: a byte copy of a pointer into the
//! field, a whole-owner store through a raw pointer, the field rewritten byte
//! by byte, and a `usize` write followed by a store through the owner itself.
//!
//! COPY CHAIN AND OPERAND (review of fix/chc-lost-writes round 6,
//! 2026-09-27, findings 1 and 3). The escape check covered only the FINAL
//! owner, while `pointer_field_value_source` follows copies of the owner to
//! the aggregate (`let h2 = h;`) and returns the aggregate's operand. A copy
//! carries the bytes the original owner held when it was copied, and the
//! operand local can itself be rewritten before the aggregate is built (a
//! `usize` store through `addr_of_mut!(a)`, `mem::swap`, a byte copy, a
//! transmuted byte array). The safe rows `safe_copy_owner_after_untyped`,
//! `safe_source_local_rewritten`, `safe_source_swapped` and
//! `safe_source_rewritten_shared_owner_ref` were certified Genuine on the
//! round-6 bundle (main answered SUCCESSFUL by ignoring the rewrite), and every
//! bug row from `bug_copy_owner_after_untyped` on was a clean missed bug on
//! main and on the branch: the direct provenance lanes trust a pointer
//! local's single definition whatever rewrites its bytes. Now every owner on
//! the copy chain and every local on the operand's copy chain must pass the
//! escape check, and the untyped-view net
//! (stmt/codegen_stmt_store/untyped_view_scan.rs) fails closed any block that
//! can rewrite pointer-carrying bytes without a typed pointer store. Every bug
//! row fails without a certificate; the safe rows are known-red false
//! failures.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s pointer_field_value_edge_dual.rs

struct HM<'a> {
    n: u32,
    p: &'a mut u32,
}
struct HR {
    n: u32,
    p: *mut u32,
}
#[derive(Clone, Copy)]
struct HC {
    n: u32,
    p: *mut u32,
}
#[derive(Clone, Copy)]
union UP {
    p: *mut u32,
    a: usize,
}
struct Outer<'a> {
    k: u8,
    h: HM<'a>,
}
#[inline(never)]
fn hm_store(h: &mut HM) {
    *h.p = 7;
}
#[inline(never)]
fn set(p: &mut u32) {
    *p = 7;
}

#[kani::proof]
fn bug_heap_direct() {
    let mut bx: Box<u32> = Box::new(kani::any());
    kani::assume(*bx != 7);
    let mut h = HM { n: 0, p: &mut *bx };
    let r = &mut h;
    *r.p = 7;
    drop(h);
    assert!(*bx != 7);
}

#[kani::proof]
fn safe_heap_direct() {
    let mut bx: Box<u32> = Box::new(kani::any());
    let mut h = HM { n: 0, p: &mut *bx };
    let r = &mut h;
    *r.p = 7;
    drop(h);
    assert!(*bx == 7);
}

#[kani::proof]
fn bug_heap_helper() {
    let mut bx: Box<u32> = Box::new(kani::any());
    kani::assume(*bx != 7);
    let mut h = HM { n: 0, p: &mut *bx };
    hm_store(&mut h);
    assert!(h.n == 0);
    drop(h);
    assert!(*bx != 7);
}

#[kani::proof]
fn safe_heap_helper() {
    let mut bx: Box<u32> = Box::new(kani::any());
    let mut h = HM { n: 0, p: &mut *bx };
    hm_store(&mut h);
    drop(h);
    assert!(*bx == 7);
}

// The pointer field must keep pointing at the referent after the store.
#[kani::proof]
fn safe_heap_helper_slot_kept() {
    let mut bx: Box<u32> = Box::new(kani::any());
    let mut h = HM { n: 0, p: &mut *bx };
    hm_store(&mut h);
    assert!(*h.p == 7);
}

#[kani::proof]
fn bug_stack_helper() {
    let mut x: u32 = kani::any();
    kani::assume(x != 7);
    let mut h = HM { n: 0, p: &mut x };
    hm_store(&mut h);
    drop(h);
    assert!(x != 7);
}

#[kani::proof]
fn safe_stack_helper() {
    let mut x: u32 = kani::any();
    let mut h = HM { n: 0, p: &mut x };
    hm_store(&mut h);
    drop(h);
    assert!(x == 7);
}

#[kani::proof]
fn bug_heap_raw_field() {
    let mut bx: Box<u32> = Box::new(kani::any());
    kani::assume(*bx != 7);
    let mut h = HR { n: 0, p: &mut *bx as *mut u32 };
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*bx != 7);
}

#[kani::proof]
fn safe_heap_raw_field() {
    let mut bx: Box<u32> = Box::new(kani::any());
    let mut h = HR { n: 0, p: &mut *bx as *mut u32 };
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*bx == 7);
}

#[kani::proof]
fn bug_heap_reborrow_helper() {
    let mut bx: Box<u32> = Box::new(kani::any());
    kani::assume(*bx != 7);
    let mut h = HM { n: 0, p: &mut *bx };
    let r = &mut h;
    set(r.p);
    assert!(*bx != 7);
}

#[kani::proof]
fn safe_heap_reborrow_helper() {
    let mut bx: Box<u32> = Box::new(kani::any());
    let mut h = HM { n: 0, p: &mut *bx };
    let r = &mut h;
    set(r.p);
    assert!(*bx == 7);
}

#[kani::proof]
fn bug_heap_nested() {
    let mut bx: Box<u32> = Box::new(kani::any());
    kani::assume(*bx != 7);
    let mut o = Outer { k: 1, h: HM { n: 0, p: &mut *bx } };
    let r = &mut o;
    *r.h.p = 7;
    assert!(*bx != 7);
}

#[kani::proof]
fn safe_heap_nested() {
    let mut bx: Box<u32> = Box::new(kani::any());
    let mut o = Outer { k: 1, h: HM { n: 0, p: &mut *bx } };
    let r = &mut o;
    *r.h.p = 7;
    assert!(*bx == 7);
}

#[kani::proof]
fn bug_heap_closure() {
    let mut bx: Box<u32> = Box::new(kani::any());
    kani::assume(*bx != 7);
    let mut h = HM { n: 0, p: &mut *bx };
    let mut f = || {
        *h.p = 7;
    };
    f();
    assert!(*bx != 7);
}

#[kani::proof]
fn safe_heap_closure() {
    let mut bx: Box<u32> = Box::new(kani::any());
    let mut h = HM { n: 0, p: &mut *bx };
    let mut f = || {
        *h.p = 7;
    };
    f();
    assert!(*bx == 7);
}

// A pointer field rebound by a store that is not a pointer store.
#[kani::proof]
fn bug_usize_write_into_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut h = HC { n: 0, p: &mut *bx };
    unsafe {
        *(std::ptr::addr_of_mut!(h.p) as *mut usize) = yp as usize;
    }
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_usize_write_into_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut h = HC { n: 0, p: &mut *bx };
    unsafe {
        *(std::ptr::addr_of_mut!(h.p) as *mut usize) = yp as usize;
    }
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*bx == 0);
}

// The owner overwritten by a byte copy of another aggregate.
#[kani::proof]
fn bug_copy_whole_over_owner() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let h2 = HC { n: 1, p: &mut *y };
    let mut h = HC { n: 0, p: &mut *bx };
    unsafe {
        std::ptr::copy_nonoverlapping(&h2 as *const HC, &mut h as *mut HC, 1);
    }
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_copy_whole_over_owner() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let h2 = HC { n: 1, p: &mut *y };
    let mut h = HC { n: 0, p: &mut *bx };
    unsafe {
        std::ptr::copy_nonoverlapping(&h2 as *const HC, &mut h as *mut HC, 1);
    }
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*bx == 0);
}

// The pointer field rebound through a pointer cast from a SHARED borrow.
#[kani::proof]
fn bug_shared_cast_write_into_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut h = HC { n: 0, p: &mut *bx };
    let hp = &h as *const HC as *mut HC;
    unsafe {
        *(std::ptr::addr_of_mut!((*hp).p) as *mut usize) = yp as usize;
    }
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_shared_cast_write_into_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut h = HC { n: 0, p: &mut *bx };
    let hp = &h as *const HC as *mut HC;
    unsafe {
        *(std::ptr::addr_of_mut!((*hp).p) as *mut usize) = yp as usize;
    }
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*bx == 0);
}

// A union owner: another field's store rewrites the pointer field.
#[kani::proof]
fn bug_union_other_field_rebinds() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut u = UP { p: &mut *bx };
    u.a = yp as usize;
    let r = &mut u;
    unsafe {
        *r.p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_union_other_field_rebinds() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut u = UP { p: &mut *bx };
    u.a = yp as usize;
    let r = &mut u;
    unsafe {
        *r.p = 7;
    }
    assert!(*bx == 0);
}

// Further rebinding writers (review of fix/chc-lost-writes, 2026-09-27,
// lostwrite-review/src/b3 and b4): a byte copy of a pointer into the field, a
// whole-owner store through a raw pointer, the field rewritten byte by byte,
// and a usize write with the store through the owner itself.
#[kani::proof]
fn bug_copy_pointer_into_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut h = HC { n: 0, p: &mut *bx };
    unsafe {
        std::ptr::copy_nonoverlapping(&yp as *const *mut u32, std::ptr::addr_of_mut!(h.p), 1);
    }
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_copy_pointer_into_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut h = HC { n: 0, p: &mut *bx };
    unsafe {
        std::ptr::copy_nonoverlapping(&yp as *const *mut u32, std::ptr::addr_of_mut!(h.p), 1);
    }
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_whole_store_through_raw_owner() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let h2 = HC { n: 1, p: &mut *y };
    let mut h = HC { n: 0, p: &mut *bx };
    let ph: *mut HC = &mut h;
    unsafe {
        *ph = h2;
    }
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_whole_store_through_raw_owner() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let h2 = HC { n: 1, p: &mut *y };
    let mut h = HC { n: 0, p: &mut *bx };
    let ph: *mut HC = &mut h;
    unsafe {
        *ph = h2;
    }
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_bytes_write_into_field() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut h = HC { n: 0, p: &mut *bx };
    let bytes = (yp as usize).to_ne_bytes();
    let dst = std::ptr::addr_of_mut!(h.p) as *mut u8;
    let mut i = 0;
    while i < 8 {
        unsafe {
            *dst.add(i) = bytes[i];
        }
        i += 1;
    }
    let r = &mut h;
    unsafe {
        *r.p = 7;
    }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_usize_write_no_reborrow() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut h = HC { n: 0, p: &mut *bx };
    unsafe {
        *(std::ptr::addr_of_mut!(h.p) as *mut usize) = yp as usize;
    }
    unsafe {
        *h.p = 7;
    }
    assert!(*bx == 0);
}

// --- copy chain and operand (review round 6) ------------------------------

#[kani::proof]
fn bug_copy_owner_after_untyped() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut h = HC { n: 0, p: &mut *bx };
    unsafe { *(std::ptr::addr_of_mut!(h.p) as *mut usize) = yp as usize; }
    let mut h2 = h;
    let r = &mut h2;
    unsafe { *r.p = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_copy_owner_after_untyped() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut h = HC { n: 0, p: &mut *bx };
    unsafe { *(std::ptr::addr_of_mut!(h.p) as *mut usize) = yp as usize; }
    let mut h2 = h;
    let r = &mut h2;
    unsafe { *r.p = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_copy_owner_after_memcpy() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let hy = HC { n: 1, p: &mut *y };
    let mut h = HC { n: 0, p: &mut *bx };
    unsafe { std::ptr::copy_nonoverlapping(&hy as *const HC, &mut h as *mut HC, 1); }
    let mut h2 = h;
    let r = &mut h2;
    unsafe { *r.p = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_copy_owner_after_memcpy() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let hy = HC { n: 1, p: &mut *y };
    let mut h = HC { n: 0, p: &mut *bx };
    unsafe { std::ptr::copy_nonoverlapping(&hy as *const HC, &mut h as *mut HC, 1); }
    let mut h2 = h;
    let r = &mut h2;
    unsafe { *r.p = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_copy_owner_after_untyped_stack() {
    let mut x: u32 = 0;
    let mut z: u32 = 0;
    let zp: *mut u32 = &mut z;
    let mut h = HC { n: 0, p: &mut x };
    unsafe { *(std::ptr::addr_of_mut!(h.p) as *mut usize) = zp as usize; }
    let mut h2 = h;
    let r = &mut h2;
    unsafe { *r.p = 7; }
    assert!(z != 7);
}

#[kani::proof]
fn safe_copy_owner_after_untyped_stack() {
    let mut x: u32 = 0;
    let mut z: u32 = 0;
    let zp: *mut u32 = &mut z;
    let mut h = HC { n: 0, p: &mut x };
    unsafe { *(std::ptr::addr_of_mut!(h.p) as *mut usize) = zp as usize; }
    let mut h2 = h;
    let r = &mut h2;
    unsafe { *r.p = 7; }
    assert!(x == 0);
}

#[kani::proof]
fn bug_source_local_rewritten() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    unsafe { *(std::ptr::addr_of_mut!(a) as *mut usize) = yp as usize; }
    let mut h = HC { n: 0, p: a };
    let r = &mut h;
    unsafe { *r.p = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_source_local_rewritten() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    unsafe { *(std::ptr::addr_of_mut!(a) as *mut usize) = yp as usize; }
    let mut h = HC { n: 0, p: a };
    let r = &mut h;
    unsafe { *r.p = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_source_local_memcpy() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    unsafe { std::ptr::copy_nonoverlapping(&yp as *const *mut u32, &mut a as *mut *mut u32, 1); }
    let mut h = HC { n: 0, p: a };
    let r = &mut h;
    unsafe { *r.p = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_source_local_memcpy() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    unsafe { std::ptr::copy_nonoverlapping(&yp as *const *mut u32, &mut a as *mut *mut u32, 1); }
    let mut h = HC { n: 0, p: a };
    let r = &mut h;
    unsafe { *r.p = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_source_swapped() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let mut yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    core::mem::swap(&mut a, &mut yp);
    let mut h = HC { n: 0, p: a };
    let r = &mut h;
    unsafe { *r.p = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_source_swapped() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let mut yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    core::mem::swap(&mut a, &mut yp);
    let mut h = HC { n: 0, p: a };
    let r = &mut h;
    unsafe { *r.p = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_source_rewritten_shared_owner_ref() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    unsafe { *(std::ptr::addr_of_mut!(a) as *mut usize) = yp as usize; }
    let h = HC { n: 0, p: a };
    let r = &h;
    unsafe { *r.p = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_source_rewritten_shared_owner_ref() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    unsafe { *(std::ptr::addr_of_mut!(a) as *mut usize) = yp as usize; }
    let h = HC { n: 0, p: a };
    let r = &h;
    unsafe { *r.p = 7; }
    assert!(*bx == 0);
}

#[kani::proof]
fn bug_source_zeroed_null_deref() {
    let mut bx: Box<u32> = Box::new(0);
    let mut a: *mut u32 = &mut *bx;
    unsafe { core::ptr::write_bytes(&mut a as *mut *mut u32, 0, 1); }
    let mut h = HC { n: 0, p: a };
    let r = &mut h;
    unsafe { *r.p = 7; }
}

#[kani::proof]
fn bug_source_transmuted_from_usize() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let pa = std::ptr::addr_of_mut!(a) as *mut [u8; 8];
    unsafe { *pa = core::mem::transmute::<usize, [u8; 8]>(yp as usize); }
    let mut h = HC { n: 0, p: a };
    let r = &mut h;
    unsafe { *r.p = 7; }
    assert!(*y != 7);
}

#[kani::proof]
fn safe_source_transmuted_from_usize() {
    let mut bx: Box<u32> = Box::new(0);
    let mut y: Box<u32> = Box::new(0);
    let yp: *mut u32 = &mut *y;
    let mut a: *mut u32 = &mut *bx;
    let pa = std::ptr::addr_of_mut!(a) as *mut [u8; 8];
    unsafe { *pa = core::mem::transmute::<usize, [u8; 8]>(yp as usize); }
    let mut h = HC { n: 0, p: a };
    let r = &mut h;
    unsafe { *r.p = 7; }
    assert!(*bx == 0);
}
