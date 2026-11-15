// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: stores through pointers whose address carries a field offset,
// pointer arithmetic, a second dereference or a pointer slot, and pointers whose
// allocation a side table could inherit from the wrong local.
//
// Found while fixing negative/box_new_payload.rs (2026-09-12). The CHC lane
// minted the store address `obj ++ 0` from alloc-id side tables that crossed
// value-changing hops (a ref target `(*p).b` at offset 1, a slot borrow, a load
// through a pointer, a field of a two-pointer tuple), and wrote an offset store
// into a Vec only to address memory the model never reads. The BMC lane kept a
// stale pointee binding after `*r = q` with `r = &mut p`, returned the Vec
// model's unlinked buffer pointer from as_mut_ptr, and let a stack slot share
// bytes with a box payload. Measured on bundle 31793ccc3:
//   chc SUCCESSFUL on box_wide_field_ref_store, box_field_ref_callee,
//       box_raw_field_store, vec_add_store, pair_second_store and
//       loaded_ptr_store must-fails; each safe twin plus ptr_slot_store_safe and
//       box_raw_store_in_branch_safe FAILED with CTREX_CAT:Genuine.
//   bmc FAILED with CTREX_CAT:Genuine on ptr_slot_store_safe,
//       vec_add_store_safe, pair_second_store_safe and loaded_ptr_store_safe.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample (SUCCESSFUL or an honestly
//                    demoted FAILED)

#[repr(C)]
struct S {
    a: u8,
    b: u8,
}

#[repr(C)]
struct W {
    x: u32,
    y: u32,
}

fn set_b(p: &mut u8) {
    *p = 9;
}

#[kani::proof]
fn box_wide_field_ref_store_must_fail() {
    let mut w = Box::new(W { x: 1, y: 2 });
    let py = &mut w.y;
    *py = 9;
    // FALSE: the store went to y.
    assert!(w.y == 2);
}

#[kani::proof]
fn box_wide_field_ref_store_safe() {
    let mut w = Box::new(W { x: 1, y: 2 });
    let py = &mut w.y;
    *py = 9;
    assert!(w.y == 9 && w.x == 1);
}

#[kani::proof]
fn box_field_ref_callee_must_fail() {
    let mut s = Box::new(S { a: 1, b: 2 });
    set_b(&mut s.b);
    assert!(s.b == 2);
}

#[kani::proof]
fn box_field_ref_callee_safe() {
    let mut s = Box::new(S { a: 1, b: 2 });
    set_b(&mut s.b);
    assert!(s.b == 9 && s.a == 1);
}

#[kani::proof]
fn box_raw_field_store_must_fail() {
    let p = Box::into_raw(Box::new(S { a: 1, b: 2 }));
    unsafe {
        let pb = &raw mut (*p).b;
        *pb = 9;
        assert!((*p).b == 2);
    }
}

#[kani::proof]
fn box_raw_field_store_safe() {
    let p = Box::into_raw(Box::new(S { a: 1, b: 2 }));
    unsafe {
        let pb = &raw mut (*p).b;
        *pb = 9;
        assert!((*p).b == 9 && (*p).a == 1);
    }
}

#[kani::proof]
fn box_raw_add_store_must_fail() {
    let p = Box::into_raw(Box::new([0u8; 4])) as *mut u8;
    unsafe {
        *p.add(1) = 9;
        assert!(*p.add(1) == 0);
    }
}

#[kani::proof]
fn box_raw_add_base_must_fail() {
    let p = Box::into_raw(Box::new([0u8; 4])) as *mut u8;
    unsafe {
        *p.add(1) = 9;
        // FALSE: the store went to byte 1, not byte 0.
        assert!(*p == 9);
    }
}

#[kani::proof]
fn box_raw_add_store_safe() {
    let p = Box::into_raw(Box::new([0u8; 4])) as *mut u8;
    unsafe {
        *p.add(1) = 9;
        assert!(*p.add(1) == 9 && *p == 0);
    }
}

#[kani::proof]
fn box_add_write_must_fail() {
    let p = Box::into_raw(Box::new([0u8; 4])) as *mut u8;
    unsafe {
        p.add(2).write(7);
        assert!(p.read() == 7);
    }
}

#[kani::proof]
fn box_add_write_safe() {
    let p = Box::into_raw(Box::new([0u8; 4])) as *mut u8;
    unsafe {
        p.add(2).write(7);
        assert!(p.read() == 0 && p.add(2).read() == 7);
    }
}

#[kani::proof]
fn stack_add_store_must_fail() {
    let mut a = [0u8; 4];
    let p = a.as_mut_ptr();
    unsafe {
        *p.add(2) = 7;
    }
    assert!(a[2] == 0);
}

#[kani::proof]
fn stack_add_store_safe() {
    let mut a = [0u8; 4];
    let p = a.as_mut_ptr();
    unsafe {
        *p.add(2) = 7;
    }
    assert!(a[2] == 7 && a[0] == 0);
}

#[kani::proof]
fn vec_add_store_must_fail() {
    let mut v = vec![0u8; 4];
    let p = v.as_mut_ptr();
    unsafe {
        *p.add(3) = 5;
    }
    assert!(v[3] == 0);
}

#[kani::proof]
fn vec_add_store_safe() {
    let mut v = vec![0u8; 4];
    let p = v.as_mut_ptr();
    unsafe {
        *p.add(3) = 5;
    }
    assert!(v[3] == 5 && v[0] == 0);
}

#[kani::proof]
fn rc_get_mut_store_must_fail() {
    let mut r = std::rc::Rc::new(5u8);
    *std::rc::Rc::get_mut(&mut r).unwrap() = 6;
    assert!(*r == 5);
}

#[kani::proof]
fn rc_get_mut_store_safe() {
    let mut r = std::rc::Rc::new(5u8);
    *std::rc::Rc::get_mut(&mut r).unwrap() = 6;
    assert!(*r == 6);
}

#[kani::proof]
fn rc_into_raw_store_must_fail() {
    let r = std::rc::Rc::new(5u64);
    let p = std::rc::Rc::into_raw(r) as *mut u64;
    unsafe {
        *p = 6;
        let back = std::rc::Rc::from_raw(p);
        assert!(*back == 5);
    }
}

#[kani::proof]
fn rc_into_raw_store_safe() {
    let r = std::rc::Rc::new(5u64);
    let p = std::rc::Rc::into_raw(r) as *mut u64;
    unsafe {
        *p = 6;
        let back = std::rc::Rc::from_raw(p);
        assert!(*back == 6);
    }
}

#[kani::proof]
fn ptr_slot_store_must_fail() {
    let b1 = Box::into_raw(Box::new(1u8));
    let b2 = Box::into_raw(Box::new(2u8));
    let mut p = b1;
    let r = &mut p;
    *r = b2;
    // FALSE: p now points to b2.
    unsafe { assert!(*p == 1) }
}

#[kani::proof]
fn ptr_slot_store_safe() {
    let b1 = Box::into_raw(Box::new(1u8));
    let b2 = Box::into_raw(Box::new(2u8));
    let mut p = b1;
    let r = &mut p;
    *r = b2;
    unsafe { assert!(*p == 2 && *b1 == 1) }
}

#[kani::proof]
fn box_ref_deref_store_must_fail() {
    let mut b = Box::new(3u8);
    let rb = &mut b;
    **rb = 4;
    assert!(*b == 3);
}

#[kani::proof]
fn box_ref_deref_store_safe() {
    let mut b = Box::new(3u8);
    let rb = &mut b;
    **rb = 4;
    assert!(*b == 4);
}

#[kani::proof]
fn pair_second_store_must_fail() {
    let pair = (Box::into_raw(Box::new(1u8)), Box::into_raw(Box::new(2u8)));
    unsafe {
        let q = pair.1;
        *q = 9;
        // FALSE: the store went to the second box.
        assert!(*pair.0 == 9);
    }
}

#[kani::proof]
fn pair_second_store_safe() {
    let pair = (Box::into_raw(Box::new(1u8)), Box::into_raw(Box::new(2u8)));
    unsafe {
        let q = pair.1;
        *q = 9;
        assert!(*pair.0 == 1 && *pair.1 == 9);
    }
}

#[kani::proof]
fn loaded_ptr_store_must_fail() {
    let inner = Box::into_raw(Box::new(1u8));
    let outer = Box::into_raw(Box::new(inner));
    unsafe {
        let d = *outer;
        *d = 9;
        // FALSE: d is inner.
        assert!(*inner == 1);
    }
}

#[kani::proof]
fn loaded_ptr_store_safe() {
    let inner = Box::into_raw(Box::new(1u8));
    let outer = Box::into_raw(Box::new(inner));
    unsafe {
        let d = *outer;
        *d = 9;
        assert!(*inner == 9 && *outer == inner);
    }
}

#[kani::proof]
fn raw_store_in_branch_must_fail() {
    let mut x: u8 = 0;
    let p = &mut x as *mut u8;
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 }
    }
    unsafe { assert!(*p == 1) }
}

#[kani::proof]
fn raw_store_in_branch_safe() {
    let mut x: u8 = 0;
    let p = &mut x as *mut u8;
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 }
    }
    unsafe { assert!(*p == if c { 1 } else { 0 }) }
}

#[kani::proof]
fn box_raw_store_in_branch_must_fail() {
    let p = Box::into_raw(Box::new(0u8));
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 }
    }
    unsafe { assert!(*p == 1) }
}

#[kani::proof]
fn box_raw_store_in_branch_safe() {
    let p = Box::into_raw(Box::new(0u8));
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 }
    }
    unsafe { assert!(*p == if c { 1 } else { 0 }) }
}
