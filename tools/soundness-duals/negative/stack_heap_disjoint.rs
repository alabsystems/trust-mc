// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: address-taken stack objects and heap objects never share bytes.
//
// Found while fixing negative/alloc_provenance_stores.rs (2026-09-12). The BMC
// byte-memory model gave heap objects concrete regions but an address-taken
// stack local only a symbolic address that nothing kept off heap regions or
// other stack objects. Inlining Box::into_raw stores a ManuallyDrop slot to
// memory, and the solver placed it on a box payload: every safe harness below
// that reads a box after a second allocation or a stack borrow FAILED with
// CTREX_CAT:Genuine on bundle 31793ccc3, and ptr::eq held for two distinct
// locals. The CHC lane's `stack_then_box_safe` also FAILED Genuine there.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

#[kani::proof]
fn two_boxes_safe() {
    let a = Box::into_raw(Box::new(1u8));
    let b = Box::into_raw(Box::new(2u8));
    unsafe {
        *b = 9;
        assert!(*a == 1 && *b == 9);
    }
}

#[kani::proof]
fn two_boxes_must_fail() {
    let a = Box::into_raw(Box::new(1u8));
    let b = Box::into_raw(Box::new(2u8));
    unsafe {
        *b = 9;
        assert!(*a == 9);
    }
}

#[kani::proof]
fn pair_no_store_safe() {
    let pair = (Box::into_raw(Box::new(1u8)), Box::into_raw(Box::new(2u8)));
    unsafe { assert!(*pair.0 == 1 && *pair.1 == 2) }
}

#[kani::proof]
fn pair_no_store_must_fail() {
    let pair = (Box::into_raw(Box::new(1u8)), Box::into_raw(Box::new(2u8)));
    unsafe { assert!(*pair.0 == 2) }
}

#[kani::proof]
fn loaded_no_store_safe() {
    let inner = Box::into_raw(Box::new(1u8));
    let outer = Box::into_raw(Box::new(inner));
    unsafe {
        let d = *outer;
        assert!(*d == 1 && d == inner);
    }
}

#[kani::proof]
fn loaded_no_store_must_fail() {
    let inner = Box::into_raw(Box::new(1u8));
    let outer = Box::into_raw(Box::new(inner));
    unsafe {
        let d = *outer;
        assert!(*d == 2);
    }
}

#[kani::proof]
fn two_stack_ptrs_safe() {
    let mut a = 1u8;
    let mut b = 2u8;
    let pa = &mut a as *mut u8;
    let pb = &mut b as *mut u8;
    unsafe {
        *pb = 9;
        assert!(*pa == 1 && *pb == 9);
    }
}

#[kani::proof]
fn two_stack_ptrs_must_fail() {
    let mut a = 1u8;
    let mut b = 2u8;
    let pa = &mut a as *mut u8;
    let pb = &mut b as *mut u8;
    unsafe {
        *pb = 9;
        assert!(*pa == 9);
    }
}

#[kani::proof]
fn stack_then_box_safe() {
    let mut a = 1u8;
    let pa = &mut a as *mut u8;
    let b = Box::into_raw(Box::new(2u8));
    unsafe {
        *b = 9;
        assert!(*pa == 1 && *b == 9);
    }
}

#[kani::proof]
fn stack_then_box_must_fail() {
    let mut a = 1u8;
    let pa = &mut a as *mut u8;
    let b = Box::into_raw(Box::new(2u8));
    unsafe {
        *b = 9;
        assert!(*pa == 9);
    }
}

#[kani::proof]
fn box_then_stack_safe() {
    let b = Box::into_raw(Box::new(2u8));
    let mut a = 1u8;
    let pa = &mut a as *mut u8;
    unsafe {
        *pa = 7;
        assert!(*b == 2 && *pa == 7);
    }
}

#[kani::proof]
fn box_then_stack_must_fail() {
    let b = Box::into_raw(Box::new(2u8));
    let mut a = 1u8;
    let pa = &mut a as *mut u8;
    unsafe {
        *pa = 7;
        assert!(*b == 7);
    }
}

#[kani::proof]
fn distinct_locals_not_ptr_eq_safe() {
    let a = 1u8;
    let b = 1u8;
    assert!(!core::ptr::eq(&a, &b));
}

#[kani::proof]
fn same_local_ptr_eq_must_fail() {
    let a = 1u8;
    assert!(!core::ptr::eq(&a, &a));
}
