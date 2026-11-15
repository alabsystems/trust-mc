// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a whole struct stored through a reference or raw pointer reaches the local.
//
// Found while adding negative/branch_memory_stores.rs (2026-09-12). The CHC lane
// flattens a struct local into one state variable per field, but a store of a
// whole struct through `&mut`/`*mut` to that local was encoded against the
// local's single state slot, so the fields never changed: `let r = &mut s;
// *r = S { a: 1, b: 2 }; assert!(s.b == 0)` verified SUCCESSFUL, and every safe
// twin below failed with CTREX_CAT:Genuine, on main 31793ccc3 and on the
// re-land bundle. Stores to a single field were not affected.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

#[derive(Clone, Copy, PartialEq)]
struct Same {
    a: u16,
    b: u16,
}

#[derive(Clone, Copy, PartialEq)]
struct Mixed {
    a: u8,
    b: u16,
}

#[derive(Clone, Copy, PartialEq)]
struct Outer {
    tag: u8,
    inner: Same,
}

#[kani::proof]
fn ref_store_safe() {
    let mut s = Same { a: 0, b: 0 };
    {
        let r = &mut s;
        *r = Same { a: 1, b: 2 };
    }
    assert!(s.a == 1 && s.b == 2);
}

#[kani::proof]
fn ref_store_must_fail() {
    let mut s = Same { a: 0, b: 0 };
    {
        let r = &mut s;
        *r = Same { a: 1, b: 2 };
    }
    assert!(s.b == 0);
}

#[kani::proof]
fn raw_store_read_through_pointer_safe() {
    let mut s = Mixed { a: 0, b: 0 };
    let p = &mut s as *mut Mixed;
    unsafe {
        *p = Mixed { a: 1, b: 2 };
        assert!((*p).b == 2);
    }
}

#[kani::proof]
fn raw_store_read_through_pointer_must_fail() {
    let mut s = Mixed { a: 0, b: 0 };
    let p = &mut s as *mut Mixed;
    unsafe {
        *p = Mixed { a: 1, b: 2 };
        assert!((*p).b == 0);
    }
}

#[kani::proof]
fn raw_store_read_local_safe() {
    let mut s = Mixed { a: 0, b: 0 };
    let p = &mut s as *mut Mixed;
    unsafe { *p = Mixed { a: 1, b: 2 } }
    assert!(s.a == 1 && s.b == 2);
}

#[kani::proof]
fn raw_store_read_local_must_fail() {
    let mut s = Mixed { a: 0, b: 0 };
    let p = &mut s as *mut Mixed;
    unsafe { *p = Mixed { a: 1, b: 2 } }
    assert!(s.a == 0);
}

#[kani::proof]
fn ref_store_in_branch_safe() {
    let mut s = Mixed { a: 0, b: 0 };
    let c: bool = kani::any();
    {
        let r = &mut s;
        if c {
            *r = Mixed { a: 1, b: 2 };
        }
    }
    assert!(s.b == if c { 2 } else { 0 });
}

#[kani::proof]
fn ref_store_in_branch_must_fail() {
    let mut s = Mixed { a: 0, b: 0 };
    let c: bool = kani::any();
    {
        let r = &mut s;
        if c {
            *r = Mixed { a: 1, b: 2 };
        }
    }
    assert!(s.b == 2);
}

#[kani::proof]
fn tuple_store_safe() {
    let mut t = (0u8, 0u16);
    let p = &mut t as *mut (u8, u16);
    unsafe { *p = (1, 2) }
    assert!(t.0 == 1 && t.1 == 2);
}

#[kani::proof]
fn tuple_store_must_fail() {
    let mut t = (0u8, 0u16);
    let p = &mut t as *mut (u8, u16);
    unsafe { *p = (1, 2) }
    assert!(t.1 == 0);
}

#[kani::proof]
fn nested_store_safe() {
    let mut o = Outer { tag: 0, inner: Same { a: 0, b: 0 } };
    {
        let r = &mut o;
        *r = Outer { tag: 3, inner: Same { a: 4, b: 5 } };
    }
    assert!(o.tag == 3 && o.inner.b == 5);
}

#[kani::proof]
fn nested_store_must_fail() {
    let mut o = Outer { tag: 0, inner: Same { a: 0, b: 0 } };
    {
        let r = &mut o;
        *r = Outer { tag: 3, inner: Same { a: 4, b: 5 } };
    }
    assert!(o.inner.b == 0);
}

#[kani::proof]
fn copy_from_other_local_safe() {
    let mut s = Same { a: 0, b: 0 };
    let t = Same { a: 7, b: 8 };
    {
        let r = &mut s;
        *r = t;
    }
    assert!(s.a == 7 && s.b == 8);
}

#[kani::proof]
fn copy_from_other_local_must_fail() {
    let mut s = Same { a: 0, b: 0 };
    let t = Same { a: 7, b: 8 };
    {
        let r = &mut s;
        *r = t;
    }
    assert!(s.b == 0);
}

#[kani::proof]
fn nondet_store_safe() {
    let mut s = Same { a: 0, b: 0 };
    let v = Same { a: kani::any(), b: kani::any() };
    {
        let r = &mut s;
        *r = v;
    }
    assert!(s == v);
}

#[kani::proof]
fn nondet_store_must_fail() {
    let mut s = Same { a: 0, b: 0 };
    let v = Same { a: kani::any(), b: kani::any() };
    {
        let r = &mut s;
        *r = v;
    }
    assert!(s.b == 0);
}
