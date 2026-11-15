// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a store at an index through a `&mut [T; N]` reference — direct, with a
// symbolic index, read back through the same reference, inside a callee, into a struct
// field's array, and through a `Box<[T; N]>`.
//
// Found while pinning the slice-view fixes of m3/soundness-fixes-2 (2026-09-12). In
// the BMC lane `(*r)[i] = v` reached no store handler: the generic path bound a
// register named `r_deref_idx_by_i` and the referent never changed. Measured on
// bundle 31793ccc3 (main) and e18dbf853 (BMC): every *_must_fail below except the
// Box shape verified SUCCESSFUL (a false proof of `lhs[0] == 1` after `r[0] = 9`,
// even read back through `r` itself), and every *_safe twin FAILED with
// [AY:CTREX_CAT:Genuine]; the CHC lane was exact. The store now reaches the
// referent (codegen_assign_ref_deref.rs, `try_codegen_assign_ref_deref_index`).
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample
#[kani::proof]
fn array_ref_write_must_fail() {
    let mut lhs = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut lhs;
        r[0] = 9;
    }
    assert!(lhs[0] == 1);
}

#[kani::proof]
fn array_ref_write_safe() {
    let mut lhs = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut lhs;
        r[0] = 9;
    }
    assert!(lhs[0] == 9 && lhs[1] == 2);
}

#[kani::proof]
fn array_ref_symbolic_write_must_fail() {
    let mut lhs = [1u8, 2, 3, 4];
    let i: usize = kani::any();
    kani::assume(i < 4);
    {
        let r: &mut [u8; 4] = &mut lhs;
        r[i] = 9;
    }
    assert!(lhs[0] == 1);
}

#[kani::proof]
fn array_ref_symbolic_write_safe() {
    let mut lhs = [1u8, 2, 3, 4];
    let i: usize = kani::any();
    kani::assume(i < 4);
    {
        let r: &mut [u8; 4] = &mut lhs;
        r[i] = 9;
    }
    assert!(lhs[i] == 9);
}

#[kani::proof]
fn array_ref_write_then_read_through_ref_safe() {
    let mut lhs = [1u8, 2];
    let r: &mut [u8; 2] = &mut lhs;
    r[0] = 9;
    assert!(r[0] == 9 && r[1] == 2);
}

#[kani::proof]
fn array_ref_write_then_read_through_ref_must_fail() {
    let mut lhs = [1u8, 2];
    let r: &mut [u8; 2] = &mut lhs;
    r[0] = 9;
    assert!(r[0] == 1);
}

#[kani::proof]
fn array_ref_param_write_must_fail() {
    fn set(r: &mut [u8; 2]) {
        r[1] = 7;
    }
    let mut lhs = [1u8, 2];
    set(&mut lhs);
    assert!(lhs[1] == 2);
}

#[kani::proof]
fn array_ref_param_write_safe() {
    fn set(r: &mut [u8; 2]) {
        r[1] = 7;
    }
    let mut lhs = [1u8, 2];
    set(&mut lhs);
    assert!(lhs[1] == 7);
}

#[kani::proof]
fn box_array_write_must_fail() {
    let mut b: Box<[u8; 2]> = Box::new([1u8, 2]);
    b[0] = 9;
    assert!(b[0] == 1);
}

#[kani::proof]
fn box_array_write_safe() {
    let mut b: Box<[u8; 2]> = Box::new([1u8, 2]);
    b[0] = 9;
    assert!(b[0] == 9);
}

#[kani::proof]
fn struct_field_array_ref_write_must_fail() {
    struct S {
        buf: [u8; 2],
    }
    let mut s = S { buf: [1, 2] };
    {
        let r: &mut [u8; 2] = &mut s.buf;
        r[0] = 9;
    }
    assert!(s.buf[0] == 1);
}

#[kani::proof]
fn struct_field_array_ref_write_safe() {
    struct S {
        buf: [u8; 2],
    }
    let mut s = S { buf: [1, 2] };
    {
        let r: &mut [u8; 2] = &mut s.buf;
        r[0] = 9;
    }
    assert!(s.buf[0] == 9);
}
