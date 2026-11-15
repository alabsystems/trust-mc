// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: `&mut [T]` / `&[T]` carried in a struct field, an `Option`, an
// array of slices, a `Vec` (deref, `as_mut_slice`, `iter_mut`), a `Box<[T]>`
// and a 2-D array reference — measured and stored through.
//
// Written by the adversarial review of m3/soundness-fixes-2 (2026-09-12) around
// 212720222 (a reborrow of a wide pointer keeps its metadata) and edec8fd8a
// (a store at an index through `&mut [T; N]` / `&mut [T]` reaches the
// referent): the metadata and the store must survive every carrier.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED; never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

struct W<'x> {
    s: &'x mut [u8],
}

#[kani::proof]
fn vec_deref_mut_store_safe() {
    let mut v = vec![1u8, 2];
    {
        let s: &mut [u8] = &mut v;
        s[0] = 9;
    }
    assert!(v[0] == 9 && v[1] == 2);
}

#[kani::proof]
fn vec_deref_mut_store_must_fail() {
    let mut v = vec![1u8, 2];
    {
        let s: &mut [u8] = &mut v;
        s[0] = 9;
    }
    assert!(v[0] == 1);
}

#[kani::proof]
fn vec_as_mut_slice_store_safe() {
    let mut v = vec![1u8, 2];
    v.as_mut_slice()[0] = 9;
    assert!(v[0] == 9 && v[1] == 2);
}

#[kani::proof]
fn vec_as_mut_slice_store_must_fail() {
    let mut v = vec![1u8, 2];
    v.as_mut_slice()[0] = 9;
    assert!(v[0] == 1);
}

#[kani::proof]
fn vec_iter_mut_store_safe() {
    let mut v = vec![1u8, 2];
    for x in v.iter_mut() {
        *x = 0;
    }
    assert!(v[0] == 0 && v[1] == 0);
}

#[kani::proof]
fn vec_iter_mut_store_must_fail() {
    let mut v = vec![1u8, 2];
    for x in v.iter_mut() {
        *x = 0;
    }
    assert!(v[1] == 2);
}

#[kani::proof]
fn boxed_slice_store_safe() {
    let mut b: Box<[u8]> = vec![1u8, 2].into_boxed_slice();
    b[0] = 9;
    assert!(b[0] == 9 && b[1] == 2 && b.len() == 2);
}

#[kani::proof]
fn boxed_slice_store_must_fail() {
    let mut b: Box<[u8]> = vec![1u8, 2].into_boxed_slice();
    b[0] = 9;
    assert!(b[0] == 1);
}

#[kani::proof]
fn grid_ref_store_safe() {
    let mut g = [[0u8; 2]; 2];
    {
        let r: &mut [[u8; 2]; 2] = &mut g;
        r[1][0] = 9;
    }
    assert!(g[1][0] == 9 && g[0][0] == 0 && g[1][1] == 0);
}

#[kani::proof]
fn grid_ref_store_must_fail() {
    let mut g = [[0u8; 2]; 2];
    {
        let r: &mut [[u8; 2]; 2] = &mut g;
        r[1][0] = 9;
    }
    assert!(g[1][0] == 0);
}

#[kani::proof]
fn slice_oob_symbolic_store_must_fail() {
    let mut a = [1u8; 4];
    let i: usize = kani::any();
    kani::assume(i < 5);
    let s: &mut [u8] = &mut a;
    s[i] = 9;
}

#[kani::proof]
fn wide_in_struct_len_safe() {
    let mut a = [1u8, 2];
    let w = W { s: &mut a };
    assert!(w.s.len() == 2 && w.s[1] == 2);
}

#[kani::proof]
fn wide_in_struct_len_must_fail() {
    let mut a = [1u8, 2];
    let w = W { s: &mut a };
    assert!(w.s.len() == 3);
}

#[kani::proof]
fn wide_in_struct_store_safe() {
    let mut a = [1u8, 2];
    {
        let mut w = W { s: &mut a };
        w.s[0] = 9;
    }
    assert!(a[0] == 9 && a[1] == 2);
}

#[kani::proof]
fn wide_in_struct_store_must_fail() {
    let mut a = [1u8, 2];
    {
        let mut w = W { s: &mut a };
        w.s[0] = 9;
    }
    assert!(a[0] == 1);
}

#[kani::proof]
fn option_wide_len_safe() {
    let a = [1u8, 2];
    let o: Option<&[u8]> = Some(&a);
    if let Some(s) = o {
        assert!(s.len() == 2 && s[0] == 1);
    }
}

#[kani::proof]
fn option_wide_len_must_fail() {
    let a = [1u8, 2];
    let o: Option<&[u8]> = Some(&a);
    if let Some(s) = o {
        assert!(s.len() == 3);
    }
}

#[kani::proof]
fn array_of_slices_len_safe() {
    let x = [1u8, 2];
    let y = [3u8, 4, 5];
    let parts: [&[u8]; 2] = [&x, &y];
    assert!(parts[0].len() == 2 && parts[1].len() == 3 && parts[1][2] == 5);
}

#[kani::proof]
fn array_of_slices_len_must_fail() {
    let x = [1u8, 2];
    let y = [3u8, 4, 5];
    let parts: [&[u8]; 2] = [&x, &y];
    assert!(parts[1].len() == 2);
}

#[kani::proof]
fn wide_param_in_struct_store_safe() {
    fn set_first(w: &mut W<'_>) {
        w.s[0] = 9;
    }
    let mut a = [1u8, 2];
    {
        let mut w = W { s: &mut a };
        set_first(&mut w);
    }
    assert!(a[0] == 9);
}

#[kani::proof]
fn wide_param_in_struct_store_must_fail() {
    fn set_first(w: &mut W<'_>) {
        w.s[0] = 9;
    }
    let mut a = [1u8, 2];
    {
        let mut w = W { s: &mut a };
        set_first(&mut w);
    }
    assert!(a[0] == 1);
}

#[kani::proof]
fn vec_of_slices_len_safe() {
    let x = [1u8, 2];
    let y = [3u8, 4, 5];
    let parts: Vec<&[u8]> = vec![&x, &y];
    assert!(parts[1].len() == 3 && parts[0][1] == 2);
}

#[kani::proof]
fn vec_of_slices_len_must_fail() {
    let x = [1u8, 2];
    let y = [3u8, 4, 5];
    let parts: Vec<&[u8]> = vec![&x, &y];
    assert!(parts[1].len() == 2);
}

// --- further carriers, added by the third adversarial review (2026-09-14) ---
//
// Every one of these is a SAFE program that was FAILED [AY:CTREX_CAT:Genuine]:
// an ENUM PAYLOAD and a NESTED Option in chc, a `dyn` carrier in chc, and the
// same value beside a `dyn` in a tuple in bmc. All four are red on origin/main
// too. The family is wider than the two rows this pack used to carry.

enum E<'a> {
    A(&'a [u8]),
    B(u8),
}

trait Get {
    fn get0(&self) -> u8;
}

struct G<'a>(&'a [u8]);

impl<'a> Get for G<'a> {
    fn get0(&self) -> u8 {
        self.0[0]
    }
}

#[kani::proof]
fn slice_in_enum_payload_safe() {
    let a = [1u8, 2, 3];
    let e = E::A(&a[..]);
    match e {
        E::A(s) => assert!(s.len() == 3 && s[0] == 1),
        E::B(_) => assert!(false),
    }
}

#[kani::proof]
fn slice_in_enum_payload_must_fail() {
    let a = [1u8, 2, 3];
    let e = E::A(&a[..]);
    match e {
        E::A(s) => assert!(s.len() == 2),
        E::B(_) => {}
    }
}

#[kani::proof]
fn slice_in_nested_option_safe() {
    let a = [1u8, 2, 3];
    let o: Option<Option<&[u8]>> = Some(Some(&a[..]));
    let s = o.unwrap().unwrap();
    assert!(s.len() == 3 && s[0] == 1);
}

#[kani::proof]
fn slice_in_nested_option_must_fail() {
    let a = [1u8, 2, 3];
    let o: Option<Option<&[u8]>> = Some(Some(&a[..]));
    let s = o.unwrap().unwrap();
    assert!(s.len() == 2);
}

#[kani::proof]
fn slice_behind_dyn_safe() {
    let a = [1u8, 2, 3];
    let g = G(&a[..]);
    let d: &dyn Get = &g;
    assert!(d.get0() == 1);
}

#[kani::proof]
fn slice_behind_dyn_must_fail() {
    let a = [1u8, 2, 3];
    let g = G(&a[..]);
    let d: &dyn Get = &g;
    assert!(d.get0() == 2);
}

#[kani::proof]
fn dyn_in_tuple_safe() {
    let a = [1u8, 2, 3];
    let g = G(&a[..]);
    let t: (u8, &dyn Get) = (5, &g);
    assert!(t.1.get0() == 1 && t.0 == 5);
}

#[kani::proof]
fn dyn_in_tuple_must_fail() {
    let a = [1u8, 2, 3];
    let g = G(&a[..]);
    let t: (u8, &dyn Get) = (5, &g);
    assert!(t.1.get0() == 2);
}
