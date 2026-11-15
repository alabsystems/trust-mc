// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Regression guard for 7427e34c5 (canonical_zst_expr_for_sort): a zero-sized
// enum's one value is its inhabited variant, taken from rustc's
// `VariantsShape::Single { index }`, which is not always variant 0. If the
// encoding picked variant 0 (`A(Infallible)`) where the layout says `B`, every
// `if let ..B` below would become unreachable and a real failure would be
// missed. Covers the value read directly, through a reference, a Box, a
// generic parameter, `Result<Infallible, ()>` (variant 1), `Result<(),
// Infallible>` (variant 0), a struct field and an `Option` payload.
//
// Oracles, each confirmed with Kani 0.67.0 (kani-src at the corpus rev): every
// bug_* FAILED, safe_iflet_b_direct SUCCESSFUL.

use std::convert::Infallible;

#[allow(dead_code)]
enum E {
    A(Infallible),
    B,
}

enum Outer {
    X(E),
    Y(u32),
}

fn mk(flag: bool, v: u32) -> Outer {
    if flag { Outer::X(E::B) } else { Outer::Y(v) }
}

#[kani::proof]
fn bug_iflet_b_direct() {
    let o = mk(kani::any(), kani::any());
    if let Outer::X(e) = o {
        if let E::B = e {
            assert!(false); // reachable
        }
    }
}

#[kani::proof]
fn bug_iflet_b_ref() {
    let o = mk(kani::any(), kani::any());
    let r = &o;
    if let Outer::X(E::B) = r {
        assert!(false); // reachable
    }
}

#[kani::proof]
fn bug_iflet_b_boxed() {
    let o = Box::new(mk(kani::any(), kani::any()));
    if let Outer::X(E::B) = *o {
        assert!(false); // reachable
    }
}

#[allow(dead_code)]
enum G<T> {
    A(T),
    B,
}

enum OuterG {
    X(G<Infallible>),
    Y(u8),
}

#[kani::proof]
fn bug_generic_zst_enum() {
    let flag: bool = kani::any();
    let o = if flag { OuterG::X(G::B) } else { OuterG::Y(1) };
    if let OuterG::X(G::B) = o {
        assert!(false); // reachable
    }
}

enum Holder {
    R(Result<Infallible, ()>),
    N(u16),
}

#[kani::proof]
fn bug_result_infallible_err_iflet() {
    let flag: bool = kani::any();
    let h = if flag { Holder::R(Err(())) } else { Holder::N(3) };
    if let Holder::R(Err(())) = h {
        assert!(false); // reachable
    }
}

enum Holder2 {
    R(Result<(), Infallible>),
    N(u16),
}

#[kani::proof]
fn bug_result_unit_ok_iflet() {
    let flag: bool = kani::any();
    let h = if flag { Holder2::R(Ok(())) } else { Holder2::N(3) };
    if let Holder2::R(Ok(())) = h {
        assert!(false); // reachable
    }
}

// Struct holding a ZST enum next to data.
struct S {
    tag: E,
    x: u32,
}

#[kani::proof]
fn bug_struct_zst_enum_field() {
    let s = S { tag: E::B, x: kani::any() };
    match s.tag {
        E::B => assert!(s.x != 3), // FAILS for x == 3
        E::A(n) => match n {},
    }
}

// ZST enum returned through Option<ZstEnum> (not ZST: 2 values).
fn opt_e(flag: bool) -> Option<E> {
    if flag { Some(E::B) } else { None }
}

#[kani::proof]
fn bug_option_of_zst_enum() {
    if let Some(E::B) = opt_e(kani::any()) {
        assert!(false); // reachable
    }
}

// Option<Infallible> as a struct field: always None.
struct T2 {
    o: Option<Infallible>,
    y: u8,
}

#[kani::proof]
fn bug_option_infallible_field() {
    let t = T2 { o: None, y: kani::any() };
    if t.o.is_none() {
        assert!(t.y != 9); // FAILS for y == 9
    }
}

#[kani::proof]
fn safe_iflet_b_direct() {
    let o = mk(true, 0);
    let mut hit = false;
    if let Outer::X(E::B) = o {
        hit = true;
    }
    assert!(hit);
}
