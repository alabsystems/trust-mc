// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- enums whose discriminant VALUES are not their variant
//! indices (`#[repr(u8)] enum PF { Val(u8) = 7, Nothing = 2 }`), read from a
//! datatype value, a constant, and their memory bytes (review of
//! fix/chc-lost-writes, lostwrite track round 3, findings 1 and 3).
//!
//! A MIR `SwitchInt` on `Discriminant(_)` compares against discriminant values.
//! The Option-like and two-payload discriminant reads returned the variant
//! INDEX, so a value read from a tuple field, a struct field, an array element
//! or an `Option` payload matched no arm and the `otherwise -> unreachable`
//! edge was reachable: certified Genuine on the safe rows once the round-2
//! variant-order sort made the read exact (EncodingGap on main), and missed
//! on `bug_pf_array` / `bug_pf_matches_tuple` on main too. A constant's
//! direct tag was decoded as the variant index (`Perm::A = 1` read as `B`), and
//! a flattened enum's tag byte in memory was `ite(fld0, 1, 0)` whatever the
//! encoding: wrong for an explicit discriminant, for a `Result` (whose `fld0`
//! names `Ok`) and for every niche-encoded enum.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_pf_tuple                 -> SUCCESSFUL
//!   bug_pf_tuple                  -> FAILED ('assertion failed: ok')
//!   safe_pf_struct_field          -> SUCCESSFUL
//!   bug_pf_struct_field           -> FAILED ('assertion failed: ok')
//!   safe_pf_array                 -> SUCCESSFUL
//!   bug_pf_array                  -> FAILED ('assertion failed: ok')
//!   safe_pf_option                -> SUCCESSFUL
//!   bug_pf_option                 -> FAILED ('assertion failed: ok')
//!   safe_pf_matches_tuple         -> SUCCESSFUL
//!   bug_pf_matches_tuple          -> FAILED ('assertion failed: !matches!(d.0, PF::Val(_))')
//!   safe_pf_iflet_tuple           -> SUCCESSFUL
//!   bug_pf_iflet_tuple            -> FAILED ('assertion failed: w == 4')
//!   safe_pf_wild_tuple            -> SUCCESSFUL
//!   bug_pf_wild_tuple             -> FAILED ('assertion failed: w == 4')
//!   safe_pl_tuple                 -> SUCCESSFUL
//!   bug_pl_tuple                  -> FAILED ('assertion failed: ok')
//!   safe_pl_struct_field          -> SUCCESSFUL
//!   safe_twop_tuple               -> SUCCESSFUL
//!   bug_twop_tuple                -> FAILED ('assertion failed: ok')
//!   safe_tag_byte_symbolic        -> SUCCESSFUL
//!   bug_tag_byte_symbolic         -> FAILED ('assertion failed: if c { tag == 0 } else { tag == 1 }')
//!   safe_tag_byte_const           -> SUCCESSFUL
//!   safe_result_err_tag_byte      -> SUCCESSFUL
//!   bug_result_err_tag_byte       -> FAILED ('assertion failed: t == 0')
//!   safe_opt_bool_none_byte       -> SUCCESSFUL
//!   bug_opt_bool_none_byte        -> FAILED ('assertion failed: b == 0')
//!   safe_opt_bool_some_true_byte  -> SUCCESSFUL
//!   bug_opt_bool_some_false_byte  -> FAILED ('assertion failed: b == 1')
//!   safe_opt_nonzero_some_byte    -> SUCCESSFUL
//!   bug_opt_nonzero_some_byte     -> FAILED ('assertion failed: b == 1')
//!   safe_const_perm_a_ref         -> SUCCESSFUL
//!   bug_const_perm_a_ref          -> FAILED ('assertion failed: matches!(*r, Perm::B)')
//!   safe_const_perm_b_ref         -> SUCCESSFUL
//!   bug_const_perm_b_ref          -> FAILED ('assertion failed: !matches!(*r, Perm::B)')
//!   safe_const_disc_ref           -> SUCCESSFUL
//!   bug_const_disc_ref            -> FAILED ('assertion failed: matches!(*r, PF::Nothing)')
//!   safe_const_three_ref          -> SUCCESSFUL
//!   bug_const_three_ref           -> FAILED ('assertion failed: matches!(*r, Three::Y)')
//!
#![allow(unused)]
use std::num::NonZeroU8;

#[derive(Clone, Copy)]
#[repr(u8)]
enum PF {
    Val(u8) = 7,
    Nothing = 2,
}

#[derive(Clone, Copy)]
#[repr(u8)]
enum PL {
    Nothing = 2,
    Val(u8) = 7,
}

#[derive(Clone, Copy)]
#[repr(u8)]
enum TwoP {
    A(u8) = 5,
    B(u16) = 9,
}

#[derive(Clone, Copy)]
#[repr(u8)]
enum Perm {
    A(u8) = 1,
    B = 0,
}

#[derive(Clone, Copy)]
#[repr(u8)]
enum Three {
    X(u8) = 2,
    Y = 0,
    Z(u16) = 1,
}

struct HoldPF {
    x: u8,
    d: PF,
}

const CA: Perm = Perm::A(5);
const CB: Perm = Perm::B;
const CD: PF = PF::Val(3);
const TX: Three = Three::X(4);

#[inline(never)]
fn mk_pf(c: bool, v: u8) -> PF {
    if c { PF::Val(v) } else { PF::Nothing }
}

#[inline(never)]
fn mk_pl(c: bool, v: u8) -> PL {
    if c { PL::Val(v) } else { PL::Nothing }
}

#[inline(never)]
fn mk_twop(c: bool) -> TwoP {
    if c { TwoP::A(3) } else { TwoP::B(4) }
}

#[kani::proof]
fn safe_pf_tuple() {
    let c: bool = kani::any();
    let d = (mk_pf(c, 3), 1u8);
    let ok = match d.0 {
        PF::Val(w) => c && w == 3,
        PF::Nothing => !c,
    };
    assert!(ok);
}

#[kani::proof]
fn bug_pf_tuple() {
    let c: bool = kani::any();
    let d = (mk_pf(c, 3), 1u8);
    let ok = match d.0 {
        PF::Val(w) => w == 4,
        PF::Nothing => true,
    };
    assert!(ok);
}

#[kani::proof]
fn safe_pf_struct_field() {
    let c: bool = kani::any();
    let h = HoldPF { x: 1, d: mk_pf(c, 5) };
    let ok = match h.d {
        PF::Val(w) => c && w == 5,
        PF::Nothing => !c,
    };
    assert!(ok);
}

#[kani::proof]
fn bug_pf_struct_field() {
    let c: bool = kani::any();
    let h = HoldPF { x: 1, d: mk_pf(c, 5) };
    let ok = match h.d {
        PF::Val(w) => w == 6,
        PF::Nothing => true,
    };
    assert!(ok);
}

#[kani::proof]
fn safe_pf_array() {
    let c: bool = kani::any();
    let a = [mk_pf(c, 3), PF::Nothing];
    let i: usize = kani::any();
    kani::assume(i < 2);
    let ok = match a[i] {
        PF::Val(w) => i == 0 && c && w == 3,
        PF::Nothing => i == 1 || !c,
    };
    assert!(ok);
}

#[kani::proof]
fn bug_pf_array() {
    let c: bool = kani::any();
    let a = [mk_pf(c, 3), PF::Nothing];
    let ok = match a[0] {
        PF::Val(_) => false,
        PF::Nothing => true,
    };
    assert!(ok);
}

#[kani::proof]
fn safe_pf_option() {
    let c: bool = kani::any();
    let o = Some(mk_pf(c, 5));
    let ok = match o {
        Some(PF::Val(w)) => c && w == 5,
        Some(PF::Nothing) => !c,
        None => false,
    };
    assert!(ok);
}

#[kani::proof]
fn bug_pf_option() {
    let c: bool = kani::any();
    let o = Some(mk_pf(c, 5));
    let ok = match o {
        Some(PF::Val(_)) => false,
        Some(PF::Nothing) => true,
        None => true,
    };
    assert!(ok);
}

#[kani::proof]
fn safe_pf_matches_tuple() {
    let c: bool = kani::any();
    let d = (mk_pf(c, 3), 1u8);
    assert!(matches!(d.0, PF::Val(_)) == c);
}

#[kani::proof]
fn bug_pf_matches_tuple() {
    let c: bool = kani::any();
    let d = (mk_pf(c, 3), 1u8);
    assert!(!matches!(d.0, PF::Val(_)));
}

#[kani::proof]
fn safe_pf_iflet_tuple() {
    let c: bool = kani::any();
    let d = (mk_pf(c, 3), 1u8);
    if let PF::Val(w) = d.0 {
        assert!(c && w == 3);
    }
}

#[kani::proof]
fn bug_pf_iflet_tuple() {
    let c: bool = kani::any();
    let d = (mk_pf(c, 3), 1u8);
    if let PF::Val(w) = d.0 {
        assert!(w == 4);
    }
}

#[kani::proof]
fn safe_pf_wild_tuple() {
    let c: bool = kani::any();
    let d = (mk_pf(c, 3), 1u8);
    match d.0 {
        PF::Val(w) => assert!(c && w == 3),
        _ => assert!(!c),
    }
}

#[kani::proof]
fn bug_pf_wild_tuple() {
    let c: bool = kani::any();
    let d = (mk_pf(c, 3), 1u8);
    match d.0 {
        PF::Val(w) => assert!(w == 4),
        _ => {}
    }
}

#[kani::proof]
fn safe_pl_tuple() {
    let c: bool = kani::any();
    let d = (mk_pl(c, 3), 1u8);
    let ok = match d.0 {
        PL::Val(w) => c && w == 3,
        PL::Nothing => !c,
    };
    assert!(ok);
}

#[kani::proof]
fn bug_pl_tuple() {
    let c: bool = kani::any();
    let d = (mk_pl(c, 3), 1u8);
    let ok = match d.0 {
        PL::Val(w) => w == 4,
        PL::Nothing => true,
    };
    assert!(ok);
}

#[kani::proof]
fn safe_pl_struct_field() {
    let c: bool = kani::any();
    let h = (1u8, mk_pl(c, 5));
    let ok = match h.1 {
        PL::Val(w) => c && w == 5,
        PL::Nothing => !c,
    };
    assert!(ok);
}

#[kani::proof]
fn safe_twop_tuple() {
    let c: bool = kani::any();
    let d = (mk_twop(c), 1u8);
    let ok = match d.0 {
        TwoP::A(w) => c && w == 3,
        TwoP::B(w) => !c && w == 4,
    };
    assert!(ok);
}

#[kani::proof]
fn bug_twop_tuple() {
    let c: bool = kani::any();
    let d = (mk_twop(c), 1u8);
    let ok = match d.0 {
        TwoP::A(_) => !c,
        TwoP::B(_) => true,
    };
    assert!(ok);
}

#[kani::proof]
fn safe_tag_byte_symbolic() {
    let c: bool = kani::any();
    let v: u8 = kani::any();
    let d = mk_pf(c, v);
    let tag = unsafe { *(&d as *const PF as *const u8) };
    assert!(if c { tag == 7 } else { tag == 2 });
}

#[kani::proof]
fn bug_tag_byte_symbolic() {
    let c: bool = kani::any();
    let v: u8 = kani::any();
    let d = mk_pf(c, v);
    let tag = unsafe { *(&d as *const PF as *const u8) };
    assert!(if c { tag == 0 } else { tag == 1 });
}

#[kani::proof]
fn safe_tag_byte_const() {
    let d = PF::Val(3);
    let tag = unsafe { *(&d as *const PF as *const u8) };
    assert!(tag == 7);
}

#[kani::proof]
fn safe_result_err_tag_byte() {
    let r: Result<u8, u8> = Err(3);
    let p = &r as *const Result<u8, u8> as *const u8;
    let (t, v) = unsafe { (*p, *p.add(1)) };
    assert!(t == 1 && v == 3);
}

#[kani::proof]
fn bug_result_err_tag_byte() {
    let r: Result<u8, u8> = Err(3);
    let p = &r as *const Result<u8, u8> as *const u8;
    let t = unsafe { *p };
    assert!(t == 0);
}

#[kani::proof]
fn safe_opt_bool_none_byte() {
    let o: Option<bool> = None;
    let b = unsafe { *(&o as *const Option<bool> as *const u8) };
    assert!(b == 2);
}

#[kani::proof]
fn bug_opt_bool_none_byte() {
    let o: Option<bool> = None;
    let b = unsafe { *(&o as *const Option<bool> as *const u8) };
    assert!(b == 0);
}

#[kani::proof]
fn safe_opt_bool_some_true_byte() {
    let o: Option<bool> = Some(true);
    let b = unsafe { *(&o as *const Option<bool> as *const u8) };
    assert!(b == 1);
}

#[kani::proof]
fn bug_opt_bool_some_false_byte() {
    let o: Option<bool> = Some(false);
    let b = unsafe { *(&o as *const Option<bool> as *const u8) };
    assert!(b == 1);
}

#[kani::proof]
fn safe_opt_nonzero_some_byte() {
    let o: Option<NonZeroU8> = NonZeroU8::new(5);
    let b = unsafe { *(&o as *const Option<NonZeroU8> as *const u8) };
    assert!(b == 5);
}

#[kani::proof]
fn bug_opt_nonzero_some_byte() {
    let o: Option<NonZeroU8> = NonZeroU8::new(5);
    let b = unsafe { *(&o as *const Option<NonZeroU8> as *const u8) };
    assert!(b == 1);
}

#[kani::proof]
fn safe_const_perm_a_ref() {
    let r: &Perm = &CA;
    assert!(matches!(*r, Perm::A(5)));
}

#[kani::proof]
fn bug_const_perm_a_ref() {
    let r: &Perm = &CA;
    assert!(matches!(*r, Perm::B));
}

#[kani::proof]
fn safe_const_perm_b_ref() {
    let r: &Perm = &CB;
    assert!(matches!(*r, Perm::B));
}

#[kani::proof]
fn bug_const_perm_b_ref() {
    let r: &Perm = &CB;
    assert!(!matches!(*r, Perm::B));
}

#[kani::proof]
fn safe_const_disc_ref() {
    let r: &PF = &CD;
    assert!(matches!(*r, PF::Val(3)));
}

#[kani::proof]
fn bug_const_disc_ref() {
    let r: &PF = &CD;
    assert!(matches!(*r, PF::Nothing));
}

#[kani::proof]
fn safe_const_three_ref() {
    let r = &TX;
    assert!(matches!(*r, Three::X(4)));
}

#[kani::proof]
fn bug_const_three_ref() {
    let r = &TX;
    assert!(matches!(*r, Three::Y));
}
