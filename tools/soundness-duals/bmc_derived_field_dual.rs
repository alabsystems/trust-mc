// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a struct field written after a borrow
//! of that field (fix/chc-walker-fail-closed, repair round 4: found probing
//! the class of walker fail-closed review 6 round 3 finding 7 on the BMC
//! lane).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01):
//!   s1_field_after_field_ref_bug          -> VERIFICATION:- FAILED  ('s.a == 1')
//!   s1_field_after_field_ref_safe         -> VERIFICATION:- SUCCESSFUL
//!   s2_direct_field_after_field_ref_bug   -> VERIFICATION:- FAILED  ('s.a == 1')
//!   s5_whole_store_through_ref_bug        -> VERIFICATION:- FAILED  ('s.a == 1')
//!   s5_whole_store_through_ref_safe       -> VERIFICATION:- SUCCESSFUL
//!   s6_whole_direct_store_bug             -> VERIFICATION:- FAILED  ('s.a == 1')
//!
//! MECHANISM UNDER TEST. The BMC lane keeps a borrowed field under a derived
//! name (`s_field_0`) and reads a field place by that name first; a write
//! through the name is carried up into `s`, but a write of `s` (a field store
//! through `r = &mut s`, a direct `s.a = ..`, a whole store) never came down
//! to it, so `s.a` read the value the borrow left: s1, s2 and s6 verified
//! clean on main and s1's safe twin was certified Genuine. Every derived field
//! entry is re-selected from the root's new value now
//! (`statement/env/mod.rs`, `refresh_derived_field_entries`).

struct P {
    a: u8,
    b: u8,
}

#[kani::proof]
fn s1_field_after_field_ref_bug() {
    let mut s = P { a: 0, b: 0 };
    {
        let q = &mut s.a;
        *q = 1;
    }
    {
        let r = &mut s;
        r.a = 5;
    }
    assert!(s.a == 1);
}

#[kani::proof]
fn s1_field_after_field_ref_safe() {
    let mut s = P { a: 0, b: 0 };
    {
        let q = &mut s.a;
        *q = 1;
    }
    {
        let r = &mut s;
        r.a = 5;
    }
    assert!(s.a == 5 && s.b == 0);
}

#[kani::proof]
fn s2_direct_field_after_field_ref_bug() {
    let mut s = P { a: 0, b: 0 };
    {
        let q = &mut s.a;
        *q = 1;
    }
    s.a = 7;
    assert!(s.a == 1);
}

#[kani::proof]
fn s5_whole_store_through_ref_bug() {
    let mut s = P { a: 0, b: 0 };
    {
        let q = &mut s.a;
        *q = 1;
    }
    {
        let r = &mut s;
        *r = P { a: 9, b: 9 };
    }
    assert!(s.a == 1);
}

#[kani::proof]
fn s5_whole_store_through_ref_safe() {
    let mut s = P { a: 0, b: 0 };
    {
        let q = &mut s.a;
        *q = 1;
    }
    {
        let r = &mut s;
        *r = P { a: 9, b: 9 };
    }
    assert!(s.a == 9 && s.b == 9);
}

#[kani::proof]
fn s6_whole_direct_store_bug() {
    let mut s = P { a: 0, b: 0 };
    {
        let q = &mut s.a;
        *q = 1;
    }
    s = P { a: 4, b: 4 };
    assert!(s.a == 1);
}
