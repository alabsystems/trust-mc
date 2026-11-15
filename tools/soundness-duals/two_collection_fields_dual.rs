// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a struct with two collection fields
//! (fix/chc-walker-fail-closed, walker fail-closed repair round 5, review
//! finding 5).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   t1_field_len_on_one_path_bug         -> VERIFICATION:- FAILED  ('assertion failed: t.a.len() == 2')
//!   t1_field_len_on_one_path_safe        -> VERIFICATION:- SUCCESSFUL
//!   t2_unrelated_check_on_one_path_bug   -> VERIFICATION:- FAILED  ('assertion failed: x != 9')
//!   t2_unrelated_check_on_one_path_safe  -> VERIFICATION:- SUCCESSFUL
//!   t3_unconditional_field_len_bug       -> VERIFICATION:- FAILED  ('assertion failed: t.a.len() == 2')
//!   t3_unconditional_field_len_safe      -> VERIFICATION:- SUCCESSFUL
//!   t4_unconditional_unrelated_check_bug -> VERIFICATION:- FAILED  ('assertion failed: x != 9')
//!   t5_new_then_literal_bug              -> VERIFICATION:- FAILED  ('assertion failed: x != 9')
//!   t6_vec_and_string_bug                -> VERIFICATION:- FAILED  ('assertion failed: x != 9')
//!   t7_with_capacity_bug                 -> VERIFICATION:- FAILED  ('assertion failed: x != 9')
//!   t8_no_drop_bug                       -> VERIFICATION:- FAILED  ('assertion failed: x != 9')
//!   t9_second_field_len_bug              -> VERIFICATION:- FAILED  ('assertion failed: t.b.len() == 3')
//!   t9_second_field_len_safe             -> VERIFICATION:- SUCCESSFUL
//!   c1_one_field_control_bug             -> VERIFICATION:- FAILED  ('assertion failed: t.a.len() == 2')
//!   c1_one_field_control_safe            -> VERIFICATION:- SUCCESSFUL
//!   s1_swap_fields_bug                   -> VERIFICATION:- FAILED  ('assertion failed: t.b.len() == 0')
//!   s1_swap_fields_safe                  -> VERIFICATION:- SUCCESSFUL
//!   s2_replace_field_bug                 -> VERIFICATION:- FAILED  ('assertion failed: t.b.is_empty()')
//!
//! MECHANISM UNDER TEST. Collection side state (a length, capacity or
//! presence var) is keyed by LOCAL, and an aggregate inherited its
//! collection operand's vars: with two collection operands the struct
//! aliased the first and its length was equated with both. Where the two
//! lengths differ the path that builds the struct was infeasible, so every
//! check after it on that path was lost (checks unrelated to the
//! collections included), and an unconditional construction left the
//! harness VACUOUS. A kind of side state two operands carry is now aliased
//! to neither (`propagate_collection_presence_from_aggregate`,
//! `propagate_collection_len_cap_from_flattened_aggregate`).

struct Two {
    a: Vec<u8>,
    b: Vec<u8>,
}

struct VecString {
    a: Vec<u8>,
    s: String,
}

struct One {
    a: Vec<u8>,
}

#[kani::proof]
fn t1_field_len_on_one_path_bug() {
    let c: bool = kani::any();
    if c {
        let t = Two { a: vec![1, 2, 3], b: Vec::new() };
        assert!(t.a.len() == 2);
    }
}

#[kani::proof]
fn t1_field_len_on_one_path_safe() {
    let c: bool = kani::any();
    if c {
        let t = Two { a: vec![1, 2, 3], b: Vec::new() };
        assert!(t.a.len() == 3 && t.b.is_empty());
    }
}

#[kani::proof]
fn t2_unrelated_check_on_one_path_bug() {
    let c: bool = kani::any();
    let x: u8 = kani::any();
    if c {
        let t = Two { a: vec![1, 2, 3], b: Vec::new() };
        assert!(x != 9);
        drop(t);
    }
}

#[kani::proof]
fn t2_unrelated_check_on_one_path_safe() {
    let c: bool = kani::any();
    let x: u8 = kani::any();
    kani::assume(x != 9);
    if c {
        let t = Two { a: vec![1, 2, 3], b: Vec::new() };
        assert!(x != 9);
        drop(t);
    }
}

#[kani::proof]
fn t3_unconditional_field_len_bug() {
    let t = Two { a: vec![1, 2, 3], b: Vec::new() };
    assert!(t.a.len() == 2);
}

#[kani::proof]
fn t3_unconditional_field_len_safe() {
    let t = Two { a: vec![1, 2, 3], b: Vec::new() };
    assert!(t.a.len() == 3);
}

#[kani::proof]
fn t4_unconditional_unrelated_check_bug() {
    let x: u8 = kani::any();
    let t = Two { a: vec![1, 2, 3], b: Vec::new() };
    assert!(x != 9);
    drop(t);
}

#[kani::proof]
fn t5_new_then_literal_bug() {
    let c: bool = kani::any();
    let x: u8 = kani::any();
    if c {
        let t = Two { a: Vec::new(), b: vec![1, 2] };
        assert!(x != 9);
        drop(t);
    }
}

#[kani::proof]
fn t6_vec_and_string_bug() {
    let c: bool = kani::any();
    let x: u8 = kani::any();
    if c {
        let t = VecString { a: vec![1, 2, 3], s: String::new() };
        assert!(x != 9);
        drop(t);
    }
}

#[kani::proof]
fn t7_with_capacity_bug() {
    let c: bool = kani::any();
    let x: u8 = kani::any();
    if c {
        let t = Two { a: Vec::with_capacity(3), b: Vec::new() };
        assert!(x != 9);
        drop(t);
    }
}

#[kani::proof]
fn t8_no_drop_bug() {
    let c: bool = kani::any();
    let x: u8 = kani::any();
    if c {
        let t = Two { a: vec![1, 2, 3], b: Vec::new() };
        assert!(x != 9);
        std::mem::forget(t);
    }
}

#[kani::proof]
fn t9_second_field_len_bug() {
    let t = Two { a: vec![1, 2, 3], b: Vec::new() };
    assert!(t.b.len() == 3);
}

#[kani::proof]
fn t9_second_field_len_safe() {
    let t = Two { a: vec![1, 2, 3], b: Vec::new() };
    assert!(t.b.len() == 0);
}

#[kani::proof]
fn c1_one_field_control_bug() {
    let t = One { a: vec![1, 2, 3] };
    assert!(t.a.len() == 2);
}

#[kani::proof]
fn c1_one_field_control_safe() {
    let t = One { a: vec![1, 2, 3] };
    assert!(t.a.len() == 3);
}

#[kani::proof]
fn s1_swap_fields_bug() {
    let c: bool = kani::any();
    let mut t = Two { a: vec![1, 2, 3], b: Vec::new() };
    if c {
        std::mem::swap(&mut t.a, &mut t.b);
    }
    assert!(t.b.len() == 0);
}

#[kani::proof]
fn s1_swap_fields_safe() {
    let c: bool = kani::any();
    let mut t = Two { a: vec![1, 2, 3], b: Vec::new() };
    if c {
        std::mem::swap(&mut t.a, &mut t.b);
    }
    assert!(t.a.len() + t.b.len() == 3);
}

#[kani::proof]
fn s2_replace_field_bug() {
    let c: bool = kani::any();
    let mut t = Two { a: vec![1, 2, 3], b: Vec::new() };
    if c {
        let _old = std::mem::replace(&mut t.b, vec![9]);
    }
    assert!(t.b.is_empty());
}
