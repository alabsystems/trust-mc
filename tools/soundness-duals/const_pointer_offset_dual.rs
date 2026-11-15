// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness):
//   safe_e                       -> VERIFICATION:- SUCCESSFUL
//   bug_e                        -> VERIFICATION:- FAILED (assertion)
//   safe_second                  -> VERIFICATION:- SUCCESSFUL
//   bug_second_base              -> VERIFICATION:- FAILED (assertion)
//   bug_second_value             -> VERIFICATION:- FAILED (assertion)
//   safe_bool                    -> VERIFICATION:- SUCCESSFUL
//   bug_bool                     -> VERIFICATION:- FAILED (assertion)
//   safe_char                    -> VERIFICATION:- SUCCESSFUL
//   bug_char                     -> VERIFICATION:- FAILED (assertion)
//   safe_i16                     -> VERIFICATION:- SUCCESSFUL
//   bug_i16                      -> VERIFICATION:- FAILED (assertion)
//   safe_tuple_field             -> VERIFICATION:- SUCCESSFUL
//   bug_tuple_field              -> VERIFICATION:- FAILED (assertion)
//   safe_float                   -> VERIFICATION:- SUCCESSFUL
//   bug_float                    -> VERIFICATION:- FAILED (assertion)
//   safe_nested                  -> VERIFICATION:- SUCCESSFUL
//   bug_nested                   -> VERIFICATION:- FAILED (assertion)
//   safe_nested_str              -> VERIFICATION:- SUCCESSFUL
//   bug_nested_str               -> VERIFICATION:- FAILED (assertion)
//   safe_substr                  -> VERIFICATION:- SUCCESSFUL
//   bug_substr_len               -> VERIFICATION:- FAILED (assertion)
//   bug_substr_byte              -> VERIFICATION:- FAILED (assertion)
//   safe_subslice                -> VERIFICATION:- SUCCESSFUL
//   bug_subslice_len             -> VERIFICATION:- FAILED (assertion)
//   bug_subslice_elem            -> VERIFICATION:- FAILED (assertion)
//   safe_raw_static_field        -> VERIFICATION:- SUCCESSFUL
//   bug_raw_static_field         -> VERIFICATION:- FAILED (assertion)
//   safe_static_ref              -> VERIFICATION:- SUCCESSFUL
//   bug_static_ref_value         -> VERIFICATION:- FAILED (assertion)
//   bug_static_ref_base          -> VERIFICATION:- FAILED (assertion)
//   safe_option_ref              -> VERIFICATION:- SUCCESSFUL
//   bug_option_ref               -> VERIFICATION:- FAILED (assertion)
//   safe_option_str              -> VERIFICATION:- SUCCESSFUL
//   bug_option_str               -> VERIFICATION:- FAILED (assertion)
//   safe_identity                -> VERIFICATION:- SUCCESSFUL
//   bug_identity                 -> VERIFICATION:- FAILED (assertion)
//   safe_enum_tagged             -> VERIFICATION:- SUCCESSFUL
//   bug_enum_tagged              -> VERIFICATION:- FAILED (assertion)
//   safe_enum_unit               -> VERIFICATION:- SUCCESSFUL
//   bug_enum_unit                -> VERIFICATION:- FAILED (assertion)
//   safe_static_struct_ptr_field -> VERIFICATION:- SUCCESSFUL
//   bug_static_struct_ptr_field  -> VERIFICATION:- FAILED (assertion)
//   safe_extend_subslice         -> VERIFICATION:- SUCCESSFUL
//   bug_extend_subslice          -> VERIFICATION:- FAILED (assertion)
//   safe_from_utf8               -> VERIFICATION:- SUCCESSFUL
//   bug_from_utf8                -> VERIFICATION:- FAILED (assertion)
//   safe_str_nth                 -> VERIFICATION:- SUCCESSFUL
//   bug_str_nth                  -> VERIFICATION:- FAILED (assertion)
//   safe_enum_tagged_match       -> VERIFICATION:- SUCCESSFUL
//   bug_enum_tagged_match        -> VERIFICATION:- FAILED (assertion)
//   safe_enum_unit_match         -> VERIFICATION:- SUCCESSFUL
//   bug_enum_unit_match          -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. A constant pointer is what const-eval recorded: the
// relocation AT the pointer's own bytes names a target allocation, and those
// bytes carry an offset into it. Every harness here reads a constant whose
// pointee sits at a NONZERO offset (`E = &[1u32, 2, 3][1]` is `alloc+0x4`), or
// reaches its target through a nested pointer. The rule is stated once, in
// trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs.
//
// Measured on main 5b8582dd4 (scripts/soundness-dual-gate.py, 30 s per harness,
// ay 48c98a43d, seal 9192): the CHC lane decoded every such constant from its
// target's byte 0 and placed it at the target's base, so `*E == 1`, `ptr::eq(E0,
// E1)`, `T.len() == 5`, `**NN == 1`, `matches!(*OE, None)` and 20 more false
// claims PROVED, and their safe twins FAILED certified Genuine. The BMC lane read
// `&str` / `&[T]` windows and `Option<&T>` payloads from byte 0 (`T[0] == b'h'`
// and `SL[0] == 1` PROVED).

#![allow(dead_code)]

static PAIR: (u32, u32) = (1, 2);
static ARR: [u32; 3] = [1, 2, 3];

const E: &u32 = &[1u32, 2, 3][1];
const SECOND: &u32 = &PAIR.1;
const BT: &bool = &[true, false][1];
const C: &char = &['a', 'b'][1];
const I: &i16 = &[-1i16, 5][1];
const TF: &u16 = &(7u16, 9u16).1;
const FL: &f32 = &[1.0f32, 2.5][1];
const NN: &&u32 = &&[1u32, 2, 3][2];
const SS: &&str = &["ab", "cd"][1];
const T: &str = "hello".split_at(2).1;
const SL: &[u32] = {
    let a: &[u32] = &[1, 2, 3, 4];
    a.split_at(1).1
};
const P: *const u32 = &raw const PAIR.1;
static R: &u32 = &ARR[1];
const O: Option<&u32> = Some(&[1u32, 2, 3][1]);
const OS: Option<&str> = Some("hello".split_at(1).1);
const A3: &[u32; 3] = &[10, 20, 30];
const E0: &u32 = &A3[0];
const E1: &u32 = &A3[1];
const OE: &Option<u8> = &[None, Some(3u8)][1];
#[derive(Clone, Copy)]
enum Dir {
    A,
    B,
}
const DR: &Dir = &[Dir::B, Dir::A][1];
struct Holder {
    r: &'static u32,
}
static HS: Holder = Holder { r: &ARR[1] };
const BS: &[u8] = b"hello".split_at(2).1;

#[kani::proof]
fn safe_e() {
    assert!(*E == 2);
}

#[kani::proof]
fn bug_e() {
    assert!(*E == 1);
}

#[kani::proof]
fn safe_second() {
    assert!(*SECOND == 2);
    assert!(std::ptr::eq(SECOND, &PAIR.1));
}

#[kani::proof]
fn bug_second_base() {
    assert!(std::ptr::eq(SECOND, &PAIR.0));
}

#[kani::proof]
fn bug_second_value() {
    assert!(*SECOND == 1);
}

#[kani::proof]
fn safe_bool() {
    assert!(!*BT);
}

#[kani::proof]
fn bug_bool() {
    assert!(*BT);
}

#[kani::proof]
fn safe_char() {
    assert!(*C == 'b');
}

#[kani::proof]
fn bug_char() {
    assert!(*C == 'a');
}

#[kani::proof]
fn safe_i16() {
    assert!(*I == 5);
}

#[kani::proof]
fn bug_i16() {
    assert!(*I == -1);
}

#[kani::proof]
fn safe_tuple_field() {
    assert!(*TF == 9);
}

#[kani::proof]
fn bug_tuple_field() {
    assert!(*TF == 7);
}

#[kani::proof]
fn safe_float() {
    assert!(*FL == 2.5);
}

#[kani::proof]
fn bug_float() {
    assert!(*FL == 1.0);
}

#[kani::proof]
fn safe_nested() {
    assert!(**NN == 3);
}

#[kani::proof]
fn bug_nested() {
    assert!(**NN == 1);
}

#[kani::proof]
fn safe_nested_str() {
    assert!(SS.len() == 2);
    assert!(SS.as_bytes()[0] == b'c');
}

#[kani::proof]
fn bug_nested_str() {
    assert!(SS.as_bytes()[0] == b'a');
}

#[kani::proof]
fn safe_substr() {
    assert!(T.len() == 3);
    assert!(T.as_bytes()[0] == b'l');
}

#[kani::proof]
fn bug_substr_len() {
    assert!(T.len() == 5);
}

#[kani::proof]
fn bug_substr_byte() {
    assert!(T.as_bytes()[0] == b'h');
}

#[kani::proof]
fn safe_subslice() {
    assert!(SL.len() == 3);
    assert!(SL[0] == 2);
}

#[kani::proof]
fn bug_subslice_len() {
    assert!(SL.len() == 4);
}

#[kani::proof]
fn bug_subslice_elem() {
    assert!(SL[0] == 1);
}

#[kani::proof]
fn safe_raw_static_field() {
    assert!(unsafe { *P } == 2);
}

#[kani::proof]
fn bug_raw_static_field() {
    assert!(unsafe { *P } == 1);
}

#[kani::proof]
fn safe_static_ref() {
    assert!(*R == 2);
    assert!(std::ptr::eq(R, &ARR[1]));
}

#[kani::proof]
fn bug_static_ref_value() {
    assert!(*R == 1);
}

#[kani::proof]
fn bug_static_ref_base() {
    assert!(std::ptr::eq(R, &ARR[0]));
}

#[kani::proof]
fn safe_option_ref() {
    assert!(*O.unwrap() == 2);
}

#[kani::proof]
fn bug_option_ref() {
    assert!(*O.unwrap() == 1);
}

#[kani::proof]
fn safe_option_str() {
    assert!(OS.unwrap().len() == 4);
    assert!(OS.unwrap().as_bytes()[0] == b'e');
}

#[kani::proof]
fn bug_option_str() {
    assert!(OS.unwrap().as_bytes()[0] == b'h');
}

#[kani::proof]
fn safe_identity() {
    assert!(!std::ptr::eq(E0, E1));
    assert!(*E0 == 10);
    assert!(*E1 == 20);
}

#[kani::proof]
fn bug_identity() {
    assert!(std::ptr::eq(E0, E1));
}

#[kani::proof]
fn safe_enum_tagged() {
    assert!(matches!(*OE, Some(3)));
}

#[kani::proof]
fn bug_enum_tagged() {
    assert!(matches!(*OE, None));
}

#[kani::proof]
fn safe_enum_unit() {
    assert!(matches!(*DR, Dir::A));
}

#[kani::proof]
fn bug_enum_unit() {
    assert!(matches!(*DR, Dir::B));
}

#[kani::proof]
fn safe_static_struct_ptr_field() {
    assert!(*HS.r == 2);
}

#[kani::proof]
fn bug_static_struct_ptr_field() {
    assert!(*HS.r == 1);
}

#[kani::proof]
fn safe_extend_subslice() {
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(BS);
    assert!(v.len() == 3);
    assert!(v[0] == b'l');
}

#[kani::proof]
fn bug_extend_subslice() {
    let mut v: Vec<u8> = Vec::new();
    v.extend_from_slice(BS);
    assert!(v[0] == b'h');
}

#[kani::proof]
fn safe_from_utf8() {
    let s = std::str::from_utf8(b"hi").unwrap();
    assert!(s.as_bytes()[0] == b'h');
}

#[kani::proof]
fn bug_from_utf8() {
    let s = std::str::from_utf8(b"hi").unwrap();
    assert!(s.as_bytes()[0] == 0);
}

#[kani::proof]
fn safe_str_nth() {
    assert!(T.chars().nth(0) == Some('l'));
}

#[kani::proof]
fn bug_str_nth() {
    assert!(T.chars().nth(0) == Some('h'));
}

#[kani::proof]
fn safe_enum_tagged_match() {
    let v = match *OE {
        None => 0u8,
        Some(x) => x,
    };
    assert!(v == 3);
}

#[kani::proof]
fn bug_enum_tagged_match() {
    let v = match *OE {
        None => 0u8,
        Some(x) => x,
    };
    assert!(v == 0);
}

#[kani::proof]
fn safe_enum_unit_match() {
    let v = match *DR {
        Dir::A => 1u8,
        Dir::B => 2u8,
    };
    assert!(v == 1);
}

#[kani::proof]
fn bug_enum_unit_match() {
    let v = match *DR {
        Dir::A => 1u8,
        Dir::B => 2u8,
    };
    assert!(v == 2);
}
