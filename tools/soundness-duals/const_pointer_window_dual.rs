// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle (per harness; Rust semantics, confirmed by running the program
// natively under Trust seal 9192, one process per harness):
//   safe_row                                -> VERIFICATION:- SUCCESSFUL
//   bug_row                                 -> VERIFICATION:- FAILED (assertion)
//   safe_struct_elem_reordered              -> VERIFICATION:- SUCCESSFUL
//   bug_struct_elem_reordered               -> VERIFICATION:- FAILED (assertion)
//   safe_struct_field_reordered             -> VERIFICATION:- SUCCESSFUL
//   bug_struct_field_reordered              -> VERIFICATION:- FAILED (assertion)
//   safe_deep_const_field                   -> VERIFICATION:- SUCCESSFUL
//   bug_deep_const_field                    -> VERIFICATION:- FAILED (assertion)
//   safe_ptr_inside_window                  -> VERIFICATION:- SUCCESSFUL
//   bug_ptr_inside_window                   -> VERIFICATION:- FAILED (assertion)
//   safe_same_base_two_types                -> VERIFICATION:- SUCCESSFUL
//   bug_same_base_two_types                 -> VERIFICATION:- FAILED (assertion)
//   safe_distinct_fields_const_mem          -> VERIFICATION:- SUCCESSFUL
//   bug_distinct_fields_const_mem           -> VERIFICATION:- FAILED (assertion)
//   bug_distinct_fields_const_mem_addr_diff -> VERIFICATION:- FAILED (assertion)
//   safe_elem_pair_distinct                 -> VERIFICATION:- SUCCESSFUL
//   safe_symbolic_index_offset_slice        -> VERIFICATION:- SUCCESSFUL
//   bug_symbolic_index_offset_slice         -> VERIFICATION:- FAILED (assertion)
//   bug_symbolic_index_offset_slice_len     -> VERIFICATION:- FAILED (assertion)
//   safe_assoc_const                        -> VERIFICATION:- SUCCESSFUL
//   bug_assoc_const                         -> VERIFICATION:- FAILED (assertion)
//   safe_inline_const                       -> VERIFICATION:- SUCCESSFUL
//   bug_inline_const                        -> VERIFICATION:- FAILED (assertion)
//   safe_callee_const                       -> VERIFICATION:- SUCCESSFUL
//   bug_callee_const                        -> VERIFICATION:- FAILED (assertion)
//   safe_big_enum_discr                     -> VERIFICATION:- SUCCESSFUL
//   bug_big_enum_discr                      -> VERIFICATION:- FAILED (assertion)
//   safe_wide_enum_discr                    -> VERIFICATION:- SUCCESSFUL
//   bug_wide_enum_discr                     -> VERIFICATION:- FAILED (assertion)
//   safe_dyn_offset                         -> VERIFICATION:- SUCCESSFUL
//   bug_dyn_offset                          -> VERIFICATION:- FAILED (assertion)
//
// WHY THIS FILE EXISTS. The window a constant pointer names must be decoded at
// ITS offset, whatever shape leads there: an array row, an element of an array
// of structs whose fields rustc reorders, a nested field, a pointer stored
// inside the window, two constants into one allocation, a symbolic index into
// an offset slice, and the same shapes reaching a body through an associated
// const, an inline `const {}` block or an inlined callee. `&dyn` data pointers
// at an offset are here too. The rule is stated once, in
// trust-mc-compiler/src/codegen_ay/shared/const_pointer.rs.
//
// Measured on main 5b8582dd4 (round-10 challenge, 30 s per harness, ay
// 48c98a43d): the CHC lane read every window from its target's byte 0 and gave
// one allocation several objects, so `ROW[0] == 1`, `SB.c == 3`, `ptr::eq(G0,
// G1)` and the three promoted-constant claims PROVED, and `safe_ptr_inside_window`
// FAILED certified Genuine (the pointer stored in the window read as its raw
// offset). On BMC a symbolic index into an offset slice (`SL[i] != 4`) PROVED.

#![allow(dead_code)]

const ROW: &[u32; 2] = &[[1u32, 2], [3, 4]][1];
struct S {
    a: u8,
    b: u32,
    c: u16,
}
const SB: &S = &[S { a: 1, b: 2, c: 3 }, S { a: 4, b: 5, c: 6 }][1];
const SC: &u16 = &S { a: 1, b: 2, c: 3 }.c;
struct Two {
    a: u8,
    b: (u16, u32),
}
const DEEPC: &u32 = &[Two { a: 1, b: (2, 3) }, Two { a: 4, b: (5, 6) }][1].b.1;
static ARR: [u32; 3] = [1, 2, 3];
#[repr(C)]
struct Tagged {
    tag: u64,
    r: &'static u32,
}
const NH: &Tagged = &[Tagged { tag: 0, r: &ARR[0] }, Tagged { tag: 1, r: &ARR[2] }][1];
const W: &[u32; 3] = &[1, 2, 3];
const W0: &u32 = &W[0];
const W1: &u32 = &W[1];
#[repr(C)]
struct PairC {
    x: u32,
    y: u32,
}
const CP: &PairC = &PairC { x: 5, y: 6 };
const G0: &u32 = &CP.x;
const G1: &u32 = &CP.y;
const E: &u32 = &[1u32, 2, 3][1];
const SL: &[u32] = {
    let a: &[u32] = &[1, 2, 3, 4];
    a.split_at(1).1
};

trait Tr {
    const C: &'static u32;
}
struct X;
impl Tr for X {
    const C: &'static u32 = &[1u32, 2, 3][1];
}
fn generic<T: Tr>() -> u32 {
    *T::C
}
fn get() -> &'static u16 {
    const { &(7u16, 9u16).1 }
}

const BIG: &Option<[u64; 4]> = &[None, Some([1u64, 2, 3, 4])][1];
#[derive(Clone, Copy)]
enum Wide {
    A([u64; 3]),
    B([u64; 3]),
}
const WD: &Wide = &[Wide::B([0; 3]), Wide::A([7; 3])][1];

trait Get {
    fn get(&self) -> u32;
}
struct A(u32);
impl Get for A {
    fn get(&self) -> u32 {
        self.0
    }
}
const D: &dyn Get = &[A(1), A(2)][1];

#[kani::proof]
fn safe_row() {
    assert!(ROW[0] == 3);
    assert!(ROW[1] == 4);
}

#[kani::proof]
fn bug_row() {
    assert!(ROW[0] == 1);
}

#[kani::proof]
fn safe_struct_elem_reordered() {
    assert!(SB.a == 4);
    assert!(SB.b == 5);
    assert!(SB.c == 6);
}

#[kani::proof]
fn bug_struct_elem_reordered() {
    assert!(SB.c == 3);
}

#[kani::proof]
fn safe_struct_field_reordered() {
    assert!(*SC == 3);
}

#[kani::proof]
fn bug_struct_field_reordered() {
    assert!(*SC == 2);
}

#[kani::proof]
fn safe_deep_const_field() {
    assert!(*DEEPC == 6);
}

#[kani::proof]
fn bug_deep_const_field() {
    assert!(*DEEPC == 3);
}

#[kani::proof]
fn safe_ptr_inside_window() {
    assert!(NH.tag == 1);
    assert!(*NH.r == 3);
}

#[kani::proof]
fn bug_ptr_inside_window() {
    assert!(*NH.r == 1);
}

#[kani::proof]
fn safe_same_base_two_types() {
    assert!(std::ptr::eq(W as *const [u32; 3] as *const u32, W0));
}

#[kani::proof]
fn bug_same_base_two_types() {
    assert!(!std::ptr::eq(W as *const [u32; 3] as *const u32, W0));
}

#[kani::proof]
fn safe_distinct_fields_const_mem() {
    assert!(!std::ptr::eq(G0, G1));
    assert!(std::ptr::eq((G0 as *const u32).wrapping_add(1), G1));
    assert!(*G0 == 5 && *G1 == 6);
}

#[kani::proof]
fn bug_distinct_fields_const_mem() {
    assert!(std::ptr::eq(G0, G1));
}

#[kani::proof]
fn bug_distinct_fields_const_mem_addr_diff() {
    assert!((G1 as *const u32 as usize) - (G0 as *const u32 as usize) == 0);
}

#[kani::proof]
fn safe_elem_pair_distinct() {
    assert!(!std::ptr::eq(W0, W1));
    assert!(*W1 == 2);
}

#[kani::proof]
fn safe_symbolic_index_offset_slice() {
    let i: usize = kani::any();
    if i < SL.len() {
        assert!(SL[i] != 1);
    }
}

#[kani::proof]
fn bug_symbolic_index_offset_slice() {
    let i: usize = kani::any();
    if i < SL.len() {
        assert!(SL[i] != 4);
    }
}

#[kani::proof]
fn bug_symbolic_index_offset_slice_len() {
    let i: usize = kani::any();
    if i < 4 {
        assert!(i < SL.len());
    }
}

#[kani::proof]
fn safe_assoc_const() {
    assert!(generic::<X>() == 2);
}

#[kani::proof]
fn bug_assoc_const() {
    assert!(generic::<X>() == 1);
}

#[kani::proof]
fn safe_inline_const() {
    let r: &u32 = const { &[1u32, 2, 3][1] };
    assert!(*r == 2);
}

#[kani::proof]
fn bug_inline_const() {
    let r: &u32 = const { &[1u32, 2, 3][1] };
    assert!(*r == 1);
}

#[kani::proof]
fn safe_callee_const() {
    assert!(*get() == 9);
}

#[kani::proof]
fn bug_callee_const() {
    assert!(*get() == 7);
}

#[kani::proof]
fn safe_big_enum_discr() {
    assert!(matches!(*BIG, Some(_)));
}

#[kani::proof]
fn bug_big_enum_discr() {
    assert!(matches!(*BIG, None));
}

#[kani::proof]
fn safe_wide_enum_discr() {
    let v = match *WD {
        Wide::A(_) => 1u8,
        Wide::B(_) => 2u8,
    };
    assert!(v == 1);
}

#[kani::proof]
fn bug_wide_enum_discr() {
    let v = match *WD {
        Wide::A(_) => 1u8,
        Wide::B(_) => 2u8,
    };
    assert!(v == 2);
}

#[kani::proof]
fn safe_dyn_offset() {
    assert!(D.get() == 2);
}

#[kani::proof]
fn bug_dyn_offset() {
    assert!(D.get() == 1);
}
