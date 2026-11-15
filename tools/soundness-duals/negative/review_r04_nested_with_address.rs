// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r04): EnumPlacement::Nested + ty_holds_address keeps the ADDRESS binding (inline_ref_arg_binding.rs).
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r04. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   struct_opt_and_ref_eq_must_fail      -> VERIFICATION:- FAILED (assertion)
//   struct_opt_and_ref_eq_safe           -> VERIFICATION:- SUCCESSFUL
//   struct_opt_and_ref_matches_must_fail -> VERIFICATION:- FAILED (assertion)
//   struct_opt_and_ref_matches_safe      -> VERIFICATION:- SUCCESSFUL
//   struct_opt_and_ref_get_a_must_fail   -> VERIFICATION:- FAILED (assertion)
//   struct_opt_and_ref_get_b_must_fail   -> VERIFICATION:- FAILED (assertion)
//   struct_opt_and_ref_get_safe          -> VERIFICATION:- SUCCESSFUL
//   struct_opt_and_box_must_fail         -> VERIFICATION:- FAILED (assertion)
//   struct_opt_and_box_safe              -> VERIFICATION:- SUCCESSFUL

struct W<'a> {
    o: Option<u8>,
    p: &'a u8,
}
impl<'a> W<'a> {
    fn hit(&self) -> bool {
        self.o == Some(4)
    }
    fn hit_match(&self) -> bool {
        matches!(self.o, Some(4))
    }
    fn get(&self) -> Option<u8> {
        self.o
    }
}
struct WB {
    o: Option<u8>,
    bx: Box<u8>,
}
impl WB {
    fn hit(&self) -> bool {
        self.o == Some(4)
    }
}

#[kani::proof]
fn struct_opt_and_ref_eq_must_fail() {
    let x = 1u8;
    let b: bool = kani::any();
    let w = if b { W { o: Some(4), p: &x } } else { W { o: Some(4), p: &x } };
    assert!(!w.hit());
}
#[kani::proof]
fn struct_opt_and_ref_eq_safe() {
    let x = 1u8;
    let b: bool = kani::any();
    let w = if b { W { o: Some(4), p: &x } } else { W { o: Some(4), p: &x } };
    assert!(w.hit() && *w.p == 1);
}
#[kani::proof]
fn struct_opt_and_ref_matches_must_fail() {
    let x = 1u8;
    let b: bool = kani::any();
    let w = if b { W { o: Some(4), p: &x } } else { W { o: Some(4), p: &x } };
    assert!(!w.hit_match());
}
#[kani::proof]
fn struct_opt_and_ref_matches_safe() {
    let x = 1u8;
    let b: bool = kani::any();
    let w = if b { W { o: Some(4), p: &x } } else { W { o: Some(4), p: &x } };
    assert!(w.hit_match());
}
#[kani::proof]
fn struct_opt_and_ref_get_a_must_fail() {
    let x = 1u8;
    let b: bool = kani::any();
    let w = if b { W { o: Some(1), p: &x } } else { W { o: Some(2), p: &x } };
    assert!(w.get() == Some(1));
}
#[kani::proof]
fn struct_opt_and_ref_get_b_must_fail() {
    let x = 1u8;
    let b: bool = kani::any();
    let w = if b { W { o: Some(1), p: &x } } else { W { o: Some(2), p: &x } };
    assert!(w.get() == Some(2));
}
#[kani::proof]
fn struct_opt_and_ref_get_safe() {
    let x = 1u8;
    let b: bool = kani::any();
    let w = if b { W { o: Some(1), p: &x } } else { W { o: Some(2), p: &x } };
    assert!((w.get() == Some(1)) == b);
}
#[kani::proof]
fn struct_opt_and_box_must_fail() {
    let b: bool = kani::any();
    let w = if b { WB { o: Some(4), bx: Box::new(1) } } else { WB { o: Some(4), bx: Box::new(1) } };
    assert!(!w.hit());
}
#[kani::proof]
fn struct_opt_and_box_safe() {
    let b: bool = kani::any();
    let w = if b { WB { o: Some(4), bx: Box::new(1) } } else { WB { o: Some(4), bx: Box::new(1) } };
    assert!(w.hit() && *w.bx == 1);
}
