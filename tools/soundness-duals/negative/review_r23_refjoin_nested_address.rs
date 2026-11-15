// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r23): Joined REFERENCES to aggregates holding an enum AND an address: an Unreported referent whose pointee is
// EnumPlacement::Nested + ty_holds_address keeps the ADDRESS binding in bind_inline_referent_arg.
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r23. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   refjoin_w_hit_a_must_fail   -> VERIFICATION:- FAILED (assertion)
//   refjoin_w_hit_b_must_fail   -> VERIFICATION:- FAILED (assertion)
//   refjoin_w_hit_safe          -> VERIFICATION:- SUCCESSFUL
//   refjoin_w_match_a_must_fail -> VERIFICATION:- FAILED (assertion)
//   refjoin_w_match_b_must_fail -> VERIFICATION:- FAILED (assertion)
//   refjoin_w_match_safe        -> VERIFICATION:- SUCCESSFUL
//   refjoin_w_get_a_must_fail   -> VERIFICATION:- FAILED (assertion)
//   refjoin_w_get_b_must_fail   -> VERIFICATION:- FAILED (assertion)
//   refjoin_w_get_safe          -> VERIFICATION:- SUCCESSFUL
//   refjoin_w_same_must_fail    -> VERIFICATION:- FAILED (assertion)
//   refjoin_w_same_safe         -> VERIFICATION:- SUCCESSFUL
//   refjoin_wb_hit_a_must_fail  -> VERIFICATION:- FAILED (assertion)
//   refjoin_wb_hit_b_must_fail  -> VERIFICATION:- FAILED (assertion)
//   refjoin_wb_hit_safe         -> VERIFICATION:- SUCCESSFUL

struct W<'a> {
    o: Option<u8>,
    p: &'a u8,
}
impl<'a> W<'a> {
    fn hit(&self) -> bool {
        self.o == Some(1)
    }
    fn hit_match(&self) -> bool {
        matches!(self.o, Some(1))
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
        self.o == Some(1)
    }
}

#[kani::proof]
fn refjoin_w_hit_a_must_fail() {
    let x = 0u8;
    let w1 = W { o: Some(1), p: &x };
    let w2 = W { o: Some(2), p: &x };
    let b: bool = kani::any();
    let r: &W = if b { &w1 } else { &w2 };
    assert!(r.hit());
}
#[kani::proof]
fn refjoin_w_hit_b_must_fail() {
    let x = 0u8;
    let w1 = W { o: Some(1), p: &x };
    let w2 = W { o: Some(2), p: &x };
    let b: bool = kani::any();
    let r: &W = if b { &w1 } else { &w2 };
    assert!(!r.hit());
}
#[kani::proof]
fn refjoin_w_hit_safe() {
    let x = 0u8;
    let w1 = W { o: Some(1), p: &x };
    let w2 = W { o: Some(2), p: &x };
    let b: bool = kani::any();
    let r: &W = if b { &w1 } else { &w2 };
    assert!(r.hit() == b && *r.p == 0);
}
#[kani::proof]
fn refjoin_w_match_a_must_fail() {
    let x = 0u8;
    let w1 = W { o: Some(1), p: &x };
    let w2 = W { o: Some(2), p: &x };
    let b: bool = kani::any();
    let r: &W = if b { &w1 } else { &w2 };
    assert!(r.hit_match());
}
#[kani::proof]
fn refjoin_w_match_b_must_fail() {
    let x = 0u8;
    let w1 = W { o: Some(1), p: &x };
    let w2 = W { o: Some(2), p: &x };
    let b: bool = kani::any();
    let r: &W = if b { &w1 } else { &w2 };
    assert!(!r.hit_match());
}
#[kani::proof]
fn refjoin_w_match_safe() {
    let x = 0u8;
    let w1 = W { o: Some(1), p: &x };
    let w2 = W { o: Some(2), p: &x };
    let b: bool = kani::any();
    let r: &W = if b { &w1 } else { &w2 };
    assert!(r.hit_match() == b);
}
#[kani::proof]
fn refjoin_w_get_a_must_fail() {
    let x = 0u8;
    let w1 = W { o: Some(1), p: &x };
    let w2 = W { o: Some(2), p: &x };
    let b: bool = kani::any();
    let r: &W = if b { &w1 } else { &w2 };
    assert!(r.get() == Some(1));
}
#[kani::proof]
fn refjoin_w_get_b_must_fail() {
    let x = 0u8;
    let w1 = W { o: Some(1), p: &x };
    let w2 = W { o: Some(2), p: &x };
    let b: bool = kani::any();
    let r: &W = if b { &w1 } else { &w2 };
    assert!(r.get() == Some(2));
}
#[kani::proof]
fn refjoin_w_get_safe() {
    let x = 0u8;
    let w1 = W { o: Some(1), p: &x };
    let w2 = W { o: Some(2), p: &x };
    let b: bool = kani::any();
    let r: &W = if b { &w1 } else { &w2 };
    assert!((r.get() == Some(1)) == b);
}
#[kani::proof]
fn refjoin_w_same_must_fail() {
    let x = 0u8;
    let w1 = W { o: Some(1), p: &x };
    let w2 = W { o: Some(1), p: &x };
    let b: bool = kani::any();
    let r: &W = if b { &w1 } else { &w2 };
    assert!(!r.hit());
}
#[kani::proof]
fn refjoin_w_same_safe() {
    let x = 0u8;
    let w1 = W { o: Some(1), p: &x };
    let w2 = W { o: Some(1), p: &x };
    let b: bool = kani::any();
    let r: &W = if b { &w1 } else { &w2 };
    assert!(r.hit());
}
#[kani::proof]
fn refjoin_wb_hit_a_must_fail() {
    let w1 = WB { o: Some(1), bx: Box::new(0) };
    let w2 = WB { o: Some(2), bx: Box::new(0) };
    let b: bool = kani::any();
    let r: &WB = if b { &w1 } else { &w2 };
    assert!(r.hit());
}
#[kani::proof]
fn refjoin_wb_hit_b_must_fail() {
    let w1 = WB { o: Some(1), bx: Box::new(0) };
    let w2 = WB { o: Some(2), bx: Box::new(0) };
    let b: bool = kani::any();
    let r: &WB = if b { &w1 } else { &w2 };
    assert!(!r.hit());
}
#[kani::proof]
fn refjoin_wb_hit_safe() {
    let w1 = WB { o: Some(1), bx: Box::new(0) };
    let w2 = WB { o: Some(2), bx: Box::new(0) };
    let b: bool = kani::any();
    let r: &WB = if b { &w1 } else { &w2 };
    assert!(r.hit() == b);
}
