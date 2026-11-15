// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK (review bypass r06): References INTO a joined Option's payload (match ergonomics on &o / on a joined &Option).
//
// Audit evidence: review of m3/chc-joined-option-eq at f1373b8d1 (2026-09-12),
// bypass pack r06. Every `_must_fail` assertion is violated on a path native Rust
// takes; every `_safe` assertion holds on every path. A `SUCCESSFUL` on a `_must_fail`
// harness in either lane is a false proof.
//
// Oracle (per harness):
//   iflet_ref_payload_join_must_fail     -> VERIFICATION:- FAILED (assertion)
//   iflet_ref_payload_join_safe          -> VERIFICATION:- SUCCESSFUL
//   iflet_ref_payload_differ_a_must_fail -> VERIFICATION:- FAILED (assertion)
//   iflet_ref_payload_differ_b_must_fail -> VERIFICATION:- FAILED (assertion)
//   iflet_ref_payload_differ_safe        -> VERIFICATION:- SUCCESSFUL
//   match_guard_ref_join_must_fail       -> VERIFICATION:- FAILED (assertion)
//   match_guard_ref_join_safe            -> VERIFICATION:- SUCCESSFUL
//   refjoin_payload_a_must_fail          -> VERIFICATION:- FAILED (assertion)
//   refjoin_payload_b_must_fail          -> VERIFICATION:- FAILED (assertion)
//   refjoin_payload_safe                 -> VERIFICATION:- SUCCESSFUL

#[kani::proof]
fn iflet_ref_payload_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    if let Some(x) = &o {
        assert!(*x != 4);
    }
}
#[kani::proof]
fn iflet_ref_payload_join_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    if let Some(x) = &o {
        assert!(*x == 4);
    } else {
        assert!(false);
    }
}
#[kani::proof]
fn iflet_ref_payload_differ_a_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(1) } else { Some(2) };
    if let Some(x) = &o {
        assert!(*x == 1);
    }
}
#[kani::proof]
fn iflet_ref_payload_differ_b_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(1) } else { Some(2) };
    if let Some(x) = &o {
        assert!(*x == 2);
    }
}
#[kani::proof]
fn iflet_ref_payload_differ_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(1) } else { Some(2) };
    if let Some(x) = &o {
        assert!((*x == 1) == b);
    } else {
        assert!(false);
    }
}
#[kani::proof]
fn match_guard_ref_join_must_fail() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    match &o {
        Some(x) if *x == 4 => panic!("hit"),
        _ => {}
    }
}
#[kani::proof]
fn match_guard_ref_join_safe() {
    let b: bool = kani::any();
    let o: Option<u8> = if b { Some(4) } else { Some(4) };
    match &o {
        Some(x) if *x == 4 => {}
        _ => panic!("miss"),
    }
}
#[kani::proof]
fn refjoin_payload_a_must_fail() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &m } else { &n };
    if let Some(x) = r {
        assert!(*x == 1);
    }
}
#[kani::proof]
fn refjoin_payload_b_must_fail() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &m } else { &n };
    if let Some(x) = r {
        assert!(*x == 2);
    }
}
#[kani::proof]
fn refjoin_payload_safe() {
    let m = Some(1u8);
    let n = Some(2u8);
    let b: bool = kani::any();
    let r: &Option<u8> = if b { &m } else { &n };
    if let Some(x) = r {
        assert!((*x == 1) == b);
    } else {
        assert!(false);
    }
}
