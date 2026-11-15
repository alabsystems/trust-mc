// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- an `Unreachable` terminator the program
//! can reach, in a body the CHC inline walker walks (Mechanism D for the
//! terminator).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   bug_intrinsic_arm_multi          -> VERIFICATION:- FAILED  ('unreachable code')
//!   safe_intrinsic_arm_multi         -> VERIFICATION:- SUCCESSFUL
//!   bug_intrinsic_enum_arm_multi     -> VERIFICATION:- FAILED  ('unreachable code')
//!   safe_intrinsic_enum_arm_multi    -> VERIFICATION:- SUCCESSFUL
//!   bug_region_intrinsic_multi       -> VERIFICATION:- FAILED  ('unreachable code')
//!   safe_exhaustive_enum_match_multi -> VERIFICATION:- SUCCESSFUL
//!   safe_region_check_free_multi     -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. `core::intrinsics::unreachable()` is lowered by
//! rustc's `LowerIntrinsics` to `TerminatorKind::Unreachable`, not left as a
//! call, so the first cut of fix/chc-walker-fail-closed (which matched
//! `unreachable_unchecked` by callee name) never saw it. The walker filtered
//! every arm that goes straight to `Unreachable` as dead (`is_unreachable_block`,
//! #3889), returned `None` where a walk reached one, and the bailed-arm region
//! scan did not count it: the bug rows verified SUCCESSFUL clean on the
//! a15de6272 base bundle and on that cut. FIXED in the review round: an
//! `Unreachable` arm is Kani's "unreachable code" check whose "not taken"
//! condition is recorded (an explicit enum arm included, which a valid `None`
//! selects), a reached one records `false` on its path, and the region scan
//! counts it. The one arm that stays dead is the `otherwise` rustc adds to an
//! EXHAUSTIVE enum `match`, which no valid value selects
//! (`obligation_free_walk::switch_otherwise_is_invalid_only`;
//! `safe_exhaustive_enum_match_multi` holds the line). The check-free region
//! row is the precision control of the same scan (`saturating_add` reaches a
//! body-less intrinsic, which used to read as "may carry an obligation").
//! Promoted from the review probes rv_diverge.rs, rv_arms3.rs and rv_unreach.rs.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_unreachable_terminator_dual.rs
#![feature(core_intrinsics)]
#![allow(internal_features)]

/// Keeps its argument alive through rustc's MIR optimisations and is
/// obligation-free by inspection (see `unchecked_arith_walker_dual.rs`).
#[inline(never)]
fn sink<T>(_value: T) {}

pub struct Other;

// The intrinsic on an arm of an integer test.
pub trait TArm {
    fn run(&self, a: u8) -> u8;
}
pub struct CArm;
impl TArm for CArm {
    fn run(&self, a: u8) -> u8 {
        if a == 7 {
            unsafe { core::intrinsics::unreachable() }
        }
        a
    }
}
impl TArm for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_intrinsic_arm_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TArm> = if kani::any() { Box::new(CArm) } else { Box::new(Other) };
    sink(o.run(a));
}

#[kani::proof]
fn safe_intrinsic_arm_multi() {
    let a: u8 = kani::any();
    kani::assume(a != 7);
    let o: Box<dyn TArm> = if kani::any() { Box::new(CArm) } else { Box::new(Other) };
    sink(o.run(a));
}

// The intrinsic on an EXPLICIT arm of an enum `match`: a valid `None`
// reaches it.
pub trait TEnum {
    fn run(&self, a: u8) -> u8;
}
pub struct CEnum;
impl TEnum for CEnum {
    fn run(&self, a: u8) -> u8 {
        let o = if a == 3 { None } else { Some(a) };
        match o {
            Some(x) => x,
            None => unsafe { core::intrinsics::unreachable() },
        }
    }
}
impl TEnum for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_intrinsic_enum_arm_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TEnum> = if kani::any() { Box::new(CEnum) } else { Box::new(Other) };
    sink(o.run(a));
}

#[kani::proof]
fn safe_intrinsic_enum_arm_multi() {
    let a: u8 = kani::any();
    kani::assume(a != 3);
    let o: Box<dyn TEnum> = if kani::any() { Box::new(CEnum) } else { Box::new(Other) };
    sink(o.run(a));
}

// The intrinsic inside an arm the walker abandons (the element is read
// before the switch, so the `a > 10` region holds only the untranslatable
// branch and the intrinsic).
pub trait TRegion {
    fn run(&self, a: u8, i: u8) -> u8;
}
pub struct CRegion;
impl TRegion for CRegion {
    fn run(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let v = arr[(i % 4) as usize];
        if a > 10 {
            if v == 100 {
                unsafe { core::intrinsics::unreachable() }
            }
            v
        } else {
            a
        }
    }
}
impl TRegion for Other {
    fn run(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_region_intrinsic_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TRegion> = if kani::any() { Box::new(CRegion) } else { Box::new(Other) };
    sink(o.run(a, i));
}

// Precision: an exhaustive enum `match` (rustc's `otherwise` arm is an
// `Unreachable` no valid value selects).
#[derive(Clone, Copy)]
pub enum Three {
    A,
    B,
    C,
}
impl kani::Arbitrary for Three {
    fn any() -> Self {
        match kani::any::<u8>() % 3 {
            0 => Three::A,
            1 => Three::B,
            _ => Three::C,
        }
    }
}
pub trait TMatch {
    fn run(&self, e: Three) -> u8;
}
pub struct CMatch;
impl TMatch for CMatch {
    fn run(&self, e: Three) -> u8 {
        match e {
            Three::A => 1,
            Three::B => 2,
            Three::C => 3,
        }
    }
}
impl TMatch for Other {
    fn run(&self, _e: Three) -> u8 {
        0
    }
}

#[kani::proof]
fn safe_exhaustive_enum_match_multi() {
    let e: Three = kani::any();
    let o: Box<dyn TMatch> = if kani::any() { Box::new(CMatch) } else { Box::new(Other) };
    sink(o.run(e));
}

// Precision: the abandoned region's only call is check-free arithmetic.
pub trait TFree {
    fn run(&self, a: u8, i: u8) -> u8;
}
pub struct CFree;
impl TFree for CFree {
    fn run(&self, a: u8, i: u8) -> u8 {
        let arr = [a, 1, 2, 3];
        let v = arr[(i % 4) as usize];
        if a > 10 {
            if v > 50 { v.saturating_add(3) } else { v }
        } else {
            a
        }
    }
}
impl TFree for Other {
    fn run(&self, a: u8, _i: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn safe_region_check_free_multi() {
    let a: u8 = kani::any();
    let i: u8 = kani::any();
    let o: Box<dyn TFree> = if kani::any() { Box::new(CFree) } else { Box::new(Other) };
    sink(o.run(a, i));
}
