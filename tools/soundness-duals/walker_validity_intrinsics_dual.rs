// Oracle: corpus-rev Kani, measured 2026-09-24 (per-harness table below).
//
// The CHC inline walker and the type-validity requirements of `assert_*`,
// `mem::zeroed` and `mem::uninitialized`, reached through a dyn-dispatched
// body that the walker walks itself. One trait per scenario: the walker
// dispatches over every impl of a trait, so a shared trait would let one
// scenario's translation drops demote the others.
//
// * zvalid_generic_bug / uvalid_generic_bug: a user generic fn calls
//   `assert_zero_valid::<T>` / `assert_mem_uninitialized_valid::<T>`, so the
//   call survives InstSimplify and the walker meets it. The walker's misc
//   intrinsic arm claimed both as `true` ahead of the arm that decides them,
//   so the requirement was never checked.
// * zeroed_bug / uninit_bug: `mem::zeroed::<&u8>()` and
//   `mem::uninitialized::<TwoThree>()` are claimed WHOLE by the walker, so the
//   assertion at the top of their bodies was never walked either.
// * iref_bug: `MaybeUninit::<Void>::assume_init_ref` reaches
//   `assert_inhabited::<Void>` inside a generic std body; c0d6bbc66 routed it.
// * diverge_bug: a user `-> !` fn that panics, called in a walked body. The
//   call has no target, and the walker pruned an unrecognized diverging call
//   as a dead path (its arm bailed into a blessed havoc). FIXED on
//   fix/chc-walker-fail-closed (2026-09-26): reaching an unmodelled diverging
//   call whose callee can carry an obligation is a check that fails wherever
//   it is reached, never certified.
//
// Kani: every *_bug FAILED, every *_safe SUCCESSFUL.

#![feature(core_intrinsics)]
#![allow(invalid_value, deprecated, internal_features, unused)]

use std::mem::MaybeUninit;

#[derive(Clone, Copy)]
pub enum Void {}

#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum TwoThree {
    A = 2,
    B = 3,
}

struct Empty;

#[inline(never)]
fn zv<T>() {
    core::intrinsics::assert_zero_valid::<T>();
}

#[inline(never)]
fn uv<T>() {
    core::intrinsics::assert_mem_uninitialized_valid::<T>();
}

#[inline(never)]
fn die(code: u8) -> ! {
    panic!("user diverging fn reached with {}", code)
}

// Kani: FAILED (zero-initialising `&u8` is invalid).
trait ZvalidBug {
    fn run(&self, x: u8) -> u8;
}
struct CZvalidBug;
impl ZvalidBug for CZvalidBug {
    fn run(&self, x: u8) -> u8 {
        if x == 7 {
            zv::<&u8>();
            return 1;
        }
        0
    }
}
impl ZvalidBug for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}
fn drive_zvalid_bug(t: &dyn ZvalidBug) -> u8 {
    let x: u8 = kani::any();
    let e = Empty;
    let d: &dyn ZvalidBug = if kani::any() { t } else { &e };
    d.run(x)
}
#[kani::proof]
fn zvalid_generic_bug() {
    drive_zvalid_bug(&CZvalidBug);
}

// Kani: SUCCESSFUL.
trait ZvalidSafe {
    fn run(&self, x: u8) -> u8;
}
struct CZvalidSafe;
impl ZvalidSafe for CZvalidSafe {
    fn run(&self, x: u8) -> u8 {
        if x == 7 {
            zv::<u32>();
            return 1;
        }
        0
    }
}
impl ZvalidSafe for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}
fn drive_zvalid_safe(t: &dyn ZvalidSafe) -> u8 {
    let x: u8 = kani::any();
    let e = Empty;
    let d: &dyn ZvalidSafe = if kani::any() { t } else { &e };
    d.run(x)
}
#[kani::proof]
fn zvalid_generic_safe() {
    drive_zvalid_safe(&CZvalidSafe);
}

// Kani: FAILED (leaving `TwoThree` uninitialized is invalid).
trait UvalidBug {
    fn run(&self, x: u8) -> u8;
}
struct CUvalidBug;
impl UvalidBug for CUvalidBug {
    fn run(&self, x: u8) -> u8 {
        if x == 7 {
            uv::<TwoThree>();
            return 1;
        }
        0
    }
}
impl UvalidBug for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}
fn drive_uvalid_bug(t: &dyn UvalidBug) -> u8 {
    let x: u8 = kani::any();
    let e = Empty;
    let d: &dyn UvalidBug = if kani::any() { t } else { &e };
    d.run(x)
}
#[kani::proof]
fn uvalid_generic_bug() {
    drive_uvalid_bug(&CUvalidBug);
}

// Kani: FAILED (zero-initialising `&u8` is invalid).
trait ZeroedBug {
    fn run(&self, x: u8) -> u8;
}
struct CZeroedBug;
impl ZeroedBug for CZeroedBug {
    fn run(&self, x: u8) -> u8 {
        if x == 7 {
            let r: &u8 = unsafe { std::mem::zeroed() };
            let _ = r as *const u8;
            return 1;
        }
        0
    }
}
impl ZeroedBug for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}
fn drive_zeroed_bug(t: &dyn ZeroedBug) -> u8 {
    let x: u8 = kani::any();
    let e = Empty;
    let d: &dyn ZeroedBug = if kani::any() { t } else { &e };
    d.run(x)
}
#[kani::proof]
fn zeroed_bug() {
    drive_zeroed_bug(&CZeroedBug);
}

// Kani: SUCCESSFUL.
trait ZeroedSafe {
    fn run(&self, x: u8) -> u8;
}
struct CZeroedSafe;
impl ZeroedSafe for CZeroedSafe {
    fn run(&self, x: u8) -> u8 {
        if x == 7 {
            let r: u32 = unsafe { std::mem::zeroed() };
            return r as u8;
        }
        0
    }
}
impl ZeroedSafe for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}
fn drive_zeroed_safe(t: &dyn ZeroedSafe) -> u8 {
    let x: u8 = kani::any();
    let e = Empty;
    let d: &dyn ZeroedSafe = if kani::any() { t } else { &e };
    d.run(x)
}
#[kani::proof]
fn zeroed_safe() {
    drive_zeroed_safe(&CZeroedSafe);
}

// Kani: FAILED (leaving `TwoThree` uninitialized is invalid).
trait UninitBug {
    fn run(&self, x: u8) -> u8;
}
struct CUninitBug;
impl UninitBug for CUninitBug {
    fn run(&self, x: u8) -> u8 {
        if x == 7 {
            let t: TwoThree = unsafe { std::mem::uninitialized() };
            let _ = t;
            return 1;
        }
        0
    }
}
impl UninitBug for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}
fn drive_uninit_bug(t: &dyn UninitBug) -> u8 {
    let x: u8 = kani::any();
    let e = Empty;
    let d: &dyn UninitBug = if kani::any() { t } else { &e };
    d.run(x)
}
#[kani::proof]
fn uninit_bug() {
    drive_uninit_bug(&CUninitBug);
}

// Kani: FAILED (instantiating the uninhabited `Void`).
trait IrefBug {
    fn run(&self, x: u8) -> u8;
}
struct CIrefBug;
impl IrefBug for CIrefBug {
    fn run(&self, x: u8) -> u8 {
        if x == 7 {
            let mu = MaybeUninit::<Void>::uninit();
            let r: &Void = unsafe { mu.assume_init_ref() };
            let _ = r as *const Void;
            return 1;
        }
        0
    }
}
impl IrefBug for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}
fn drive_iref_bug(t: &dyn IrefBug) -> u8 {
    let x: u8 = kani::any();
    let e = Empty;
    let d: &dyn IrefBug = if kani::any() { t } else { &e };
    d.run(x)
}
#[kani::proof]
fn iref_bug() {
    drive_iref_bug(&CIrefBug);
}

// Kani: SUCCESSFUL.
trait IrefSafe {
    fn run(&self, x: u8) -> u8;
}
struct CIrefSafe;
impl IrefSafe for CIrefSafe {
    fn run(&self, x: u8) -> u8 {
        if x == 7 {
            let mu = MaybeUninit::<u8>::new(3);
            let r: &u8 = unsafe { mu.assume_init_ref() };
            return *r;
        }
        0
    }
}
impl IrefSafe for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}
fn drive_iref_safe(t: &dyn IrefSafe) -> u8 {
    let x: u8 = kani::any();
    let e = Empty;
    let d: &dyn IrefSafe = if kani::any() { t } else { &e };
    d.run(x)
}
#[kani::proof]
fn iref_safe() {
    drive_iref_safe(&CIrefSafe);
}

// Kani: FAILED ("user diverging fn reached").
trait DivergeBug {
    fn run(&self, x: u8) -> u8;
}
struct CDivergeBug;
impl DivergeBug for CDivergeBug {
    fn run(&self, x: u8) -> u8 {
        if x == 7 {
            die(x)
        }
        0
    }
}
impl DivergeBug for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}
fn drive_diverge_bug(t: &dyn DivergeBug) -> u8 {
    let x: u8 = kani::any();
    let e = Empty;
    let d: &dyn DivergeBug = if kani::any() { t } else { &e };
    d.run(x)
}
#[kani::proof]
fn diverge_bug() {
    drive_diverge_bug(&CDivergeBug);
}
