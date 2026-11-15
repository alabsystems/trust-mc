// Oracle: corpus-rev Kani, measured 2026-09-24:
//   forget_bug, vecnew_bug, write_bug, plain_bug   MUST FAIL
//   forget_safe, vecnew_safe, write_safe, plain_safe   SUCCESSFUL
//
// WHY THIS FILE EXISTS: the CHC inline walker's no-op tables
// (`inline_call_classify.rs`: `is_inline_noop_call`, `is_inline_vec_internal_noop`)
// matched callee PATH TEXT only -- `ends_with("::forget") && contains("mem")`,
// `contains("Vec") && ends_with("::new")` -- so a USER function whose path
// happens to match (`mem::forget`, `memw::forget`, `Vec3::new`) was replaced by
// a no-op: its assertion and its write through `&mut` disappeared, and the
// harness PROVED.
//
// * plain_bug: the arguments translate; the table fires on the main path. This
//   was already a missed bug on main (68c0f116d808).
// * forget_bug, vecnew_bug, write_bug: one argument is an f64 product the walker
//   cannot translate. On main that call fell back to the havoc path, whose
//   guards book `nested_call_dropped_obligation` / a pointer-write refusal and
//   fail closed. 527a00a16 added a rescue that returns the no-op when argument
//   translation fails and the path matches the tables, which bypassed both
//   guards and turned these into missed bugs on the branch (a4b2d1695c12).
//
// The callees are reached through a dyn-dispatched body, which the walker walks
// itself. `#[inline(never)]` keeps the MIR inliner from dissolving them.

mod mem {
    #[inline(never)]
    pub fn forget<T>(x: u8, _arg: T) {
        assert!(x < 10, "user forget obligation");
    }
}

mod memw {
    #[inline(never)]
    pub fn forget<T>(slot: &mut u8, _arg: T) {
        *slot = 42;
    }
}

pub struct Vec3;

impl Vec3 {
    #[inline(never)]
    pub fn new(x: u8, _s: f64) {
        assert!(x < 10, "user Vec3::new obligation");
    }
}

// One trait per scenario: the walker dispatches a `dyn` call over every impl
// of the trait, so a shared trait would let one scenario's translation drops
// demote the others and hide what each one measures.
trait RunForget {
    fn run(&self, x: u8) -> u8;
}
trait RunVecNew {
    fn run(&self, x: u8) -> u8;
}
trait RunWrite {
    fn run(&self, x: u8) -> u8;
}
trait RunPlain {
    fn run(&self, x: u8) -> u8;
}

struct Forget;
struct VecNew;
struct Write;
struct Plain;
struct Empty;

impl RunForget for Forget {
    fn run(&self, x: u8) -> u8 {
        let a = (x as f64) * 1.5;
        mem::forget(x, a);
        0
    }
}

impl RunVecNew for VecNew {
    fn run(&self, x: u8) -> u8 {
        let a = (x as f64) * 1.5;
        Vec3::new(x, a);
        0
    }
}

impl RunWrite for Write {
    fn run(&self, x: u8) -> u8 {
        let mut s = 0u8;
        let a = (x as f64) * 1.5;
        memw::forget(&mut s, a);
        s
    }
}

impl RunPlain for Plain {
    fn run(&self, x: u8) -> u8 {
        mem::forget(x, x);
        0
    }
}

impl RunForget for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}
impl RunVecNew for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}
impl RunWrite for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}
impl RunPlain for Empty {
    fn run(&self, _x: u8) -> u8 {
        0
    }
}

fn drive_forget(t: &dyn RunForget, x: u8) -> u8 {
    let e = Empty;
    let d: &dyn RunForget = if kani::any() { t } else { &e };
    d.run(x)
}

fn drive_vecnew(t: &dyn RunVecNew, x: u8) -> u8 {
    let e = Empty;
    let d: &dyn RunVecNew = if kani::any() { t } else { &e };
    d.run(x)
}

fn drive_write(t: &dyn RunWrite, x: u8) -> u8 {
    let e = Empty;
    let d: &dyn RunWrite = if kani::any() { t } else { &e };
    d.run(x)
}

fn drive_plain(t: &dyn RunPlain, x: u8) -> u8 {
    let e = Empty;
    let d: &dyn RunPlain = if kani::any() { t } else { &e };
    d.run(x)
}

// Kani: FAILED (x = 10 violates the callee assertion).
#[kani::proof]
fn forget_bug() {
    let x: u8 = kani::any();
    drive_forget(&Forget, x);
}

// Kani: SUCCESSFUL.
#[kani::proof]
fn forget_safe() {
    let x: u8 = kani::any();
    kani::assume(x < 10);
    drive_forget(&Forget, x);
}

// Kani: FAILED.
#[kani::proof]
fn vecnew_bug() {
    let x: u8 = kani::any();
    drive_vecnew(&VecNew, x);
}

// Kani: SUCCESSFUL.
#[kani::proof]
fn vecnew_safe() {
    let x: u8 = kani::any();
    kani::assume(x < 10);
    drive_vecnew(&VecNew, x);
}

// Kani: FAILED (the dispatched body writes 42 through the &mut argument).
#[kani::proof]
fn write_bug() {
    let x: u8 = kani::any();
    let r = drive_write(&Write, x);
    assert!(r == 0, "write dropped");
}

// Kani: SUCCESSFUL.
#[kani::proof]
fn write_safe() {
    let x: u8 = kani::any();
    let r = drive_write(&Write, x);
    assert!(r == 0 || r == 42);
}

// Kani: FAILED (the arguments translate; the table path itself drops it).
#[kani::proof]
fn plain_bug() {
    let x: u8 = kani::any();
    drive_plain(&Plain, x);
}

// Kani: SUCCESSFUL.
#[kani::proof]
fn plain_safe() {
    let x: u8 = kani::any();
    kani::assume(x < 10);
    drive_plain(&Plain, x);
}
