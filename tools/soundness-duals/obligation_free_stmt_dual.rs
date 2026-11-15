// Oracle: MUST FAIL. Every harness below carries exactly ONE obligation, and
// that obligation is a STATEMENT: no `Assert` terminator, no panic call and
// no Kani hook stands in front of it. That is the shape the obligation-free
// certificate could not see while `codegen_ay/obligation_free_walk.rs` read
// terminators only.
//
// WHY THIS FILE EXISTS
//
// `ArtifactMetadata.obligation_free_body` is positive compiler evidence that
// zero emitted checks means "nothing to prove" rather than "we dropped it",
// and D16 lets a certified harness exit 0. The certificate is only as
// complete as the walk's idea of an obligation site. Safe code puts an
// `Assert` in front of `a + b`, `v[i]` and `*p`, but the ENCODER does not
// check the `Assert`; it checks the statement behind it, and that statement
// stands alone whenever rustc's `LowerIntrinsics` produced it
// (`unchecked_add`, `unchecked_div`, `offset`, `copy_nonoverlapping`,
// `read_via_copy`), whenever the body is core's own MIR (compiled without the
// debug assertions that add the `Assert`s), and whenever the harness crate is
// compiled under `--prove-safety-only`. Each harness here is one of those
// bare statements, written with the intrinsic so that the terminator walk has
// nothing to refuse and only the statement rule stands between the
// certificate and a false Safe.
//
// Every result is CONSUMED by `sink`, a local `#[inline(never)]` function
// with an empty body. A pure rvalue whose result nothing reads
// (`let _ = unchecked_add(a, 1)`) is removed by rustc's own MIR optimisations
// before either the encoder or the walk sees it — UB is not a side effect —
// so the first draft of this file emitted ZERO checks for five of its
// harnesses, exactly as Kani would. A call to `sink` survives every MIR pass,
// the walk follows it into a body with nothing to prove, and the statement
// stays the only obligation in sight.
//
// `obligation_free_walk_dual.rs` holds the terminator-level tripwires (an
// assert behind a call, an unwrap, a null deref with its `Assert` still in
// front). `obligation_free_stmt_dual_safe.rs` holds the twins: the same
// statement kinds with nothing to prove, which the walk must still certify.
//
// If any harness here reports SUCCESSFUL, either the certificate vouched for
// a statement that can fail or the encoder dropped the check it emits for
// it. Both are false-Safe channels.
#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::intrinsics;

/// Keeps its argument alive through rustc's MIR optimisations. Obligation-free
/// by inspection, and the walk inspects it.
#[inline(never)]
fn sink<T>(_value: T) {}

// `unchecked_add` lowers to `BinOp::AddUnchecked`. Overflow is UB, and the
// encoder's `emit_overflow_check` (CHC: `bvadd_no_overflow_*`) is the only
// thing that catches `u32::MAX + 1`.
#[kani::proof]
fn bug_unchecked_add_overflows() {
    let a: u32 = kani::any();
    sink(unsafe { intrinsics::unchecked_add(a, 1u32) });
}

// `unchecked_mul` lowers to `BinOp::MulUnchecked`.
#[kani::proof]
fn bug_unchecked_mul_overflows() {
    let a: u32 = kani::any();
    sink(unsafe { intrinsics::unchecked_mul(a, 2u32) });
}

// `unchecked_div` lowers to a plain `BinOp::Div` with NO division-by-zero
// `Assert` (`emit_division_by_zero_check`; CHC: `divisor_nonzero`).
#[kani::proof]
fn bug_unchecked_div_by_zero() {
    let d: u32 = kani::any();
    sink(unsafe { intrinsics::unchecked_div(7u32, d) });
}

// `unchecked_rem` lowers to a plain `BinOp::Rem`.
#[kani::proof]
fn bug_unchecked_rem_by_zero() {
    let d: u32 = kani::any();
    sink(unsafe { intrinsics::unchecked_rem(7u32, d) });
}

// `unchecked_shl` lowers to `BinOp::ShlUnchecked`: a distance of 32 or more
// is UB (`emit_shift_distance_check`).
#[kani::proof]
fn bug_unchecked_shl_distance() {
    let s: u32 = kani::any();
    sink(unsafe { intrinsics::unchecked_shl(1u32, s) });
}

// `offset` lowers to `BinOp::Offset`: eight elements past a two-element
// array leaves the object (`emit_offset_object_bounds_check`).
#[kani::proof]
fn bug_offset_leaves_the_object() {
    let a = [1u32, 2];
    let p: *const u32 = a.as_ptr();
    sink(unsafe { intrinsics::offset(p, 8isize) });
}

// `copy_nonoverlapping` lowers to `StatementKind::Intrinsic(CopyNonOverlapping)`:
// the regions overlap (`codegen_copy_nonoverlapping`;
// `try_encode_copy_nonoverlapping_intrinsic` on the CHC side).
#[kani::proof]
fn bug_copy_nonoverlapping_overlaps() {
    let mut a = [1u32, 2, 3, 4];
    let p: *mut u32 = a.as_mut_ptr();
    unsafe { intrinsics::copy_nonoverlapping(p, p.wrapping_add(1), 2) };
}

// `read_via_copy` lowers to `Use(Copy(*p))`: a raw-pointer `Deref`
// projection with no `CheckNull` / `CheckAlignment` `Assert` in front
// (`emit_raw_ptr_deref_checks`).
#[kani::proof]
fn bug_raw_read_through_null() {
    let p = 0usize as *const u32;
    sink(unsafe { intrinsics::read_via_copy(p) });
}

// `write_via_move` lowers to `*p = move v`: the same projection on the
// left-hand side.
#[kani::proof]
fn bug_raw_write_through_null() {
    let p = 0usize as *mut u32;
    unsafe { intrinsics::write_via_move(p, 7u32) };
}

// Comparing pointers to trait objects compares vtable addresses, which the
// compiler may duplicate or merge at will; Kani reports reaching one as the
// failure `unstable_vtable_comparison`, and so does the BMC encoder.
trait Tr {
    fn f(&self) -> u32;
}
struct S;
impl Tr for S {
    fn f(&self) -> u32 {
        1
    }
}
#[kani::proof]
fn bug_dyn_pointer_comparison() {
    let s = S;
    let a: *const dyn Tr = &s;
    let b: *const dyn Tr = &s;
    sink(a == b);
}
