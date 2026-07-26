// Copyright Andrew Yates. Apache-2.0 OR MIT
//
// Soundness dual for the `breakpoint` intrinsic no-op fix
// (codegen_ay/chc/call/codegen_call_cmp_string/misc_intrinsics.rs).
//
// Modeling `std::intrinsics::breakpoint()` as a pure no-op (goto-to-target, no
// inferable-predicate demotion) must NOT swallow a following assertion. If the
// no-op mis-modeled control flow, the false assertion below would be missed.
//
// MUST FAIL (Genuine): `x == x.wrapping_add(1)` is false for every i32.
#![feature(core_intrinsics)]

#[kani::proof]
fn breakpoint_does_not_swallow_following_failure() {
    unsafe { std::intrinsics::breakpoint() };
    let x: i32 = kani::any();
    assert!(x == x.wrapping_add(1));
}
