// Copyright Andrew Yates. Apache-2.0 OR MIT
//
// Soundness dual for the fmt-stub no-op fix
// (codegen_ay/chc/call/codegen_call_dispatch_overapprox.rs, `is_fmt` branch).
//
// Gating the spurious fmt Panic head to a side-effects-only no-op for the
// INFALLIBLE Arguments-construction stubs (Arguments::new / new_display /
// from_str) must NOT swallow a genuine failure that follows a print macro. If
// the no-op incorrectly cut the control flow past the following statement, the
// false assertion below would go undetected — a masked bug.
//
// MUST FAIL (Genuine): `x == x.wrapping_add(1)` is false for every i32.
#[kani::proof]
fn fmt_does_not_swallow_following_failure() {
    let x: i32 = kani::any();
    println!("side-effect print of x = {}", x);
    assert!(x == x.wrapping_add(1));
}
