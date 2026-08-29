// Oracle: MUST FAIL.
//
// `catch_unwind` over a closure that PANICS. The result is `Err`, so
// `assert!(r.is_ok())` is FALSE and must be refuted.
//
// WHY THIS FILE EXISTS — deleted outcome, not a missing feature. There IS a
// dedicated handler (codegen_call_catch_unwind.rs) with Err-construction
// machinery; it was defeated by ONE CONSTANT:
//
//     // Model as always 0 (no unwind) — sound over-approximation.
//     let result_value = Expr::bitvec_const(0, 32);   // :164-165
//
// The comment is wrong about itself. Hard-coding "no unwind" is an UNDER-
// approximation: it deletes the Err outcome outright. A real over-approximation
// is NONDETERMINISTIC (0 or 1), which admits both continuations. With the
// constant in place the encoder proves `r.is_ok()` for a closure whose body is
// `panic!`, and emits no check for the swallowed panic.
//
// NON-VACUITY IS REQUIRED. A planted `assert!(1 == 2)` in the same body DOES
// fail, so the proof above is not an empty-body artifact — the harness is
// reachable and the assertion is genuinely being discharged. Calling the same
// closure directly also fails. Both controls are what separate "proved a false
// thing" from "never encoded anything".
//
// If this file ever reports SUCCESSFUL, the unwind outcome is hard-coded again.

#[kani::proof]
fn bug_catch_unwind_swallows_panic() {
    let r = std::panic::catch_unwind(|| {
        panic!("oh no!");
    });
    assert!(r.is_ok());
}

#[kani::proof]
fn bug_catch_unwind_conditional_panic() {
    let x: bool = kani::any();
    let r = std::panic::catch_unwind(move || {
        if x {
            panic!("conditional");
        }
        7i32
    });
    // FALSE: when x is true the closure unwinds and r is Err.
    assert!(r.is_ok());
}
