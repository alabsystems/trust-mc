// Oracle: MUST be SUCCESSFUL.
//
// The non-vacuity twin of unreachable_discharge_dual.rs: the SAME shape, with
// the input constrained so the `unreachable_unchecked` genuinely cannot be
// reached. It witnesses that the twin's failure comes from the obligation being
// refuted, not from every unreachable arm failing wholesale.

fn inner(x: u32) -> u32 {
    if x < 100 { x } else { unsafe { std::hint::unreachable_unchecked() } }
}

#[kani::proof]
fn safe_unreachable_is_unreachable() {
    let x: u32 = kani::any();
    kani::assume(x < 100);
    let _ = inner(x);
}
