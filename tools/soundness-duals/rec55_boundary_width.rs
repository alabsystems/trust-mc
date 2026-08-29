// Oracle (per harness):
//   check_boundary_pass -> VERIFICATION:- SUCCESSFUL
//   check_boundary_fail -> VERIFICATION:- FAILED
//
// Boundary-width discriminant duals: i8 match arms cross the sign boundary —
// SwitchTargets stores raw-bits u128 (-1i8 => 255), so a fold with wrong
// width-masking or sign handling picks the wrong arm.
fn step(n: i8) -> i8 {
    match n {
        -1 => 42,
        0 => 0,
        _ => step(n - 1),
    }
}
#[kani::proof]
fn check_boundary_pass() {
    assert!(step(3) == 0); // 3 -> 2 -> 1 -> 0: never hits -1
}
#[kani::proof]
fn check_boundary_fail() {
    assert!(step(-1) == 0); // WRONG: step(-1) == 42 — must FAIL
}
