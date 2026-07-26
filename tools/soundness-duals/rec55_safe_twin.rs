// Safe twin (MUST PASS once depth-relief lands): identical recursion,
// correct postcondition.
fn count(n: u32) -> u32 {
    if n == 0 { 0 } else { count(n - 1) + 1 }
}
#[kani::proof]
fn check_safe_twin() {
    assert!(count(6) == 6);
}
