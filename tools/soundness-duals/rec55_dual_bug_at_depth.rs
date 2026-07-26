// Dual (MUST FAIL): concrete recursion walked to depth 6 with a wrong
// postcondition — the const-fold must NOT prune the error arm.
fn count(n: u32) -> u32 {
    if n == 0 { 0 } else { count(n - 1) + 1 }
}
#[kani::proof]
fn check_bug_at_depth() {
    assert!(count(6) == 7); // WRONG: count(6) == 6
}
