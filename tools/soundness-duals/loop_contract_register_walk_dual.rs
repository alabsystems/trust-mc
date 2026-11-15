// Oracle: corpus-rev Kani (-Z loop-contracts), measured 2026-09-24:
//   retry_plain_bug, retry_slice_bug       MUST FAIL (the post-loop assertion)
//   mod_exit_post_bug, mod_exit_body_bug   MUST FAIL (invariant after step)
//   inv_oob_bug, inv_idx_bug               MUST FAIL (index out of bounds)
//   retry_slice_safe, mod_exit_safe,
//   inv_oob_safe                           SUCCESSFUL
//
// WHY THIS FILE EXISTS: a CHC-lane change (290ac7cb8, reverted before landing)
// made the inline walker evaluate the invariant closure at every legacy
// `kani_register_loop_contract` call instead of the raw `{ true }` breadcrumb.
// The walker reads a closure's by-reference captures as ADDRESSES, and the
// macro lowers `while guard` to `while kani_register_loop_contract(&inv, _) &&
// guard`, so a garbage invariant value silently EXITED the loop:
//
// * the `loop_modifies` loops (which the #47 rule declines, keeping the legacy
//   encoding) collapsed to the degenerate VC `(rule (=> false error))` and
//   PROVED mod_exit_body_bug, while mod_exit_safe came back FAILED Genuine;
// * every loop the #47 rule DOES encode reaches the legacy encoding in Lane P
//   of the two-lane retry, which runs after ANY lane-1 failure, so
//   retry_plain_bug (a plain counter loop with a correct invariant) PROVED;
// * the invariant's own bounds check read a declined slice length and was
//   dropped by the walker's "assume the Assert passes" policy (#4014), so
//   inv_oob_bug and inv_idx_bug PROVED.
//
// Measured on the branch bundle a4b2d1695c12 against main 68c0f116d808 and
// Kani; the probes came from the soundness review of land/array-param-mid-guard.
// The safe twins guard the other direction: a fix must not buy these rows with
// a Genuine false alarm.

#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

// Kani: FAILED (n == 4 at the real exit).
#[kani::proof]
fn retry_plain_bug() {
    let mut n: u32 = 0;
    #[kani::loop_invariant(n <= 4)]
    while n < 4 {
        n += 1;
    }
    assert!(n <= 1, "real exit has n == 4");
}

// Kani: FAILED (i == 4 at the real exit).
#[kani::proof]
fn retry_slice_bug() {
    let a: [u8; 4] = kani::any();
    let s: &[u8] = &a;
    let mut i: usize = 0;
    #[kani::loop_invariant(i <= s.len())]
    while i < s.len() {
        i += 1;
    }
    assert!(i <= 1, "real exit has i == 4");
}

// Kani: SUCCESSFUL.
#[kani::proof]
fn retry_slice_safe() {
    let a: [u8; 4] = kani::any();
    let s: &[u8] = &a;
    let mut i: usize = 0;
    #[kani::loop_invariant(i <= s.len())]
    while i < s.len() {
        i += 1;
    }
    assert!(i == 4);
}

// An explicit `loop_modifies` clause makes the #47 rule decline, so the legacy
// encoding carries the loop. Kani: FAILED (the invariant n <= 1 breaks).
#[kani::proof]
fn mod_exit_post_bug() {
    let mut n: u32 = 0;
    #[kani::loop_invariant(n <= 1)]
    #[kani::loop_modifies(&n)]
    while n < 4 {
        n += 1;
    }
    assert!(n == 2, "real exit has n == 4");
}

// Kani: FAILED (the invariant breaks; the body assertion fails on the third
// iteration of the concrete loop).
#[kani::proof]
fn mod_exit_body_bug() {
    let mut n: u32 = 0;
    #[kani::loop_invariant(n <= 1)]
    #[kani::loop_modifies(&n)]
    while n < 4 {
        assert!(n != 2, "third iteration");
        n += 1;
    }
}

// Kani: SUCCESSFUL.
#[kani::proof]
fn mod_exit_safe() {
    let mut n: u32 = 0;
    #[kani::loop_invariant(n <= 4)]
    #[kani::loop_modifies(&n)]
    while n < 4 {
        n += 1;
    }
    assert!(n == 4);
}

// The invariant indexes the captured slice out of bounds once the loop has
// finished (i == 4). Kani: FAILED (index out of bounds).
#[kani::proof]
fn inv_oob_bug() {
    let a: [u8; 4] = kani::any();
    let s: &[u8] = &a;
    let mut i: usize = 0;
    #[kani::loop_invariant(i <= 4 && s[i] == s[i])]
    while i < 4 {
        i += 1;
    }
}

// Kani: FAILED (the invariant reads s[4] once the loop is done).
#[kani::proof]
fn inv_idx_bug() {
    let a: [u8; 4] = kani::any();
    let s: &[u8] = &a;
    let mut i: usize = 0;
    #[kani::loop_invariant(i <= 4 && s[i] <= 255)]
    while i < 4 {
        i += 1;
    }
}

// Kani: SUCCESSFUL.
#[kani::proof]
fn inv_oob_safe() {
    let a: [u8; 4] = kani::any();
    let s: &[u8] = &a;
    let mut i: usize = 0;
    #[kani::loop_invariant(i <= 4 && (i >= 4 || s[i] == s[i]))]
    while i < 4 {
        i += 1;
    }
}
