// Copyright Andrew Yates. Apache-2.0 OR MIT
//
// Soundness dual for the `Option<char>` niche payload-offset fix
// (codegen_ay/chc/expr/codegen_expr_constant_payload.rs).
//
// A niche-encoded `Some('o')` stores the char in-place at offset 0; the old
// code read at `align_of()` (4), ran past the 4-byte allocation, and decoded a
// spurious 0x00000000. The fix reads the REAL stored bits. These duals prove
// the recovered value is the true char, not a forced/zero constant:
//
//   niche_value_is_real  — MUST FAIL: Some('o') (0x6f) != Some('z') (0x7a).
//   niche_value_correct  — MUST SUCCEED: Some('o') == Some('o').
#[kani::proof]
fn niche_value_is_real() {
    let x: Option<char> = Some('o');
    assert!(x == Some('z'));
}

#[kani::proof]
fn niche_value_correct() {
    let x: Option<char> = Some('o');
    assert!(x == Some('o'));
}
