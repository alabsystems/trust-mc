// Oracle: corpus-rev Kani 4c0fce8c3, measured 2026-09-26: every `bug_` harness
// FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: a `&str` joined from two literals has no single
// constant behind it, and the slice-equality fallback resolved its "referent"
// to the operand's own wide POINTER while the literal side resolved to its
// bytes. The fallback then compared the 128-bit pointer with sixteen bytes
// read from the literal (two real, fourteen past its end): constant false.
// Measured on fix/chc-slice-length 619f6ad86 and main 25905b622 (ay
// 643b2851f), chc lane: bug_str_join_ne_literal and
// bug_str_join_same_len_ne_literal PROVED (SUCCESSFUL,
// [AY:PROOF_QUALIFIERS:clean]) and safe_str_join_eq_one FAILED certified
// Genuine. codegen_call_slice.rs now refuses a pointer-sorted unreported
// referent and falls back soundly. The safe twin is NOT_GENUINE: the fallback
// is imprecise (FAILED OverApproximation), and it must never be certified.

#[kani::proof]
#[kani::unwind(8)]
fn bug_str_join_ne_literal() {
    let c: bool = kani::any();
    let s: &str = if c { "hi" } else { "hello" };
    assert!(s != "hi");
}

#[kani::proof]
#[kani::unwind(8)]
fn bug_str_join_same_len_ne_literal() {
    let c: bool = kani::any();
    let s: &str = if c { "hi" } else { "ho" };
    assert!(s != "hi");
}

#[kani::proof]
#[kani::unwind(8)]
fn safe_str_join_eq_one() {
    let c: bool = kani::any();
    let s: &str = if c { "hi" } else { "hello" };
    assert!(s == "hi" || s == "hello");
}

#[kani::proof]
#[kani::unwind(8)]
fn bug_str_join_eq_other() {
    let c: bool = kani::any();
    let s: &str = if c { "hi" } else { "hello" };
    assert!(s == "hello");
}

// Controls: a single literal and a byte-string join resolve exactly.
#[kani::proof]
#[kani::unwind(8)]
fn bug_str_single_ne_literal() {
    let s: &str = "hi";
    assert!(s != "hi");
}

#[kani::proof]
#[kani::unwind(8)]
fn safe_str_single_eq_literal() {
    let s: &str = "hi";
    assert!(s == "hi");
}

#[kani::proof]
#[kani::unwind(8)]
fn bug_bytes_join_ne_literal() {
    let c: bool = kani::any();
    let s: &[u8] = if c { b"hi" } else { b"hello" };
    assert!(s != b"hi");
}
