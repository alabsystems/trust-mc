// Oracle: MUST NOT report SUCCESSFUL (FAILED or INCONCLUSIVE both acceptable).
//
// A loop invariant that holds at entry and breaks after one step: when the
// first byte is ASCII whitespace the loop sets `bytes = rest`, so
// `bytes.len() == s.len()` is false after the step. Kani fails "Check invariant
// after step". The array is `kani::any()`, so a whitespace first byte exists.
//
// WHY THIS FILE EXISTS: it was a FALSE PROOF through the CHC no-derivation
// shortcut. The CHC system registered the invariant obligations, yet no rule
// derived `error` (the compiler warns "registered properties but no error rules
// (lost checks, not proved checks)"), and the driver reported
//
//     [AY:PROOF_QUALIFIERS:trivial_safe=no_error_rule]
//     VERIFICATION:- SUCCESSFUL
//
// without running a solver (main 5aec7f89b, ay 10bc4b185). The same shape
// carries the offset_from family's `same_dangling` harnesses and 23 other corpus
// units. The driver now fails that shape closed:
//
//     [AY:UNKNOWN_REASON:LostErrorRules]
//     VERIFICATION:- INCONCLUSIVE (checks lost from the CHC encoding ...)
//
// If this file ever reports SUCCESSFUL again, registered checks are being
// credited as proved with no error rule behind them.
//
// Twin: lost_error_rules_discharged_twin.rs (certified discharges stay proofs).

#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]

#[kani::proof]
fn lost_rules_invariant_breaks_after_step() {
    let a: [u8; 10] = kani::any();
    let s = a.as_slice();
    let mut bytes = s;
    #[kani::loop_invariant(bytes.len() == s.len())]
    while let [first, rest @ ..] = bytes {
        if first.is_ascii_whitespace() {
            bytes = rest;
        } else {
            break;
        }
    }
}
