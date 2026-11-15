// Oracle: MUST be SUCCESSFUL.
//
// The non-vacuity twin of lost_error_rules_dual.rs. Each assertion here is
// constant-true and the compiler's straight-line discharge PROVES it at codegen:
// it rewrites the system to the certified obligation `(=> false error)`, which the
// driver interprets as a proof (`interpret_chc_false_error_safe`,
// `[AY:PROOF_QUALIFIERS:clean]`).
//
// The dual's fail-close keys on the OTHER shape: registered checks and no rule
// deriving `error` at all, which the compiler itself calls "lost checks, not
// proved checks". If this file stops reporting SUCCESSFUL, the fail-close has
// started refusing certified discharges too, and every constant-true assertion
// in the corpus would turn INCONCLUSIVE with it.

#[kani::proof]
fn discharged_constant_true_wrapping_add() {
    let x: u8 = 5;
    let y = x.wrapping_add(1);
    assert!(y == 6);
}

#[kani::proof]
fn discharged_constant_true_array_index() {
    let a = [1u8, 2, 3];
    assert!(a[1] == 2);
}
