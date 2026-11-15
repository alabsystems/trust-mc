// Route dual: two `min` calls with equal arguments whose results the relation must not force
// equal, straight-line and in a loop. The straight-line pair was fixed by the first parity-1
// repair (two different destinations). The loop writes the same destination local on two
// iterations; the CHC straightline discharge left that destination's `__out` variable unbound
// (the relation constrains it without equating it), carried the raw variable name into the
// frame, and gave both iterations one value, so `r[0].to_bits() == r[1].to_bits()` was proved
// SUCCESSFUL clean with a rule-less VC on both routes. An unbound rule-local is now fresh per
// firing.

#[kani::proof]
fn two_calls_same_bits_unprovable() {
    let a = 0.0f32;
    let b = -0.0f32;
    let m1 = a.min(b);
    let m2 = a.min(b);
    assert!(m1.to_bits() == m2.to_bits());
}

#[kani::proof]
fn two_calls_both_zero_holds() {
    let a = 0.0f32;
    let b = -0.0f32;
    let m1 = a.min(b);
    let m2 = a.min(b);
    assert!(m1 == 0.0 && m2 == 0.0);
}

#[kani::proof]
#[kani::unwind(3)]
fn loop_calls_same_bits_unprovable() {
    let a: f32 = kani::any();
    kani::assume(a == 0.0 && a.is_sign_positive());
    let mut r = [0.0f32; 2];
    let mut i = 0;
    while i < 2 {
        r[i] = a.min(-0.0);
        i += 1;
    }
    assert!(r[0].to_bits() == r[1].to_bits());
}

#[kani::proof]
#[kani::unwind(3)]
fn loop_calls_both_zero_holds() {
    let a: f32 = kani::any();
    kani::assume(a == 0.0 && a.is_sign_positive());
    let mut r = [1.0f32; 2];
    let mut i = 0;
    while i < 2 {
        r[i] = a.min(-0.0);
        i += 1;
    }
    assert!(r[0] == 0.0 && r[1] == 0.0);
}

#[kani::proof]
#[kani::unwind(3)]
fn loop_calls_ordered_value_holds() {
    let mut r = [0.0f32; 2];
    let mut i = 0;
    while i < 2 {
        r[i] = 3.0f32.min(-1.0);
        i += 1;
    }
    assert!(r[0] == -1.0 && r[1] == -1.0);
}

#[kani::proof]
#[kani::unwind(3)]
fn loop_calls_ordered_value_refuted() {
    let mut r = [0.0f32; 2];
    let mut i = 0;
    while i < 2 {
        r[i] = 3.0f32.min(-1.0);
        i += 1;
    }
    assert!(r[1] == 3.0);
}
