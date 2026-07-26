// CONTROL — trust-mc SHOULD get these right, isolating the bug to the
// same-object / dropped-offset case.

#[repr(C)]
struct Pair {
    a: u32,
    b: u32,
}

// CONTROL 1 (should PASS, and does): writes only the declared field.
#[kani::modifies(&p.a)]
fn good(p: &mut Pair) {
    p.a = 1;
}

#[kani::proof_for_contract(good)]
fn check_good() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    good(&mut p);
}

// CONTROL 2 (should FAIL, and does): the out-of-frame write targets a DIFFERENT
// object (q). Here same_obj is genuinely false in modifies_frame_store_check
// (obj_a != obj_b), so the frame check DOES emit an error edge => FAILED.
// This proves the enforcement works in general and that the leak is specific
// to same-object writes whose field/index offset was dropped.
#[kani::modifies(&p.a)]
fn caught(p: &mut Pair, q: &mut u32) {
    p.a = 1;
    *q = 9; // different object -> correctly flagged as a frame violation
}

#[kani::proof_for_contract(caught)]
fn check_caught() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    let mut q: u32 = kani::any();
    caught(&mut p, &mut q);
}
