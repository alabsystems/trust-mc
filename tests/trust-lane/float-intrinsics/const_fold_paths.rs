// Route dual: the constant fold of `min` / `max` reached through locals assigned on more than
// one path. The CHC fold used to take the FIRST `local = const` found anywhere in the body,
// flow-insensitively, so `let mut a = 1.0; if c { a = -0.0 } a.min(0.0)` folded as
// `min(1.0, 0.0)` and CHC proved a sign the `c` path leaves to either zero, SUCCESSFUL clean on
// both routes. A local now folds only from its sole plain assignment (no second write, borrow,
// call destination or partial write); anything else is the relation.
#![allow(static_mut_refs)]

#[kani::proof]
fn fold_phi_sign_unprovable() {
    let c: bool = kani::any();
    let mut a = 1.0f32;
    if c {
        a = -0.0;
    }
    let m = a.min(0.0);
    assert!(m.is_sign_positive());
}

#[kani::proof]
fn fold_phi_guarded_holds() {
    let c: bool = kani::any();
    let mut a = 1.0f32;
    if c {
        a = -0.0;
    }
    let m = a.min(0.0);
    assert!(m.is_sign_positive() || c);
}

#[kani::proof]
fn fold_phi_value_holds() {
    let c: bool = kani::any();
    let mut a = 1.0f32;
    if c {
        a = -0.0;
    }
    assert!(a.min(0.0) == 0.0);
}

#[kani::proof]
fn fold_reassigned_sign_unprovable() {
    let mut a = 1.0f32;
    a = -0.0;
    assert!(a.min(0.0).is_sign_positive());
}

#[kani::proof]
fn fold_reassigned_value_refuted() {
    let mut a = 1.0f32;
    a = -0.0;
    assert!(a.min(0.0) == 1.0);
}

#[kani::proof]
fn fold_computed_zero_sign_unprovable() {
    let one = 1.0f32;
    let z = one - one;
    let nz = z * -1.0;
    assert!(nz.min(z).is_sign_positive());
}

#[kani::proof]
fn fold_via_mul_add_path_sign_unprovable() {
    let x = 0.0f64;
    let y = x * -1.0;
    let m = y.max(x);
    assert!(m.to_bits() == 0);
}

#[kani::proof]
fn fold_negated_const_sign_unprovable() {
    const Z: f32 = 0.0;
    let nz = -Z;
    assert!(Z.min(nz).is_sign_positive());
}

#[kani::proof]
fn fold_tuple_fields_sign_unprovable() {
    let t = (0.0f64, -0.0f64);
    assert!(t.1.max(t.0).is_sign_negative());
}

#[kani::proof]
fn fold_array_elems_sign_unprovable() {
    let arr = [-0.0f32, 0.0];
    assert!(arr[0].min(arr[1]).is_sign_positive());
}

static ZS: [f32; 2] = [0.0, -0.0];

#[kani::proof]
fn fold_static_elems_sign_unprovable() {
    assert!(ZS[0].max(ZS[1]).is_sign_negative());
}

#[inline(never)]
fn set_neg_zero(p: &mut f32) {
    *p = -0.0;
}

#[kani::proof]
fn fold_borrowed_sign_unprovable() {
    let mut a = 1.0f32;
    set_neg_zero(&mut a);
    assert!(a.min(0.0).is_sign_positive());
}

#[kani::proof]
fn fold_borrowed_value_refuted() {
    let mut a = 1.0f32;
    set_neg_zero(&mut a);
    assert!(a.min(0.0) == 1.0);
}

static mut SLOT: f32 = 0.0;

#[kani::proof]
fn fold_static_mut_written_sign_unprovable() {
    unsafe {
        SLOT = -0.0;
        assert!(SLOT.max(0.0).is_sign_negative());
    }
}

#[kani::proof]
fn fold_sole_assignment_value_holds() {
    let a = 1.0f32;
    let b = a;
    assert!(b.min(0.0) == 0.0 && a.max(0.5) == 1.0);
}

#[kani::proof]
fn fold_sole_assignment_value_refuted() {
    let a = 1.0f32;
    assert!(a.min(0.0) == 1.0);
}

#[kani::proof]
fn fold_const_fn_eval_value_holds() {
    const M: f32 = 3.0f32.min(-2.0);
    assert!(M == -2.0);
}
