// Dual repro for the FastMath congruent-lane fix: INFINITY + NEG_INFINITY
// produces NaN, so Kani (--nan-check, default-on) reports FAILED. Before the
// fix, trust-mc failed this only ACCIDENTALLY via the chc_fallback demotion
// of a PROOF; after the fix it must stay FAILED via a live NaN-generation
// obligation CTREX (lhs is a non-finite constant → no discharge).
// Expected: VERIFICATION FAILED.

#[kani::proof]
fn main() {
    let y: f32 = kani::any();
    kani::assume(y == f32::NEG_INFINITY);
    let z = f32::INFINITY + y;
    assert!(z == z || z != z);
}
