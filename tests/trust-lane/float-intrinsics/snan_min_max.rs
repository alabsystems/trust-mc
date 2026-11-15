// Route dual: a signalling NaN argument to `min` / `max`.
//
// The documented contract of `f32::min` / `f32::max` (and the intrinsics under them: nightly
// `minnumf*` / `maxnumf*`, Trust `minimum_number_nsz_f*` / `maximum_number_nsz_f*`) returns the
// other argument for ANY NaN. Measured on this host (arm64): Trust build 8590 does that at run
// time and in const evaluation, and nightly-2025-12-03 does it in const evaluation; but the
// nightly's RUN TIME `f32::min(sNaN, 1.0)` is the quiet NaN `0x7fc00001` at O0 and O3. An engine
// built by that nightly folded `min(sNaN, 2.0)` with the host's `f32::min` and proved `.is_nan()`
// (DevCli CHC) where the Trust-built engine proved `== 2.0`: opposite clean verdicts on one
// harness. No fold decides a signalling NaN any more; the relation does, identically on both
// routes, and says what the contract says. The `_holds` below are that contract, not a promise
// about the nightly's run time.

#[kani::proof]
fn snan_first_min_holds() {
    let s = f32::from_bits(0x7f80_0001);
    assert!(s.min(1.5).to_bits() == 1.5f32.to_bits());
}

#[kani::proof]
fn snan_first_min_refuted() {
    let s = f32::from_bits(0x7f80_0001);
    assert!(s.min(1.5).is_nan());
}

#[kani::proof]
fn snan_const_other_min_holds() {
    let s = f32::from_bits(0x7f80_0001);
    assert!(s.min(2.0).to_bits() == 2.0f32.to_bits());
}

#[kani::proof]
fn snan_const_other_min_refuted() {
    let s = f32::from_bits(0x7f80_0001);
    assert!(s.min(2.0).is_nan());
}

#[kani::proof]
fn snan_const_literal_min_refuted() {
    assert!(f32::from_bits(0x7f80_0001).min(2.0).is_nan());
}

#[kani::proof]
fn snan_second_max64_holds() {
    let s = f64::from_bits(0xfff0_0000_0000_0001);
    assert!((-2.5f64).max(s).to_bits() == (-2.5f64).to_bits());
}

#[kani::proof]
fn snan_vs_pz_max_holds() {
    let s = f32::from_bits(0xff80_0001);
    assert!(s.max(0.0).to_bits() == 0);
}

#[kani::proof]
fn snan_sym_other_min_holds() {
    let s = f32::from_bits(0x7f80_0001);
    let y: f32 = kani::any();
    kani::assume(!y.is_nan());
    assert!(s.min(y).to_bits() == y.to_bits());
}

#[kani::proof]
fn snan_sym_other_min_refuted() {
    let s = f32::from_bits(0x7f80_0001);
    let y: f32 = kani::any();
    kani::assume(!y.is_nan());
    assert!(s.min(y).is_nan());
}

#[kani::proof]
fn snan_sym_other_max64_holds() {
    let s = f64::from_bits(0xfff0_0000_0000_0001);
    let y: f64 = kani::any();
    kani::assume(!y.is_nan());
    assert!(y.max(s).to_bits() == y.to_bits());
}

// Two signalling NaNs are two NaNs: a NaN comes back, with no sign, payload or quiet bit promised.
#[kani::proof]
fn both_snan_quiet_bit_unprovable() {
    let a = f32::from_bits(0x7f80_0001);
    let b = f32::from_bits(0xff80_0002);
    assert!((a.max(b).to_bits() & 0x0040_0000) != 0);
}

#[kani::proof]
fn both_snan_is_nan_holds() {
    let a = f32::from_bits(0x7f80_0001);
    let b = f32::from_bits(0xff80_0002);
    assert!(a.max(b).is_nan() && a.min(b).is_nan());
}
