// CHAR_FROM_U32_OPTION_MODEL dual (missed-bug tripwire) — soundness net for the
// checked `char::from_u32` Option model (`inline_char_from_u32_expr`).
//
// `kani::any_where(|v| char::from_u32(*v).is_none())` must constrain `x` to an
// INVALID Unicode scalar value (a surrogate or > 0x10FFFF). Transmuting such an
// `x` into a `char` is UB and MUST be detected. If the from_u32 model were
// FALSE-modeled wrong (e.g. `is_none` never satisfiable, or the validity
// predicate inverted), the assumed constraint would let a valid value slip in
// and this could wrongly SUCCEED — or an invalid value would reach the `char`
// use unchecked. Either way the model bug shows up as a lost FAILURE here.
//
// Oracle: MUST be FAILED — "Invalid value of type `char`".
// kani-flags: -Z valid-value-checks
#[kani::proof]
fn from_u32_none_reaches_char_use() {
    let x = kani::any_where(|v: &u32| char::from_u32(*v).is_none());
    // `x` is assumed to be an INVALID char, so transmuting it to `char` is UB.
    let c: char = unsafe { std::mem::transmute(x) };
    std::hint::black_box(c);
}
