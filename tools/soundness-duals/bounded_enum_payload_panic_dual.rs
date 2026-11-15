// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// `kani::BoundedArbitrary` enums whose variants carry a bounded `String` or
// `Vec<T>`. Building the payload inside `bounded_any` reaches the CHC inline
// ADT aggregate with a field whose sort no coercion matched. Since ay
// ad07c5cc63 checks constructor argument sorts, `Expr::datatype_constructor`
// panicked there, `codegen_chc_path` caught the panic and emitted its forced
// `chc_codegen_error` fact, and that counterexample carried no taint.
//
// Measured 2026-09-15 on bundle-m3 (main 498d0c80f, ay 10bc4b185), CHC lane:
// every harness below logged `CHC codegen panic ... datatype_constructor
// requires a matching datatype constructor signature` and FAILED
// `[AY:CTREX_CAT:Genuine]`, the safe ones included
// (expected/derive-bounded-arbitrary/enum.rs and enum_one_variant.rs, both
// Kani SUCCESSFUL, were false_positive). BMC lane on the same bundle: the
// String harnesses FAILED `OverApproximation:chc_sound_havoc_drop=1`, the enum
// harnesses INCONCLUSIVE.
//
// Oracles, each confirmed with Kani 0.67.0:
//   safe_bounded_enum_payload_len_at_most_bound          SUCCESSFUL -> NOT_GENUINE
//   safe_bounded_single_variant_string_len_at_most_bound SUCCESSFUL -> NOT_GENUINE
//   bug_bounded_enum_payload_len_below_bound             FAILED (length 4 exists)
//   bug_bounded_single_variant_string_len_below_bound    FAILED (length 4 exists)
//
// The fix: the panic fallback records the demoting per-fn `chc_fallback`, so a
// forced counterexample is EncodingGap, and the inline aggregate declines a
// field-sort mismatch instead of panicking.

#[allow(unused)]
#[derive(kani::BoundedArbitrary)]
enum Payload<T> {
    A(#[bounded] String),
    B(#[bounded] Vec<T>, usize),
    C {
        #[bounded]
        x: Vec<T>,
        y: bool,
    },
}

#[allow(unused)]
#[derive(kani::BoundedArbitrary)]
enum OnlyString {
    A(#[bounded] String),
}

#[kani::proof]
#[kani::unwind(6)]
fn safe_bounded_enum_payload_len_at_most_bound() {
    let any_enum: Payload<bool> = kani::bounded_any::<_, 4>();
    match any_enum {
        Payload::A(s) => assert!(s.len() <= 4),
        Payload::B(v, _) => assert!(v.len() <= 4),
        Payload::C { x, y: _ } => assert!(x.len() <= 4),
    }
}

#[kani::proof]
#[kani::unwind(6)]
fn safe_bounded_single_variant_string_len_at_most_bound() {
    let any_enum: OnlyString = kani::bounded_any::<_, 4>();
    let OnlyString::A(s) = any_enum;
    assert!(s.len() <= 4);
}

#[kani::proof]
#[kani::unwind(6)]
fn bug_bounded_enum_payload_len_below_bound() {
    let any_enum: Payload<bool> = kani::bounded_any::<_, 4>();
    match any_enum {
        Payload::A(s) => assert!(s.len() < 4),
        Payload::B(v, _) => assert!(v.len() < 4),
        Payload::C { x, y: _ } => assert!(x.len() < 4),
    }
}

#[kani::proof]
#[kani::unwind(6)]
fn bug_bounded_single_variant_string_len_below_bound() {
    let any_enum: OnlyString = kani::bounded_any::<_, 4>();
    let OnlyString::A(s) = any_enum;
    assert!(s.len() < 4);
}
