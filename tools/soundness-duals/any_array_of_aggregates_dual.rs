// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// kani-flags: (none)
//
// `kani::any()` for an array of aggregates, and the CHC codegen-panic fallback.
//
// The default `Arbitrary::any_array` is `[(); N].map(|_| T::any())`, so an array
// of tuples or structs reaches `core::array::map`, whose
// `NeverShortCircuit::wrap_mut_1(f)` builds `Wrapped { f, p: PhantomData }`.
// The CHC inline walker built that aggregate with a field value whose sort did
// not match the constructor's, `Expr::datatype_constructor` panicked, and the
// codegen-panic fallback emitted a one-fact VC (`chc_codegen_error`) that the
// driver reported as "error reachable (exact CHC derivation)" with
// [AY:CTREX_CAT:Genuine]. tests/expected/loop-contract/for_loop_for_tuple.rs and
// for_loop_for_tuple_with_quantifiers.rs were false positives that way (Kani:
// SUCCESSFUL). A codegen panic is a statement about the encoder, never a
// counterexample.
//
// Oracles (each measured with the corpus-rev Kani, 4c0fce8c3, 2026-09-15):
//   tuple_array_any_sum_bounded_safe              SUCCESSFUL
//   tuple_array_any_sum_can_reach_max_bug         FAILED (assertion)
//   struct_array_any_sum_bounded_safe             SUCCESSFUL
//   struct_array_any_elements_independent_bug     FAILED (assertion)
//
// The loop-invariant form of the same shape is the corpus units themselves; it is
// not repeated here because its VC is large enough that one CHC row overran its
// budget by 143 s under load, and the driver watchdog then cut the other
// harnesses of the file (measured 2026-09-15 on the fixed bundle).
#[derive(kani::Arbitrary, Clone, Copy)]
struct Pair {
    x: u8,
    y: u8,
}

#[kani::proof]
fn tuple_array_any_sum_bounded_safe() {
    let a: [(u8, u8); 3] = kani::any();
    let s = a[1].0 as u32 + a[1].1 as u32;
    assert!(s <= 510);
}

#[kani::proof]
fn tuple_array_any_sum_can_reach_max_bug() {
    let a: [(u8, u8); 3] = kani::any();
    let s = a[1].0 as u32 + a[1].1 as u32;
    assert!(s < 510);
}

#[kani::proof]
fn struct_array_any_sum_bounded_safe() {
    let a: [Pair; 3] = kani::any();
    assert!(a[2].x as u32 + a[2].y as u32 <= 510);
}

#[kani::proof]
fn struct_array_any_elements_independent_bug() {
    let a: [Pair; 3] = kani::any();
    assert!(a[0].x == a[1].x);
}
