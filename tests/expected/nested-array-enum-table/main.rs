// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Regression: a 2-D `const` lookup table of fieldless enums indexed by a
// *symbolic* pair of discriminants — the shape of aterm's provenance / policy
// join tables (`const T: [[OriginTag; 6]; 6]; T[a as usize][b as usize]`).
//
// `select(outer, i)` for a symbolic `i` whose elements are themselves arrays
// (ay#5148) was left unconstrained: the whole table came back as an
// unconstrained array, so every downstream read was symbolic and the harness
// went INCONCLUSIVE (and, with store-chains, produced a spurious FAILURE on a
// property that holds). The codegen now (a) decodes the nested `const`
// allocation instead of returning `None`, and (b) Ackermann-expands a symbolic
// nested-array index into an `ite` cascade of concrete-index selects (which AY
// resolves soundly), distributing `select` through the resulting `ite`.
//
// This harness pins both directions: the diagonal property is TRUE and must
// prove (SUCCESS); the all-cells-equal-row property is FALSE for off-diagonal
// cells and must produce a counterexample (FAILURE) — so the proof is not
// vacuous and the solver genuinely reads the concrete cell values.

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum E {
    A = 0,
    B = 1,
    C = 2,
}

const TABLE: [[E; 3]; 3] = [
    [E::A, E::B, E::C],
    [E::B, E::B, E::C],
    [E::C, E::C, E::C],
];

fn decode(v: u8) -> E {
    match v {
        0 => E::A,
        1 => E::B,
        _ => E::C,
    }
}

#[kani::proof]
fn main() {
    let i: u8 = kani::any();
    let j: u8 = kani::any();
    kani::assume(i < 3);
    kani::assume(j < 3);

    let a = decode(i);
    let b = decode(j);
    let r = TABLE[a as usize][b as usize] as u8;

    // Diagonal of this join table is the identity: TABLE[i][i] == i.
    // TRUE for all in-bounds i — provable only if the symbolic nested-array
    // select is encoded soundly.
    assert!(i != j || r == i, "diagonal join is identity");

    // Off the diagonal the cells are not equal to the row index (e.g.
    // TABLE[0][1] = B = 1 != 0), so this is FALSE — a non-vacuity witness
    // that the solver reads the real concrete cell values.
    assert!(r == i, "table read equals row index");
}
