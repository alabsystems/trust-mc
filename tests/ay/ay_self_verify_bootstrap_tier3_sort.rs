// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

//! AY self-verification: ay-core/src/sort.rs
//!
//! Port of `proof_bitvec_width_distinguishes` from ay-core Sort.
//! Standalone — models the Sort::BitVec(BitVecSort { width }) case without ay imports.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

/// Minimal model of ay's Sort::BitVec case — only the width-bearing case needed.
#[derive(Debug, Clone, Copy)]
struct Sort {
    bitvec: BitVecSort,
}

#[derive(Debug, Clone, Copy)]
struct BitVecSort {
    width: u32,
}

impl Sort {
    fn bitvec(width: u32) -> Self {
        Sort {
            bitvec: BitVecSort { width },
        }
    }

    fn is_distinct_from(self, other: Self) -> bool {
        self.bitvec.width != other.bitvec.width
    }
}

/// Port of ay::sort::proof_bitvec_width_distinguishes
///
/// REQUIRES: w1 != w2 (distinct bitvector widths)
/// ENSURES: BitVec(w1) != BitVec(w2) (different widths are distinct sorts)
#[kani::proof]
fn ay_sort_bitvec_width_distinguishes() {
    let w1: u32 = kani::any();
    let w2: u32 = kani::any();
    kani::assume(w1 != w2);

    let bv1 = Sort::bitvec(w1);
    let bv2 = Sort::bitvec(w2);

    assert!(
        bv1.is_distinct_from(bv2),
        "Different bitvector widths must be distinct sorts"
    );
}
