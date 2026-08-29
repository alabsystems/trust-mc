// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN

//! AY self-verification bootstrap Tier 3f: XOR packed-row iterator invariant.
//!
//! This mirrors the remaining easy `#[kani::proof]` from `ay-xor/src/lib.rs`
//! that is not yet present in the tracked bootstrap files at `HEAD`.
//! The standalone model keeps only the row shape needed for the
//! `iter_set_bits()` single-bit invariant.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

/// Iterator over the set bits in one packed row word.
struct SetBitsIter {
    word: u64,
    base_col: usize,
    num_cols: usize,
}

impl Iterator for SetBitsIter {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.word == 0 {
            return None;
        }
        let bit = self.word.trailing_zeros() as usize;
        self.word &= self.word - 1;
        let col = self.base_col + bit;
        if col < self.num_cols {
            Some(col)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PackedRow {
    bits: u64,
    num_cols: usize,
}

impl PackedRow {
    fn new(num_cols: usize) -> Self {
        Self {
            bits: 0,
            num_cols,
        }
    }

    fn set(&mut self, col: usize, value: bool) {
        let bit = col % 64;
        if value {
            self.bits |= 1u64 << bit;
        } else {
            self.bits &= !(1u64 << bit);
        }
    }

    fn iter_set_bits(&self) -> impl Iterator<Item = usize> + '_ {
        SetBitsIter {
            word: self.bits,
            base_col: 0,
            num_cols: self.num_cols,
        }
    }
}

/// Port of ay::xor::proof_packed_row_single_set_bit
#[kani::proof]
fn ay_xor_packed_row_single_set_bit() {
    let col: usize = kani::any();
    kani::assume(col < 64);

    let mut row = PackedRow::new(64);
    row.set(col, true);

    let mut bits = row.iter_set_bits();
    assert_eq!(
        bits.next(),
        Some(col),
        "iter_set_bits must report the written column first"
    );
    assert_eq!(bits.next(), None, "Single set bit should yield exactly one column");
}
