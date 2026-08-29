// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_term_symbol_name_roundtrip=PROOF

//! AY self-verification: ay-core/src/term/kani_proofs.rs
//!
//! Port of `proof_symbol_name_roundtrip` from ay-core Symbol.
//! Standalone — models the Symbol enum without ay imports.
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

/// Minimal model of ay's Symbol enum.
/// Borrowed names keep this proof focused on the accessor contract.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Symbol {
    Named(&'static str),
    Indexed(&'static str, &'static [u32]),
}

impl Symbol {
    fn name(&self) -> &'static str {
        match self {
            Symbol::Named(s) | Symbol::Indexed(s, _) => s,
        }
    }
}

fn is_test_name(name: &'static str) -> bool {
    let bytes = name.as_bytes();
    bytes.len() == 4
        && bytes[0] == b't'
        && bytes[1] == b'e'
        && bytes[2] == b's'
        && bytes[3] == b't'
}

/// Port of ay::term::proof_symbol_name_roundtrip
///
/// REQUIRES: s is a valid Symbol::Named
/// ENSURES: s.name() returns the original name
#[kani::proof]
fn ay_term_symbol_name_roundtrip() {
    let sym = Symbol::Named("test");
    assert!(is_test_name(sym.name()), "Symbol name must match original");
}
