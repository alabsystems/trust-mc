// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

//! AY self-verification: clause arena bit-packing and stride invariants
//!
//! These harnesses verify the correctness of ay-sat's ClauseArena, which
//! stores clauses as packed u32 words with 3-word headers + inline literals.
//! Originally from ay/crates/ay-sat/src/clause_arena.rs.
//!
//! The arena uses bit-packing for flags (learned, garbage, used count)
//! and a shrink_map HashMap for tracking arena walking strides.
//! Bugs in bit masking cause silent clause corruption — exactly the kind
//! of bug formal verification catches.
//!
//! Layout: [lit_count:u16 as u32] [glue:u32] [refcount:u16 | flags:u16] [lit0] [lit1] ...

const HEADER_WORDS: usize = 3;
const LEARNED_BIT: u16 = 0b0_0000_0001;
const USED_MASK: u16 = 0b0_0011_1110;
const USED_SHIFT: u32 = 1;
const GARBAGE_BIT: u16 = 0b0_0100_0000;
const MAX_USED: u8 = 31;

/// Extract literal count from header word 0
fn lit_count(header0: u32) -> u16 {
    header0 as u16
}

/// Extract flags from header word 2 (high 16 bits)
fn flags(header2: u32) -> u16 {
    (header2 >> 16) as u16
}

/// Extract refcount from header word 2 (low 16 bits)
fn refcount(header2: u32) -> u16 {
    header2 as u16
}

/// Check if learned bit is set
fn is_learned(f: u16) -> bool {
    (f & LEARNED_BIT) != 0
}

/// Check if garbage bit is set
fn is_garbage(f: u16) -> bool {
    (f & GARBAGE_BIT) != 0
}

/// Get used counter value
fn used_count(f: u16) -> u8 {
    ((f & USED_MASK) >> USED_SHIFT) as u8
}

/// Set used counter in flags
fn set_used(f: u16, count: u8) -> u16 {
    let clamped = if count > MAX_USED { MAX_USED } else { count };
    (f & !USED_MASK) | ((clamped as u16) << USED_SHIFT)
}

/// Build header word 2 from refcount and flags
fn make_header2(rc: u16, f: u16) -> u32 {
    (rc as u32) | ((f as u32) << 16)
}

/// Compute arena stride for a clause: HEADER_WORDS + lit_count
fn stride(header0: u32) -> usize {
    HEADER_WORDS + lit_count(header0) as usize
}

// --- Harnesses ---

/// Learned bit is independent of other flags
// PROOF
#[kani::proof]
fn clause_arena_learned_bit_independent() {
    let f: u16 = kani::any();
    let with_learned = f | LEARNED_BIT;
    let without_learned = f & !LEARNED_BIT;

    assert!(is_learned(with_learned));
    assert!(!is_learned(without_learned));

    // Garbage bit should be unchanged
    assert_eq!(is_garbage(with_learned), is_garbage(f));
    assert_eq!(is_garbage(without_learned), is_garbage(f));

    // Used count should be unchanged
    assert_eq!(used_count(with_learned), used_count(f));
    assert_eq!(used_count(without_learned), used_count(f));
}

/// Garbage bit is independent of other flags
// PROOF
#[kani::proof]
fn clause_arena_garbage_bit_independent() {
    let f: u16 = kani::any();
    let with_garbage = f | GARBAGE_BIT;
    let without_garbage = f & !GARBAGE_BIT;

    assert!(is_garbage(with_garbage));
    assert!(!is_garbage(without_garbage));

    // Learned bit should be unchanged
    assert_eq!(is_learned(with_garbage), is_learned(f));
    assert_eq!(is_learned(without_garbage), is_learned(f));
}

/// Used count set/get roundtrip: set_used preserves other flag bits
// PROOF
#[kani::proof]
fn clause_arena_used_count_roundtrip() {
    let f: u16 = kani::any();
    let count: u8 = kani::any();
    kani::assume(count <= MAX_USED);

    let updated = set_used(f, count);

    // Used count is correctly stored and retrieved
    assert_eq!(used_count(updated), count);

    // Other flag bits are preserved
    assert_eq!(is_learned(updated), is_learned(f));
    assert_eq!(is_garbage(updated), is_garbage(f));
}

/// Used count clamping: values above MAX_USED are clamped
// PROOF
#[kani::proof]
fn clause_arena_used_count_clamped() {
    let f: u16 = kani::any();
    let count: u8 = kani::any();
    kani::assume(count > MAX_USED);

    let updated = set_used(f, count);
    assert_eq!(used_count(updated), MAX_USED);
}

/// Header word 2 roundtrip: refcount and flags pack/unpack correctly
// PROOF
#[kani::proof]
fn clause_arena_header2_roundtrip() {
    let rc: u16 = kani::any();
    let f: u16 = kani::any();

    let header2 = make_header2(rc, f);

    assert_eq!(refcount(header2), rc);
    assert_eq!(flags(header2), f);
}

/// Stride computation: stride = HEADER_WORDS + lit_count
// PROOF
#[kani::proof]
fn clause_arena_stride_correct() {
    let n: u16 = kani::any();
    kani::assume(n > 0); // clauses are never empty
    kani::assume(n <= 1000); // reasonable bound

    let header0 = n as u32;
    assert_eq!(stride(header0), HEADER_WORDS + n as usize);
    assert_eq!(lit_count(header0), n);
}

/// Stride is always > HEADER_WORDS (clauses always have at least 1 literal)
// PROOF
#[kani::proof]
fn clause_arena_stride_minimum() {
    let n: u16 = kani::any();
    kani::assume(n >= 1);

    let header0 = n as u32;
    assert!(stride(header0) > HEADER_WORDS);
}

/// Flag bits are disjoint: learned, garbage, and used count don't overlap
// PROOF
#[kani::proof]
fn clause_arena_flag_bits_disjoint() {
    // These masks must not overlap
    assert_eq!(LEARNED_BIT & GARBAGE_BIT, 0);
    assert_eq!(LEARNED_BIT & USED_MASK, 0);
    assert_eq!(GARBAGE_BIT & USED_MASK, 0);

    // Setting one flag doesn't affect the others
    let f: u16 = 0;
    let with_all = f | LEARNED_BIT | GARBAGE_BIT | set_used(0, MAX_USED);
    assert!(is_learned(with_all));
    assert!(is_garbage(with_all));
    assert_eq!(used_count(with_all), MAX_USED);
}
