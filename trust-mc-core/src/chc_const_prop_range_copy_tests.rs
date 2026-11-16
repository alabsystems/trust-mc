// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Pointwise range-copy laws after proven scalar constants reach its bounds.

use super::{Expr, HashMap, Sort, substitute_vars};

fn bv(value: u64) -> Expr {
    Expr::bitvec_const(value, 64)
}

fn value_at(array: &Expr, index: u64) -> Expr {
    // An unrelated constant keeps the normal expression-folding entry point
    // active; it supplies no facts about the source/destination arrays.
    let facts = HashMap::from([("unrelated".to_string(), bv(0))]);
    substitute_vars(&array.clone().select(bv(index)), &facts)
}

fn array(values: &[(u64, u64)], default: u64) -> Expr {
    let mut result = Expr::const_array(Sort::bitvec(64), bv(default));
    for &(index, value) in values {
        result = result.store(bv(index), bv(value));
    }
    result
}

#[test]
fn range_copy_proven_small_bounds_preserve_prefix_suffix_and_source_snapshot() {
    let source = array(&[(0, 10), (1, 20), (2, 30), (3, 40)], 99);
    // Deliberate overlap: every moved value comes from the original source,
    // including when dst and src are the same expression.
    let copy = source
        .clone()
        .try_array_range_copy(
            source,
            Expr::var("low", Sort::bitvec(64)),
            Expr::var("high", Sort::bitvec(64)),
            bv(0),
        )
        .unwrap();
    let folded = substitute_vars(
        &copy,
        &HashMap::from([("low".to_string(), bv(1)), ("high".to_string(), bv(4))]),
    );
    for (index, expected) in [10, 10, 20, 30, 99, 99].into_iter().enumerate() {
        assert_eq!(value_at(&folded, index as u64), bv(expected));
    }
    assert!(!folded.to_string().contains("(lambda "));
}

#[test]
fn range_copy_empty_unsigned_intervals_are_identity_and_source_offsets_wrap() {
    let dst = array(&[], 7);
    let src = array(&[(u64::MAX, 12), (0, 13)], 99);
    let facts = HashMap::from([("low".to_string(), bv(2))]);
    for high in [0, 2] {
        let copy = dst
            .clone()
            .try_array_range_copy(src.clone(), Expr::var("low", Sort::bitvec(64)), bv(high), bv(0))
            .unwrap();
        assert_eq!(substitute_vars(&copy, &facts), dst);
    }
    let copy = dst
        .try_array_range_copy(src, Expr::var("low", Sort::bitvec(64)), bv(4), bv(u64::MAX))
        .unwrap();
    let folded = substitute_vars(&copy, &facts);
    for (index, expected) in [(1, 7), (2, 12), (3, 13), (4, 7)] {
        assert_eq!(value_at(&folded, index), bv(expected));
    }
}

#[test]
fn range_copy_unknown_and_large_bounds_keep_the_complete_expression() {
    let dst = array(&[], 7);
    let src = array(&[], 9);
    let copy = dst
        .clone()
        .try_array_range_copy(src.clone(), bv(0), Expr::var("high", Sort::bitvec(64)), bv(0))
        .unwrap();
    let unknown = substitute_vars(&copy, &HashMap::from([("unrelated".to_string(), bv(0))]));
    assert_eq!(unknown, copy);
    let large = substitute_vars(&copy, &HashMap::from([("high".to_string(), bv(65))]));
    assert_eq!(large, dst.try_array_range_copy(src, bv(0), bv(65), bv(0)).unwrap());
}

#[test]
fn range_copy_cross_sort_facts_preserve_the_original_well_typed_term() {
    let arr = Sort::array(Sort::bitvec(64), Sort::bitvec(64));
    let dst = Expr::var("dst", arr.clone());
    let src = Expr::var("src", arr);
    let start = Expr::var("start", Sort::bitvec(64));
    let copy = dst.try_array_range_copy(src, bv(2), bv(4), start).unwrap();
    for (name, value) in [
        ("start", Expr::bitvec_const(0u32, 32)),
        ("dst", Expr::bool_const(false)),
        ("src", Expr::const_array(Sort::bitvec(32), bv(0))),
    ] {
        assert_eq!(substitute_vars(&copy, &HashMap::from([(name.to_string(), value)])), copy);
    }
    let symbolic = array(&[], 1)
        .try_array_range_copy(array(&[], 2), bv(2), Expr::var("high", Sort::bitvec(64)), bv(0))
        .unwrap();
    assert_eq!(
        substitute_vars(
            &symbolic,
            &HashMap::from([("high".to_string(), Expr::bitvec_const(9u32, 32)),])
        ),
        symbolic
    );
}
