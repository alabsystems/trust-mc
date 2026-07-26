// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::safety_checks::shuffle_index_in_bounds_condition;
use super::*;
use ay_bindings::ExprValue;

fn store_chain_base_and_len(expr: &Expr) -> (&Expr, usize) {
    let mut base = expr;
    let mut len = 0;
    while let ExprValue::Store { array, .. } = base.value() {
        base = array;
        len += 1;
    }
    (base, len)
}

#[test]
fn test_elementwise_binop_uses_neutral_const_array_base() {
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8));
    let lhs = Expr::var("lhs", arr_sort.clone());
    let rhs = Expr::var("rhs", arr_sort);
    let layout = SimdLayoutInfo { lane_count: 2, elem_width: 8, is_signed: true, is_float: false };

    let result = build_elementwise_result(None, &lhs, &rhs, &layout, SimdIntrinsicKind::Add)
        .expect("integer-lane build must encode soundly");
    let (base, store_count) = store_chain_base_and_len(&result);

    assert_eq!(store_count, 2);
    let ExprValue::ConstArray { value, .. } = base.value() else {
        panic!("SIMD all-lane binop should be rooted at const_array, got {base}");
    };
    assert!(matches!(
        value.value(),
        ExprValue::BitVecConst { value, width } if *width == 8 && value.to_string() == "0"
    ));
}

#[test]
fn test_shuffle_index_in_bounds_is_unsigned_upper_bound() {
    // A u32 shuffle selector against a combined length of 4 must yield the
    // predicate `sel <u 4` (bvult against a same-width bound constant), the
    // exact in-bounds condition whose negation drives the out-of-bounds UB
    // error rule. At solve time a concrete out-of-range index (e.g. 4) makes
    // `4 <u 4` false, so `error` is reachable and the harness fails.
    let sel = Expr::var("sel", Sort::bitvec(32));
    let cond = shuffle_index_in_bounds_condition(&sel, 4).expect("bitvec selector must build");
    let ExprValue::BvULt(lo, hi) = cond.value() else {
        panic!("shuffle bound should be an unsigned-less-than, got {cond}");
    };
    assert_eq!(lo.sort().bitvec_width(), Some(32), "compare in selector width");
    assert!(
        matches!(
            hi.value(),
            ExprValue::BitVecConst { value, width } if *width == 32 && value.to_string() == "4"
        ),
        "bound constant should be combined_len (4) at selector width, got {hi}",
    );
}

#[test]
fn test_shuffle_index_in_bounds_requires_bitvec_selector() {
    // A non-bit-vector selector (should never occur for a well-typed shuffle
    // index array) yields None rather than a malformed predicate.
    let sel = Expr::bool_const(true);
    assert!(shuffle_index_in_bounds_condition(&sel, 4).is_none());
}

#[test]
fn test_insert_result_writes_all_finite_lanes() {
    let arr_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(64));
    let lanes = Expr::var("lanes", arr_sort);
    let idx = Expr::bitvec_const(0u64, POINTER_WIDTH);
    let value = Expr::bitvec_const(7u64, 64);
    let layout = SimdLayoutInfo { lane_count: 2, elem_width: 64, is_signed: true, is_float: false };

    let result = build_insert_result(&lanes, &idx, &value, &layout);
    let (base, store_count) = store_chain_base_and_len(&result);

    assert_eq!(store_count, 2, "insert should materialize every finite SIMD lane");
    assert!(
        matches!(base.value(), ExprValue::ConstArray { .. }),
        "insert result should not depend on the infinite source-array background",
    );
    assert!(
        format!("{result:?}").contains("Select"),
        "non-inserted lanes should preserve source lanes",
    );
}
