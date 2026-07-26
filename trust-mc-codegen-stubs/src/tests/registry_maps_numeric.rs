// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Full-pipeline lookup() coverage for HashMap, BTreeMap, TrustMcMap, BigInt,
// BigRational, and primitive-trait override routing.

use super::{StubKind, lookup};

#[test]
fn lookup_hashmap_core_operations() {
    assert_eq!(lookup("std::collections::HashMap::<u8, u8>::new"), Some(StubKind::HashMapNew));
    assert_eq!(
        lookup("std::collections::HashMap::<u8, u8>::insert"),
        Some(StubKind::HashMapInsert)
    );
    assert_eq!(lookup("std::collections::HashMap::<u8, u8>::get"), Some(StubKind::HashMapGet));
    assert_eq!(
        lookup("std::collections::HashMap::<u8, u8>::get_mut"),
        Some(StubKind::HashMapGetMut)
    );
    assert_eq!(
        lookup("std::collections::HashMap::<u8, u8>::contains_key"),
        Some(StubKind::HashMapContainsKey)
    );
    assert_eq!(
        lookup("std::collections::HashMap::<u8, u8>::remove"),
        Some(StubKind::HashMapRemove)
    );
    assert_eq!(lookup("std::collections::HashMap::<u8, u8>::len"), Some(StubKind::HashMapLen));
    assert_eq!(
        lookup("std::collections::HashMap::<u8, u8>::is_empty"),
        Some(StubKind::HashMapIsEmpty)
    );
    assert_eq!(lookup("std::collections::HashMap::<u8, u8>::clear"), Some(StubKind::HashMapClear));
    assert_eq!(
        lookup("<std::collections::HashMap<u8, u8> as core::clone::Clone>::clone"),
        Some(StubKind::HashMapClone)
    );
    assert_eq!(
        lookup("<std::collections::HashMap<K, V, S> as std::ops::Drop>::drop"),
        Some(StubKind::HashMapDrop)
    );
    // hashbrown internals are NOT stubbed (we stub HashMap/TrustMcMap at a higher level)
    assert_eq!(lookup("hashbrown::RawTable::<u8>::get"), None);
}

#[test]
fn lookup_hashmap_iterator_operations() {
    assert_eq!(
        lookup("<std::collections::HashMap<u8, u8> as core::iter::IntoIterator>::into_iter"),
        Some(StubKind::HashMapIntoIter)
    );
    assert_eq!(lookup("std::collections::HashMap::<u8, u8>::iter"), Some(StubKind::HashMapIter));
    assert_eq!(lookup("std::collections::HashMap::<u8, u8>::keys"), Some(StubKind::HashMapKeys));
    assert_eq!(
        lookup("std::collections::HashMap::<u8, u8>::values"),
        Some(StubKind::HashMapValues)
    );
    // values_mut must NOT match values
    assert_eq!(lookup("std::collections::HashMap::<u8, u8>::values_mut"), None);
}

#[test]
fn lookup_trust_mcmap_all_operations() {
    assert_eq!(
        lookup("trust_mc::collections::TrustMcMap::<u8, u8>::new"),
        Some(StubKind::TrustMcMapNew)
    );
    assert_eq!(
        lookup("trust_mc::collections::TrustMcMap::<u8, u8>::insert"),
        Some(StubKind::TrustMcMapInsert)
    );
    assert_eq!(
        lookup("trust_mc::collections::TrustMcMap::<u8, u8>::get"),
        Some(StubKind::TrustMcMapGet)
    );
    assert_eq!(
        lookup("trust_mc::collections::TrustMcMap::<u8, u8>::contains_key"),
        Some(StubKind::TrustMcMapContainsKey)
    );
    assert_eq!(
        lookup("trust_mc::collections::TrustMcMap::<u8, u8>::remove"),
        Some(StubKind::TrustMcMapRemove)
    );
    assert_eq!(
        lookup("trust_mc::collections::TrustMcMap::<u8, u8>::len"),
        Some(StubKind::TrustMcMapLen)
    );
    assert_eq!(
        lookup("trust_mc::collections::TrustMcMap::<u8, u8>::is_empty"),
        Some(StubKind::TrustMcMapIsEmpty)
    );
    assert_eq!(
        lookup("trust_mc::collections::TrustMcMap::<u8, u8>::clear"),
        Some(StubKind::TrustMcMapClear)
    );
    assert_eq!(
        lookup("trust_mc::collections::TrustMcMap::<u8, u8>::clone"),
        Some(StubKind::TrustMcMapClone)
    );
    assert_eq!(
        lookup(
            "<trust_mc::collections::TrustMcMap<u8, u8> as core::iter::IntoIterator>::into_iter"
        ),
        Some(StubKind::TrustMcMapIntoIter)
    );
    assert_eq!(
        lookup("trust_mc::collections::TrustMcMapIntoIter::<u8, u8>::next"),
        Some(StubKind::TrustMcMapIterNext)
    );
}

#[test]
fn lookup_bigint_arithmetic() {
    assert_eq!(lookup("<num_bigint::BigInt as core::ops::Add>::add"), Some(StubKind::BigIntAdd));
    assert_eq!(lookup("<num_bigint::BigInt as core::ops::Sub>::sub"), Some(StubKind::BigIntSub));
    assert_eq!(lookup("<num_bigint::BigInt as core::ops::Mul>::mul"), Some(StubKind::BigIntMul));
    assert_eq!(lookup("<num_bigint::BigInt as core::ops::Div>::div"), Some(StubKind::BigIntDiv));
    assert_eq!(lookup("<num_bigint::BigInt as core::ops::Rem>::rem"), Some(StubKind::BigIntRem));
    assert_eq!(lookup("<num_bigint::BigInt as core::ops::Neg>::neg"), Some(StubKind::BigIntNeg));
    assert_eq!(
        lookup("<num_bigint::BigInt as num_traits::sign::Signed>::abs"),
        Some(StubKind::BigIntAbs)
    );
}

#[test]
fn lookup_bigint_assign_ops() {
    assert_eq!(
        lookup("<num_bigint::BigInt as core::ops::AddAssign>::add_assign"),
        Some(StubKind::BigIntAddAssign)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as core::ops::SubAssign>::sub_assign"),
        Some(StubKind::BigIntSubAssign)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as core::ops::MulAssign>::mul_assign"),
        Some(StubKind::BigIntMulAssign)
    );
}

#[test]
fn lookup_bigint_comparisons() {
    assert_eq!(
        lookup("<num_bigint::BigInt as core::cmp::PartialEq>::eq"),
        Some(StubKind::BigIntEq)
    );
    assert_eq!(lookup("<num_bigint::BigInt as core::cmp::Ord>::cmp"), Some(StubKind::BigIntCmp));
    assert_eq!(
        lookup("<num_bigint::BigInt as core::cmp::PartialOrd>::partial_cmp"),
        Some(StubKind::BigIntPartialCmp)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as core::cmp::PartialOrd>::lt"),
        Some(StubKind::BigIntLt)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as core::cmp::PartialOrd>::le"),
        Some(StubKind::BigIntLe)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as core::cmp::PartialOrd>::gt"),
        Some(StubKind::BigIntGt)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as core::cmp::PartialOrd>::ge"),
        Some(StubKind::BigIntGe)
    );
}

#[test]
fn lookup_bigint_constructors_and_predicates() {
    assert_eq!(
        lookup("<num_bigint::BigInt as core::convert::From<i64>>::from"),
        Some(StubKind::BigIntFrom)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as num_traits::identities::One>::one"),
        Some(StubKind::BigIntOne)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as num_traits::identities::Zero>::zero"),
        Some(StubKind::BigIntZero)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as num_traits::identities::Zero>::is_zero"),
        Some(StubKind::BigIntIsZero)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as num_traits::sign::Signed>::is_negative"),
        Some(StubKind::BigIntIsNegative)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as core::clone::Clone>::clone"),
        Some(StubKind::BigIntClone)
    );
}

#[test]
fn lookup_bigint_bitwise_and_shift() {
    assert_eq!(lookup("<num_bigint::BigInt as core::ops::Shl>::shl"), Some(StubKind::BigIntShl));
    assert_eq!(lookup("<num_bigint::BigInt as core::ops::Shr>::shr"), Some(StubKind::BigIntShr));
    assert_eq!(
        lookup("<num_bigint::BigInt as core::ops::ShlAssign>::shl_assign"),
        Some(StubKind::BigIntShlAssign)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as core::ops::ShrAssign>::shr_assign"),
        Some(StubKind::BigIntShrAssign)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as core::ops::BitAnd>::bitand"),
        Some(StubKind::BigIntBitAnd)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as core::ops::BitOr>::bitor"),
        Some(StubKind::BigIntBitOr)
    );
    assert_eq!(
        lookup("<num_bigint::BigInt as core::ops::BitXor>::bitxor"),
        Some(StubKind::BigIntBitXor)
    );
}

/// Part of #3687: MIR paths use `<impl Trait for Type>` format instead of
/// `<Type as Trait>`. The trait_guard must match both formats.
#[test]
fn lookup_bigint_mir_format_paths() {
    // MIR format: `module::<impl Trait for Type>::method`
    assert_eq!(
        lookup(
            "num_bigint::bigint::multiplication::<impl std::ops::MulAssign for num_bigint::BigInt>::mul_assign"
        ),
        Some(StubKind::BigIntMulAssign)
    );
    assert_eq!(
        lookup("num_bigint::bigint::addition::<impl std::ops::Add for num_bigint::BigInt>::add"),
        Some(StubKind::BigIntAdd)
    );
    assert_eq!(
        lookup("num_bigint::bigint::subtraction::<impl std::ops::Sub for num_bigint::BigInt>::sub"),
        Some(StubKind::BigIntSub)
    );
    assert_eq!(
        lookup(
            "num_bigint::bigint::multiplication::<impl std::ops::Mul for num_bigint::BigInt>::mul"
        ),
        Some(StubKind::BigIntMul)
    );
    // MIR format with generic type arg: `<impl Trait<T> for Type>`
    assert_eq!(
        lookup(
            "num_bigint::bigint::multiplication::<impl std::ops::Mul<i32> for num_bigint::BigInt>::mul"
        ),
        Some(StubKind::BigIntMul)
    );
    assert_eq!(
        lookup(
            "num_bigint::bigint::addition::<impl std::ops::AddAssign<&num_bigint::BigInt> for num_bigint::BigInt>::add_assign"
        ),
        Some(StubKind::BigIntAddAssign)
    );
}

#[test]
fn lookup_bigrational_arithmetic() {
    assert_eq!(
        lookup("<num_rational::BigRational as core::ops::Add>::add"),
        Some(StubKind::BigRationalAdd)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::ops::Sub>::sub"),
        Some(StubKind::BigRationalSub)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::ops::Mul>::mul"),
        Some(StubKind::BigRationalMul)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::ops::Div>::div"),
        Some(StubKind::BigRationalDiv)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::ops::Neg>::neg"),
        Some(StubKind::BigRationalNeg)
    );
}

#[test]
fn lookup_bigrational_comparisons() {
    assert_eq!(
        lookup("<num_rational::BigRational as core::cmp::PartialEq>::eq"),
        Some(StubKind::BigRationalEq)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::cmp::PartialOrd>::lt"),
        Some(StubKind::BigRationalLt)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::cmp::PartialOrd>::le"),
        Some(StubKind::BigRationalLe)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::cmp::PartialOrd>::gt"),
        Some(StubKind::BigRationalGt)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::cmp::PartialOrd>::ge"),
        Some(StubKind::BigRationalGe)
    );
}

#[test]
fn lookup_bigrational_constructors_and_clone() {
    assert_eq!(
        lookup("num_rational::Rational::<num_bigint::BigInt>::new"),
        Some(StubKind::BigRationalNew)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::convert::From<num_bigint::BigInt>>::from"),
        Some(StubKind::BigRationalFrom)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::clone::Clone>::clone"),
        Some(StubKind::BigRationalClone)
    );
}

#[test]
fn lookup_bigrational_assign_ops() {
    assert_eq!(
        lookup("<num_rational::BigRational as core::ops::AddAssign>::add_assign"),
        Some(StubKind::BigRationalAddAssign)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::ops::SubAssign>::sub_assign"),
        Some(StubKind::BigRationalSubAssign)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::ops::MulAssign>::mul_assign"),
        Some(StubKind::BigRationalMulAssign)
    );
    assert_eq!(
        lookup("<num_rational::BigRational as core::ops::DivAssign>::div_assign"),
        Some(StubKind::BigRationalDivAssign)
    );
}

/// Part of #3850: bare user-defined `Rational` paths must NOT match BigRational stubs.
///
/// The BigRational category guard in `category_table.rs:241-252` requires one of
/// `BigRational`, `num_rational`, or `Ratio<...BigInt` in the path. Bare `Rational`
/// (e.g., a user-defined struct) must not be intercepted, as that forces locals into
/// `Sort::real()` and causes the `coerce_store_value` Real→BV128 warning (#3850).
///
/// Positive controls verify real BigRational paths still resolve correctly.
#[test]
fn lookup_bare_rational_does_not_match_bigrational() {
    // Negative: bare user-defined Rational methods must return None
    assert_eq!(lookup("Rational::add"), None);
    assert_eq!(lookup("Rational::is_zero"), None);
    assert_eq!(lookup("Rational::zero"), None);
    assert_eq!(lookup("Rational::from_i64"), None);
    assert_eq!(lookup("Rational::new"), None);
    assert_eq!(lookup("Rational::sub"), None);
    assert_eq!(lookup("Rational::mul"), None);
    // Trait-impl paths with bare Rational: Add/Sub/Mul should NOT match BigRational stubs.
    // Note: PartialEq::eq matches PrimitivePartialEqEq (not BigRational) — that's correct.
    assert_eq!(lookup("<Rational as core::ops::Add>::add"), None);
    assert_eq!(lookup("<Rational as core::ops::Sub>::sub"), None);
    assert_eq!(lookup("<Rational as core::ops::Mul>::mul"), None);

    // Positive controls: real BigRational paths still resolve
    assert_eq!(
        lookup("<num_rational::BigRational as core::ops::Add>::add"),
        Some(StubKind::BigRationalAdd)
    );
    assert_eq!(
        lookup("num_rational::Rational::<num_bigint::BigInt>::new"),
        Some(StubKind::BigRationalNew)
    );
}

#[test]
fn lookup_primitive_trait_overrides() {
    assert_eq!(lookup("<u32 as core::cmp::PartialEq>::eq"), Some(StubKind::PrimitivePartialEqEq));
    assert_eq!(lookup("<u32 as core::cmp::PartialEq>::ne"), Some(StubKind::PrimitivePartialEqNe));
    assert_eq!(
        lookup("<std::ptr::NonNull<u8> as std::cmp::PartialEq>::eq"),
        Some(StubKind::PrimitivePartialEqEq)
    );
    assert_eq!(
        lookup("<std::ptr::NonNull<u8> as std::cmp::PartialEq>::ne"),
        Some(StubKind::PrimitivePartialEqNe)
    );
    // PartialOrd comparisons for primitives
    assert_eq!(lookup("<i32 as core::cmp::PartialOrd>::lt"), Some(StubKind::PrimitivePartialOrdLt));
    assert_eq!(lookup("<i32 as core::cmp::PartialOrd>::le"), Some(StubKind::PrimitivePartialOrdLe));
    assert_eq!(lookup("<u64 as core::cmp::PartialOrd>::gt"), Some(StubKind::PrimitivePartialOrdGt));
    assert_eq!(lookup("<u64 as core::cmp::PartialOrd>::ge"), Some(StubKind::PrimitivePartialOrdGe));
    // Ord::cmp
    assert_eq!(lookup("core::cmp::Ord::cmp"), Some(StubKind::OrdCmp));
    // Clone for primitives
    assert_eq!(lookup("<bool as core::clone::Clone>::clone"), Some(StubKind::PrimitiveClone));
    assert_eq!(lookup("<u8 as core::clone::Clone>::clone"), Some(StubKind::PrimitiveClone));
}
