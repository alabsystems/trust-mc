// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Direct suffix tests for HashMap, TrustMcMap, BigInt, BigRational,
// and primitive trait lookup.

use super::{StubKind, StubRegistry};

// -- lookup_hashmap_suffix --

#[test]
fn hashmap_suffix_with_hasher_routes_to_new() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix(
            "std::collections::HashMap::<u32, u32, RandomState>::with_hasher"
        ),
        Some(StubKind::HashMapNew)
    );
}

#[test]
fn hashmap_suffix_with_capacity_routes_to_new() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::HashMap::<u32, u32>::with_capacity"),
        Some(StubKind::HashMapNew)
    );
}

#[test]
fn hashmap_suffix_default_routes_to_new() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix(
            "<std::collections::HashMap<u32, u32> as Default>::default"
        ),
        Some(StubKind::HashMapNew)
    );
}

#[test]
fn hashmap_suffix_unknown_method_returns_none() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::HashMap::<u32, u32>::drain"),
        None
    );
}

#[test]
fn hashmap_suffix_clone_requires_hashmap_in_path() {
    // Clone on a nested type inside HashMap should not match
    assert_eq!(StubRegistry::lookup_hashmap_suffix("SomeStruct::clone"), None);
}

#[test]
fn hashmap_suffix_btreemap_insert_returns_btreemap_variant() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::BTreeMap::<u32, u32>::insert"),
        Some(StubKind::BTreeMapInsert)
    );
}

#[test]
fn hashmap_suffix_btreemap_get_returns_btreemap_variant() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::BTreeMap::<u32, u32>::get"),
        Some(StubKind::BTreeMapGet)
    );
}

#[test]
fn hashmap_suffix_btreemap_get_mut_returns_btreemap_variant() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::BTreeMap::<u32, u32>::get_mut"),
        Some(StubKind::BTreeMapGetMut)
    );
}

#[test]
fn hashmap_suffix_btreemap_contains_key_returns_btreemap_variant() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::BTreeMap::<u32, u32>::contains_key"),
        Some(StubKind::BTreeMapContainsKey)
    );
}

#[test]
fn hashmap_suffix_btreemap_remove_returns_btreemap_variant() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::BTreeMap::<u32, u32>::remove"),
        Some(StubKind::BTreeMapRemove)
    );
}

#[test]
fn hashmap_suffix_btreemap_len_returns_btreemap_variant() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::BTreeMap::<u32, u32>::len"),
        Some(StubKind::BTreeMapLen)
    );
}

#[test]
fn hashmap_suffix_btreemap_is_empty_returns_btreemap_variant() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::BTreeMap::<u32, u32>::is_empty"),
        Some(StubKind::BTreeMapIsEmpty)
    );
}

#[test]
fn hashmap_suffix_btreemap_clear_returns_btreemap_variant() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::BTreeMap::<u32, u32>::clear"),
        Some(StubKind::BTreeMapClear)
    );
}

#[test]
fn hashmap_suffix_btreemap_clone_returns_btreemap_variant() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix(
            "<std::collections::BTreeMap<u32, u32> as Clone>::clone"
        ),
        Some(StubKind::BTreeMapClone)
    );
}

#[test]
fn hashmap_suffix_btreemap_drop_routes_to_shared_drop() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix(
            "<std::collections::BTreeMap<K, V, A> as std::ops::Drop>::drop"
        ),
        Some(StubKind::HashMapDrop)
    );
}

#[test]
fn hashmap_suffix_into_iter_shared_between_map_types() {
    // into_iter uses shared StubKind::HashMapIntoIter regardless of map type
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix(
            "<std::collections::HashMap<u32, u32> as IntoIterator>::into_iter"
        ),
        Some(StubKind::HashMapIntoIter)
    );
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix(
            "<std::collections::BTreeMap<u32, u32> as IntoIterator>::into_iter"
        ),
        Some(StubKind::HashMapIntoIter)
    );
}

#[test]
fn hashmap_suffix_iter_excludes_into_iter() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::HashMap::<u32, u32>::iter"),
        Some(StubKind::HashMapIter)
    );
    // into_iter path should NOT match iter
    assert_ne!(
        StubRegistry::lookup_hashmap_suffix("<HashMap<u32, u32> as IntoIterator>::into_iter"),
        Some(StubKind::HashMapIter)
    );
}

#[test]
fn hashmap_suffix_values_excludes_values_mut() {
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::HashMap::<u32, u32>::values"),
        Some(StubKind::HashMapValues)
    );
    assert_eq!(
        StubRegistry::lookup_hashmap_suffix("std::collections::HashMap::<u32, u32>::values_mut"),
        None
    );
}

#[test]
fn hashmap_suffix_no_method_returns_none() {
    assert_eq!(StubRegistry::lookup_hashmap_suffix("HashMap"), None);
}

// -- lookup_trust_mcmap_suffix --

#[test]
fn trust_mcmap_suffix_all_operations() {
    let cases = vec![
        ("trust_mc::collections::TrustMcMap::<K, V>::new", StubKind::TrustMcMapNew),
        ("<TrustMcMap<K, V> as Default>::default", StubKind::TrustMcMapNew),
        ("trust_mc::collections::TrustMcMap::<K, V>::insert", StubKind::TrustMcMapInsert),
        ("trust_mc::collections::TrustMcMap::<K, V>::get", StubKind::TrustMcMapGet),
        (
            "trust_mc::collections::TrustMcMap::<K, V>::contains_key",
            StubKind::TrustMcMapContainsKey,
        ),
        ("trust_mc::collections::TrustMcMap::<K, V>::remove", StubKind::TrustMcMapRemove),
        ("trust_mc::collections::TrustMcMap::<K, V>::len", StubKind::TrustMcMapLen),
        ("trust_mc::collections::TrustMcMap::<K, V>::is_empty", StubKind::TrustMcMapIsEmpty),
        ("trust_mc::collections::TrustMcMap::<K, V>::clear", StubKind::TrustMcMapClear),
        ("trust_mc::collections::TrustMcMap::<K, V>::clone", StubKind::TrustMcMapClone),
        ("<TrustMcMap<K, V> as IntoIterator>::into_iter", StubKind::TrustMcMapIntoIter),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_trust_mcmap_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn trust_mcmap_suffix_iter_next_requires_trust_mcmapintoiter() {
    assert_eq!(
        StubRegistry::lookup_trust_mcmap_suffix(
            "trust_mc::collections::TrustMcMapIntoIter::<K, V>::next"
        ),
        Some(StubKind::TrustMcMapIterNext)
    );
    // Generic next without TrustMcMapIntoIter should not match
    assert_eq!(
        StubRegistry::lookup_trust_mcmap_suffix("trust_mc::collections::TrustMcMap::<K, V>::next"),
        None
    );
}

#[test]
fn trust_mcmap_suffix_unknown_returns_none() {
    assert_eq!(
        StubRegistry::lookup_trust_mcmap_suffix("trust_mc::collections::TrustMcMap::<K, V>::drain"),
        None
    );
}

// -- lookup_bigint_suffix --

#[test]
fn bigint_suffix_shift_and_bitwise_all_variants() {
    let cases = vec![
        ("<BigInt as Shl>::shl", StubKind::BigIntShl),
        ("<BigInt as Shr>::shr", StubKind::BigIntShr),
        ("<BigInt as ShlAssign>::shl_assign", StubKind::BigIntShlAssign),
        ("<BigInt as ShrAssign>::shr_assign", StubKind::BigIntShrAssign),
        ("<BigInt as BitAnd>::bitand", StubKind::BigIntBitAnd),
        ("<BigInt as BitOr>::bitor", StubKind::BigIntBitOr),
        ("<BigInt as BitXor>::bitxor", StubKind::BigIntBitXor),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_bigint_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn bigint_suffix_from_requires_from_trait() {
    // "from" without "From" in path should not match
    assert_eq!(StubRegistry::lookup_bigint_suffix("<BigInt as SomeTrait>::from"), None);
    assert_eq!(
        StubRegistry::lookup_bigint_suffix("<BigInt as core::convert::From<i64>>::from"),
        Some(StubKind::BigIntFrom)
    );
}

#[test]
fn bigint_suffix_add_requires_add_trait() {
    // "add" without "Add>" in path should not match
    assert_eq!(StubRegistry::lookup_bigint_suffix("<BigInt as SomeTrait>::add"), None);
}

#[test]
fn bigint_suffix_unknown_method_returns_none() {
    assert_eq!(StubRegistry::lookup_bigint_suffix("<BigInt as Display>::fmt"), None);
}

// -- lookup_bigrational_suffix --

#[test]
fn bigrational_suffix_compound_assign_all_variants() {
    let cases = vec![
        ("<BigRational as AddAssign>::add_assign", StubKind::BigRationalAddAssign),
        ("<BigRational as SubAssign>::sub_assign", StubKind::BigRationalSubAssign),
        ("<BigRational as MulAssign>::mul_assign", StubKind::BigRationalMulAssign),
        ("<BigRational as DivAssign>::div_assign", StubKind::BigRationalDivAssign),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_bigrational_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn bigrational_suffix_new_requires_rational() {
    assert_eq!(
        StubRegistry::lookup_bigrational_suffix("num_rational::Rational::<BigInt>::new"),
        Some(StubKind::BigRationalNew)
    );
    // "new" without "Rational" should not match
    assert_eq!(StubRegistry::lookup_bigrational_suffix("SomeType::new"), None);
}

#[test]
fn bigrational_suffix_from_requires_rational() {
    // BigRational contains "Rational" substring, so lookup matches
    assert_eq!(
        StubRegistry::lookup_bigrational_suffix("<BigRational as From<BigInt>>::from"),
        Some(StubKind::BigRationalFrom)
    );
    // Explicit Rational path also matches
    assert_eq!(
        StubRegistry::lookup_bigrational_suffix("<num_rational::Rational as From<BigInt>>::from"),
        Some(StubKind::BigRationalFrom)
    );
    // Path without Rational should not match
    assert_eq!(StubRegistry::lookup_bigrational_suffix("<SomeType as From<BigInt>>::from"), None);
}

// -- lookup_primitive_trait --

#[test]
fn primitive_trait_all_operations() {
    let cases = vec![
        ("<u32 as PartialEq>::eq", StubKind::PrimitivePartialEqEq),
        ("<u32 as PartialEq>::ne", StubKind::PrimitivePartialEqNe),
        ("<i32 as PartialOrd>::lt", StubKind::PrimitivePartialOrdLt),
        ("<i32 as PartialOrd>::le", StubKind::PrimitivePartialOrdLe),
        ("<i32 as PartialOrd>::gt", StubKind::PrimitivePartialOrdGt),
        ("<i32 as PartialOrd>::ge", StubKind::PrimitivePartialOrdGe),
        ("<bool as Clone>::clone", StubKind::PrimitiveClone),
        ("<u32 as core::cmp::Ord>::cmp", StubKind::OrdCmp),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_primitive_trait(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn primitive_trait_unknown_returns_none() {
    assert_eq!(StubRegistry::lookup_primitive_trait("<u32>::max_value"), None);
}
