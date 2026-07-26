// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// extract_method_name and is_primitive_trait_path edge cases.

use super::StubRegistry;

// =============================================================================
// extract_method_name: edge cases (Part of #2016)
// =============================================================================

#[test]
fn extract_method_name_generic_impl_pattern() {
    // `>::method` pattern (generic impl)
    assert_eq!(StubRegistry::extract_method_name("<Vec<u32> as Clone>::clone"), Some("clone"));
}

#[test]
fn extract_method_name_direct_impl_pattern() {
    // `::method` pattern (direct impl)
    assert_eq!(StubRegistry::extract_method_name("std::vec::Vec::<u32>::push"), Some("push"));
}

#[test]
fn extract_method_name_no_separator() {
    // No `::` at all — returns None
    assert_eq!(StubRegistry::extract_method_name("standalone_fn"), None);
}

#[test]
fn extract_method_name_prefers_generic_over_direct() {
    // Path with both `>::` and `::` — should prefer `>::` (checked first)
    assert_eq!(
        StubRegistry::extract_method_name("<alloc::string::String as core::fmt::Display>::fmt"),
        Some("fmt")
    );
}

#[test]
fn extract_method_name_nested_generics() {
    // Deeply nested generics: `HashMap<K, Vec<V>>::get`
    assert_eq!(
        StubRegistry::extract_method_name("std::collections::HashMap::<u32, Vec<u32>>::get"),
        Some("get")
    );
}

// =============================================================================
// is_primitive_trait_path: edge cases (Part of #2016)
// =============================================================================

#[test]
fn is_primitive_trait_path_accepts_primitive_eq() {
    assert!(StubRegistry::is_primitive_trait_path("<u32 as PartialEq>::eq"));
    assert!(StubRegistry::is_primitive_trait_path("<i64 as PartialEq>::ne"));
}

#[test]
fn is_primitive_trait_path_accepts_primitive_ord() {
    assert!(StubRegistry::is_primitive_trait_path("<u32 as PartialOrd>::lt"));
    assert!(StubRegistry::is_primitive_trait_path("<i32 as PartialOrd>::ge"));
}

#[test]
fn is_primitive_trait_path_accepts_clone() {
    assert!(StubRegistry::is_primitive_trait_path("<bool as Clone>::clone"));
}

#[test]
fn is_primitive_trait_path_accepts_ord_cmp() {
    // `::Ord` must match, but not `Ordering` or `Record`
    assert!(StubRegistry::is_primitive_trait_path("<u32 as core::cmp::Ord>::cmp"));
}

#[test]
fn is_primitive_trait_path_rejects_bigint() {
    // BigInt has custom impls — must not use primitive stubs
    assert!(!StubRegistry::is_primitive_trait_path("<num_bigint::BigInt as PartialEq>::eq"));
    assert!(!StubRegistry::is_primitive_trait_path("<BigInt as core::ops::Add>::add"));
}

#[test]
fn is_primitive_trait_path_rejects_collections() {
    assert!(!StubRegistry::is_primitive_trait_path("<HashMap<u32, u32> as Clone>::clone"));
    assert!(!StubRegistry::is_primitive_trait_path("<Vec<u32> as PartialEq>::eq"));
    assert!(!StubRegistry::is_primitive_trait_path("<BTreeSet<u32> as Clone>::clone"));
    assert!(!StubRegistry::is_primitive_trait_path("<String as PartialEq>::eq"));
    assert!(!StubRegistry::is_primitive_trait_path("<&str as core::cmp::PartialEq>::eq"));
}

#[test]
fn is_primitive_trait_path_rejects_non_trait_methods() {
    // Methods that aren't in the trait list
    assert!(!StubRegistry::is_primitive_trait_path("<u32>::max_value"));
    assert!(!StubRegistry::is_primitive_trait_path("std::u32::pow"));
}

#[test]
fn is_primitive_trait_path_rejects_tuples() {
    // Tuples have derived PartialEq that requires structural decomposition (#3786).
    assert!(!StubRegistry::is_primitive_trait_path("<(u8, bool) as PartialEq>::eq"));
    assert!(!StubRegistry::is_primitive_trait_path("<(u8, u8) as PartialEq<(u8, u8)>>::eq"));
    assert!(!StubRegistry::is_primitive_trait_path("<(i32, i32, i32) as PartialEq>::eq"));
    assert!(!StubRegistry::is_primitive_trait_path(
        "core::tuple::<impl std::cmp::PartialEq for (U, T)>::eq"
    ));
    assert!(!StubRegistry::is_primitive_trait_path(
        "core::tuple::<impl std::cmp::PartialOrd for (U, T)>::lt"
    ));
    assert!(!StubRegistry::is_primitive_trait_path(
        "core::tuple::<impl std::clone::Clone for (A, B)>::clone"
    ));
    assert!(!StubRegistry::is_primitive_trait_path("<(u8, bool) as PartialOrd>::lt"));
    assert!(!StubRegistry::is_primitive_trait_path("<(u8, bool) as Clone>::clone"));
}

#[test]
fn is_primitive_trait_path_rejects_no_separator() {
    assert!(!StubRegistry::is_primitive_trait_path("standalone_fn"));
}
