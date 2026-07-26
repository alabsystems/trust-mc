// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Direct suffix tests for BTreeSet, HashSet, and BTreeMap internal helpers.

use super::{StubKind, StubRegistry};

// -- lookup_btreeset_suffix --

#[test]
fn btreeset_suffix_all_operations() {
    let cases = vec![
        ("std::collections::BTreeSet::<u32>::new", StubKind::BTreeSetNew),
        ("<BTreeSet<u32> as Default>::default", StubKind::BTreeSetNew),
        ("std::collections::BTreeSet::<u32>::insert", StubKind::BTreeSetInsert),
        ("std::collections::BTreeSet::<u32>::contains", StubKind::BTreeSetContains),
        ("std::collections::BTreeSet::<u32>::remove", StubKind::BTreeSetRemove),
        ("std::collections::BTreeSet::<u32>::len", StubKind::BTreeSetLen),
        ("std::collections::BTreeSet::<u32>::is_empty", StubKind::BTreeSetIsEmpty),
        ("std::collections::BTreeSet::<u32>::clear", StubKind::BTreeSetClear),
        ("<BTreeSet<u32> as Clone>::clone", StubKind::BTreeSetClone),
        ("<BTreeSet<u32> as IntoIterator>::into_iter", StubKind::BTreeSetIntoIter),
        ("std::collections::BTreeSet::<u32>::iter", StubKind::BTreeSetIter),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_btreeset_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn btreeset_suffix_iter_excludes_into_iter() {
    // "iter" method should not match when "into_iter" is in the path
    assert_ne!(
        StubRegistry::lookup_btreeset_suffix("<BTreeSet<u32> as IntoIterator>::into_iter"),
        Some(StubKind::BTreeSetIter)
    );
}

#[test]
fn btreeset_suffix_clone_requires_btreeset() {
    assert_eq!(StubRegistry::lookup_btreeset_suffix("SomeStruct::clone"), None);
}

// -- lookup_hashset_suffix --

#[test]
fn hashset_suffix_all_operations() {
    let cases = vec![
        ("std::collections::HashSet::<u32>::new", StubKind::HashSetNew),
        ("<HashSet<u32> as Default>::default", StubKind::HashSetNew),
        ("std::collections::HashSet::<u32, RandomState>::with_hasher", StubKind::HashSetNew),
        ("std::collections::HashSet::<u32>::with_capacity", StubKind::HashSetNew),
        ("std::collections::HashSet::<u32>::insert", StubKind::HashSetInsert),
        ("std::collections::HashSet::<u32>::contains", StubKind::HashSetContains),
        ("std::collections::HashSet::<u32>::remove", StubKind::HashSetRemove),
        ("std::collections::HashSet::<u32>::len", StubKind::HashSetLen),
        ("std::collections::HashSet::<u32>::is_empty", StubKind::HashSetIsEmpty),
        ("std::collections::HashSet::<u32>::clear", StubKind::HashSetClear),
        ("<HashSet<u32> as Clone>::clone", StubKind::HashSetClone),
        ("<HashSet<u32> as IntoIterator>::into_iter", StubKind::HashSetIntoIter),
        ("std::collections::HashSet::<u32>::iter", StubKind::HashSetIter),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_hashset_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn hashset_suffix_iter_excludes_into_iter() {
    assert_ne!(
        StubRegistry::lookup_hashset_suffix("<HashSet<u32> as IntoIterator>::into_iter"),
        Some(StubKind::HashSetIter)
    );
}

// -- lookup_btreemap_internal_suffix --

#[test]
fn btreemap_internal_entry() {
    assert_eq!(
        StubRegistry::lookup_btreemap_internal_suffix(
            "std::collections::BTreeMap::<u32, ()>::entry"
        ),
        Some(StubKind::BTreeMapEntry)
    );
}

#[test]
fn btreemap_internal_vacant_insert_entry() {
    assert_eq!(
        StubRegistry::lookup_btreemap_internal_suffix(
            "alloc::btree::map::VacantEntry::<u32, ()>::insert_entry"
        ),
        Some(StubKind::BTreeMapVacantInsertEntry)
    );
}

#[test]
fn btreemap_internal_occupied_insert() {
    assert_eq!(
        StubRegistry::lookup_btreemap_internal_suffix(
            "std::btree_map::OccupiedEntry::<u32, ()>::insert"
        ),
        Some(StubKind::BTreeMapOccupiedInsert)
    );
}

#[test]
fn btreemap_internal_occupied_get_mut() {
    assert_eq!(
        StubRegistry::lookup_btreemap_internal_suffix(
            "alloc::btree::map::OccupiedEntry::<u32, ()>::get_mut"
        ),
        Some(StubKind::BTreeMapOccupiedGetMut)
    );
}

#[test]
fn btreemap_internal_occupied_into_mut() {
    assert_eq!(
        StubRegistry::lookup_btreemap_internal_suffix(
            "alloc::btree::map::OccupiedEntry::<u32, ()>::into_mut"
        ),
        Some(StubKind::BTreeMapOccupiedIntoMut)
    );
}

#[test]
fn btreemap_internal_entry_or_insert() {
    assert_eq!(
        StubRegistry::lookup_btreemap_internal_suffix(
            "alloc::btree::map::Entry::<u32, ()>::or_insert"
        ),
        Some(StubKind::BTreeMapEntryOrInsert)
    );
}

#[test]
fn btreemap_internal_entry_or_insert_with() {
    assert_eq!(
        StubRegistry::lookup_btreemap_internal_suffix(
            "std::btree_map::Entry::<u32, ()>::or_insert_with"
        ),
        Some(StubKind::BTreeMapEntryOrInsertWith)
    );
}

#[test]
fn btreemap_internal_entry_or_insert_with_key() {
    assert_eq!(
        StubRegistry::lookup_btreemap_internal_suffix(
            "alloc::btree::map::Entry::<u32, ()>::or_insert_with_key"
        ),
        Some(StubKind::BTreeMapEntryOrInsertWithKey)
    );
}

#[test]
fn btreemap_internal_search_tree() {
    assert_eq!(
        StubRegistry::lookup_btreemap_internal_suffix("alloc::btree::search::search_tree"),
        Some(StubKind::BTreeSearchTree)
    );
}

#[test]
fn btreemap_internal_node_reborrow() {
    assert_eq!(
        StubRegistry::lookup_btreemap_internal_suffix(
            "alloc::btree::node::NodeRef::<Mut, K, V, Leaf>::reborrow"
        ),
        Some(StubKind::BTreeNodeReborrow)
    );
}

#[test]
fn btreemap_internal_handle_into_kv() {
    assert_eq!(
        StubRegistry::lookup_btreemap_internal_suffix(
            "alloc::btree::node::Handle::<NodeRef, K, V>::into_kv"
        ),
        Some(StubKind::BTreeHandleIntoKv)
    );
}

#[test]
fn btreemap_internal_unknown_returns_none() {
    assert_eq!(
        StubRegistry::lookup_btreemap_internal_suffix(
            "alloc::btree::map::BTreeMap::<u32, ()>::drain"
        ),
        None
    );
}
