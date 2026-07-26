// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Full-pipeline lookup() coverage for iterator intrinsics and end-to-end
// iterator routing cases.

use super::{StubKind, lookup};

#[test]
fn lookup_iterator_intrinsics() {
    // Iterator intrinsics for Range loops (Part of #1712)
    // checked_add_unsigned - used by Range iterator
    assert_eq!(
        lookup("core::num::<impl i32>::checked_add_unsigned"),
        Some(StubKind::CheckedAddUnsigned)
    );
    assert_eq!(
        lookup("core::num::<impl usize>::checked_add_unsigned"),
        Some(StubKind::CheckedAddUnsigned)
    );

    // unwrap_unchecked - used to extract Option values
    assert_eq!(
        lookup("std::option::Option::<i32>::unwrap_unchecked"),
        Some(StubKind::OptionUnwrapUnchecked)
    );
    assert_eq!(
        lookup("core::option::Option::<usize>::unwrap_unchecked"),
        Some(StubKind::OptionUnwrapUnchecked)
    );
}

// =============================================================================
// HashMap suffix: negative cases and edge guards (Part of #2016)
// =============================================================================

#[test]
fn lookup_hashmap_insert_excludes_internal_methods() {
    // insert_at_index and find_insert are internal methods, not user-facing insert
    assert_eq!(lookup("std::collections::HashMap::<u32, u32>::insert_at_index"), None);
    assert_eq!(lookup("std::collections::HashMap::<u32, u32>::find_insert"), None);
}

#[test]
fn lookup_hashmap_get_excludes_internal_methods() {
    // get_key_value and RawTable::get should not match HashMap::get
    assert_eq!(lookup("std::collections::HashMap::<u32, u32>::get_key_value"), None);
}

#[test]
fn lookup_hashmap_remove_excludes_remove_entry() {
    assert_eq!(lookup("std::collections::HashMap::<u32, u32>::remove_entry"), None);
}

#[test]
fn lookup_hashmap_len_excludes_rawtable() {
    // RawTable::len should not match HashMap::len
    assert_eq!(lookup("hashbrown::raw::RawTable::<(u32, u32)>::len"), None);
}

#[test]
fn lookup_btreemap_vs_hashmap_distinguishes() {
    // BTreeMap paths should return BTreeMap stubs, not HashMap
    assert_eq!(lookup("std::collections::BTreeMap::<u32, u32>::new"), Some(StubKind::BTreeMapNew));
    assert_eq!(lookup("std::collections::HashMap::<u32, u32>::new"), Some(StubKind::HashMapNew));
}

#[test]
fn lookup_btreemap_core_operations() {
    assert_eq!(lookup("std::collections::BTreeMap::<u32, u32>::new"), Some(StubKind::BTreeMapNew));
    assert_eq!(
        lookup("std::collections::BTreeMap::<u32, u32>::insert"),
        Some(StubKind::BTreeMapInsert)
    );
    assert_eq!(lookup("std::collections::BTreeMap::<u32, u32>::get"), Some(StubKind::BTreeMapGet));
    assert_eq!(
        lookup("std::collections::BTreeMap::<u32, u32>::get_mut"),
        Some(StubKind::BTreeMapGetMut)
    );
    assert_eq!(
        lookup("std::collections::BTreeMap::<u32, u32>::contains_key"),
        Some(StubKind::BTreeMapContainsKey)
    );
    assert_eq!(
        lookup("std::collections::BTreeMap::<u32, u32>::remove"),
        Some(StubKind::BTreeMapRemove)
    );
    assert_eq!(lookup("std::collections::BTreeMap::<u32, u32>::len"), Some(StubKind::BTreeMapLen));
    assert_eq!(
        lookup("std::collections::BTreeMap::<u32, u32>::is_empty"),
        Some(StubKind::BTreeMapIsEmpty)
    );
    assert_eq!(
        lookup("std::collections::BTreeMap::<u32, u32>::clear"),
        Some(StubKind::BTreeMapClear)
    );
    assert_eq!(
        lookup("<std::collections::BTreeMap<u32, u32> as core::clone::Clone>::clone"),
        Some(StubKind::BTreeMapClone)
    );
    assert_eq!(
        lookup("<std::collections::BTreeMap<K, V, A> as std::ops::Drop>::drop"),
        Some(StubKind::HashMapDrop)
    );
}

#[test]
fn lookup_btreemap_internal_search_and_node() {
    // Internal BTree operations for SetValZST-based inlining
    assert_eq!(
        lookup("alloc::collections::btree::search::search_tree"),
        Some(StubKind::BTreeSearchTree)
    );
    assert_eq!(
        lookup("alloc::collections::btree::node::NodeRef::<Mut, K, V, Leaf>::reborrow"),
        Some(StubKind::BTreeNodeReborrow)
    );
    assert_eq!(
        lookup("alloc::collections::btree::node::Handle::<NodeRef, K, V>::into_kv"),
        Some(StubKind::BTreeHandleIntoKv)
    );
}

#[test]
fn lookup_btreeset_iterator_operations() {
    assert_eq!(
        lookup("<std::collections::BTreeSet<u32> as core::iter::IntoIterator>::into_iter"),
        Some(StubKind::BTreeSetIntoIter)
    );
    assert_eq!(lookup("std::collections::BTreeSet::<u32>::iter"), Some(StubKind::BTreeSetIter));
}

#[test]
fn lookup_hashset_iterator_operations() {
    assert_eq!(
        lookup("<std::collections::HashSet<u32> as core::iter::IntoIterator>::into_iter"),
        Some(StubKind::HashSetIntoIter)
    );
    assert_eq!(lookup("std::collections::HashSet::<u32>::iter"), Some(StubKind::HashSetIter));
}

#[test]
fn lookup_collection_iter_next() {
    // HashMap iterator next
    assert_eq!(
        lookup("std::collections::hash_map::IntoIter::<u32, u32>::next"),
        Some(StubKind::HashMapIterNext)
    );
    // BTreeSet iterator next
    assert_eq!(
        lookup("alloc::collections::btree_set::IntoIter::<u32>::next"),
        Some(StubKind::BTreeSetIterNext)
    );
    // HashSet iterator next
    assert_eq!(
        lookup("std::collections::hash_set::IntoIter::<u32>::next"),
        Some(StubKind::HashSetIterNext)
    );
}

// End-to-end lookup tests for slice::Iter/IterMut routing through main entry point (Part of #1751)
#[test]
fn lookup_slice_iter_next_routes_to_intoiter_next() {
    // The full path goes through the `Iterator for` guard in mod.rs
    assert_eq!(
        lookup("core::slice::iter::<impl Iterator for Iter<'_, i32>>::next"),
        Some(StubKind::IntoIterNext)
    );
    assert_eq!(
        lookup("core::slice::iter::<impl Iterator for IterMut<'_, u32>>::next"),
        Some(StubKind::IntoIterNext)
    );
    // Direct path variant
    assert_eq!(lookup("core::slice::Iter::<i32>::next"), Some(StubKind::IntoIterNext));
    // Range iterator next() lowering used in for-loop desugaring.
    assert_eq!(
        lookup("<std::ops::Range<T> as std::iter::range::RangeIteratorImpl>::spec_next"),
        Some(StubKind::RangeSpecNext)
    );
}

#[test]
fn lookup_slice_iter_and_chars_clone_routes_to_primitive_clone() {
    assert_eq!(
        lookup("<core::slice::iter::Iter<'_, u8> as core::clone::Clone>::clone"),
        Some(StubKind::PrimitiveClone)
    );
    assert_eq!(
        lookup("<core::slice::iter::IterMut<'_, u8> as core::clone::Clone>::clone"),
        Some(StubKind::PrimitiveClone)
    );
    assert_eq!(
        lookup("<core::str::iter::Chars<'_> as core::clone::Clone>::clone"),
        Some(StubKind::PrimitiveClone)
    );
    assert_eq!(
        lookup("<std::str::Chars<'_> as std::clone::Clone>::clone"),
        Some(StubKind::PrimitiveClone)
    );
}

// End-to-end lookup tests for slice IntoIterator trait paths (Part of #3602)
#[test]
fn lookup_slice_into_iter_routes_to_vec_iter() {
    // Polymorphic form from MIR lowering
    assert_eq!(
        lookup("core::slice::iter::<impl std::iter::IntoIterator for &'a [T]>::into_iter"),
        Some(StubKind::VecIter)
    );
    // Monomorphized form
    assert_eq!(
        lookup("core::slice::iter::<impl std::iter::IntoIterator for &[usize]>::into_iter"),
        Some(StubKind::VecIter)
    );
    // Mutable variant
    assert_eq!(
        lookup("core::slice::iter::<impl std::iter::IntoIterator for &'a mut [T]>::into_iter"),
        Some(StubKind::VecIterMut)
    );
}

#[test]
fn lookup_manuallydrop_identity_helpers() {
    assert_eq!(lookup("std::mem::ManuallyDrop::<u32>::new"), Some(StubKind::GlobalAllocImpl));
    assert_eq!(
        lookup("<std::mem::ManuallyDrop<u32> as std::ops::Deref>::deref"),
        Some(StubKind::GlobalAllocImpl)
    );
    // DerefMut::deref_mut — appears in Vec::IntoIter paths (Part of #2967)
    assert_eq!(
        lookup("<std::mem::ManuallyDrop<T> as std::ops::DerefMut>::deref_mut"),
        Some(StubKind::GlobalAllocImpl)
    );
}
