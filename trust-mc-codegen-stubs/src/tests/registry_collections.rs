// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Full-pipeline lookup() coverage for Vec, String, set, SetValZST,
// BTree internal routes, and collection-specific negative guards.

use super::{StubKind, lookup};

#[test]
fn lookup_vec_operations() {
    assert_eq!(lookup("alloc::vec::Vec::<u32>::new"), Some(StubKind::VecNew));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::with_capacity"), Some(StubKind::VecWithCapacity));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::push"), Some(StubKind::VecPush));
    assert_eq!(lookup("std::vec::Vec::<T, A>::push_mut"), Some(StubKind::VecPush));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::reserve"), Some(StubKind::VecReserve));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::reserve_exact"), Some(StubKind::VecReserveExact));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::shrink_to_fit"), Some(StubKind::VecShrinkToFit));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::pop"), Some(StubKind::VecPop));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::len"), Some(StubKind::VecLen));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::capacity"), Some(StubKind::VecCapacity));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::is_empty"), Some(StubKind::VecIsEmpty));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::contains"), Some(StubKind::VecContains));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::clear"), Some(StubKind::VecClear));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::set_len"), Some(StubKind::VecSetLen));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::splice"), Some(StubKind::VecSplice));
    assert_eq!(
        lookup("<alloc::vec::Vec<u32> as core::clone::Clone>::clone"),
        Some(StubKind::VecClone)
    );
    assert_eq!(lookup("<alloc::vec::Vec<T, A> as std::ops::Drop>::drop"), Some(StubKind::VecDrop));
    assert_eq!(
        lookup("<std::vec::IntoIter<T, A> as std::ops::Drop>::drop"),
        Some(StubKind::VecDrop)
    );
    // RawVec stubs (Part of #1037)
    assert_eq!(lookup("alloc::raw_vec::RawVec::<u32>::new_in"), Some(StubKind::RawVecNewIn));
    assert_eq!(lookup("alloc::raw_vec::RawVec::<u32>::capacity"), Some(StubKind::RawVecCapacity));
    assert_eq!(lookup("alloc::raw_vec::RawVec::<u32>::grow_one"), Some(StubKind::RawVecGrowOne));
    assert_eq!(lookup("alloc::raw_vec::RawVec::<u32>::ptr"), Some(StubKind::RawVecPtr));
    // RawVec::new (without allocator) - not stubbed, should use new_in
    assert_eq!(lookup("alloc::raw_vec::RawVec::<u32>::new"), None);
    // Part of #1841: RawVec::from_nonnull_in and Drop.
    // RawVecInner::deallocate is the same deallocation lane in newer stdlib MIR.
    assert_eq!(
        lookup("alloc::raw_vec::RawVec::<u32>::from_nonnull_in"),
        Some(StubKind::RawVecFromNonNullIn)
    );
    assert_eq!(
        lookup("alloc::raw_vec::RawVec::<T, A>::from_nonnull_in"),
        Some(StubKind::RawVecFromNonNullIn)
    );
    assert_eq!(
        lookup("<alloc::raw_vec::RawVec<T, A> as std::ops::Drop>::drop"),
        Some(StubKind::RawVecDrop)
    );
    assert_eq!(lookup("alloc::raw_vec::RawVecInner::<A>::deallocate"), Some(StubKind::RawVecDrop));
    assert_eq!(
        lookup("alloc::raw_vec::RawVec::<T, A>::shrink_to_fit"),
        Some(StubKind::RawVecShrinkToFit)
    );
    // VecFromSlice (#3673) — <Vec<T> as From<&[T]>>::from
    assert_eq!(
        lookup("<alloc::vec::Vec<u32> as core::convert::From<&[u32]>>::from"),
        Some(StubKind::VecFromSlice)
    );
    assert_eq!(lookup("alloc::slice::<impl [u32]>::to_vec"), Some(StubKind::VecFromSlice));
    assert_eq!(lookup("alloc::slice::<impl [u32]>::to_vec_in"), Some(StubKind::VecFromSlice));
}

#[test]
fn lookup_vec_slice_and_iterator_operations() {
    assert_eq!(
        lookup("<alloc::vec::Vec<u32> as core::ops::Index<usize>>::index"),
        Some(StubKind::IndexIndex)
    );
    assert_eq!(
        lookup("<alloc::vec::Vec<u32> as core::ops::Deref>::deref"),
        Some(StubKind::VecAsSlice)
    );
    assert_eq!(lookup("alloc::vec::Vec::<u32>::as_slice"), Some(StubKind::VecAsSlice));
    assert_eq!(
        lookup("<alloc::vec::Vec<u32> as core::ops::DerefMut>::deref_mut"),
        Some(StubKind::VecAsSlice)
    );
    assert_eq!(lookup("alloc::vec::Vec::<u32>::as_mut_slice"), Some(StubKind::VecAsSlice));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::as_ptr"), Some(StubKind::VecAsPtr));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::as_mut_ptr"), Some(StubKind::VecAsMutPtr));
    assert_eq!(
        lookup("<alloc::vec::Vec<u32> as core::iter::IntoIterator>::into_iter"),
        Some(StubKind::VecIntoIter)
    );
    assert_eq!(lookup("alloc::vec::Vec::<u32>::iter"), Some(StubKind::VecIter));
    assert_eq!(lookup("alloc::vec::Vec::<u32>::iter_mut"), Some(StubKind::VecIterMut));
    // into_iter should NOT match iter
    assert_eq!(lookup("alloc::vec::Vec::<u32>::into_iter"), Some(StubKind::VecIntoIter));
}

#[test]
fn lookup_string_core_operations() {
    assert_eq!(lookup("alloc::string::String::new"), Some(StubKind::StringNew));
    assert_eq!(
        lookup("<alloc::string::String as core::convert::From<&str>>::from"),
        Some(StubKind::StringFrom)
    );
    assert_eq!(lookup("alloc::string::String::len"), Some(StubKind::StringLen));
    assert_eq!(lookup("alloc::string::String::is_empty"), Some(StubKind::StringIsEmpty));
    // String/str Bool predicates (Part of #2125 Phase 2)
    assert_eq!(lookup("alloc::string::String::contains"), Some(StubKind::StringContains));
    assert_eq!(lookup("alloc::string::String::starts_with"), Some(StubKind::StringStartsWith));
    assert_eq!(lookup("alloc::string::String::ends_with"), Some(StubKind::StringEndsWith));
    assert_eq!(lookup("alloc::string::String::is_ascii"), Some(StubKind::StringIsAscii));
    // str-level predicate routing (Part of #2125 Phase 2)
    assert_eq!(lookup("core::str::<impl str>::is_ascii"), Some(StubKind::StringIsAscii));
    assert_eq!(lookup("core::str::<impl str>::contains"), Some(StubKind::StringContains));
    assert_eq!(lookup("core::str::<impl str>::starts_with"), Some(StubKind::StringStartsWith));
    assert_eq!(lookup("core::str::<impl str>::ends_with"), Some(StubKind::StringEndsWith));
    // Trait-lowered Pattern paths (Part of #2170 Phase 2)
    // rustc lowers str::contains/starts_with/ends_with to Pattern trait methods in MIR.
    assert_eq!(
        lookup("<&str as core::str::pattern::Pattern>::is_contained_in"),
        Some(StubKind::StringContains)
    );
    assert_eq!(
        lookup("<&str as core::str::pattern::Pattern>::is_prefix_of"),
        Some(StubKind::StringStartsWith)
    );
    assert_eq!(
        lookup("<&str as core::str::pattern::Pattern>::is_suffix_of"),
        Some(StubKind::StringEndsWith)
    );
    // Char-based Pattern lowering
    assert_eq!(
        lookup("<char as core::str::pattern::Pattern>::is_contained_in"),
        Some(StubKind::StringContains)
    );
    // Internal ascii helpers (Part of #2170 Phase 2)
    assert_eq!(lookup("core::str::is_ascii_simple"), Some(StubKind::StringIsAscii));
    assert_eq!(lookup("core::str::contains_nonascii"), Some(StubKind::StringIsAscii));
    // slice::ascii lowered paths (Part of #2196)
    assert_eq!(lookup("core::slice::ascii::<impl [u8]>::is_ascii"), Some(StubKind::StringIsAscii));
    assert_eq!(lookup("alloc::string::String::push"), Some(StubKind::StringPush));
    assert_eq!(lookup("alloc::string::String::push_str"), Some(StubKind::StringPushStr));
    assert_eq!(lookup("alloc::string::String::clear"), Some(StubKind::StringClear));
    assert_eq!(
        lookup("<alloc::string::String as core::clone::Clone>::clone"),
        Some(StubKind::StringClone)
    );
    // String::deref_mut → StringAsStr (Part of #3698)
    assert_eq!(
        lookup("<alloc::string::String as core::ops::DerefMut>::deref_mut"),
        Some(StubKind::StringAsStr)
    );
    // StringIntoBoxedStr (#3646)
    assert_eq!(lookup("alloc::string::String::into_boxed_str"), Some(StubKind::StringIntoBoxedStr));
    assert_eq!(lookup("std::string::String::into_boxed_str"), Some(StubKind::StringIntoBoxedStr));
    // StrFromUtf8 (#3672) — core::str::from_utf8, NOT from_utf8_lossy or from_utf8_unchecked
    assert_eq!(lookup("core::str::converts::from_utf8"), Some(StubKind::StrFromUtf8));
    assert_eq!(lookup("core::str::from_utf8"), Some(StubKind::StrFromUtf8));
    // IntParse (#3676) — <integer as FromStr>::from_str, NOT fmt::Arguments::from_str
    assert_eq!(
        lookup("core::num::<impl core::str::FromStr for i32>::from_str"),
        Some(StubKind::IntParse)
    );
    assert_eq!(
        lookup("core::num::<impl core::str::FromStr for u64>::from_str"),
        Some(StubKind::IntParse)
    );
}

#[test]
fn lookup_string_tostring_and_format() {
    // CowToString - collapse Cow<str> to String (#1691)
    // ToString trait is in alloc::string (re-exported to std::string)
    assert_eq!(
        lookup("<std::borrow::Cow<str> as alloc::string::ToString>::to_string"),
        Some(StubKind::CowToString)
    );
    assert_eq!(
        lookup("<alloc::borrow::Cow<str> as alloc::string::ToString>::to_string"),
        Some(StubKind::CowToString)
    );
    // String::to_string - routes to StringClone (identity/clone)
    // Must NOT match DisplayToString
    assert_eq!(
        lookup("<alloc::string::String as alloc::string::ToString>::to_string"),
        Some(StubKind::StringClone)
    );
    assert_eq!(
        lookup("<std::string::String as std::string::ToString>::to_string"),
        Some(StubKind::StringClone)
    );
    // DisplayToString - generic handler for Display types (#1700, #1701)
    // Catches any ToString::to_string not handled by String or Cow
    assert_eq!(
        lookup("<perf::display_trait::Foo as alloc::string::ToString>::to_string"),
        Some(StubKind::DisplayToString)
    );
    assert_eq!(
        lookup("<core::fmt::Arguments as std::string::ToString>::to_string"),
        Some(StubKind::DisplayToString)
    );
    assert_eq!(
        lookup("<i32 as std::string::ToString>::to_string"),
        Some(StubKind::DisplayToString)
    );
    // StringFromUtf8Lossy - converts bytes to String via Cow<str> (#1610)
    assert_eq!(
        lookup("alloc::string::String::from_utf8_lossy"),
        Some(StubKind::StringFromUtf8Lossy)
    );
    // StringTruncate (#1610)
    assert_eq!(lookup("alloc::string::String::truncate"), Some(StubKind::StringTruncate));
    // StringEq - String equality via PartialEq (#1610)
    assert_eq!(
        lookup("<alloc::string::String as core::cmp::PartialEq>::eq"),
        Some(StubKind::StringEq)
    );
    assert_eq!(lookup("<&str as core::cmp::PartialEq>::eq"), Some(StubKind::StringEq));
    // FmtFormat - format! macro (#1704)
    assert_eq!(lookup("std::fmt::format"), Some(StubKind::FmtFormat));
    assert_eq!(lookup("core::fmt::format"), Some(StubKind::FmtFormat));
    assert_eq!(lookup("alloc::fmt::format"), Some(StubKind::FmtFormat));
}

#[test]
fn lookup_btreeset_operations() {
    assert_eq!(lookup("std::collections::BTreeSet::<u32>::new"), Some(StubKind::BTreeSetNew));
    assert_eq!(lookup("alloc::collections::BTreeSet::<u32>::new"), Some(StubKind::BTreeSetNew));
    assert_eq!(
        lookup("alloc::collections::btree_set::BTreeSet::<u32>::new"),
        Some(StubKind::BTreeSetNew)
    );
    assert_eq!(
        lookup("<std::collections::BTreeSet<u32> as core::default::Default>::default"),
        Some(StubKind::BTreeSetNew)
    );
    assert_eq!(
        lookup("<alloc::collections::BTreeSet<u32> as std::default::Default>::default"),
        Some(StubKind::BTreeSetNew)
    );
    assert_eq!(lookup("std::collections::BTreeSet::<u32>::insert"), Some(StubKind::BTreeSetInsert));
    assert_eq!(
        lookup("std::collections::BTreeSet::<u32>::contains"),
        Some(StubKind::BTreeSetContains)
    );
    assert_eq!(lookup("std::collections::BTreeSet::<u32>::remove"), Some(StubKind::BTreeSetRemove));
    assert_eq!(lookup("std::collections::BTreeSet::<u32>::len"), Some(StubKind::BTreeSetLen));
    assert_eq!(
        lookup("std::collections::BTreeSet::<u32>::is_empty"),
        Some(StubKind::BTreeSetIsEmpty)
    );
    assert_eq!(lookup("std::collections::BTreeSet::<u32>::clear"), Some(StubKind::BTreeSetClear));
    assert_eq!(
        lookup("<std::collections::BTreeSet<u32> as core::clone::Clone>::clone"),
        Some(StubKind::BTreeSetClone)
    );
}

#[test]
fn lookup_hashset_operations() {
    // HashSet operations (Part of #1613)
    assert_eq!(lookup("std::collections::HashSet::<u32>::new"), Some(StubKind::HashSetNew));
    // Test default via Default trait impl
    assert_eq!(
        lookup("<std::collections::HashSet<u32> as core::default::Default>::default"),
        Some(StubKind::HashSetNew)
    );
    assert_eq!(
        lookup("std::collections::HashSet::<u32>::with_capacity"),
        Some(StubKind::HashSetNew)
    );
    // Test with_hasher for custom hasher support
    assert_eq!(
        lookup("std::collections::HashSet::<u32, std::hash::RandomState>::with_hasher"),
        Some(StubKind::HashSetNew)
    );
    assert_eq!(lookup("std::collections::HashSet::<u32>::insert"), Some(StubKind::HashSetInsert));
    assert_eq!(
        lookup("std::collections::HashSet::<u32>::contains"),
        Some(StubKind::HashSetContains)
    );
    assert_eq!(lookup("std::collections::HashSet::<u32>::remove"), Some(StubKind::HashSetRemove));
    assert_eq!(lookup("std::collections::HashSet::<u32>::len"), Some(StubKind::HashSetLen));
    assert_eq!(
        lookup("std::collections::HashSet::<u32>::is_empty"),
        Some(StubKind::HashSetIsEmpty)
    );
    assert_eq!(lookup("std::collections::HashSet::<u32>::clear"), Some(StubKind::HashSetClear));
    assert_eq!(
        lookup("<std::collections::HashSet<u32> as core::clone::Clone>::clone"),
        Some(StubKind::HashSetClone)
    );
}

/// Regression test for StubRegistry dispatch bug (Part of #1751).
/// IntoIterator trait paths must route to collection-specific handlers,
/// not the generic IntoIter iterator handler.
#[test]
fn lookup_set_into_iterator_trait_paths() {
    // These paths contain "IntoIter" substring (from IntoIterator trait name),
    // but should route to HashSet/BTreeSet handlers, not generic IntoIter handler.
    // Bug was: IntoIter check came before HashSet/BTreeSet checks.

    // HashSet as IntoIterator
    assert_eq!(
        lookup("<std::collections::HashSet<u32> as core::iter::IntoIterator>::into_iter"),
        Some(StubKind::HashSetIntoIter)
    );
    assert_eq!(
        lookup("<std::collections::hash_set::HashSet<i32> as IntoIterator>::into_iter"),
        Some(StubKind::HashSetIntoIter)
    );

    // BTreeSet as IntoIterator
    assert_eq!(
        lookup("<std::collections::BTreeSet<u32> as core::iter::IntoIterator>::into_iter"),
        Some(StubKind::BTreeSetIntoIter)
    );
    assert_eq!(
        lookup("<alloc::collections::btree_set::BTreeSet<i32> as IntoIterator>::into_iter"),
        Some(StubKind::BTreeSetIntoIter)
    );

    // Vec still routes to generic handler (Vec has its own into_iter)
    assert_eq!(
        lookup("<alloc::vec::Vec<u32> as core::iter::IntoIterator>::into_iter"),
        Some(StubKind::VecIntoIter)
    );
}

#[test]
fn lookup_btreemap_internal_operations() {
    // BTreeMap internal operations (Part of #1622)
    // Test both alloc:: and std:: path variants since MIR may use either

    // BTreeMap::entry - both path styles
    assert_eq!(
        lookup("alloc::collections::btree::map::BTreeMap::<u32, ()>::entry"),
        Some(StubKind::BTreeMapEntry)
    );
    assert_eq!(
        lookup("std::collections::BTreeMap::<i32, ()>::entry"),
        Some(StubKind::BTreeMapEntry)
    );

    // VacantEntry::insert - std path (used in actual MIR)
    assert_eq!(
        lookup("std::collections::btree_map::VacantEntry::<i32, ()>::insert"),
        Some(StubKind::BTreeMapVacantInsert)
    );

    // VacantEntry::insert_entry - alloc path (alternative API)
    assert_eq!(
        lookup("alloc::collections::btree::map::VacantEntry::<u32, ()>::insert_entry"),
        Some(StubKind::BTreeMapVacantInsertEntry)
    );

    // OccupiedEntry::insert - std path (used in actual MIR)
    assert_eq!(
        lookup("std::collections::btree_map::OccupiedEntry::<i32, ()>::insert"),
        Some(StubKind::BTreeMapOccupiedInsert)
    );

    // OccupiedEntry::get_mut and into_mut
    assert_eq!(
        lookup("alloc::collections::btree::map::OccupiedEntry::<u32, ()>::get_mut"),
        Some(StubKind::BTreeMapOccupiedGetMut)
    );
    assert_eq!(
        lookup("alloc::collections::btree::map::OccupiedEntry::<u32, ()>::into_mut"),
        Some(StubKind::BTreeMapOccupiedIntoMut)
    );

    // Entry::or_insert and variants
    assert_eq!(
        lookup("alloc::collections::btree::map::Entry::<u32, ()>::or_insert"),
        Some(StubKind::BTreeMapEntryOrInsert)
    );
    assert_eq!(
        lookup("std::collections::btree_map::Entry::<u32, ()>::or_insert_with"),
        Some(StubKind::BTreeMapEntryOrInsertWith)
    );
    assert_eq!(
        lookup("alloc::collections::btree::map::Entry::<u32, ()>::or_insert_with_key"),
        Some(StubKind::BTreeMapEntryOrInsertWithKey)
    );

    // HashMap Entry APIs should not match BTreeMap internal stubs.
    assert_eq!(lookup("std::collections::hash_map::Entry::<u32, ()>::or_insert"), None);
    assert_eq!(lookup("std::collections::hash_map::VacantEntry::<u32, ()>::insert"), None);
    assert_eq!(lookup("std::collections::hash_map::OccupiedEntry::<u32, ()>::insert"), None);
}

#[test]
fn lookup_setvalzst_default() {
    // SetValZST::default - ZST marker for BTreeSet values (Part of #1622)
    // Used when BTreeSet::insert inlines to BTreeMap::insert with SetValZST value
    assert_eq!(
        lookup(
            "<alloc::collections::btree::set_val::SetValZST as core::default::Default>::default"
        ),
        Some(StubKind::SetValZstDefault)
    );
    // Alternative trait impl path
    assert_eq!(
        lookup("<SetValZST as core::default::Default>::default"),
        Some(StubKind::SetValZstDefault)
    );
    // Ensure non-SetValZST default paths don't match
    assert_eq!(lookup("<u32 as core::default::Default>::default"), None);
}

#[test]
fn lookup_btreemap_setvalzst_operations() {
    // BTreeMap<K, SetValZST> operations redirect to BTreeSet stubs (Part of #1622)
    // When BTreeSet::insert is inlined, it becomes BTreeMap::insert with SetValZST value

    // BTreeMap<K, SetValZST>::insert -> BTreeSetInsert
    assert_eq!(
        lookup(
            "alloc::collections::btree::map::BTreeMap::<i32, alloc::collections::btree::set_val::SetValZST>::insert"
        ),
        Some(StubKind::BTreeSetInsert)
    );
    assert_eq!(
        lookup("std::collections::BTreeMap::<u32, SetValZST>::insert"),
        Some(StubKind::BTreeSetInsert)
    );

    // BTreeMap<K, SetValZST>::contains_key -> BTreeSetContains
    assert_eq!(
        lookup("alloc::collections::btree::map::BTreeMap::<i32, SetValZST>::contains_key"),
        Some(StubKind::BTreeSetContains)
    );

    // BTreeMap<K, SetValZST>::new -> BTreeSetNew
    assert_eq!(
        lookup("alloc::collections::btree::map::BTreeMap::<i32, SetValZST>::new"),
        Some(StubKind::BTreeSetNew)
    );

    // Regular BTreeMap (without SetValZST) should NOT redirect to BTreeSet
    // Part of #1752: BTreeMap has its own stub kinds (same model as HashMap)
    assert_eq!(
        lookup("std::collections::BTreeMap::<u32, u32>::insert"),
        Some(StubKind::BTreeMapInsert)
    );
}

#[test]
fn lookup_mem_replace_setvalzst_returns_none() {
    // mem::replace<SetValZST> is NOT matched by stub registry (Part of #1627)
    // Reason: def_path_str doesn't include generic args, so path is just "std::mem::replace"
    // The actual handling is done by try_codegen_btree_internal_precheck() in dispatch.rs
    // which examines the function type's generic arguments directly.
    assert_eq!(
        lookup("std::mem::replace::<alloc::collections::btree::set_val::SetValZST>"),
        None, // Would need precheck, not stub lookup
    );
    assert_eq!(
        lookup("std::mem::replace"),
        None, // This is what def_path_str actually produces
    );
}

#[test]
fn lookup_option_as_ref_btree_returns_none() {
    // Option::as_ref<NodeRef> is NOT matched by stub registry (Part of #1627)
    // Reason: def_path_str doesn't include generic args reliably
    // The actual handling is done by try_codegen_btree_internal_precheck() in dispatch.rs
    assert_eq!(
        lookup(
            "std::option::Option::<alloc::collections::btree::node::NodeRef<Mut, K, V, Leaf>>::as_ref"
        ),
        None, // Would need precheck, not stub lookup
    );
    // Regular Option::as_ref also doesn't match (expected)
    assert_eq!(lookup("std::option::Option::<u32>::as_ref"), None);
}

/// Part of #4208: Vec methods needed for dterm Kani proofs.
/// Tests full-pipeline lookup for insert, remove, truncate, retain_mut, splice.
#[test]
fn lookup_vec_dterm_methods() {
    // Vec::insert
    assert_eq!(lookup("alloc::vec::Vec::<u32>::insert"), Some(StubKind::VecInsert));
    assert_eq!(lookup("std::vec::Vec::<String>::insert"), Some(StubKind::VecInsert));
    // Vec::remove
    assert_eq!(lookup("alloc::vec::Vec::<u32>::remove"), Some(StubKind::VecRemove));
    assert_eq!(lookup("std::vec::Vec::<String>::remove"), Some(StubKind::VecRemove));
    // Vec::truncate
    assert_eq!(lookup("alloc::vec::Vec::<u32>::truncate"), Some(StubKind::VecTruncate));
    assert_eq!(lookup("std::vec::Vec::<String>::truncate"), Some(StubKind::VecTruncate));
    // Vec::retain_mut — reuses VecRetain (same semantics, closure over-approximated)
    assert_eq!(lookup("alloc::vec::Vec::<u32>::retain_mut"), Some(StubKind::VecRetain));
    assert_eq!(lookup("std::vec::Vec::<String>::retain_mut"), Some(StubKind::VecRetain));
    // Vec::retain
    assert_eq!(lookup("alloc::vec::Vec::<u32>::retain"), Some(StubKind::VecRetain));
    // Vec::splice (already tested above, confirm still works)
    assert_eq!(lookup("std::vec::Vec::<u32>::splice"), Some(StubKind::VecSplice));
}

/// Part of #4208: Slice methods needed for dterm Kani proofs.
/// Tests full-pipeline lookup for last, binary_search_by_key, chunks, windows.
#[test]
fn lookup_slice_dterm_methods() {
    // slice::last
    assert_eq!(lookup("core::slice::<impl [T]>::last"), Some(StubKind::SliceLast));
    assert_eq!(lookup("std::slice::<impl [T]>::last"), Some(StubKind::SliceLast));
    assert_eq!(lookup("core::slice::<impl [u8]>::last"), Some(StubKind::SliceLast));
    // slice::last must NOT match last_mut
    assert_eq!(lookup("core::slice::<impl [T]>::last_mut"), None);
    // slice::binary_search_by_key
    assert_eq!(
        lookup("core::slice::<impl [T]>::binary_search_by_key"),
        Some(StubKind::SliceBinarySearchByKey)
    );
    assert_eq!(
        lookup("std::slice::<impl [T]>::binary_search_by_key"),
        Some(StubKind::SliceBinarySearchByKey)
    );
    // slice::chunks
    assert_eq!(lookup("core::slice::<impl [T]>::chunks"), Some(StubKind::SliceChunks));
    assert_eq!(lookup("std::slice::<impl [T]>::chunks"), Some(StubKind::SliceChunks));
    // chunks must NOT match chunks_mut
    assert_eq!(lookup("core::slice::<impl [T]>::chunks_mut"), None);
    // slice::windows
    assert_eq!(lookup("core::slice::<impl [T]>::windows"), Some(StubKind::SliceWindows));
    assert_eq!(lookup("std::slice::<impl [T]>::windows"), Some(StubKind::SliceWindows));
}

/// Part of #4208: Option methods needed for dterm Kani proofs.
/// Tests full-pipeline lookup for take, map_or.
#[test]
fn lookup_option_dterm_methods() {
    // Option::take
    assert_eq!(lookup("core::option::Option::<u32>::take"), Some(StubKind::OptionTake));
    assert_eq!(lookup("std::option::Option::<String>::take"), Some(StubKind::OptionTake));
    // Option::map_or
    assert_eq!(lookup("core::option::Option::<u32>::map_or"), Some(StubKind::OptionMapOr));
    assert_eq!(lookup("std::option::Option::<String>::map_or"), Some(StubKind::OptionMapOr));
    // map_or must NOT match map (should be its own variant)
    assert_ne!(lookup("core::option::Option::<u32>::map_or"), Some(StubKind::OptionMap));
    // map must still work (not broken by map_or)
    assert_eq!(lookup("core::option::Option::<u32>::map"), Some(StubKind::OptionMap));
}

/// Part of #4209: ArrayVec methods must NOT match Vec stubs.
/// arrayvec::ArrayVec<T, CAP> contains "Vec<" as a substring, so without
/// the exclusion guard, methods like is_full are routed to Vec stubs.
#[test]
fn arrayvec_methods_do_not_match_vec_stubs() {
    // ArrayVec-specific methods should return None (not stubbed)
    assert_eq!(lookup("arrayvec::ArrayVec::<T, CAP>::is_full"), None);
    assert_eq!(lookup("arrayvec::ArrayVec::<u8, 64>::push"), None);
    assert_eq!(lookup("arrayvec::ArrayVec::<u8, 64>::len"), None);
    assert_eq!(lookup("arrayvec::ArrayVec::<u8, 64>::pop"), None);
    assert_eq!(lookup("arrayvec::ArrayVec::<u8, 64>::capacity"), None);
    assert_eq!(lookup("arrayvec::ArrayVec::<u8, 64>::new"), None);
    assert_eq!(lookup("arrayvec::ArrayVec::<u8, 64>::clear"), None);
}
