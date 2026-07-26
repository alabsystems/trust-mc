// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Direct suffix tests for RawVec, Vec, iterator, and String helpers.

use super::{StubKind, StubRegistry};

// -- lookup_rawvec_suffix --

#[test]
fn rawvec_suffix_all_operations() {
    let cases = vec![
        ("alloc::raw_vec::RawVec::<u32>::new_in", StubKind::RawVecNewIn),
        ("alloc::raw_vec::RawVec::<u32>::capacity", StubKind::RawVecCapacity),
        ("alloc::raw_vec::RawVec::<u32>::grow_one", StubKind::RawVecGrowOne),
        ("alloc::raw_vec::RawVec::<u32>::ptr", StubKind::RawVecPtr),
        ("alloc::raw_vec::RawVecInner::<A>::non_null", StubKind::RawVecPtr),
        ("alloc::raw_vec::RawVec::<u32>::from_nonnull_in", StubKind::RawVecFromNonNullIn),
        ("<alloc::raw_vec::RawVec<T, A> as Drop>::drop", StubKind::RawVecDrop),
        ("alloc::raw_vec::RawVecInner::<A>::deallocate", StubKind::RawVecDrop),
        ("alloc::raw_vec::RawVec::<u32>::shrink_to_fit", StubKind::RawVecShrinkToFit),
        // Part of #2876 RC2: pre-inlined Vec capacity growth paths
        ("alloc::raw_vec::RawVecInner::<A>::reserve_exact", StubKind::RawVecGrowOne),
        ("alloc::raw_vec::RawVecInner::<A>::grow_amortized", StubKind::RawVecGrowOne),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_rawvec_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn rawvec_suffix_drop_requires_drop_trait() {
    // "drop" without "Drop" in path should not match
    assert_eq!(StubRegistry::lookup_rawvec_suffix("alloc::raw_vec::RawVec::<u32>::drop"), None);
}

#[test]
fn rawvec_suffix_unknown_returns_none() {
    assert_eq!(StubRegistry::lookup_rawvec_suffix("alloc::raw_vec::RawVec::<u32>::shrink"), None);
}

// -- lookup_vec_suffix --

#[test]
fn vec_suffix_all_operations() {
    let cases = vec![
        ("alloc::vec::Vec::<u32>::new", StubKind::VecNew),
        ("<Vec<u32> as Default>::default", StubKind::VecNew),
        ("alloc::vec::Vec::<u32>::with_capacity", StubKind::VecWithCapacity),
        ("alloc::vec::Vec::<u32>::push", StubKind::VecPush),
        ("std::vec::Vec::<T, A>::push_mut", StubKind::VecPush),
        ("alloc::vec::Vec::<u32>::reserve", StubKind::VecReserve),
        ("alloc::vec::Vec::<u32>::reserve_exact", StubKind::VecReserveExact),
        ("alloc::vec::Vec::<u32>::shrink_to_fit", StubKind::VecShrinkToFit),
        ("alloc::vec::Vec::<u32>::pop", StubKind::VecPop),
        ("alloc::vec::Vec::<u32>::len", StubKind::VecLen),
        ("alloc::vec::Vec::<u32>::capacity", StubKind::VecCapacity),
        ("alloc::vec::Vec::<u32>::is_empty", StubKind::VecIsEmpty),
        ("alloc::vec::Vec::<u32>::clear", StubKind::VecClear),
        ("<alloc::vec::Vec<u32> as Clone>::clone", StubKind::VecClone),
        ("<alloc::vec::Vec<T, A> as std::ops::Drop>::drop", StubKind::VecDrop),
        ("alloc::vec::Vec::<u32>::contains", StubKind::VecContains),
        ("<alloc::vec::Vec<u32> as core::ops::Index<usize>>::index", StubKind::IndexIndex),
        ("<alloc::vec::Vec<u32> as core::ops::Deref>::deref", StubKind::VecAsSlice),
        ("<alloc::vec::Vec<u32> as core::ops::DerefMut>::deref_mut", StubKind::VecAsSlice),
        ("alloc::vec::Vec::<u32>::as_slice", StubKind::VecAsSlice),
        ("alloc::vec::Vec::<u32>::as_mut_slice", StubKind::VecAsSlice),
        // Part of #2917: std::vec spellings emitted by IntoIter mut-path MIR.
        ("<std::vec::Vec<T, A> as std::ops::DerefMut>::deref_mut", StubKind::VecAsSlice),
        ("std::vec::Vec::<T, A>::as_mut_slice", StubKind::VecAsSlice),
        ("alloc::vec::Vec::<u32>::as_ptr", StubKind::VecAsPtr),
        ("alloc::vec::Vec::<u32>::as_mut_ptr", StubKind::VecAsMutPtr),
        ("alloc::vec::Vec::<u32>::allocator", StubKind::GlobalAllocImpl),
        ("<Vec<u32> as IntoIterator>::into_iter", StubKind::VecIntoIter),
        ("alloc::vec::Vec::<u32>::iter", StubKind::VecIter),
        ("alloc::vec::Vec::<u32>::iter_mut", StubKind::VecIterMut),
        ("alloc::vec::Vec::<u32>::splice", StubKind::VecSplice),
        // Part of #4208: additional Vec methods for dterm Kani proofs
        ("alloc::vec::Vec::<u32>::insert", StubKind::VecInsert),
        ("alloc::vec::Vec::<u32>::remove", StubKind::VecRemove),
        ("alloc::vec::Vec::<u32>::truncate", StubKind::VecTruncate),
        ("alloc::vec::Vec::<u32>::retain", StubKind::VecRetain),
        ("alloc::vec::Vec::<u32>::retain_mut", StubKind::VecRetain),
        ("alloc::vec::Vec::<u32>::append", StubKind::VecAppend),
        ("alloc::vec::Vec::<u32>::last", StubKind::VecLast),
        ("alloc::vec::Vec::<u32>::reverse", StubKind::VecReverse),
        ("alloc::vec::Vec::<u32>::dedup", StubKind::VecDedup),
        ("alloc::vec::Vec::<u32>::dedup_by_key", StubKind::VecDedup),
        ("alloc::vec::Vec::<u32>::dedup_by", StubKind::VecDedup),
        ("alloc::vec::Vec::<u32>::split_off", StubKind::VecSplitOff),
        ("alloc::vec::Vec::<u32>::sort", StubKind::VecSort),
        ("alloc::vec::Vec::<u32>::sort_unstable", StubKind::VecSort),
        ("alloc::vec::Vec::<u32>::sort_by", StubKind::VecSort),
        ("alloc::vec::Vec::<u32>::drain", StubKind::VecDrain),
        ("alloc::vec::Vec::<u32>::swap", StubKind::VecSwap),
        ("alloc::vec::Vec::<u32>::resize", StubKind::VecResize),
        ("alloc::vec::Vec::<u32>::set_len", StubKind::VecSetLen),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_vec_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn vec_suffix_len_excludes_rawvec() {
    assert_eq!(StubRegistry::lookup_vec_suffix("alloc::raw_vec::RawVec::<u32>::len"), None);
}

#[test]
fn vec_suffix_clone_requires_vec_in_path() {
    // Clone without "Vec" in path should not match
    assert_eq!(StubRegistry::lookup_vec_suffix("SomeStruct::clone"), None);
}

#[test]
fn vec_suffix_iter_excludes_into_iter_substring() {
    // "iter" method should not match when "into_iter" is in the path
    assert_eq!(
        StubRegistry::lookup_vec_suffix("alloc::vec::Vec::<u32>::into_iter"),
        Some(StubKind::VecIntoIter) // matches into_iter, not iter
    );
}

// -- lookup_iter_suffix --

#[test]
fn iter_suffix_flatten_next_priority_over_intoiter_next() {
    // Flatten<IntoIter<T>>::next contains both "Flatten" and "IntoIter"
    // Must route to FlattenNext, not IntoIterNext
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "core::iter::adapters::flatten::Flatten::<IntoIter<i32>>::next"
        ),
        Some(StubKind::FlattenNext)
    );
}

#[test]
fn iter_suffix_map_next_priority_over_intoiter_next() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "core::iter::adapters::map::Map::<IntoIter<i32>, fn(i32) -> i64>::next"
        ),
        Some(StubKind::MapNext)
    );
}

#[test]
fn iter_suffix_filter_next_priority_over_intoiter_next() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "core::iter::adapters::filter::Filter::<IntoIter<i32>, fn(&i32) -> bool>::next"
        ),
        Some(StubKind::FilterNext)
    );
}

#[test]
fn iter_suffix_vec_into_iter_drop_routes_to_vec_drop() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix("<std::vec::IntoIter<T, A> as std::ops::Drop>::drop"),
        Some(StubKind::VecDrop)
    );
}

#[test]
fn iter_suffix_hashmap_iter_next_priority_over_generic_intoiter() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix("std::collections::hash_map::IntoIter::<u32, u32>::next"),
        Some(StubKind::HashMapIterNext)
    );
    // hashbrown path
    assert_eq!(
        StubRegistry::lookup_iter_suffix("hashbrown::map::IntoIter::<u32, u32>::next"),
        Some(StubKind::HashMapIterNext)
    );
}

#[test]
fn iter_suffix_btreemap_iter_next_shared_with_hashmap() {
    // BTreeMap uses same Array<K, Option<V>> model as HashMap, so shares HashMapIterNext (Part of #1751)
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "alloc::collections::btree_map::IntoIter::<u32, u32>::next"
        ),
        Some(StubKind::HashMapIterNext)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix("std::collections::btree_map::IntoIter::<u32, u32>::next"),
        Some(StubKind::HashMapIterNext)
    );
}

#[test]
fn iter_suffix_btreeset_iter_next() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix("alloc::collections::btree_set::IntoIter::<u32>::next"),
        Some(StubKind::BTreeSetIterNext)
    );
}

#[test]
fn iter_suffix_hashset_iter_next() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix("std::collections::hash_set::IntoIter::<u32>::next"),
        Some(StubKind::HashSetIterNext)
    );
}

#[test]
fn iter_suffix_generic_intoiter_next() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix("alloc::vec::into_iter::IntoIter::<i32>::next"),
        Some(StubKind::IntoIterNext)
    );
}

#[test]
fn iter_suffix_slice_iter_next_routes_to_intoiter_next() {
    // slice::Iter::next uses same (fld_vec, fld_pos) layout as VecIntoIter (Part of #1751)
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "core::slice::iter::<impl Iterator for Iter<'_, i32>>::next"
        ),
        Some(StubKind::IntoIterNext)
    );
    // Also matches slice::Iter path variant
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::slice::Iter::<i32>::next"),
        Some(StubKind::IntoIterNext)
    );
}

#[test]
fn iter_suffix_str_chars_next_routes_to_intoiter_next() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::str::iter::Chars::next"),
        Some(StubKind::IntoIterNext)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix("std::str::iter::Chars::next"),
        Some(StubKind::IntoIterNext)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "<core::str::iter::Chars<'_> as core::iter::Iterator>::next"
        ),
        Some(StubKind::IntoIterNext)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix("<std::str::Chars<'_> as std::iter::Iterator>::next"),
        Some(StubKind::IntoIterNext)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix("<std::str::Chars<'a> as std::iter::Iterator>::next"),
        Some(StubKind::IntoIterNext)
    );
}

#[test]
fn iter_suffix_slice_and_chars_clone_route_to_primitive_clone() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "<core::slice::iter::Iter<'_, u8> as core::clone::Clone>::clone"
        ),
        Some(StubKind::PrimitiveClone)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "<core::slice::iter::IterMut<'_, u8> as core::clone::Clone>::clone"
        ),
        Some(StubKind::PrimitiveClone)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "<core::str::iter::Chars<'_> as core::clone::Clone>::clone"
        ),
        Some(StubKind::PrimitiveClone)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix("<std::str::Chars<'_> as std::clone::Clone>::clone"),
        Some(StubKind::PrimitiveClone)
    );
}

#[test]
fn iter_suffix_slice_iter_mut_next_routes_to_intoiter_next() {
    // slice::IterMut::next uses same (fld_vec, fld_pos) layout as VecIntoIter (Part of #1751)
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "core::slice::iter::<impl Iterator for IterMut<'_, i32>>::next"
        ),
        Some(StubKind::IntoIterNext)
    );
}

#[test]
fn iter_suffix_range_spec_next() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "<std::ops::Range<T> as std::iter::range::RangeIteratorImpl>::spec_next"
        ),
        Some(StubKind::RangeSpecNext)
    );
}

#[test]
fn iter_suffix_range_into_iter() {
    // Part of #3002: Range<T>::into_iter identity stub
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "<core::ops::Range<u32> as core::iter::traits::collect::IntoIterator>::into_iter"
        ),
        Some(StubKind::RangeIntoIter)
    );
    // std variant
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "<std::ops::Range<u32> as std::iter::IntoIterator>::into_iter"
        ),
        Some(StubKind::RangeIntoIter)
    );
    // Must NOT match non-Range into_iter (Vec, HashMap handled by other lookups)
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::iter::traits::collect::IntoIterator::into_iter"),
        None
    );
}

#[test]
fn iter_suffix_slice_into_iter_immutable() {
    // Part of #3602: <&[T] as IntoIterator>::into_iter reuses VecIter
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "core::slice::iter::<impl std::iter::IntoIterator for &'a [T]>::into_iter"
        ),
        Some(StubKind::VecIter)
    );
    // Monomorphized form
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "core::slice::iter::<impl std::iter::IntoIterator for &[u32]>::into_iter"
        ),
        Some(StubKind::VecIter)
    );
}

#[test]
fn iter_suffix_slice_into_iter_mutable() {
    // Part of #3602: <&mut [T] as IntoIterator>::into_iter reuses VecIterMut
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "core::slice::iter::<impl std::iter::IntoIterator for &'a mut [T]>::into_iter"
        ),
        Some(StubKind::VecIterMut)
    );
    // Monomorphized form
    assert_eq!(
        StubRegistry::lookup_iter_suffix(
            "core::slice::iter::<impl std::iter::IntoIterator for &mut [u32]>::into_iter"
        ),
        Some(StubKind::VecIterMut)
    );
}

#[test]
fn iter_suffix_slice_into_iter_does_not_match_generic() {
    // Must NOT match generic IntoIterator::into_iter (not slice-specific)
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::iter::traits::collect::IntoIterator::into_iter"),
        None
    );
}

#[test]
fn iter_suffix_flatten_requires_iterator_trait() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::iter::traits::iterator::Iterator::flatten"),
        Some(StubKind::IterFlatten)
    );
    // "flatten" without "Iterator" should not match
    assert_eq!(StubRegistry::lookup_iter_suffix("some::module::flatten"), None);
}

#[test]
fn iter_suffix_collect_requires_iterator_trait() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::iter::traits::iterator::Iterator::collect"),
        Some(StubKind::IterCollect)
    );
}

#[test]
fn iter_suffix_adapter_methods() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::iter::traits::iterator::Iterator::map"),
        Some(StubKind::IterMap)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::iter::traits::iterator::Iterator::filter"),
        Some(StubKind::IterFilter)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::iter::traits::iterator::Iterator::filter_map"),
        Some(StubKind::IterFilterMap)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::iter::traits::iterator::Iterator::zip"),
        Some(StubKind::IterZip)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::iter::traits::iterator::Iterator::fold"),
        Some(StubKind::IterFold)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::iter::traits::iterator::Iterator::try_fold"),
        Some(StubKind::IterFold)
    );
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::iter::traits::iterator::Iterator::sum"),
        Some(StubKind::IterSum)
    );
}

#[test]
fn iter_suffix_unknown_returns_none() {
    assert_eq!(
        StubRegistry::lookup_iter_suffix("core::iter::traits::iterator::Iterator::count"),
        None
    );
}

// -- lookup_string_suffix --

#[test]
fn string_suffix_all_operations() {
    let cases = vec![
        ("alloc::string::String::new", StubKind::StringNew),
        ("<String as Default>::default", StubKind::StringNew),
        ("<String as From<&str>>::from", StubKind::StringFrom),
        ("alloc::string::String::from_raw_parts", StubKind::StringFromRawParts),
        ("alloc::string::String::len", StubKind::StringLen),
        ("alloc::string::String::is_empty", StubKind::StringIsEmpty),
        ("alloc::string::String::push_str", StubKind::StringPushStr),
        ("alloc::string::String::push", StubKind::StringPush),
        ("alloc::string::String::clear", StubKind::StringClear),
        ("<String as Clone>::clone", StubKind::StringClone),
        ("alloc::string::String::truncate", StubKind::StringTruncate),
        ("alloc::string::String::from_utf8_lossy", StubKind::StringFromUtf8Lossy),
        ("core::str::<impl str>::split_whitespace", StubKind::SplitWhitespace),
        ("<String as PartialEq>::eq", StubKind::StringEq),
        ("alloc::string::String::contains", StubKind::StringContains),
        ("alloc::string::String::starts_with", StubKind::StringStartsWith),
        ("alloc::string::String::ends_with", StubKind::StringEndsWith),
        ("alloc::string::String::is_ascii", StubKind::StringIsAscii),
        ("alloc::string::String::into_boxed_str", StubKind::StringIntoBoxedStr),
        // Part of #3698: String::deref_mut → StringAsStr (same as deref)
        ("<alloc::string::String as core::ops::DerefMut>::deref_mut", StubKind::StringAsStr),
        // Part of #4071: String::as_mut_str → StringAsStr (same semantics as as_str)
        ("alloc::string::String::as_mut_str", StubKind::StringAsStr),
        ("core::str::iter::SplitWhitespace::next", StubKind::SplitWhitespaceNext),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_string_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn string_suffix_eq_matches_str_paths() {
    // StringEq should match both String and str paths
    assert_eq!(
        StubRegistry::lookup_string_suffix("<str as PartialEq>::eq"),
        Some(StubKind::StringEq)
    );
}

#[test]
fn string_suffix_from_requires_from_trait() {
    // "from" without "From" should not match
    assert_eq!(StubRegistry::lookup_string_suffix("alloc::string::String::from"), None);
}

#[test]
fn string_suffix_clone_requires_string_in_path() {
    assert_eq!(StubRegistry::lookup_string_suffix("SomeStruct::clone"), None);
}

#[test]
fn string_suffix_unknown_returns_none() {
    assert_eq!(StubRegistry::lookup_string_suffix("alloc::string::String::capacity"), None);
}
