// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Full-pipeline lookup() coverage for slice, iterator, allocation, pointer,
// layout, kani::mem, option, and result routing.

use super::{StubKind, lookup};

#[test]
fn lookup_slice_operations() {
    assert_eq!(
        lookup("core::slice::cmp::SlicePartialEq::equal"),
        Some(StubKind::SlicePartialEqEqual)
    );
    assert_eq!(lookup("std::slice::index::SliceIndex::index"), Some(StubKind::SliceIndexIndex));
    // Index::index - generic Index trait (Part of #2196 coverage)
    // Exact HashMap match for bare trait paths
    assert_eq!(lookup("core::ops::Index::index"), Some(StubKind::IndexIndex));
    assert_eq!(lookup("std::ops::Index::index"), Some(StubKind::IndexIndex));
    // Suffix matching: paths ending in ops::Index::index
    assert_eq!(lookup("mymod::ops::Index::index"), Some(StubKind::IndexIndex));
    // Trait-impl paths from resolve_callee_path in MIR call dispatch.
    assert_eq!(
        lookup("<usize as std::slice::SliceIndex<[T]>>::index"),
        Some(StubKind::SliceIndexIndex)
    );
    assert_eq!(
        lookup("<std::vec::Vec<T> as std::ops::Index<usize>>::index"),
        Some(StubKind::IndexIndex)
    );
    // Part of #3348: Range-based slice indexing via full module path
    // MIR emits `core::slice::index::SliceIndex<[T]>` (with `index::` module prefix).
    assert_eq!(
        lookup(
            "<core::ops::range::RangeInclusive<usize> as core::slice::index::SliceIndex<[bool]>>::index"
        ),
        Some(StubKind::SliceIndexIndex)
    );
    assert_eq!(
        lookup("<core::ops::range::Range<usize> as core::slice::index::SliceIndex<[bool]>>::index"),
        Some(StubKind::SliceIndexIndex)
    );
}

#[test]
fn lookup_slice_is_empty() {
    // Part of #3713: slice::is_empty stub registration
    assert_eq!(lookup("core::slice::<impl [T]>::is_empty"), Some(StubKind::SliceIsEmpty));
    assert_eq!(lookup("std::slice::<impl [T]>::is_empty"), Some(StubKind::SliceIsEmpty));
    // Trait-impl path form (e.g. from def_path_str)
    assert_eq!(lookup("core::slice::<impl [u8]>::is_empty"), Some(StubKind::SliceIsEmpty));
}

#[test]
fn lookup_slice_first() {
    // Part of #3768: slice::first stub registration
    assert_eq!(lookup("core::slice::<impl [T]>::first"), Some(StubKind::SliceFirst));
    assert_eq!(lookup("std::slice::<impl [T]>::first"), Some(StubKind::SliceFirst));
    assert_eq!(lookup("core::slice::<impl [u8]>::first"), Some(StubKind::SliceFirst));
}

#[test]
fn lookup_slice_partition_point() {
    // Part of #4202: slice::partition_point stub registration
    assert_eq!(
        lookup("core::slice::<impl [T]>::partition_point"),
        Some(StubKind::SlicePartitionPoint)
    );
    assert_eq!(
        lookup("std::slice::<impl [T]>::partition_point"),
        Some(StubKind::SlicePartitionPoint)
    );
    assert_eq!(
        lookup("core::slice::<impl [u8]>::partition_point"),
        Some(StubKind::SlicePartitionPoint)
    );
}

#[test]
fn lookup_iterator_operations() {
    assert_eq!(
        lookup("core::iter::traits::iterator::Iterator::flatten"),
        Some(StubKind::IterFlatten)
    );
    assert_eq!(
        lookup("core::iter::traits::iterator::Iterator::collect"),
        Some(StubKind::IterCollect)
    );
    // IntoIterNext - must match IntoIter paths but NOT Flatten<IntoIter> paths
    assert_eq!(
        lookup("alloc::vec::into_iter::IntoIter::<i32>::next"),
        Some(StubKind::IntoIterNext)
    );
    // FlattenNext - must match Flatten paths even when they contain IntoIter
    assert_eq!(
        lookup("core::iter::adapters::flatten::Flatten::<core::vec::IntoIter<i32>>::next"),
        Some(StubKind::FlattenNext)
    );
    // Iterator adapters (Part of #1751) - map, filter, fold, sum
    assert_eq!(lookup("core::iter::traits::iterator::Iterator::map"), Some(StubKind::IterMap));
    assert_eq!(
        lookup("core::iter::traits::iterator::Iterator::filter"),
        Some(StubKind::IterFilter)
    );
    assert_eq!(
        lookup("core::iter::traits::iterator::Iterator::filter_map"),
        Some(StubKind::IterFilterMap)
    );
    assert_eq!(lookup("core::iter::traits::iterator::Iterator::zip"), Some(StubKind::IterZip));
    assert_eq!(lookup("core::iter::traits::iterator::Iterator::fold"), Some(StubKind::IterFold));
    assert_eq!(
        lookup("core::iter::traits::iterator::Iterator::try_fold"),
        Some(StubKind::IterFold)
    );
    assert_eq!(lookup("core::iter::traits::iterator::Iterator::sum"), Some(StubKind::IterSum));
    // Map and Filter adapter next()
    assert_eq!(
        lookup("core::iter::adapters::map::Map::<IntoIter<i32>, fn(i32) -> i64>::next"),
        Some(StubKind::MapNext)
    );
    assert_eq!(
        lookup("core::iter::adapters::filter::Filter::<IntoIter<i32>, fn(&i32) -> bool>::next"),
        Some(StubKind::FilterNext)
    );
    // FilterMap adapter creation and next() (Part of #3692)
    assert_eq!(
        lookup(
            "core::iter::adapters::filter_map::FilterMap::<IntoIter<&str>, fn(&str) -> Option<i32>>::next"
        ),
        Some(StubKind::FilterMapNext)
    );
    // Zip adapter next() — advance both inner iterators (Part of #3381)
    assert_eq!(
        lookup("core::iter::adapters::zip::Zip::<IntoIter<bool>, IntoIter<bool>>::next"),
        Some(StubKind::ZipNext)
    );
    assert_eq!(
        lookup("<std::ops::Range<T> as std::iter::range::RangeIteratorImpl>::spec_next"),
        Some(StubKind::RangeSpecNext)
    );

    // Part of #3189: turbofish generic paths from def_path_str.
    // When calls have explicit generic args, def_path_str includes them as
    // turbofish (e.g., `>::collect::<Vec<i32>>`). extract_method_name must
    // strip these to match the stub lookup tables.
    assert_eq!(
        lookup(
            "<std::iter::FilterMap<std::vec::IntoIter<&str>, {closure}> as std::iter::Iterator>::collect::<std::vec::Vec<i32>>"
        ),
        Some(StubKind::IterCollect),
        "collect with turbofish Vec<i32> should resolve to IterCollect (#3189)"
    );
    assert_eq!(
        lookup("<std::vec::IntoIter<&str> as std::iter::Iterator>::filter_map::<i32, {closure}>"),
        Some(StubKind::IterFilterMap),
        "filter_map with turbofish should resolve to IterFilterMap (#3189)"
    );
}

#[test]
fn lookup_split_whitespace_next() {
    assert_eq!(lookup("core::str::<impl str>::split_whitespace"), Some(StubKind::SplitWhitespace));
    assert_eq!(lookup("std::str::<impl str>::split_whitespace"), Some(StubKind::SplitWhitespace));
    assert_eq!(
        lookup("core::str::iter::SplitWhitespace::next"),
        Some(StubKind::SplitWhitespaceNext)
    );
    assert_eq!(
        lookup("std::str::iter::SplitWhitespace::next"),
        Some(StubKind::SplitWhitespaceNext)
    );
}

#[test]
fn lookup_allocator_operations() {
    // Core allocator functions
    assert_eq!(lookup("alloc::alloc::alloc"), Some(StubKind::RustAlloc));
    assert_eq!(lookup("__rust_alloc"), Some(StubKind::RustAlloc));
    assert_eq!(lookup("std::alloc::alloc_zeroed"), Some(StubKind::RustAllocZeroed));
    assert_eq!(lookup("__rust_alloc_zeroed"), Some(StubKind::RustAllocZeroed));
    assert_eq!(lookup("__rust_dealloc"), Some(StubKind::RustDealloc));
    assert_eq!(lookup("__rust_realloc"), Some(StubKind::RustRealloc));
    // Global::deallocate trait method (used by Box::drop)
    assert_eq!(
        lookup("<std::alloc::Global as std::alloc::Allocator>::deallocate"),
        Some(StubKind::RustDealloc)
    );
    // Allocator::allocate trait method
    assert_eq!(
        lookup("<std::alloc::Global as std::alloc::Allocator>::allocate"),
        Some(StubKind::AllocatorAllocate)
    );
    assert_eq!(lookup("alloc::alloc::realloc"), Some(StubKind::RustRealloc));
    // exchange_malloc is used by Box::new via vec! macro
    assert_eq!(lookup("alloc::alloc::exchange_malloc"), Some(StubKind::RustAlloc));
    // Global low-level implementation path
    assert_eq!(lookup("std::alloc::Global::alloc_impl"), Some(StubKind::GlobalAllocImpl));
    // rustc no-alloc shim guard symbol
    assert_eq!(
        lookup("__rust_no_alloc_shim_is_unstable_v2"),
        Some(StubKind::RustNoAllocShimIsUnstable)
    );
    // handle_alloc_error for error paths
    assert_eq!(lookup("std::alloc::handle_alloc_error"), Some(StubKind::HandleAllocError));
    assert_eq!(
        lookup("alloc::alloc::handle_alloc_error::rt_error"),
        Some(StubKind::HandleAllocError)
    );
    assert_eq!(lookup("std::alloc::handle_alloc_error_v2"), None);
    assert_eq!(lookup("core::alloc::Layout::size"), Some(StubKind::LayoutSize));
    // Pointer utilities (used in allocation paths)
    assert_eq!(lookup("core::ptr::NonNull::<u8>::new"), Some(StubKind::NonNullNew));
    // NonNull::as_mut_ptr for slice pointer extraction
    assert_eq!(lookup("std::ptr::NonNull::<[u8]>::as_mut_ptr"), Some(StubKind::NonNullAsMutPtr));
    // Box::into_raw_with_allocator for Box decomposition
    assert_eq!(
        lookup("std::boxed::Box::<i32, std::alloc::Global>::into_raw_with_allocator"),
        Some(StubKind::BoxIntoRawWithAllocator)
    );
    // Vec::from_raw_parts_in for Vec construction
    assert_eq!(
        lookup("std::vec::Vec::<i32, std::alloc::Global>::from_raw_parts_in"),
        Some(StubKind::VecFromRawPartsIn)
    );
    // Vec::from_raw_parts (non-_in variant) reuses same stub (#3451)
    assert_eq!(lookup("std::vec::Vec::<i32>::from_raw_parts"), Some(StubKind::VecFromRawPartsIn));
    // Try::branch and FromResidual::from_residual - ? operator stubs (Part of #2196 coverage)
    assert_eq!(
        lookup("<core::result::Result<*mut u8, core::alloc::AllocError> as std::ops::Try>::branch"),
        Some(StubKind::TryBranch)
    );
    assert_eq!(
        lookup(
            "<core::result::Result<(), core::alloc::AllocError> as std::ops::FromResidual>::from_residual"
        ),
        Some(StubKind::FromResidualFromResidual)
    );
}

#[test]
fn lookup_layout_format_and_memory_intrinsics() {
    // Layout::new<T>() - create layout from type (#1037)
    assert_eq!(lookup("core::alloc::Layout::<i32>::new"), Some(StubKind::LayoutNew));
    // Layout::new MUST NOT match hypothetical new_* methods
    assert_eq!(lookup("core::alloc::Layout::<i32>::new_for_value"), None);
    // Layout::array<T>(n) - compute array layout (#1037)
    assert_eq!(lookup("core::alloc::Layout::<i32>::array"), Some(StubKind::LayoutArray));
    // Layout::array MUST NOT match hypothetical array_* methods
    assert_eq!(lookup("core::alloc::Layout::<i32>::array_of"), None);
    // Part of #3273: Layout::array::inner(element_size, align, n)
    assert_eq!(lookup("std::alloc::Layout::array::inner"), Some(StubKind::LayoutArrayInner));
    assert_eq!(lookup("core::alloc::Layout::array::inner"), Some(StubKind::LayoutArrayInner));

    // Part of #1529: Alignment::as_usize - extract alignment value
    assert_eq!(lookup("core::ptr::Alignment::as_usize"), Some(StubKind::AlignmentAsUsize));
    assert_eq!(lookup("core::ptr::Alignment::<u8>::as_usize"), Some(StubKind::AlignmentAsUsize));
    // Alignment::as_usize MUST NOT match hypothetical as_usize_* methods
    assert_eq!(lookup("core::ptr::Alignment::as_usize_unchecked"), None);

    // Part of #1529: fmt::rt::Argument::new_display - formatting stub
    assert_eq!(
        lookup("core::fmt::rt::Argument::new_display"),
        Some(StubKind::FmtArgumentNewDisplay)
    );
    assert_eq!(
        lookup("core::fmt::rt::Argument::<u8>::new_display"),
        Some(StubKind::FmtArgumentNewDisplay)
    );
    // fmt::Arguments constructors should route to diverging formatting stubs.
    assert_eq!(lookup("core::fmt::Arguments::new"), Some(StubKind::FmtArgumentsNew));
    assert_eq!(lookup("core::fmt::Arguments::from_str"), Some(StubKind::FmtArgumentsFromStr));
    // new_display MUST NOT match hypothetical new_display_* methods
    assert_eq!(lookup("core::fmt::rt::Argument::new_display_debug"), None);

    // mem::size_of / align_of stubs
    assert_eq!(lookup("core::mem::size_of"), Some(StubKind::MemSizeOf));
    assert_eq!(lookup("std::mem::align_of"), Some(StubKind::MemAlignOf));
    // raw intrinsics::align_of (Part of #4087: harness uses std::intrinsics::align_of)
    assert_eq!(lookup("core::intrinsics::align_of"), Some(StubKind::MemAlignOf));
    assert_eq!(lookup("std::intrinsics::align_of"), Some(StubKind::MemAlignOf));
    // size_of_val / align_of_val MUST NOT match size_of / align_of stubs.
    assert_eq!(lookup("core::mem::size_of_val"), None);
    assert_eq!(lookup("std::mem::align_of_val"), None);

    // Part of #1529: Layout::from_size_align_unchecked - unsafe layout constructor
    assert_eq!(
        lookup("core::alloc::Layout::from_size_align_unchecked"),
        Some(StubKind::LayoutFromSizeAlignUnchecked)
    );
    assert_eq!(
        lookup("core::alloc::Layout::<u8>::from_size_align_unchecked"),
        Some(StubKind::LayoutFromSizeAlignUnchecked)
    );
    // from_size_align_unchecked MUST NOT match hypothetical from_size_align_unchecked_* methods
    assert_eq!(lookup("core::alloc::Layout::from_size_align_unchecked_v2"), None);
}

#[test]
fn lookup_panic_and_ub_operations() {
    // Panic/UB helper paths and precondition checks.
    // Part of #3300: panic_nounwind/panic_nounwind_fmt reclassified to PanicError
    // because checked arithmetic overflow (e.g., ptr.offset) calls them.
    assert_eq!(lookup("core::panicking::panic_nounwind"), Some(StubKind::PanicError));
    assert_eq!(lookup("core::panicking::panic_nounwind_fmt"), Some(StubKind::PanicError));
    // Part of #2252: assert!() macro panic paths return PanicError.
    assert_eq!(lookup("core::panicking::panic"), Some(StubKind::PanicError));
    assert_eq!(lookup("core::panicking::begin_panic"), Some(StubKind::PanicError));
    assert_eq!(lookup("core::panicking::assert_failed"), Some(StubKind::PanicError));
    assert_eq!(lookup("core::ub_checks::check_language_ub"), Some(StubKind::UbCheckLanguageUb));
    assert_eq!(
        lookup("core::ub_checks::maybe_is_aligned_and_not_null"),
        Some(StubKind::UbCheckMaybeIsAligned)
    );
    assert_eq!(
        lookup("core::ub_checks::is_nonoverlapping"),
        Some(StubKind::UbCheckMaybeIsNonoverlapping)
    );
    assert_eq!(lookup("core::intrinsics::precondition_check"), Some(StubKind::PreconditionCheck));
}

#[test]
fn lookup_array_iterator_stubs() {
    // Part of #2916: 4 array-iterator internal callees
    // assert_inhabited - compile-time inhabitedness check, no-op
    assert_eq!(lookup("std::intrinsics::assert_inhabited"), Some(StubKind::AssertInhabited));
    assert_eq!(lookup("core::intrinsics::assert_inhabited"), Some(StubKind::AssertInhabited));
    // MaybeUninit::as_ptr - transparent wrapper identity
    assert_eq!(lookup("std::mem::MaybeUninit::<u32>::as_ptr"), Some(StubKind::MaybeUninitAsPtr));
    assert_eq!(lookup("core::mem::MaybeUninit::<T>::as_ptr"), Some(StubKind::MaybeUninitAsPtr));
    // SliceGetUnchecked - unchecked element access
    assert_eq!(
        lookup("core::slice::<impl [u32]>::get_unchecked"),
        Some(StubKind::SliceGetUnchecked),
    );
    assert_eq!(lookup("core::slice::<impl [T]>::get_unchecked"), Some(StubKind::SliceGetUnchecked),);
    // IndexRange::len is handled via direct path match (no StubKind), tested in CHC dispatch tests
}

#[test]
fn lookup_slice_from_raw_parts_mut_routes_to_ptr_cast() {
    // Part of #2876 post-OI4: mut slice helper routed through ptr-cast lane.
    assert_eq!(lookup("std::slice::from_raw_parts_mut"), Some(StubKind::PtrCast));
    assert_eq!(lookup("core::slice::from_raw_parts_mut"), Some(StubKind::PtrCast));
}

#[test]
fn lookup_ptr_operations() {
    // ptr::write - method form (Part of #1037)
    assert_eq!(lookup("core::ptr::mut_ptr::<u8>::write"), Some(StubKind::PtrWrite));
    assert_eq!(lookup("std::ptr::mut_ptr::<i32>::write"), Some(StubKind::PtrWrite));
    // ptr::write - standalone function form
    assert_eq!(lookup("std::ptr::write"), Some(StubKind::PtrWrite));
    assert_eq!(lookup("core::ptr::write"), Some(StubKind::PtrWrite));
    // ptr::write MUST NOT match write_bytes, write_volatile, write_unaligned
    assert_eq!(lookup("core::ptr::mut_ptr::<u8>::write_bytes"), None);
    assert_eq!(lookup("core::ptr::mut_ptr::<u8>::write_volatile"), None);
    assert_eq!(lookup("core::ptr::mut_ptr::<u8>::write_unaligned"), None);

    // ptr::read - method form
    assert_eq!(lookup("core::ptr::const_ptr::<u8>::read"), Some(StubKind::PtrRead));
    // ptr::read - standalone function form
    assert_eq!(lookup("std::ptr::read"), Some(StubKind::PtrRead));
    assert_eq!(lookup("core::ptr::read"), Some(StubKind::PtrRead));
    // ptr::read MUST NOT match read_volatile, read_unaligned
    assert_eq!(lookup("core::ptr::mut_ptr::<u8>::read_volatile"), None);
    assert_eq!(lookup("core::ptr::mut_ptr::<u8>::read_unaligned"), None);

    // ptr::add - method form
    assert_eq!(lookup("core::ptr::mut_ptr::<u8>::add"), Some(StubKind::PtrAdd));
    // ptr::add MUST NOT match add_unsigned, etc.
    assert_eq!(lookup("core::ptr::mut_ptr::<u8>::add_unsigned"), None);

    // ptr::addr - extract address as usize
    assert_eq!(lookup("core::ptr::mut_ptr::<u8>::addr"), Some(StubKind::PtrAddr));
    assert_eq!(lookup("core::ptr::const_ptr::<u8>::addr"), Some(StubKind::PtrAddr));
    // ptr::is_null
    assert_eq!(lookup("core::ptr::const_ptr::<u8>::is_null"), Some(StubKind::PtrIsNull));
    assert_eq!(lookup("core::ptr::mut_ptr::<u8>::is_null"), Some(StubKind::PtrIsNull));
    // ptr::is_null::runtime - const eval null check intrinsic (Part of #2196 coverage)
    assert_eq!(
        lookup("core::ptr::const_ptr::<u8>::is_null::runtime"),
        Some(StubKind::PtrIsNullRuntime)
    );
    assert_eq!(
        lookup("core::ptr::mut_ptr::<i32>::is_null::runtime"),
        Some(StubKind::PtrIsNullRuntime)
    );
    // ptr::cast_const - mut -> const pointer cast
    assert_eq!(lookup("core::ptr::mut_ptr::<u8>::cast_const"), Some(StubKind::PtrCastConst));
    // ptr::cast - generic type cast
    assert_eq!(lookup("core::ptr::mut_ptr::<u8>::cast"), Some(StubKind::PtrCast));
    assert_eq!(lookup("core::ptr::const_ptr::<u8>::cast"), Some(StubKind::PtrCast));
}

#[test]
fn lookup_nonnull_operations() {
    assert_eq!(lookup("core::ptr::NonNull::<u8>::new"), Some(StubKind::NonNullNew));
    assert_eq!(lookup("core::ptr::NonNull::<u8>::new_unchecked"), Some(StubKind::NonNullNew));
    assert_eq!(lookup("std::ptr::NonNull::<[u8]>::as_mut_ptr"), Some(StubKind::NonNullAsMutPtr));
    assert_eq!(
        lookup("core::ptr::NonNull::<[u8]>::slice_from_raw_parts"),
        Some(StubKind::NonNullSliceFromRawParts)
    );
    assert_eq!(
        lookup("core::ptr::NonNull::<[u8]>::as_non_null_ptr"),
        Some(StubKind::NonNullAsNonNullPtr)
    );
    assert_eq!(lookup("core::ptr::NonNull::<u8>::dangling"), Some(StubKind::NonNullDangling));
    assert_eq!(lookup("core::ptr::NonNull::<u8>::as_ptr"), Some(StubKind::NonNullAsPtr));
    // NonZero::get - extract inner value (Part of #2196 coverage)
    assert_eq!(lookup("core::num::NonZero::<u32>::get"), Some(StubKind::NonZeroGet));
    assert_eq!(lookup("core::num::NonZero::<usize>::get"), Some(StubKind::NonZeroGet));
    // Part of #2876 RC3 follow-up: Vec reserve internals call niche helper.
    assert_eq!(
        lookup("core::num::niche_types::UsizeNoHighBit::as_inner"),
        Some(StubKind::NonZeroGet)
    );
}

#[test]
fn lookup_layout_operations() {
    assert_eq!(lookup("core::alloc::Layout::size"), Some(StubKind::LayoutSize));
    assert_eq!(lookup("core::alloc::Layout::align"), Some(StubKind::LayoutAlign));
    assert_eq!(lookup("core::alloc::Layout::dangling"), Some(StubKind::LayoutDangling));
    assert_eq!(
        lookup("core::alloc::Layout::is_size_align_valid"),
        Some(StubKind::LayoutIsSizeAlignValid)
    );
    assert_eq!(
        lookup("core::alloc::Layout::padding_needed_for"),
        Some(StubKind::LayoutPaddingNeededFor)
    );
    assert_eq!(lookup("core::alloc::Layout::<i32>::new"), Some(StubKind::LayoutNew));
    assert_eq!(lookup("core::alloc::Layout::<i32>::array"), Some(StubKind::LayoutArray));
    assert_eq!(
        lookup("core::alloc::Layout::from_size_align_unchecked"),
        Some(StubKind::LayoutFromSizeAlignUnchecked)
    );
}

#[test]
fn lookup_kani_mem_and_provenance_helpers() {
    // Part of #1229: kani::mem predicates may survive as calls and require stubs.
    assert_eq!(lookup("kani::mem::is_ptr_aligned"), Some(StubKind::KaniMemIsPtrAligned));
    assert_eq!(lookup("kani::mem::is_inbounds"), Some(StubKind::KaniMemIsInbounds));
    assert_eq!(
        lookup("kani::mem::assert_is_initialized"),
        Some(StubKind::KaniMemAssertIsInitialized)
    );
    // Part of #3470: Wrapper stubs for non-inlined can_read_unaligned / can_dereference.
    assert_eq!(lookup("kani::mem::can_read_unaligned"), Some(StubKind::KaniMemCanReadUnaligned));
    assert_eq!(lookup("kani::mem::can_dereference"), Some(StubKind::KaniMemCanDereference));

    // Provenance helpers used by pointer modeling.
    assert_eq!(lookup("core::ptr::without_provenance_mut"), Some(StubKind::WithoutProvenanceMut));
    assert_eq!(lookup("core::ptr::without_provenance"), Some(StubKind::WithoutProvenance));

    // ptr::null / ptr::null_mut (Part of #3323)
    assert_eq!(lookup("core::ptr::null"), Some(StubKind::PtrNull));
    assert_eq!(lookup("std::ptr::null"), Some(StubKind::PtrNull));
    assert_eq!(lookup("core::ptr::null_mut"), Some(StubKind::PtrNull));
    assert_eq!(lookup("std::ptr::null_mut"), Some(StubKind::PtrNull));
}

#[test]
fn lookup_option_methods() {
    // Option methods are stubbed for verification simplification
    assert_eq!(lookup("core::option::Option::unwrap"), Some(StubKind::OptionUnwrap));
    assert_eq!(lookup("core::option::Option::<u8>::ok_or"), Some(StubKind::OptionOkOr));
    // Option::is_some/is_none - discriminant checks (Part of #1739)
    assert_eq!(lookup("core::option::Option::<u8>::is_some"), Some(StubKind::OptionIsSome));
    assert_eq!(lookup("std::option::Option::<u32>::is_some"), Some(StubKind::OptionIsSome));
    assert_eq!(lookup("core::option::Option::<u8>::is_some_and"), Some(StubKind::OptionIsSomeAnd));
    assert_eq!(lookup("std::option::Option::<u32>::is_some_and"), Some(StubKind::OptionIsSomeAnd));
    assert_eq!(lookup("core::option::Option::<u8>::is_none"), Some(StubKind::OptionIsNone));
    assert_eq!(lookup("std::option::Option::<u32>::is_none"), Some(StubKind::OptionIsNone));
    // Option::unwrap_or ITE(is_some, value, default) (Part of #1836)
    assert_eq!(lookup("core::option::Option::<u8>::unwrap_or"), Some(StubKind::OptionUnwrapOr));
    assert_eq!(lookup("std::option::Option::<u32>::unwrap_or"), Some(StubKind::OptionUnwrapOr));
    // unwrap_or must not false-match unwrap_or_else
    assert_eq!(
        lookup("core::option::Option::<u8>::unwrap_or_else"),
        Some(StubKind::OptionUnwrapOrElse)
    );
    // Option::expect delegates to unwrap semantics (Part of #1836)
    assert_eq!(lookup("core::option::Option::<u8>::expect"), Some(StubKind::OptionExpect));
    assert_eq!(lookup("std::option::Option::<u32>::expect"), Some(StubKind::OptionExpect));
    // Option::unwrap_or_else over-approximates closure (Part of #1836)
    assert_eq!(
        lookup("core::option::Option::<u8>::unwrap_or_else"),
        Some(StubKind::OptionUnwrapOrElse)
    );
    assert_eq!(
        lookup("std::option::Option::<u32>::unwrap_or_else"),
        Some(StubKind::OptionUnwrapOrElse)
    );
    // Result::unwrap_or must not be matched when path is Option::unwrap_or
    assert_ne!(lookup("core::option::Option::<u8>::unwrap_or"), Some(StubKind::ResultUnwrapOr));
}

#[test]
fn lookup_result_predicate_methods() {
    assert_eq!(lookup("core::result::Result::<u8, u16>::is_ok"), Some(StubKind::ResultIsOk));
    assert_eq!(lookup("std::result::Result::<u8, u16>::is_err"), Some(StubKind::ResultIsErr));
    // Result::unwrap extracts Ok value (Part of #1836)
    assert_eq!(lookup("core::result::Result::<u8, u16>::unwrap"), Some(StubKind::ResultUnwrap));
    assert_eq!(lookup("std::result::Result::<u32, ()>::unwrap"), Some(StubKind::ResultUnwrap));
    // Result::expect delegates to unwrap semantics (Part of #1836)
    assert_eq!(lookup("core::result::Result::<u8, u16>::expect"), Some(StubKind::ResultExpect));
    assert_eq!(lookup("std::result::Result::<u32, ()>::expect"), Some(StubKind::ResultExpect));
    // Result::unwrap_err extracts Err value (Part of #3587)
    assert_eq!(
        lookup("core::result::Result::<u8, u16>::unwrap_err"),
        Some(StubKind::ResultUnwrapErr)
    );
    assert_eq!(
        lookup("std::result::Result::<bool, bool>::unwrap_err"),
        Some(StubKind::ResultUnwrapErr)
    );
    // Result::unwrap_or ITE(is_ok, ok_value, default) (Part of #1836)
    assert_eq!(
        lookup("core::result::Result::<u8, u16>::unwrap_or"),
        Some(StubKind::ResultUnwrapOr)
    );
    assert_eq!(lookup("std::result::Result::<u32, ()>::unwrap_or"), Some(StubKind::ResultUnwrapOr));
    // unwrap_or must not false-match unwrap_or_else
    assert_eq!(
        lookup("core::result::Result::<u8, u16>::unwrap_or_else"),
        Some(StubKind::ResultUnwrapOrElse)
    );
    // Result::unwrap_or_else over-approximates closure (Part of #1836)
    assert_eq!(
        lookup("core::result::Result::<u8, u16>::unwrap_or_else"),
        Some(StubKind::ResultUnwrapOrElse)
    );
    assert_eq!(
        lookup("std::result::Result::<u32, ()>::unwrap_or_else"),
        Some(StubKind::ResultUnwrapOrElse)
    );
    // Result::map over-approximates closure (Part of #1836)
    assert_eq!(lookup("core::result::Result::<u8, u16>::map"), Some(StubKind::ResultMap));
    assert_eq!(lookup("std::result::Result::<u32, ()>::map"), Some(StubKind::ResultMap));
    // Result::and_then over-approximates closure (Part of #1836)
    assert_eq!(lookup("core::result::Result::<u8, u16>::and_then"), Some(StubKind::ResultAndThen));
    assert_eq!(lookup("std::result::Result::<u32, ()>::and_then"), Some(StubKind::ResultAndThen));
    // Result::map_err over-approximates closure (Part of #1836)
    // map_err must not false-match map (suffix ordering correctness)
    assert_eq!(lookup("core::result::Result::<u8, u16>::map_err"), Some(StubKind::ResultMapErr));
    assert_eq!(lookup("std::result::Result::<u32, ()>::map_err"), Some(StubKind::ResultMapErr));
    // Result::ok converts Result to Option<T> (Part of #1836)
    // ok must not false-match is_ok, ok_or, or ok_or_else
    assert_eq!(lookup("core::result::Result::<u8, u16>::ok"), Some(StubKind::ResultOk));
    assert_eq!(lookup("std::result::Result::<u32, ()>::ok"), Some(StubKind::ResultOk));
    // Result::err converts Result to Option<E> (Part of #1836)
    // err must not false-match is_err or map_err
    assert_eq!(lookup("core::result::Result::<u8, u16>::err"), Some(StubKind::ResultErr));
    assert_eq!(lookup("std::result::Result::<u32, ()>::err"), Some(StubKind::ResultErr));
    // Verify no false matches: is_ok/is_err must still match their own stubs
    assert_eq!(lookup("core::result::Result::<u8, u16>::is_ok"), Some(StubKind::ResultIsOk));
    assert_eq!(lookup("core::result::Result::<u8, u16>::is_err"), Some(StubKind::ResultIsErr));
}

#[test]
fn lookup_option_combinator_methods() {
    // Option::and_then over-approximates closure (Part of #1836)
    assert_eq!(lookup("core::option::Option::<u8>::and_then"), Some(StubKind::OptionAndThen));
    assert_eq!(lookup("std::option::Option::<u32>::and_then"), Some(StubKind::OptionAndThen));
    // Option::ok_or_else converts Option to Result (Part of #1836)
    assert_eq!(lookup("core::option::Option::<u8>::ok_or_else"), Some(StubKind::OptionOkOrElse));
    assert_eq!(lookup("std::option::Option::<u32>::ok_or_else"), Some(StubKind::OptionOkOrElse));
    // ok_or_else must not match ok_or (suffix ordering correctness)
    assert_eq!(lookup("core::option::Option::<u8>::ok_or"), Some(StubKind::OptionOkOr));
    // Option::map over-approximates closure (Part of #1836)
    assert_eq!(lookup("core::option::Option::<u8>::map"), Some(StubKind::OptionMap));
    assert_eq!(lookup("std::option::Option::<u32>::map"), Some(StubKind::OptionMap));
    // Option::map must not match Result::map
    assert_eq!(lookup("core::result::Result::<u8, u16>::map"), Some(StubKind::ResultMap));
}

#[test]
fn lookup_str_nth_helpers() {
    // kani_str_bytes_nth / kani_str_chars_nth — MIR-rewritten str helpers (#4161)
    assert_eq!(lookup("kani::iter_string::kani_str_bytes_nth"), Some(StubKind::StrBytesNth));
    assert_eq!(lookup("kani::iter_string::kani_str_chars_nth"), Some(StubKind::StrCharsNth));
    // Also match mangled paths from MIR
    assert_eq!(lookup("kani_core::iter_string::kani_str_bytes_nth"), Some(StubKind::StrBytesNth));
    assert_eq!(lookup("kani_core::iter_string::kani_str_chars_nth"), Some(StubKind::StrCharsNth));
}
