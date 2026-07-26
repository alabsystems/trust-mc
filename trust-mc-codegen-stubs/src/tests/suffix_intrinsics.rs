// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Direct suffix tests for option, result, alloc, layout, NonNull,
// raw pointer, fmt, panic, and UB/mem helpers.

use super::{StubKind, StubRegistry};

// -- lookup_option_suffix --

#[test]
fn option_suffix_all_operations() {
    let cases = vec![
        ("core::option::Option::<u32>::unwrap", StubKind::OptionUnwrap),
        ("core::option::Option::<u32>::unwrap_unchecked", StubKind::OptionUnwrapUnchecked),
        ("core::option::Option::<u32>::is_some", StubKind::OptionIsSome),
        ("core::option::Option::<u32>::is_none", StubKind::OptionIsNone),
        ("core::option::Option::<u32>::unwrap_or_else", StubKind::OptionUnwrapOrElse),
        ("core::option::Option::<u32>::unwrap_or", StubKind::OptionUnwrapOr),
        ("core::option::Option::<u32>::expect", StubKind::OptionExpect),
        ("core::option::Option::<u32>::ok_or_else", StubKind::OptionOkOrElse),
        ("core::option::Option::<u32>::ok_or", StubKind::OptionOkOr),
        ("core::option::Option::<u32>::and_then", StubKind::OptionAndThen),
        ("core::option::Option::<u32>::map", StubKind::OptionMap),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_option_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn option_suffix_unwrap_excludes_unwrap_or_and_unwrap_unchecked() {
    // "unwrap" should not false-match "unwrap_or" or "unwrap_unchecked"
    assert_ne!(
        StubRegistry::lookup_option_suffix("core::option::Option::<u32>::unwrap_or"),
        Some(StubKind::OptionUnwrap)
    );
    assert_ne!(
        StubRegistry::lookup_option_suffix("core::option::Option::<u32>::unwrap_unchecked"),
        Some(StubKind::OptionUnwrap)
    );
}

#[test]
fn option_suffix_unknown_returns_none() {
    assert_eq!(StubRegistry::lookup_option_suffix("core::option::Option::<u32>::as_ref"), None);
    assert_eq!(StubRegistry::lookup_option_suffix("core::option::Option::<u32>::as_mut"), None);
}

// -- lookup_result_suffix --

#[test]
fn result_suffix_all_operations() {
    let cases = vec![
        ("core::result::Result::<u32, ()>::is_ok", StubKind::ResultIsOk),
        ("core::result::Result::<u32, ()>::is_err", StubKind::ResultIsErr),
        ("core::result::Result::<u32, ()>::and_then", StubKind::ResultAndThen),
        ("core::result::Result::<u32, ()>::ok", StubKind::ResultOk),
        ("core::result::Result::<u32, ()>::err", StubKind::ResultErr),
        ("core::result::Result::<u32, ()>::map_err", StubKind::ResultMapErr),
        ("core::result::Result::<u32, ()>::map", StubKind::ResultMap),
        ("core::result::Result::<u32, ()>::unwrap_or_else", StubKind::ResultUnwrapOrElse),
        ("core::result::Result::<u32, ()>::unwrap_or", StubKind::ResultUnwrapOr),
        ("core::result::Result::<u32, ()>::expect", StubKind::ResultExpect),
        ("core::result::Result::<u32, ()>::unwrap_err", StubKind::ResultUnwrapErr),
        ("core::result::Result::<u32, ()>::unwrap", StubKind::ResultUnwrap),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_result_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn result_suffix_unknown_returns_none() {
    assert_eq!(
        StubRegistry::lookup_result_suffix("core::result::Result::<u32, ()>::transpose"),
        None
    );
}

// -- lookup_alloc_suffix --

#[test]
fn alloc_suffix_all_alloc_patterns() {
    assert_eq!(StubRegistry::lookup_alloc_suffix("alloc::alloc::alloc"), Some(StubKind::RustAlloc));
    assert_eq!(StubRegistry::lookup_alloc_suffix("__rust_alloc"), Some(StubKind::RustAlloc));
    assert_eq!(StubRegistry::lookup_alloc_suffix("std::alloc::alloc"), Some(StubKind::RustAlloc));
    assert_eq!(
        StubRegistry::lookup_alloc_suffix("alloc::alloc::exchange_malloc"),
        Some(StubKind::RustAlloc)
    );
}

#[test]
fn alloc_suffix_alloc_zeroed() {
    assert_eq!(
        StubRegistry::lookup_alloc_suffix("alloc::alloc::alloc_zeroed"),
        Some(StubKind::RustAllocZeroed)
    );
    assert_eq!(
        StubRegistry::lookup_alloc_suffix("__rust_alloc_zeroed"),
        Some(StubKind::RustAllocZeroed)
    );
}

#[test]
fn alloc_suffix_dealloc_with_allocator_trait() {
    assert_eq!(
        StubRegistry::lookup_alloc_suffix("<Global as Allocator>::deallocate"),
        Some(StubKind::RustDealloc)
    );
}

#[test]
fn alloc_suffix_allocator_allocate() {
    assert_eq!(
        StubRegistry::lookup_alloc_suffix("<Global as Allocator>::allocate"),
        Some(StubKind::AllocatorAllocate)
    );
}

#[test]
fn alloc_suffix_handle_alloc_error() {
    assert_eq!(
        StubRegistry::lookup_alloc_suffix("std::alloc::handle_alloc_error"),
        Some(StubKind::HandleAllocError)
    );
    assert_eq!(
        StubRegistry::lookup_alloc_suffix("alloc::alloc::handle_alloc_error::rt_error"),
        Some(StubKind::HandleAllocError)
    );
}

#[test]
fn alloc_suffix_no_alloc_shim() {
    assert_eq!(
        StubRegistry::lookup_alloc_suffix("__rust_no_alloc_shim_is_unstable"),
        Some(StubKind::RustNoAllocShimIsUnstable)
    );
}

#[test]
fn alloc_suffix_global_alloc_impl() {
    assert_eq!(
        StubRegistry::lookup_alloc_suffix("std::alloc::Global::alloc_impl"),
        Some(StubKind::GlobalAllocImpl)
    );
}

// -- lookup_layout_suffix --

#[test]
fn layout_suffix_all_operations() {
    let cases = vec![
        ("core::alloc::Layout::size", StubKind::LayoutSize),
        ("core::alloc::Layout::align", StubKind::LayoutAlign),
        ("core::alloc::Layout::dangling", StubKind::LayoutDangling),
        ("core::alloc::Layout::is_size_align_valid", StubKind::LayoutIsSizeAlignValid),
        ("core::alloc::Layout::padding_needed_for", StubKind::LayoutPaddingNeededFor),
        ("core::alloc::Layout::<i32>::array", StubKind::LayoutArray),
        ("core::alloc::Layout::<i32>::new", StubKind::LayoutNew),
        ("core::alloc::Layout::from_size_align_unchecked", StubKind::LayoutFromSizeAlignUnchecked),
        // Part of #2632: hashbrown Layout methods
        ("core::alloc::Layout::calculate_layout_for", StubKind::LayoutCalculateLayoutFor),
        ("core::alloc::Layout::for_value_raw", StubKind::LayoutForValueRaw),
        ("core::alloc::Layout::from_size_align", StubKind::LayoutFromSizeAlign),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_layout_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn layout_suffix_unknown_returns_none() {
    assert_eq!(StubRegistry::lookup_layout_suffix("core::alloc::Layout::extend"), None);
}

// -- lookup_nonnull_suffix --

#[test]
fn nonnull_suffix_all_operations() {
    let cases = vec![
        ("core::ptr::NonNull::<u8>::new_unchecked", StubKind::NonNullNew),
        ("core::ptr::NonNull::<u8>::new", StubKind::NonNullNew),
        ("core::ptr::NonNull::<[u8]>::slice_from_raw_parts", StubKind::NonNullSliceFromRawParts),
        ("core::ptr::NonNull::<[u8]>::as_non_null_ptr", StubKind::NonNullAsNonNullPtr),
        ("core::ptr::NonNull::<u8>::dangling", StubKind::NonNullDangling),
        ("core::ptr::NonNull::<u8>::as_mut_ptr", StubKind::NonNullAsMutPtr),
        ("core::ptr::NonNull::<u8>::as_ptr", StubKind::NonNullAsPtr),
        // Part of #2632: NonNull::cast used by hashbrown
        ("core::ptr::NonNull::<u8>::cast", StubKind::NonNullCast),
        // Part of #2876 RC2-B: pre-inlined Vec::IntoIter internals
        ("core::ptr::NonNull::<u8>::add", StubKind::PtrAdd),
        ("core::ptr::NonNull::<u8>::read", StubKind::PtrRead),
        // Part of #2876 post-OI4: ref/mut helper conversions route to ptr-cast lane.
        ("core::ptr::NonNull::<u8>::as_ref", StubKind::PtrCast),
        ("core::ptr::NonNull::<u8>::as_mut", StubKind::PtrCast),
        ("core::ptr::NonNull::<u8>::from_ref", StubKind::PtrCast),
        ("core::ptr::NonNull::<u8>::from_mut", StubKind::PtrCast),
        ("std::ptr::NonNull::<u8>::as_ref", StubKind::PtrCast),
        ("std::ptr::NonNull::<u8>::as_mut", StubKind::PtrCast),
        ("std::ptr::NonNull::<u8>::from_ref", StubKind::PtrCast),
        ("std::ptr::NonNull::<u8>::from_mut", StubKind::PtrCast),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_nonnull_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn nonnull_suffix_unknown_returns_none() {
    assert_eq!(StubRegistry::lookup_nonnull_suffix("core::ptr::NonNull::<u8>::offset"), None);
}

// -- lookup_raw_ptr_suffix --

#[test]
fn raw_ptr_suffix_all_operations() {
    let cases = vec![
        ("core::ptr::mut_ptr::<u8>::add", StubKind::PtrAdd),
        ("core::ptr::mut_ptr::<u8>::write", StubKind::PtrWrite),
        ("core::ptr::const_ptr::<u8>::read", StubKind::PtrRead),
        ("core::ptr::mut_ptr::<u8>::addr", StubKind::PtrAddr),
        ("core::ptr::const_ptr::<u8>::is_null", StubKind::PtrIsNull),
        ("core::ptr::mut_ptr::<u8>::cast_const", StubKind::PtrCastConst),
        ("core::ptr::mut_ptr::<u8>::cast", StubKind::PtrCast),
        ("core::ptr::const_ptr::<u8>::cast", StubKind::PtrCast),
        // Part of #2632: wrapping pointer arithmetic used by hashbrown
        ("core::ptr::mut_ptr::<u8>::sub", StubKind::PtrSub),
        ("core::ptr::mut_ptr::<u8>::wrapping_add", StubKind::PtrWrappingAdd),
        ("core::ptr::mut_ptr::<u8>::wrapping_sub", StubKind::PtrWrappingSub),
        // Part of #3514: byte-level wrapping add/sub (separate variants, no sizeof(T))
        ("core::ptr::mut_ptr::<u8>::wrapping_byte_add", StubKind::PtrWrappingByteAdd),
        ("core::ptr::const_ptr::<u8>::wrapping_byte_sub", StubKind::PtrWrappingByteSub),
        ("core::ptr::mut_ptr::<u8>::wrapping_offset", StubKind::PtrWrappingOffset),
        // Part of #3510: wrapping_byte_offset is a separate variant (byte-level, no sizeof(T))
        ("core::ptr::mut_ptr::<u8>::wrapping_byte_offset", StubKind::PtrWrappingByteOffset),
        ("core::ptr::mut_ptr::<u8>::with_metadata_of", StubKind::PtrWithMetadataOf),
    ];
    for (path, expected) in cases {
        assert_eq!(
            StubRegistry::lookup_raw_ptr_suffix(path),
            Some(expected),
            "Failed for path: {}",
            path
        );
    }
}

#[test]
fn raw_ptr_suffix_cast_const_requires_mut_ptr() {
    // cast_const is only for mut_ptr (converting *mut T to *const T)
    assert_eq!(StubRegistry::lookup_raw_ptr_suffix("core::ptr::const_ptr::<u8>::cast_const"), None);
}

#[test]
fn raw_ptr_suffix_unknown_returns_none() {
    assert_eq!(StubRegistry::lookup_raw_ptr_suffix("core::ptr::mut_ptr::<u8>::offset"), None);
}

// -- lookup_fmt_suffix --

#[test]
fn fmt_suffix_argument_new_display() {
    assert_eq!(
        StubRegistry::lookup_fmt_suffix("core::fmt::rt::Argument::<u8>::new_display"),
        Some(StubKind::FmtArgumentNewDisplay)
    );
}

#[test]
fn fmt_suffix_arguments_new() {
    assert_eq!(
        StubRegistry::lookup_fmt_suffix("core::fmt::Arguments::new"),
        Some(StubKind::FmtArgumentsNew)
    );
}

#[test]
fn fmt_suffix_arguments_from_str() {
    assert_eq!(
        StubRegistry::lookup_fmt_suffix("core::fmt::Arguments::from_str"),
        Some(StubKind::FmtArgumentsFromStr)
    );
}

#[test]
fn fmt_suffix_format_all_paths() {
    assert_eq!(StubRegistry::lookup_fmt_suffix("std::fmt::format"), Some(StubKind::FmtFormat));
    assert_eq!(StubRegistry::lookup_fmt_suffix("core::fmt::format"), Some(StubKind::FmtFormat));
    assert_eq!(StubRegistry::lookup_fmt_suffix("alloc::fmt::format"), Some(StubKind::FmtFormat));
}

#[test]
fn fmt_suffix_non_fmt_returns_none() {
    assert_eq!(StubRegistry::lookup_fmt_suffix("some::other::format"), None);
}

// -- lookup_panic_suffix --

#[test]
fn panic_suffix_unreachable_patterns() {
    // Only alloc error handler is genuinely unreachable (--no-malloc-may-fail).
    assert_eq!(
        StubRegistry::lookup_panic_suffix("__rust_alloc_error_handler"),
        Some(StubKind::PanicUnreachable)
    );
}

#[test]
fn panic_suffix_nounwind_is_error() {
    // Part of #3300: panic_nounwind/panic_nounwind_fmt reclassified to PanicError.
    // These are used by checked arithmetic overflow (e.g., checked_mul in
    // ptr.offset()) which IS reachable from user code.
    assert_eq!(
        StubRegistry::lookup_panic_suffix("core::panicking::panic_nounwind"),
        Some(StubKind::PanicError)
    );
    assert_eq!(
        StubRegistry::lookup_panic_suffix("core::panicking::panic_nounwind_fmt"),
        Some(StubKind::PanicError)
    );
}

#[test]
fn panic_suffix_rt_panic_fmt_is_error() {
    // Part of #2252: rt::panic_fmt is the user-facing panic entry point,
    // NOT a compiler-internal unreachable path. Reclassified from
    // PanicUnreachable to PanicError.
    assert_eq!(
        StubRegistry::lookup_panic_suffix("core::rt::panic_fmt"),
        Some(StubKind::PanicError)
    );
    assert_eq!(StubRegistry::lookup_panic_suffix("std::rt::panic_fmt"), Some(StubKind::PanicError));
}

#[test]
fn panic_suffix_panic_error_patterns() {
    // Part of #2252: assert!() macro panic paths return PanicError
    assert_eq!(
        StubRegistry::lookup_panic_suffix("core::panicking::begin_panic"),
        Some(StubKind::PanicError)
    );
    assert_eq!(
        StubRegistry::lookup_panic_suffix("core::panicking::panic"),
        Some(StubKind::PanicError)
    );
    assert_eq!(
        StubRegistry::lookup_panic_suffix("core::panicking::panic_explicit"),
        Some(StubKind::PanicError)
    );
    assert_eq!(
        StubRegistry::lookup_panic_suffix("core::panicking::panic_display"),
        Some(StubKind::PanicError)
    );
    assert_eq!(
        StubRegistry::lookup_panic_suffix("core::panicking::panic_fmt"),
        Some(StubKind::PanicError)
    );
    assert_eq!(
        StubRegistry::lookup_panic_suffix("core::panicking::panic_str"),
        Some(StubKind::PanicError)
    );
    assert_eq!(
        StubRegistry::lookup_panic_suffix("core::panicking::assert_failed"),
        Some(StubKind::PanicError)
    );
}

#[test]
fn panic_suffix_non_panic_returns_none() {
    assert_eq!(StubRegistry::lookup_panic_suffix("some::other::function"), None);
}

// -- lookup_ub_mem_suffix --

#[test]
fn ub_mem_suffix_all_operations() {
    assert_eq!(
        StubRegistry::lookup_ub_mem_suffix("core::ub_checks::check_language_ub"),
        Some(StubKind::UbCheckLanguageUb)
    );
    assert_eq!(
        StubRegistry::lookup_ub_mem_suffix("core::ub_checks::maybe_is_aligned_and_not_null"),
        Some(StubKind::UbCheckMaybeIsAligned)
    );
    assert_eq!(
        StubRegistry::lookup_ub_mem_suffix("core::ub_checks::is_aligned_and_not_null"),
        Some(StubKind::UbCheckMaybeIsAligned)
    );
    assert_eq!(
        StubRegistry::lookup_ub_mem_suffix("core::ub_checks::maybe_is_nonoverlapping"),
        Some(StubKind::UbCheckMaybeIsNonoverlapping)
    );
    assert_eq!(
        StubRegistry::lookup_ub_mem_suffix("core::ub_checks::is_nonoverlapping"),
        Some(StubKind::UbCheckMaybeIsNonoverlapping)
    );
    assert_eq!(StubRegistry::lookup_ub_mem_suffix("core::mem::size_of"), Some(StubKind::MemSizeOf));
    assert_eq!(
        StubRegistry::lookup_ub_mem_suffix("std::mem::align_of"),
        Some(StubKind::MemAlignOf)
    );
    // Part of #4087: raw intrinsics::align_of routing
    assert_eq!(
        StubRegistry::lookup_ub_mem_suffix("std::intrinsics::align_of"),
        Some(StubKind::MemAlignOf)
    );
    assert_eq!(
        StubRegistry::lookup_ub_mem_suffix("core::intrinsics::align_of"),
        Some(StubKind::MemAlignOf)
    );
    assert_eq!(
        StubRegistry::lookup_ub_mem_suffix("core::intrinsics::precondition_check"),
        Some(StubKind::PreconditionCheck)
    );
}

#[test]
fn ub_mem_suffix_size_of_excludes_size_of_val() {
    assert_eq!(StubRegistry::lookup_ub_mem_suffix("core::mem::size_of_val"), None);
}

#[test]
fn ub_mem_suffix_align_of_excludes_align_of_val() {
    assert_eq!(StubRegistry::lookup_ub_mem_suffix("std::mem::align_of_val"), None);
}
