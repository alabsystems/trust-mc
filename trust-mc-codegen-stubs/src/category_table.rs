// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Category dispatch table for StubRegistry::lookup() (Part of #2655).
//!
//! Replaces the 42-branch if-chain with an ordered data table.
//! ORDER MATTERS — entries with overlapping path patterns must appear
//! in the correct precedence order. See inline comments for constraints.

use super::{StubKind, StubRegistry};

/// A category dispatch entry: guard checks if path belongs to category,
/// handler resolves the specific StubKind.
///
/// When `exclusive` is true, if the guard matches then lookup stops here
/// regardless of whether handler returns Some or None. This prevents
/// substring-overlap fallthrough (e.g., RawVec matching Vec's guard).
pub(super) struct CategoryEntry {
    pub(super) guard: fn(&str) -> bool,
    pub(super) handler: fn(&str) -> Option<StubKind>,
    pub(super) exclusive: bool,
}

pub(super) const CATEGORY_TABLE: &[CategoryEntry] = &[
    // Option methods (Part of #1739, #1836)
    CategoryEntry {
        guard: |path| path.contains("Option::"),
        handler: |path| StubRegistry::lookup_option_suffix(path),
        exclusive: false,
    },
    // Result methods (Part of #2125, #1836)
    CategoryEntry {
        guard: |path| path.contains("Result::"),
        handler: |path| StubRegistry::lookup_result_suffix(path),
        exclusive: false,
    },
    // Allocation intrinsics (#1100)
    CategoryEntry {
        guard: |path| {
            path.contains("alloc")
                || path.contains("__rust_alloc")
                || path.contains("__rust_dealloc")
                || path.contains("__rust_realloc")
                || path.contains("exchange_malloc")
                || path.contains("Allocator")
        },
        handler: |path| StubRegistry::lookup_alloc_suffix(path),
        exclusive: false,
    },
    // Layout helper methods (#1112, #1037)
    CategoryEntry {
        guard: |path| path.contains("Layout::") || path.contains("Layout>"),
        handler: |path| StubRegistry::lookup_layout_suffix(path),
        exclusive: false,
    },
    // NonNull methods (#1112)
    CategoryEntry {
        guard: |path| path.contains("NonNull::"),
        handler: |path| StubRegistry::lookup_nonnull_suffix(path),
        exclusive: false,
    },
    // NonZero::get — guard is precise, handler always returns Some
    CategoryEntry {
        guard: |path| path.contains("NonZero") && path.ends_with(">::get"),
        handler: |_path| Some(StubKind::NonZeroGet),
        exclusive: false,
    },
    // core::num::niche_types::UsizeNoHighBit::as_inner behaves like NonZero::get.
    // Part of #2876 RC3 follow-up: classify pre-inlined Vec reserve path helper.
    CategoryEntry {
        guard: |path| path.contains("niche_types::UsizeNoHighBit") && path.ends_with("::as_inner"),
        handler: |_path| Some(StubKind::NonZeroGet),
        exclusive: false,
    },
    // Standalone ptr::write — guard is precise, handler always returns Some
    CategoryEntry {
        guard: |path| path.ends_with("std::ptr::write") || path.ends_with("core::ptr::write"),
        handler: |_path| Some(StubKind::PtrWrite),
        exclusive: false,
    },
    // Standalone ptr::read — guard is precise, handler always returns Some
    CategoryEntry {
        guard: |path| path.ends_with("std::ptr::read") || path.ends_with("core::ptr::read"),
        handler: |_path| Some(StubKind::PtrRead),
        exclusive: false,
    },
    // Method-form pointer operations on *const T / *mut T
    CategoryEntry {
        guard: |path| path.contains("const_ptr::") || path.contains("mut_ptr::"),
        handler: |path| StubRegistry::lookup_raw_ptr_suffix(path),
        exclusive: false,
    },
    // is_null::runtime — guard is precise, handler always returns Some
    CategoryEntry {
        guard: |path| path.contains("is_null::runtime"),
        handler: |_path| Some(StubKind::PtrIsNullRuntime),
        exclusive: false,
    },
    // Provenance helpers
    // without_provenance_mut MUST be checked before without_provenance (substring)
    CategoryEntry {
        guard: |path| path.contains("without_provenance_mut"),
        handler: |_path| Some(StubKind::WithoutProvenanceMut),
        exclusive: false,
    },
    CategoryEntry {
        guard: |path| path.contains("without_provenance"),
        handler: |_path| Some(StubKind::WithoutProvenance),
        exclusive: false,
    },
    // Alignment::new / Alignment::as_usize
    CategoryEntry {
        guard: |path| path.contains("Alignment::") || path.contains("Alignment>"),
        handler: |path| StubRegistry::lookup_alignment(path),
        exclusive: false,
    },
    // kani::mem helper functions (Part of #1229)
    CategoryEntry {
        guard: |path| path.contains("kani::mem::"),
        handler: |path| StubRegistry::lookup_kani_mem(path),
        exclusive: false,
    },
    // kani_str_bytes_nth / kani_str_chars_nth — MIR-rewritten str helpers (#4161)
    CategoryEntry {
        guard: |path| path.contains("kani_str_bytes_nth") || path.contains("kani_str_chars_nth"),
        handler: |path| {
            if path.contains("kani_str_bytes_nth") {
                Some(StubKind::StrBytesNth)
            } else {
                Some(StubKind::StrCharsNth)
            }
        },
        exclusive: true,
    },
    // Box::<T>::new — opaque allocation when MIR doesn't desugar to exchange_malloc (Fix #2745)
    // Part of #4067: require "boxed::Box::" to avoid matching OnceBox::new, DoubleBox::new, etc.
    CategoryEntry {
        guard: |path| path.contains("boxed::Box::") && path.ends_with(">::new"),
        handler: |_path| Some(StubKind::BoxNew),
        exclusive: false,
    },
    // Box::into_raw_with_allocator — guard is precise, handler always returns Some
    CategoryEntry {
        guard: |path| path.contains("Box::") && path.ends_with(">::into_raw_with_allocator"),
        handler: |_path| Some(StubKind::BoxIntoRawWithAllocator),
        exclusive: false,
    },
    // Unique::<T>::new_unchecked (Part of #1739)
    CategoryEntry {
        guard: |path| path.contains("Unique::") && path.ends_with(">::new_unchecked"),
        handler: |_path| Some(StubKind::UniqueNewUnchecked),
        exclusive: false,
    },
    // Unique::<T>::as_non_null_ptr — pointer passthrough, same as NonNull::as_non_null_ptr
    // Part of #3184: Unique wraps NonNull inside Box; this is on the Box deref critical path.
    CategoryEntry {
        guard: |path| path.contains("Unique::") && path.ends_with(">::as_non_null_ptr"),
        handler: |_path| Some(StubKind::NonNullAsNonNullPtr),
        exclusive: false,
    },
    // Unique::<T>::as_ptr — pointer identity, same as NonNull::as_ptr
    // Part of #3184: Box deref chain calls Unique::as_ptr after as_non_null_ptr.
    CategoryEntry {
        guard: |path| path.contains("Unique::") && path.ends_with(">::as_ptr"),
        handler: |_path| Some(StubKind::NonNullAsPtr),
        exclusive: false,
    },
    // Unique::<T>::cast — pointer type cast, same as NonNull::cast
    // Part of #3184: Box dealloc path calls Unique::cast for type erasure.
    CategoryEntry {
        guard: |path| path.contains("Unique::") && path.ends_with(">::cast"),
        handler: |_path| Some(StubKind::NonNullCast),
        exclusive: false,
    },
    // <NonNull<T> as From<Unique<T>>>::from — pointer identity extraction.
    // Part of #3184: Box dealloc path converts Unique to NonNull before dealloc.
    CategoryEntry {
        guard: |path| {
            path.contains("From<") && path.contains("Unique") && path.ends_with(">::from")
        },
        handler: |_path| Some(StubKind::NonNullAsNonNullPtr),
        exclusive: false,
    },
    // Vec::from_raw_parts / Vec::from_raw_parts_in — both use same stub (#3451)
    CategoryEntry {
        guard: |path| path.contains("Vec::") && path.ends_with(">::from_raw_parts_in"),
        handler: |_path| Some(StubKind::VecFromRawPartsIn),
        exclusive: false,
    },
    CategoryEntry {
        guard: |path| {
            path.contains("Vec::")
                && path.ends_with(">::from_raw_parts")
                && !path.ends_with(">::from_raw_parts_in")
        },
        handler: |_path| Some(StubKind::VecFromRawPartsIn),
        exclusive: false,
    },
    // <[T]>::into_vec / alloc::slice::hack::into_vec — vec![...] macro expansion (#2967)
    CategoryEntry {
        guard: |path| path.contains("into_vec") && (path.contains("slice") || path.contains("[T]")),
        handler: |_path| Some(StubKind::SliceIntoVec),
        exclusive: false,
    },
    // Try trait stubs (Part of #1100)
    CategoryEntry {
        guard: |path| {
            (path.contains("std::ops::Try>") && path.ends_with(">::branch"))
                || (path.contains("std::ops::FromResidual") && path.ends_with(">::from_residual"))
        },
        handler: |path| StubRegistry::lookup_try_trait(path),
        exclusive: false,
    },
    // Panic stubs
    CategoryEntry {
        guard: |path| {
            path.contains("panicking") || path.contains("panic") || path.contains("begin_panic")
        },
        handler: |path| StubRegistry::lookup_panic_suffix(path),
        exclusive: false,
    },
    // UB checks and mem intrinsics (#1478, #2916)
    CategoryEntry {
        guard: |path| {
            path.contains("ub_checks")
                || path.contains("mem::size_of")
                || path.contains("mem::align_of")
                || path.contains("precondition_check")
                || path.contains("assert_inhabited")
        },
        handler: |path| StubRegistry::lookup_ub_mem_suffix(path),
        exclusive: false,
    },
    // Formatting stubs
    CategoryEntry {
        guard: |path| path.contains("fmt::"),
        handler: |path| StubRegistry::lookup_fmt_suffix(path),
        exclusive: false,
    },
    // ManuallyDrop helpers used by pre-inlined Vec::IntoIter internals (#2876 RC2-B)
    CategoryEntry {
        guard: |path| path.contains("ManuallyDrop"),
        handler: |path| StubRegistry::lookup_manuallydrop_suffix(path),
        exclusive: false,
    },
    // Primitive trait stubs (Part of #1240, #502)
    // MUST come BEFORE BigInt/HashMap to avoid false matches on primitives
    CategoryEntry {
        guard: |path| StubRegistry::is_primitive_trait_path(path),
        handler: |path| StubRegistry::lookup_primitive_trait(path),
        exclusive: false,
    },
    // BigRational from num_rational crate (Part of #911)
    // Note: bare "Rational" excluded from guard — too broad, intercepts user-defined
    // types (e.g., standalone Rational structs in ay self-verify harnesses). Part of #3766.
    // The canonical num_rational paths contain "num_rational::Ratio" or "BigRational".
    CategoryEntry {
        guard: |path| {
            path.contains("BigRational")
                || path.contains("num_rational")
                || (path.contains("Ratio<") && path.contains("BigInt"))
        },
        handler: |path| StubRegistry::lookup_bigrational_suffix(path),
        exclusive: false,
    },
    // BigInt / BigUint (Part of #734)
    CategoryEntry {
        guard: |path| path.contains("BigInt") || path.contains("BigUint"),
        handler: |path| StubRegistry::lookup_bigint_suffix(path),
        exclusive: false,
    },
    // TrustMcMap (Part of #788) — exclusive: unmatched TrustMcMap path must not fallthrough
    CategoryEntry {
        guard: |path| path.contains("TrustMcMap"),
        handler: |path| StubRegistry::lookup_trust_mcmap_suffix(path),
        exclusive: true,
    },
    // BTreeMap<K, SetValZST> → BTreeSet stubs (Part of #1622)
    // MUST come before generic BTreeMap/HashMap
    CategoryEntry {
        guard: |path| path.contains("BTreeMap") && path.contains("SetValZST"),
        handler: |path| StubRegistry::lookup_btreemap_setvalzst(path),
        exclusive: false,
    },
    // BTreeMap internal operations (Part of #1622)
    // MUST come before general HashMap/BTreeMap
    CategoryEntry {
        guard: |path| StubRegistry::is_btreemap_internal(path),
        handler: |path| {
            let result = StubRegistry::lookup_btreemap_internal_suffix(path);
            tracing::debug!(
                "StubRegistry::lookup BTreeMap internal path={}, result={:?}",
                path,
                result
            );
            result
        },
        exclusive: false,
    },
    // HashMap and BTreeMap (Part of #788, #772) — exclusive: own all map paths
    CategoryEntry {
        guard: |path| path.contains("HashMap") || path.contains("BTreeMap"),
        handler: |path| StubRegistry::lookup_hashmap_suffix(path),
        exclusive: true,
    },
    // BTreeSet MUST be checked before IntoIter (Part of #1751) — exclusive
    CategoryEntry {
        guard: |path| path.contains("BTreeSet"),
        handler: |path| {
            let result = StubRegistry::lookup_btreeset_suffix(path);
            tracing::debug!("StubRegistry::lookup BTreeSet path={}, result={:?}", path, result);
            result
        },
        exclusive: true,
    },
    // HashSet MUST be checked before IntoIter (Part of #1751) — exclusive
    CategoryEntry {
        guard: |path| path.contains("HashSet"),
        handler: |path| {
            let result = StubRegistry::lookup_hashset_suffix(path);
            tracing::debug!("StubRegistry::lookup HashSet path={}, result={:?}", path, result);
            result
        },
        exclusive: true,
    },
    // RawVec operations (Part of #1037) — exclusive: prevents RawVec falling to Vec
    CategoryEntry {
        guard: |path| path.contains("RawVec"),
        handler: |path| StubRegistry::lookup_rawvec_suffix(path),
        exclusive: true,
    },
    // vec![val; n] — alloc::vec::from_elem (Part of #3348). MUST come before Vec
    // because from_elem's path contains "vec" (lowercase) but not "Vec<" or "Vec::".
    CategoryEntry {
        guard: |path| path.contains("from_elem") && (path.contains("vec") || path.contains("Vec")),
        handler: |_path| Some(StubKind::VecFromElem),
        exclusive: true,
    },
    // slice::to_vec / to_vec_in / to_owned -- borrowed-slice clone into owned Vec.
    // Part of #4099: <[T] as ToOwned>::to_owned is semantically identical to to_vec.
    // Kept distinct from SliceIntoVec so boxed-slice ownership stays separate.
    CategoryEntry {
        guard: |path| {
            path.contains("slice")
                && StubRegistry::extract_method_name(path).is_some_and(|method| {
                    method == "to_vec" || method == "to_vec_in" || method == "to_owned"
                })
        },
        handler: |_path| Some(StubKind::VecFromSlice),
        exclusive: true,
    },
    // Vec operations (Part of #1312) — exclusive
    // Part of #4209: Exclude ArrayVec (arrayvec crate) from Vec stub matching.
    // ArrayVec<T, CAP> paths contain "Vec<" as a substring, so without the
    // exclusion, methods like ArrayVec::is_full are routed to Vec stubs,
    // causing OOM from infinite stub expansion.
    CategoryEntry {
        guard: |path| {
            (path.contains("Vec<") || path.contains("Vec::")) && !path.contains("ArrayVec")
        },
        handler: |path| StubRegistry::lookup_vec_suffix(path),
        exclusive: true,
    },
    // RangeBounds::contains — over-approximate as true (Part of #3470)
    CategoryEntry {
        guard: |path| path.contains("RangeBounds") && path.contains("contains"),
        handler: |_path| Some(StubKind::RangeBoundsContains),
        exclusive: false,
    },
    // Iterator operations (Part of #1611, #1694, #1751) — exclusive
    // NOTE: BTreeSet/HashSet/Vec checks MUST come before this
    CategoryEntry {
        guard: |path| {
            path.contains("IntoIter")
                || path.contains("Iterator::")
                || path.contains("Iterator for")
                || path.contains("Iterator>")  // Part of #4112: <FlatMap<...> as Iterator>::next
                || path.contains("RangeIteratorImpl")
                || path.contains("Flatten")
                || path.contains("FlatMap")     // Part of #4112: flat_map adapter paths
                || path.contains("flat_map")    // Part of #4112: Iterator::flat_map constructor
                || path.contains("slice::iter")
                || path.contains("slice::Iter")
                || ((path.contains("str::iter::Chars") || path.contains("str::Chars"))
                    && StubRegistry::extract_method_name(path)
                        .is_some_and(|method| method == "next" || method == "clone"))
                || path.contains("slice::<impl") // #3012: <[T]>::iter() and <[T]>::iter_mut()
        },
        handler: |path| StubRegistry::lookup_iter_suffix(path),
        exclusive: true,
    },
    // <str as ToOwned>::to_owned -- produces String from str. Part of #4099.
    CategoryEntry {
        guard: |path| {
            path.contains("ToOwned") && path.contains("str") && path.ends_with("to_owned")
        },
        handler: |_path| Some(StubKind::StringClone),
        exclusive: false,
    },
    // String operations (Part of #1312) - exclude ToString trait.
    // Include `&str` / `str` PartialEq paths so `name == "hello"` routes
    // through StringEq instead of fn_inline falling into slice internals.
    CategoryEntry {
        guard: |path| {
            !path.contains("ToString")
                && (path.contains("String")
                    || path.contains("SplitWhitespace")
                    || path.contains("split_whitespace")
                    || (path.ends_with("::eq")
                        && path.contains("PartialEq")
                        && (path.contains("&str")
                            || path.contains("<str")
                            || path.contains("::str::"))))
        },
        handler: |path| {
            let result = StubRegistry::lookup_string_suffix(path);
            tracing::debug!("StubRegistry::lookup String path={}, result={:?}", path, result);
            result
        },
        exclusive: false,
    },
    // str-level predicate methods (Part of #2125 Phase 2)
    CategoryEntry {
        guard: |path| {
            (path.contains("core::str::") || path.contains("<impl str>"))
                && !path.contains("Cow")
                && !path.contains("ToString")
        },
        handler: |path| StubRegistry::lookup_str_predicate(path),
        exclusive: false,
    },
    // Trait-lowered string predicate paths (Part of #2170 Phase 2)
    CategoryEntry {
        guard: |path| path.contains("Pattern") || path.contains("pattern::"),
        handler: |path| StubRegistry::lookup_pattern_trait(path),
        exclusive: false,
    },
    // Internal ascii helper paths (Part of #2170 Phase 2)
    CategoryEntry {
        guard: |path| path.contains("is_ascii_simple") || path.contains("contains_nonascii"),
        handler: |_path| Some(StubKind::StringIsAscii),
        exclusive: false,
    },
    // slice::ascii lowering for [u8]::is_ascii (Part of #2196)
    CategoryEntry {
        guard: |path| {
            path.contains("slice::ascii::")
                && StubRegistry::extract_method_name(path) == Some("is_ascii")
        },
        handler: |_path| Some(StubKind::StringIsAscii),
        exclusive: false,
    },
    // Cow<str>::to_string (#1691) — handler always returns Some
    CategoryEntry {
        guard: |path| path.contains("Cow") && path.contains("to_string"),
        handler: |path| {
            tracing::debug!("StubRegistry::lookup CowToString path={}", path);
            Some(StubKind::CowToString)
        },
        exclusive: false,
    },
    // String::to_string - identity/clone (must come before generic DisplayToString)
    CategoryEntry {
        guard: |path| {
            (path.contains("string::String as") || path.contains("String as"))
                && path.contains("to_string")
        },
        handler: |path| {
            tracing::debug!("StubRegistry::lookup String::to_string -> StringClone path={}", path);
            Some(StubKind::StringClone)
        },
        exclusive: false,
    },
    // Generic ToString::to_string for Display types (#1700, #1701)
    CategoryEntry {
        guard: |path| path.contains("ToString") && path.contains("to_string"),
        handler: |path| {
            tracing::debug!("StubRegistry::lookup DisplayToString path={}", path);
            Some(StubKind::DisplayToString)
        },
        exclusive: false,
    },
    // SetValZST::default - ZST marker for BTreeSet values (Part of #1622)
    CategoryEntry {
        guard: |path| path.contains("SetValZST") && path.contains("default"),
        handler: |path| {
            tracing::debug!("StubRegistry::lookup SetValZST::default path={}", path);
            Some(StubKind::SetValZstDefault)
        },
        exclusive: false,
    },
];
