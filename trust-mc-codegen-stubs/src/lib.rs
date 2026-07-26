// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Stdlib function stub registry for AY codegen.
//!
//! `StubKind` enum is in `stub_kind/` (variants.rs + predicates.rs).
//!
//! Dispatch strategy (Part of #2655): three-tier table-driven lookup.
//! 1. HashMap exact match (fastest — O(1) for known paths)
//! 2. Suffix if-chain (ends_with/contains checks for paths with non-standard prefixes)
//! 3. Category table (ordered array of guard_fn + handler_fn for pattern-based dispatch)
//!
//! Category table ordering preserves the invariants previously implicit in
//! the if-chain: BTreeSet/HashSet before IntoIter, BTreeMap+SetValZST before
//! generic BTreeMap, primitive traits before BigInt, etc.

mod category_table;
mod inline_frozen;
mod stub_kind;
pub use inline_frozen::InlineFrozenKind;
pub use stub_kind::StubKind;

use category_table::CATEGORY_TABLE;
use std::collections::HashMap;

/// Registry of semantic stubs for stdlib functions.
pub struct StubRegistry {
    stubs: HashMap<&'static str, StubKind>,
}

impl StubRegistry {
    /// Creates a new stub registry with all known stdlib function stubs.
    ///
    /// REQUIRES: (no preconditions)
    /// ENSURES: Returned registry contains mappings for all known stdlib stubs.
    /// ENSURES: Each function path maps to exactly one StubKind.
    pub fn new() -> Self {
        let mut stubs = HashMap::with_capacity(64);
        // Slice/Index exact matches
        stubs.insert("core::slice::cmp::SlicePartialEq::equal", StubKind::SlicePartialEqEqual);
        stubs.insert("std::slice::cmp::SlicePartialEq::equal", StubKind::SlicePartialEqEqual);
        stubs.insert("core::slice::index::SliceIndex::index", StubKind::SliceIndexIndex);
        stubs.insert("std::slice::index::SliceIndex::index", StubKind::SliceIndexIndex);
        stubs.insert("core::ops::Index::index", StubKind::IndexIndex);
        stubs.insert("std::ops::Index::index", StubKind::IndexIndex);

        // Option::unwrap (#703)
        stubs.insert("core::option::Option::unwrap", StubKind::OptionUnwrap);
        stubs.insert("std::option::Option::unwrap", StubKind::OptionUnwrap);

        // Allocator intrinsics — deterministic paths (#1100)
        stubs.insert("alloc::alloc::alloc", StubKind::RustAlloc);
        stubs.insert("__rust_alloc", StubKind::RustAlloc);
        stubs.insert("std::alloc::alloc_zeroed", StubKind::RustAllocZeroed);
        stubs.insert("__rust_alloc_zeroed", StubKind::RustAllocZeroed);
        stubs.insert("__rust_dealloc", StubKind::RustDealloc);
        stubs.insert("__rust_realloc", StubKind::RustRealloc);
        stubs.insert("alloc::alloc::realloc", StubKind::RustRealloc);
        stubs.insert("alloc::alloc::exchange_malloc", StubKind::RustAlloc);
        stubs.insert("std::alloc::Global::alloc_impl", StubKind::GlobalAllocImpl);
        stubs.insert("std::alloc::handle_alloc_error", StubKind::HandleAllocError);

        // Panic/UB exact matches (Part of #3300: panic_nounwind reclassified to PanicError;
        // used by checked arithmetic overflow which IS reachable from user code)
        stubs.insert("core::panicking::panic_nounwind", StubKind::PanicError);
        stubs.insert("core::panicking::panic_nounwind_fmt", StubKind::PanicError);
        stubs.insert("core::panicking::panic", StubKind::PanicError);
        stubs.insert("core::panicking::begin_panic", StubKind::PanicError);
        stubs.insert("core::panicking::assert_failed", StubKind::PanicError);
        stubs.insert("core::ub_checks::check_language_ub", StubKind::UbCheckLanguageUb);
        stubs.insert("core::intrinsics::precondition_check", StubKind::PreconditionCheck);

        Self::register_mem_intrinsics(&mut stubs);
        // kani::mem helpers (Part of #1229, #3470): predicates + wrapper functions
        stubs.insert("kani::mem::is_ptr_aligned", StubKind::KaniMemIsPtrAligned);
        stubs.insert("kani::mem::is_inbounds", StubKind::KaniMemIsInbounds);
        stubs.insert("kani::mem::assert_is_initialized", StubKind::KaniMemAssertIsInitialized);
        stubs.insert("kani::mem::can_read_unaligned", StubKind::KaniMemCanReadUnaligned);
        stubs.insert("kani::mem::can_dereference", StubKind::KaniMemCanDereference);
        stubs.insert("kani::mem::can_write", StubKind::KaniMemCanWrite);
        // Part of #4249: Direct same_allocation stub — intercept before decomposition
        // through pointer_object hooks to enable cross-pointer obj_id comparison.
        stubs.insert("kani::mem::same_allocation", StubKind::KaniMemSameAllocation);
        stubs.insert("kani::mem::same_allocation_internal", StubKind::KaniMemSameAllocation);
        // Provenance + null pointers (Part of #3323)
        stubs.insert("core::ptr::without_provenance_mut", StubKind::WithoutProvenanceMut);
        stubs.insert("core::ptr::without_provenance", StubKind::WithoutProvenance);
        stubs.insert("std::ptr::without_provenance_mut", StubKind::WithoutProvenanceMut);
        stubs.insert("std::ptr::without_provenance", StubKind::WithoutProvenance);
        stubs.insert("core::ptr::null", StubKind::PtrNull);
        stubs.insert("std::ptr::null", StubKind::PtrNull);
        stubs.insert("core::ptr::null_mut", StubKind::PtrNull);
        stubs.insert("std::ptr::null_mut", StubKind::PtrNull);
        // Standalone ptr::write/read
        stubs.insert("std::ptr::write", StubKind::PtrWrite);
        stubs.insert("core::ptr::write", StubKind::PtrWrite);
        stubs.insert("std::ptr::read", StubKind::PtrRead);
        stubs.insert("core::ptr::read", StubKind::PtrRead);
        stubs.insert("std::slice::from_raw_parts_mut", StubKind::PtrCast);
        stubs.insert("core::slice::from_raw_parts_mut", StubKind::PtrCast);

        // Formatting
        stubs.insert("std::fmt::format", StubKind::FmtFormat);
        stubs.insert("core::fmt::format", StubKind::FmtFormat);
        stubs.insert("alloc::fmt::format", StubKind::FmtFormat);
        stubs.insert("core::fmt::Arguments::new", StubKind::FmtArgumentsNew);
        stubs.insert("core::fmt::Arguments::from_str", StubKind::FmtArgumentsFromStr);

        // Ord::cmp (bare trait path)
        stubs.insert("core::cmp::Ord::cmp", StubKind::OrdCmp);
        Self { stubs }
    }

    /// Mem intrinsics: size_of / align_of via all path variants.
    /// Part of #3367 (intrinsics:: paths), #4087 (raw intrinsics::align_of).
    fn register_mem_intrinsics(stubs: &mut HashMap<&'static str, StubKind>) {
        for path in [
            "core::mem::size_of",
            "std::mem::size_of",
            "core::intrinsics::size_of",
            "std::intrinsics::size_of",
        ] {
            stubs.insert(path, StubKind::MemSizeOf);
        }
        for path in [
            "std::mem::align_of",
            "core::mem::align_of",
            "core::intrinsics::min_align_of",
            "std::intrinsics::min_align_of",
            "core::intrinsics::align_of",
            "std::intrinsics::align_of",
        ] {
            stubs.insert(path, StubKind::MemAlignOf);
        }
    }

    /// Check whether a function path has a registered stub.
    pub fn has_stub(&self, path: &str) -> bool {
        self.lookup(path).is_some()
    }

    /// Looks up a function path in the stub registry.
    ///
    /// REQUIRES: `path` is a fully qualified function path (e.g., "std::option::Option::unwrap").
    /// ENSURES: Returns Some(StubKind) if function has known stub behavior.
    /// ENSURES: Returns None if function is not stubbed (use MIR body instead).
    ///
    /// Three-tier dispatch (Part of #2655):
    /// 1. HashMap exact match — O(1) for known deterministic paths
    /// 2. Suffix fallbacks — unambiguous suffix → StubKind for polymorphic paths
    /// 3. Category table — ordered (guard, handler) pairs for pattern-based dispatch
    pub fn lookup(&self, path: &str) -> Option<StubKind> {
        // Tier 1: Exact-match HashMap lookup (fastest path)
        if let Some(&kind) = self.stubs.get(path) {
            return Some(kind);
        }

        // Tier 2: Suffix-only fallbacks (paths that may have non-standard prefixes)
        if path.ends_with("slice::cmp::SlicePartialEq::equal") {
            return Some(StubKind::SlicePartialEqEqual);
        }
        // Part of #3495: Match slice PartialEq trait impl paths.
        // def_path_str produces: `core::slice::cmp::<impl std::cmp::PartialEq<[U]> for [T]>::eq`
        // Key: contains `slice::cmp::`, contains `PartialEq`, contains `for [`, ends with `>::eq`.
        if path.contains("slice::cmp::")
            && path.contains("PartialEq")
            && path.contains("for [")
            && path.ends_with(">::eq")
        {
            return Some(StubKind::SlicePartialEqEqual);
        }
        // SliceIndex::index — direct and trait-impl forms (Part of #3348)
        if path.ends_with("::index")
            && (path.contains("slice::index::SliceIndex") || path.contains("slice::SliceIndex<"))
        {
            return Some(StubKind::SliceIndexIndex);
        }
        if path.ends_with("ops::Index::index") {
            return Some(StubKind::IndexIndex);
        }
        // Trait-impl path form, e.g. `<Vec<T> as std::ops::Index<usize>>::index`.
        if path.contains("ops::Index<") && path.ends_with("::index") {
            return Some(StubKind::IndexIndex);
        }
        // slice/array `index_mut` — the &mut sibling of the `::index` arms above.
        // Routes `<[T] as IndexMut<I>>::index_mut` / `SliceIndex::index_mut` to
        // codegen_slice_index_stub (StubKind::IndexMut, stub_dispatch.rs) so the
        // deferred element store goes through the sound select + stub_indexed_ref
        // store-back machinery instead of falling through to the abstracted
        // "Call terminator" fallback. Scoped to slice/array receivers (Vec already
        // routes via VEC_METHOD_TABLE; this must NOT broaden to arbitrary user
        // IndexMut impls — codegen_slice_index_stub guards on slice/array receiver
        // and fails closed otherwise). A sub-slice *range* index_mut is recognised
        // and fails closed inside the stub (it is NOT silently dropped).
        if path.ends_with("::index_mut")
            && (path.contains("slice::index::SliceIndex") || path.contains("slice::SliceIndex<"))
        {
            return Some(StubKind::IndexMut);
        }
        if path.ends_with("ops::IndexMut::index_mut") {
            return Some(StubKind::IndexMut);
        }
        if path.contains("ops::IndexMut<") && path.ends_with("::index_mut") {
            return Some(StubKind::IndexMut);
        }
        if path.ends_with("option::Option::unwrap") {
            return Some(StubKind::OptionUnwrap);
        }
        if path.ends_with("slice::from_raw_parts_mut") {
            return Some(StubKind::PtrCast);
        }
        // Checked arithmetic for Range iterator (Part of #1712)
        if (path.contains("core::num::") || path.contains("std::num::"))
            && path.ends_with(">::checked_add_unsigned")
        {
            return Some(StubKind::CheckedAddUnsigned);
        }
        // MaybeUninit::as_ptr — transparent wrapper identity (Part of #2916)
        if path.contains("MaybeUninit") && path.ends_with("::as_ptr") {
            return Some(StubKind::MaybeUninitAsPtr);
        }
        // char::from_u32_unchecked — identity stub (Part of #3470)
        if path.ends_with("::from_u32_unchecked") {
            return Some(StubKind::CharFromU32Unchecked);
        }
        // slice method stubs (Part of #2916, #3713, #3768)
        if path.contains("slice") {
            // core::slice::memchr::{memchr,memchr_naive,memchr_aligned,memchr_aligned::runtime}
            // (and memchr2/3): SIMD byte-search stdlib with no inlinable MIR. Intercept BEFORE
            // the inliner sees the SIMD body. NOTE: the module segment (`slice::memchr::`)
            // makes this match memrchr (reverse search) too — deliberate: the stub's
            // over-approximation (nondet Option; Some(i) => i <= len) is equally valid there.
            if path.contains("memchr") {
                return Some(StubKind::MemchrMemchr);
            }
            if path.contains("::get_unchecked") {
                return Some(StubKind::SliceGetUnchecked);
            }
            if path.ends_with("::is_empty") {
                return Some(StubKind::SliceIsEmpty);
            }
            if path.ends_with("::first") {
                return Some(StubKind::SliceFirst);
            }
            if path.ends_with("::get") && !path.contains("get_mut") && !path.contains("get_key") {
                return Some(StubKind::SliceGet);
            }
            if path.ends_with("::partition_point") {
                return Some(StubKind::SlicePartitionPoint);
            }
            if path.ends_with("::last") && !path.contains("last_mut") {
                return Some(StubKind::SliceLast);
            }
            if path.ends_with("::binary_search_by_key") {
                return Some(StubKind::SliceBinarySearchByKey);
            }
            if path.ends_with("::chunks") && !path.contains("chunks_mut") {
                return Some(StubKind::SliceChunks);
            }
            if path.ends_with("::windows") {
                return Some(StubKind::SliceWindows);
            }
        }
        // Tier 3: Category table dispatch — ordered traversal preserves priority invariants
        for entry in CATEGORY_TABLE {
            if (entry.guard)(path) {
                let result = (entry.handler)(path);
                if result.is_some() || entry.exclusive {
                    return result;
                }
            }
        }

        None
    }

    // --- Small inline handlers for categories that were previously inline in lookup() ---

    /// Alignment::new and Alignment::as_usize handler.
    fn lookup_alignment(path: &str) -> Option<StubKind> {
        if path.ends_with("::new") || path.ends_with(">::new") {
            return Some(StubKind::AlignmentNew);
        }
        if path.ends_with("::as_usize") || path.ends_with(">::as_usize") {
            return Some(StubKind::AlignmentAsUsize);
        }
        None
    }

    /// kani::mem helpers handler.
    fn lookup_kani_mem(path: &str) -> Option<StubKind> {
        if path.contains("is_ptr_aligned") {
            return Some(StubKind::KaniMemIsPtrAligned);
        }
        if path.contains("is_inbounds") {
            return Some(StubKind::KaniMemIsInbounds);
        }
        if path.contains("assert_is_initialized") {
            return Some(StubKind::KaniMemAssertIsInitialized);
        }
        // Part of #3470: Match wrapper functions when MIR inliner doesn't expand them.
        if path.contains("can_read_unaligned") {
            return Some(StubKind::KaniMemCanReadUnaligned);
        }
        if path.contains("can_dereference") {
            return Some(StubKind::KaniMemCanDereference);
        }
        if path.contains("can_write") {
            return Some(StubKind::KaniMemCanWrite);
        }
        // Part of #4249: same_allocation / same_allocation_internal
        if path.contains("same_allocation") {
            return Some(StubKind::KaniMemSameAllocation);
        }
        None
    }

    /// Try trait (branch / from_residual) handler.
    fn lookup_try_trait(path: &str) -> Option<StubKind> {
        if path.contains("std::ops::Try>") && path.ends_with(">::branch") {
            return Some(StubKind::TryBranch);
        }
        if path.contains("std::ops::FromResidual") && path.ends_with(">::from_residual") {
            return Some(StubKind::FromResidualFromResidual);
        }
        None
    }

    /// BTreeMap<K, SetValZST> → BTreeSet stub redirect (Part of #1622).
    fn lookup_btreemap_setvalzst(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path);
        match method {
            Some("insert") => {
                tracing::debug!(
                    "StubRegistry::lookup BTreeMap<K, SetValZST>::insert -> BTreeSetInsert"
                );
                Some(StubKind::BTreeSetInsert)
            }
            Some("contains_key") => {
                tracing::debug!(
                    "StubRegistry::lookup BTreeMap<K, SetValZST>::contains_key -> BTreeSetContains"
                );
                Some(StubKind::BTreeSetContains)
            }
            Some("remove") => {
                tracing::debug!(
                    "StubRegistry::lookup BTreeMap<K, SetValZST>::remove -> BTreeSetRemove"
                );
                Some(StubKind::BTreeSetRemove)
            }
            Some("new") | Some("default") => {
                tracing::debug!("StubRegistry::lookup BTreeMap<K, SetValZST>::new -> BTreeSetNew");
                Some(StubKind::BTreeSetNew)
            }
            _ => Self::lookup_btreemap_internal_suffix(path), // non-enum: &str
        }
    }

    /// Check if path is a BTreeMap internal operation.
    fn is_btreemap_internal(path: &str) -> bool {
        (path.contains("BTreeMap::") && path.ends_with("entry"))
            || path.contains("btree_map::Entry")
            || path.contains("btree::map::Entry")
            || path.contains("btree_map::VacantEntry")
            || path.contains("btree::map::VacantEntry")
            || path.contains("btree_map::OccupiedEntry")
            || path.contains("btree::map::OccupiedEntry")
            || (path.contains("btree::")
                && (path.contains("search_tree")
                    || (path.contains("NodeRef") && path.contains("reborrow"))
                    || (path.contains("Handle") && path.contains("into_kv"))))
    }

    /// str-level predicate handler.
    fn lookup_str_predicate(path: &str) -> Option<StubKind> {
        match Self::extract_method_name(path) {
            Some("is_ascii") => Some(StubKind::StringIsAscii),
            Some("contains") => Some(StubKind::StringContains),
            Some("starts_with") => Some(StubKind::StringStartsWith),
            Some("ends_with") => Some(StubKind::StringEndsWith),
            // core::str::converts::from_utf8 — NOT from_utf8_lossy or from_utf8_unchecked (#3672)
            Some("from_utf8") => Some(StubKind::StrFromUtf8),
            // <integer as FromStr>::from_str — integer parsing (#3676)
            // Path: core::num::<impl core::str::FromStr for i32>::from_str
            // Guard: path contains "FromStr" to distinguish from fmt::Arguments::from_str
            // (which is handled earlier via exact-match HashMap).
            Some("from_str") if path.contains("FromStr") => Some(StubKind::IntParse),
            _ => None, // non-enum: &str
        }
    }

    /// Pattern trait lowered predicate handler (Part of #2170 Phase 2).
    fn lookup_pattern_trait(path: &str) -> Option<StubKind> {
        match Self::extract_method_name(path) {
            Some("is_contained_in") => Some(StubKind::StringContains),
            Some("is_prefix_of") => Some(StubKind::StringStartsWith),
            Some("is_suffix_of") => Some(StubKind::StringEndsWith),
            _ => None, // non-enum: &str
        }
    }
}

mod lookup_collections;
mod lookup_intrinsics;

#[cfg(test)]
mod tests;
