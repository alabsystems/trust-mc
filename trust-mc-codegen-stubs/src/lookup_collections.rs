// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Collection-oriented suffix-based stub lookup helpers (#2246). Covers:
// HashMap, TrustMcMap, BTreeMap, BTreeSet, HashSet, Vec, RawVec, String, Iterator.

use super::{StubKind, StubRegistry};

impl StubRegistry {
    #[inline]
    pub(super) fn contains_any(path: &str, patterns: &[&str]) -> bool {
        patterns.iter().any(|pattern| path.contains(pattern))
    }

    #[inline]
    pub(super) fn contains_all(path: &str, patterns: &[&str]) -> bool {
        patterns.iter().all(|pattern| path.contains(pattern))
    }

    #[inline]
    pub(super) fn ends_with_any(path: &str, suffixes: &[&str]) -> bool {
        suffixes.iter().any(|suffix| path.ends_with(suffix))
    }

    /// Extract method name from a path suffix (#1434).
    /// Handles `>::method` and `::method` patterns, strips turbofish (#3189).
    pub(super) fn extract_method_name(path: &str) -> Option<&str> {
        let raw = if let Some(idx) = path.rfind(">::") {
            &path[idx + 3..]
        } else if let Some(idx) = path.rfind("::") {
            &path[idx + 2..]
        } else {
            return None;
        };
        Some(raw.split("::<").next().unwrap_or(raw))
    }

    /// Suffix-based HashMap/BTreeMap stub lookup (Part of #788, #772).
    /// Maps HashMap operations to SMT Array theory operations.
    /// Handles both `::method` and `>::method` suffixes (generics in path).
    pub(super) fn lookup_hashmap_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;

        // Part of #1752: BTreeMap uses same model as HashMap but with distinct stubs
        // for explicit handling in codegen_hashmap_stub
        let is_btreemap = path.contains("BTreeMap");

        match method {
            // Constructor patterns (includes with_hasher which new() delegates to)
            "new" | "default" | "with_hasher" | "with_capacity" => {
                Some(if is_btreemap { StubKind::BTreeMapNew } else { StubKind::HashMapNew })
            }
            // Core operations
            "insert" if !path.contains("insert_at_index") && !path.contains("find_insert") => {
                Some(if is_btreemap { StubKind::BTreeMapInsert } else { StubKind::HashMapInsert })
            }
            "get_mut" => {
                Some(if is_btreemap { StubKind::BTreeMapGetMut } else { StubKind::HashMapGetMut })
            }
            "get" if !path.contains("get_key_value") && !path.contains("RawTable") => {
                Some(if is_btreemap { StubKind::BTreeMapGet } else { StubKind::HashMapGet })
            }
            "contains_key" => Some(if is_btreemap {
                StubKind::BTreeMapContainsKey
            } else {
                StubKind::HashMapContainsKey
            }),
            "remove" if !path.contains("remove_entry") => {
                Some(if is_btreemap { StubKind::BTreeMapRemove } else { StubKind::HashMapRemove })
            }
            // Size queries
            "len" if !path.contains("RawTable") => {
                Some(if is_btreemap { StubKind::BTreeMapLen } else { StubKind::HashMapLen })
            }
            "is_empty" => {
                Some(if is_btreemap { StubKind::BTreeMapIsEmpty } else { StubKind::HashMapIsEmpty })
            }
            "clear" => {
                Some(if is_btreemap { StubKind::BTreeMapClear } else { StubKind::HashMapClear })
            }
            // Clone - require HashMap/BTreeMap in the impl path, not just any clone.
            // Avoid false positives on nested types like HashMap<K, SomeStruct>::get().clone().
            "clone" if path.contains("HashMap") || path.contains("BTreeMap") => {
                Some(if is_btreemap { StubKind::BTreeMapClone } else { StubKind::HashMapClone })
            }
            // Drop destroys the collection value. The abstract map model has no
            // observable resource state, so route it through a no-op handler
            // instead of reporting an unstubbed stdlib abstraction.
            "drop" if path.contains("Drop") => Some(StubKind::HashMapDrop),
            // Iterator operations (Part of #1751) - shared between HashMap/BTreeMap
            "into_iter" => Some(StubKind::HashMapIntoIter),
            "iter" if !path.contains("into_iter") => Some(StubKind::HashMapIter),
            "keys" => Some(StubKind::HashMapKeys),
            "values" if !path.contains("values_mut") => Some(StubKind::HashMapValues),
            _ => {
                // non-enum: &str (method name)
                tracing::warn!(method, path, "unhandled HashMap/BTreeMap method in stub lookup");
                None
            }
        }
    }

    /// Suffix-based TrustMcMap stub lookup (Part of #788).
    /// TrustMcMap is a verification-friendly HashMap that doesn't inline to hashbrown.
    /// Handles both `::method` and `>::method` suffixes (generics in path).
    pub(super) fn lookup_trust_mcmap_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;

        match method {
            "new" | "default" => Some(StubKind::TrustMcMapNew),
            "insert" => Some(StubKind::TrustMcMapInsert),
            "get" => Some(StubKind::TrustMcMapGet),
            "contains_key" => Some(StubKind::TrustMcMapContainsKey),
            "remove" => Some(StubKind::TrustMcMapRemove),
            "len" => Some(StubKind::TrustMcMapLen),
            "is_empty" => Some(StubKind::TrustMcMapIsEmpty),
            "clear" => Some(StubKind::TrustMcMapClear),
            "clone" => Some(StubKind::TrustMcMapClone),
            "drop" if path.contains("Drop") => Some(StubKind::HashMapDrop),
            // <TrustMcMap as IntoIterator>::into_iter (Part of #1812)
            "into_iter" => Some(StubKind::TrustMcMapIntoIter),
            // TrustMcMapIntoIter::next (Part of #1812)
            "next" if path.contains("TrustMcMapIntoIter") => Some(StubKind::TrustMcMapIterNext),
            _ => {
                // non-enum: &str (method name)
                tracing::warn!(method, path, "unhandled TrustMcMap method in stub lookup");
                None
            }
        }
    }

    /// Suffix-based RawVec stub lookup (Part of #1037).
    /// RawVec is Vec's internal allocation layer.
    /// RawVec is modeled as a struct with (ptr, cap) fields.
    pub(super) fn lookup_rawvec_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        tracing::debug!("lookup_rawvec_suffix: path={}, method={}", path, method);
        match method {
            "new_in" => Some(StubKind::RawVecNewIn),
            "capacity" => Some(StubKind::RawVecCapacity),
            "grow_one" => Some(StubKind::RawVecGrowOne),
            "ptr" => Some(StubKind::RawVecPtr),
            // Part of #2876 RC2-B: pre-inlined Vec::IntoIter paths call RawVec{,Inner}::non_null.
            "non_null" => Some(StubKind::RawVecPtr),
            // Part of #1841: RawVec construction from NonNull pointer
            "from_nonnull_in" => Some(StubKind::RawVecFromNonNullIn),
            // Part of #1841: model RawVec drop/deallocate as the same no-op lane.
            "drop" if path.contains("Drop") => Some(StubKind::RawVecDrop),
            "deallocate" => Some(StubKind::RawVecDrop),
            // Part of #2665: shrink_to_fit is no-op (retaining larger capacity is sound)
            "shrink_to_fit" => Some(StubKind::RawVecShrinkToFit),
            // Part of #2876 RC2: RawVecInner::reserve_exact and grow_amortized appear
            // in pre-inlined Vec paths. Model as capacity-growth (same as grow_one).
            "reserve_exact" | "grow_amortized" => Some(StubKind::RawVecGrowOne),
            _ => {
                // non-enum: &str (method name)
                tracing::warn!(method, path, "unhandled RawVec method in stub lookup");
                None
            }
        }
    }

    /// Static table for simple (unguarded) Vec method-name to StubKind mappings.
    /// Guarded lookups (len, clone, drop, iter) require path context and are
    /// handled separately in `lookup_vec_suffix`.
    const VEC_METHOD_TABLE: &[(&str, StubKind)] = &[
        ("new", StubKind::VecNew),
        ("default", StubKind::VecNew),
        ("with_capacity", StubKind::VecWithCapacity),
        ("with_capacity_in", StubKind::VecWithCapacityIn),
        ("push", StubKind::VecPush),
        ("push_mut", StubKind::VecPush), // Internal helper; Vec::push delegates to push_mut in nightly
        ("insert", StubKind::VecInsert),
        ("reserve_exact", StubKind::VecReserveExact),
        ("reserve", StubKind::VecReserve),
        ("shrink_to_fit", StubKind::VecShrinkToFit),
        ("pop", StubKind::VecPop),
        ("remove", StubKind::VecRemove),
        ("capacity", StubKind::VecCapacity),
        ("is_empty", StubKind::VecIsEmpty),
        ("resize", StubKind::VecResize),
        ("set_len", StubKind::VecSetLen),
        ("clear", StubKind::VecClear),
        ("truncate", StubKind::VecTruncate),
        ("contains", StubKind::VecContains),
        ("index", StubKind::IndexIndex),
        ("index_mut", StubKind::IndexMut),
        ("deref", StubKind::VecAsSlice),
        ("deref_mut", StubKind::VecAsSlice),
        ("as_slice", StubKind::VecAsSlice),
        ("as_mut_slice", StubKind::VecAsSlice),
        ("as_ptr", StubKind::VecAsPtr),
        ("as_mut_ptr", StubKind::VecAsMutPtr),
        ("into_iter", StubKind::VecIntoIter),
        ("iter_mut", StubKind::VecIterMut),
        ("extend_from_slice", StubKind::VecExtendFromSlice),
        // Part of #4208: additional Vec methods for dterm Kani proofs
        ("append_elements", StubKind::VecAppendElements),
        ("extend_with", StubKind::VecExtendWith),
        ("spare_capacity_mut", StubKind::VecSpareCapacityMut),
        ("extend_trusted", StubKind::VecExtendTrusted),
        ("into_boxed_slice", StubKind::VecIntoBoxedSlice),
        ("swap", StubKind::VecSwap),
        ("retain", StubKind::VecRetain),
        ("retain_mut", StubKind::VecRetain),
        ("append", StubKind::VecAppend),
        ("last", StubKind::VecLast),
        ("reverse", StubKind::VecReverse),
        ("dedup", StubKind::VecDedup),
        ("dedup_by_key", StubKind::VecDedup),
        ("dedup_by", StubKind::VecDedup),
        ("split_off", StubKind::VecSplitOff),
        ("sort", StubKind::VecSort),
        ("sort_unstable", StubKind::VecSort),
        ("sort_by", StubKind::VecSort),
        ("sort_unstable_by", StubKind::VecSort),
        ("sort_by_key", StubKind::VecSort),
        ("sort_unstable_by_key", StubKind::VecSort),
        ("drain", StubKind::VecDrain),
        ("splice", StubKind::VecSplice),
    ];

    /// Suffix-based Vec stub lookup (Part of #1312).
    /// Maps Vec operations to struct with (ptr, len, cap) fields.
    /// Optimized: uses match on extracted method name to avoid allocations (#1434).
    pub(super) fn lookup_vec_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;

        // Fast path: static table for unguarded method names
        for &(name, stub) in Self::VEC_METHOD_TABLE {
            if method == name {
                return Some(stub);
            }
        }

        // Guarded lookups requiring path context
        match method {
            "len" if !path.contains("RawVec") => Some(StubKind::VecLen),
            "clone" if path.contains("Vec") => Some(StubKind::VecClone),
            "drop" if path.contains("Drop") => Some(StubKind::VecDrop),
            "iter" if !path.contains("into_iter") => Some(StubKind::VecIter),
            // Part of #3348: Vec PartialEq::eq as used by assert_eq! on Vec-containing types.
            "eq" if path.contains("Vec") || path.contains("partial_eq") => Some(StubKind::VecEq),
            // Rust MIR lowers extend/extend_from_slice to SpecExtend::spec_extend.
            "spec_extend" | "extend" if path.contains("Range") => Some(StubKind::VecExtendRange),
            "spec_extend" | "extend" => Some(StubKind::VecExtendFromSlice),
            // <Vec<T> as From<&[T]>>::from creates a Vec from a slice (#3673).
            "from" if path.contains("From") => Some(StubKind::VecFromSlice),
            // <Vec<T> as FromIterator<T>>::from_iter / SpecFromIter::from_iter (Part of #4208).
            "from_iter"
                if path.contains("FromIterator")
                    || path.contains("SpecFromIter")
                    || path.contains("FromIter") =>
            {
                Some(StubKind::VecFromIter)
            }
            // Part of #2876 RC2-B: `Vec::allocator()` appears in pre-inlined IntoIter internals.
            "allocator" => Some(StubKind::GlobalAllocImpl),
            _ => {
                // Part of #3189: turbofish "Vec<" causes Vec to claim Iterator paths.
                if path.contains("Iterator") {
                    return Self::lookup_iter_suffix(path);
                }
                tracing::warn!(method, path, "unhandled Vec method in stub lookup");
                None
            }
        }
    }

    /// Suffix-based iterator stub lookup (Part of #1611, #1694, #1751).
    pub(super) fn lookup_iter_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        match method {
            "flatten" if path.contains("Iterator") => Some(StubKind::IterFlatten),
            // Part of #4112: Iterator::flat_map creates FlatMap wrapping FlattenCompat.
            "flat_map" if path.contains("Iterator") => Some(StubKind::IterFlatten),
            "collect" if path.contains("Iterator") => Some(StubKind::IterCollect),
            // Part of #2183: route Vec::IntoIter drop through the existing VecDrop lane.
            "drop" if path.contains("IntoIter") && path.contains("Drop") => Some(StubKind::VecDrop),
            // Iterator adapters (Part of #1751) - map, filter, fold, sum
            "map" if path.contains("Iterator") => Some(StubKind::IterMap),
            "filter" if path.contains("Iterator") => Some(StubKind::IterFilter),
            "filter_map" if path.contains("Iterator") => Some(StubKind::IterFilterMap),
            "zip" if path.contains("Iterator") => Some(StubKind::IterZip),
            "fold" if path.contains("Iterator") => Some(StubKind::IterFold),
            // try_fold is the core primitive underlying fold/sum/for_each.
            // Map to IterFold: the stub produces a symbolic result of the
            // destination sort (which will be Result<B,E> or ControlFlow).
            "try_fold" if path.contains("Iterator") => Some(StubKind::IterFold),
            "sum" if path.contains("Iterator") => Some(StubKind::IterSum),
            // Flatten/FlatMap/FlattenCompat next() checked before IntoIter::next.
            // Part of #4112: FlatMap::next() resolves to <FlatMap<I,U,F> as Iterator>::next.
            "next"
                if path.contains("flatten::Flatten")
                    || path.contains("flat_map::FlatMap")
                    || path.contains("FlatMap<")
                    || path.contains("FlattenCompat") =>
            {
                Some(StubKind::FlattenNext)
            }
            // Map/Filter adapter next() - checked before generic IntoIter (Part of #1751)
            "next" if path.contains("map::Map") || path.contains("Map<") => Some(StubKind::MapNext),
            "next" if path.contains("filter::Filter") || path.contains("Filter<") => {
                Some(StubKind::FilterNext)
            }
            // FilterMap adapter next() - combined filter + map (#3692)
            "next" if path.contains("filter_map::FilterMap") || path.contains("FilterMap<") => {
                Some(StubKind::FilterMapNext)
            }
            // Zip adapter next() - advance both inner iterators (Part of #3381)
            "next" if path.contains("zip::Zip") || path.contains("Zip<") => Some(StubKind::ZipNext),
            "next" if path.contains("chain::Chain") || path.contains("Chain<") => {
                Some(StubKind::ChainNext)
            }
            // Range<T>::into_iter() — identity copy for for-loop desugaring (Part of #3002).
            "into_iter" if path.contains("Range") && path.contains("IntoIterator") => {
                Some(StubKind::RangeIntoIter)
            }
            // Range iterator next() path used by for-loop lowering in core::iter::range.
            "spec_next" if path.contains("RangeIteratorImpl") => Some(StubKind::RangeSpecNext),
            // HashMap/BTreeMap iterator next() - must be checked before generic IntoIter (Part of #1751)
            // BTreeMap uses same Array<K, Option<V>> model as HashMap, so shares the same next handler.
            "next"
                if path.contains("hash_map::")
                    || path.contains("hashbrown::map::")
                    || path.contains("btree_map::") =>
            {
                Some(StubKind::HashMapIterNext)
            }
            // BTreeSet/HashSet iterator next() - checked before generic IntoIter (Part of #1751)
            "next" if path.contains("btree_set::") => Some(StubKind::BTreeSetIterNext),
            "next" if path.contains("hash_set::") => Some(StubKind::HashSetIterNext),
            // slice::Iter/IterMut next() — VecIter creates same (fld_vec, fld_pos) layout
            // as VecIntoIter, so the IntoIterNext handler works for both (Part of #1751)
            "next" if path.contains("slice::iter") || path.contains("slice::Iter") => {
                Some(StubKind::IntoIterNext)
            }
            // str::Chars::next wraps a SliceIter<u8> in a single-field Chars
            // datatype; the CHC inline IntoIterNext handler unwraps that carrier.
            "next" if is_str_chars_path(path) => Some(StubKind::IntoIterNext),
            // slice::Iter/IterMut and str::Chars clones are structural copies.
            // Route them before the iterator category can stop fallback to the
            // generic Clone handler, preserving the iterator backing state.
            "clone" if is_slice_iter_path(path) || is_str_chars_path(path) => {
                Some(StubKind::PrimitiveClone)
            }
            // <[T]>::iter() and <[T]>::iter_mut() — slice iterator construction (#3012).
            // The Slice datatype has fld_data (Array) and fld_len, which is a subset of
            // Vec's fields. make_vec_into_iter_chc only needs fld_data to determine
            // element sort, so VecIter/VecIterMut handlers work with Slice input.
            "iter" if path.contains("slice::<impl") => Some(StubKind::VecIter),
            "iter_mut" if path.contains("slice::<impl") => Some(StubKind::VecIterMut),
            // <&[T] as IntoIterator>::into_iter / <&mut [T] as IntoIterator>::into_iter
            // — trait entrypoint for `for val in x` where x: &[T] or &mut [T] (#3602).
            // Reuses VecIter/VecIterMut since Slice has fld_data/fld_len like Vec.
            "into_iter" if is_slice_into_iter_mut_path(path) => Some(StubKind::VecIterMut),
            "into_iter" if is_slice_into_iter_path(path) => Some(StubKind::VecIter),
            // <[T]>::as_ptr / as_mut_ptr — pointer identity (Part of #3104)
            "as_ptr" if path.contains("slice::<impl") => Some(StubKind::SliceAsPtr),
            "as_mut_ptr" if path.contains("slice::<impl") => Some(StubKind::SliceAsMutPtr),
            "next" if path.contains("IntoIter") => Some(StubKind::IntoIterNext),
            // Range<T>::next via Iterator trait — fallback when the inline pass has not
            // exposed the internal spec_next call. Instance::resolve produces the trait
            // method path (e.g. <Range<u32> as Iterator>::next) rather than
            // RangeIteratorImpl::spec_next. Placed last among "next" arms so collection
            // wrapper iterators (HashMap<Range<T>>, Vec<Range<T>>, etc.) are caught first
            // by their specific arms above. Part of #3002.
            "next"
                if path.contains("Range<")
                    && !path.contains("Inclusive")
                    && !path.contains("RangeFrom") =>
            {
                Some(StubKind::RangeSpecNext)
            }
            // Iterator::size_hint — called by zip/chain/enumerate adapters internally.
            // Symbolic over-approximation is sound; eliminates unhandled_call counter.
            // Part of #3348: unblocks bv_and/or/xor harnesses with zip-based iteration.
            "size_hint" => Some(StubKind::IterSizeHint),
            _ => {
                // non-enum: &str (method name)
                // Part of #2632: hashbrown-internal iterator methods are expected and noisy
                tracing::debug!(method, path, "unhandled iterator method in stub lookup");
                None
            }
        }
    }
}

/// Returns `true` for the immutable slice `IntoIterator` trait entrypoint.
///
/// Matches `core::slice::iter::<impl ... IntoIterator for &'a [T]>::into_iter`
/// and monomorphized forms like `...for &[u32]>::into_iter`.
/// Rejects the mutable variant (path contains `mut [`).
fn is_slice_into_iter_path(path: &str) -> bool {
    path.contains("slice::iter::<impl")
        && path.contains("IntoIterator for &")
        && !path.contains("mut [")
}

/// Returns `true` for the mutable slice `IntoIterator` trait entrypoint.
///
/// Matches `core::slice::iter::<impl ... IntoIterator for &'a mut [T]>::into_iter`
/// and monomorphized forms like `...for &mut [u32]>::into_iter`.
fn is_slice_into_iter_mut_path(path: &str) -> bool {
    path.contains("slice::iter::<impl") && path.contains("IntoIterator") && path.contains("mut [")
}

fn is_slice_iter_path(path: &str) -> bool {
    path.contains("slice::iter") || path.contains("slice::Iter")
}

fn is_str_chars_path(path: &str) -> bool {
    path.contains("str::iter::Chars")
        || path.contains("str::Chars")
        || (path.contains("Iterator for") && path.contains("Chars") && path.contains("str"))
}

impl StubRegistry {
    /// Suffix-based String stub lookup (Part of #1312).
    /// Maps String operations to struct with (ptr, len, cap) fields.
    /// Optimized: uses match on extracted method name to avoid allocations (#1434).
    pub(super) fn lookup_string_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        match method {
            "new" | "default" => Some(StubKind::StringNew),
            "from" if path.contains("From") => Some(StubKind::StringFrom),
            "from_raw_parts" if path.contains("String") => Some(StubKind::StringFromRawParts),
            "len" => Some(StubKind::StringLen),
            "is_empty" => Some(StubKind::StringIsEmpty),
            "push_str" => Some(StubKind::StringPushStr),
            "push" => Some(StubKind::StringPush),
            "clear" => Some(StubKind::StringClear),
            "clone" if path.contains("String") => Some(StubKind::StringClone),
            "truncate" if path.contains("String") => Some(StubKind::StringTruncate),
            // from_utf8_lossy returns Cow<str>, modeled as String (#1610)
            "from_utf8_lossy" => Some(StubKind::StringFromUtf8Lossy),
            // Part of #4099: from_utf8_unchecked wraps Vec<u8> as String.
            "from_utf8_unchecked" if path.contains("String") || path.contains("string") => {
                Some(StubKind::StringFrom)
            }
            "split_whitespace" => Some(StubKind::SplitWhitespace),
            // String equality via PartialEq::eq (#1610)
            "eq" if path.contains("String") || path.contains("str") => Some(StubKind::StringEq),
            // String/str predicate methods (Part of #2125 Phase 2)
            "contains" => Some(StubKind::StringContains),
            "starts_with" => Some(StubKind::StringStartsWith),
            "ends_with" => Some(StubKind::StringEndsWith),
            "is_ascii" => Some(StubKind::StringIsAscii),
            // String::as_str / as_mut_str / Deref::deref / DerefMut::deref_mut → &str / &mut str
            // Part of #3582, Part of #3698, Part of #4071
            "as_str" | "as_mut_str" => Some(StubKind::StringAsStr),
            "deref" if path.contains("String") => Some(StubKind::StringAsStr),
            "deref_mut" if path.contains("String") => Some(StubKind::StringAsStr),
            "next" if path.contains("SplitWhitespace") => Some(StubKind::SplitWhitespaceNext),
            // String::into_boxed_str(self) -> Box<str> (#3646)
            "into_boxed_str" if path.contains("String") => Some(StubKind::StringIntoBoxedStr),
            _ => {
                // non-enum: &str (method name)
                tracing::warn!(method, path, "unhandled String method in stub lookup");
                None
            }
        }
    }

    /// Suffix-based BTreeSet stub lookup (Part of #1312).
    /// Maps BTreeSet operations to Array<Key, Bool> presence map.
    /// Optimized: uses match on extracted method name to avoid allocations (#1434).
    pub(super) fn lookup_btreeset_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        match method {
            "new" | "default" => Some(StubKind::BTreeSetNew),
            "insert" => Some(StubKind::BTreeSetInsert),
            "contains" => Some(StubKind::BTreeSetContains),
            "remove" => Some(StubKind::BTreeSetRemove),
            "len" => Some(StubKind::BTreeSetLen),
            "is_empty" => Some(StubKind::BTreeSetIsEmpty),
            "clear" => Some(StubKind::BTreeSetClear),
            "clone" if path.contains("BTreeSet") => Some(StubKind::BTreeSetClone),
            // Iterator operations (Part of #1751)
            "into_iter" => Some(StubKind::BTreeSetIntoIter),
            "iter" if !path.contains("into_iter") => Some(StubKind::BTreeSetIter),
            _ => {
                // non-enum: &str (method name)
                tracing::warn!(method, path, "unhandled BTreeSet method in stub lookup");
                None
            }
        }
    }

    /// Suffix-based BTreeMap internal operation stub lookup (Part of #1622).
    /// Maps BTreeMap Entry API operations to SMT Array operations.
    /// These are triggered when MIR inlines BTreeSet operations to internal BTreeMap calls.
    pub(super) fn lookup_btreemap_internal_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        match method {
            // BTreeMap::entry - returns Entry enum (Vacant or Occupied)
            "entry" if path.contains("BTreeMap") => Some(StubKind::BTreeMapEntry),
            // VacantEntry::insert - inserts value, returns &mut V (std API)
            "insert" if path.contains("VacantEntry") => Some(StubKind::BTreeMapVacantInsert),
            // VacantEntry::insert_entry - inserts value, returns OccupiedEntry (newer API)
            "insert_entry" if path.contains("VacantEntry") => {
                Some(StubKind::BTreeMapVacantInsertEntry)
            }
            // OccupiedEntry::insert - replaces value, returns old V
            "insert" if path.contains("OccupiedEntry") => Some(StubKind::BTreeMapOccupiedInsert),
            // OccupiedEntry::get_mut - returns &mut V to existing value
            "get_mut" if path.contains("OccupiedEntry") => Some(StubKind::BTreeMapOccupiedGetMut),
            // OccupiedEntry::into_mut - consumes entry, returns &mut V
            "into_mut" if path.contains("OccupiedEntry") => Some(StubKind::BTreeMapOccupiedIntoMut),
            // Entry::or_insert - inserts default value, returns &mut V
            "or_insert" if path.contains("Entry") => Some(StubKind::BTreeMapEntryOrInsert),
            // Entry::or_insert_with - inserts computed value, returns &mut V
            "or_insert_with" if path.contains("Entry") => Some(StubKind::BTreeMapEntryOrInsertWith),
            // Entry::or_insert_with_key - inserts computed value using key, returns &mut V
            "or_insert_with_key" if path.contains("Entry") => {
                Some(StubKind::BTreeMapEntryOrInsertWithKey)
            }
            // Internal BTree node operations (Part of #1622, #1627)
            // search_tree - searches for key in BTree, returns SearchResult
            "search_tree" => Some(StubKind::BTreeSearchTree),
            // NodeRef::reborrow - creates immutable borrow of node reference
            "reborrow" if path.contains("NodeRef") => Some(StubKind::BTreeNodeReborrow),
            // Handle::into_kv - extracts key-value pair from handle
            "into_kv" if path.contains("Handle") => Some(StubKind::BTreeHandleIntoKv),
            _ => {
                // non-enum: &str (method name)
                tracing::warn!(method, path, "unhandled BTreeMap internal method in stub lookup");
                None
            }
        }
    }

    /// Suffix-based HashSet stub lookup (Part of #1613).
    /// Maps HashSet operations to Array<Key, Bool> presence map.
    /// Semantically identical to BTreeSet but uses different StubKind variants.
    /// HashSet internally uses HashMap<T, ()>, but we model it as a simple set.
    pub(super) fn lookup_hashset_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        match method {
            "new" | "default" | "with_hasher" | "with_capacity" => Some(StubKind::HashSetNew),
            "insert" => Some(StubKind::HashSetInsert),
            "contains" => Some(StubKind::HashSetContains),
            "remove" => Some(StubKind::HashSetRemove),
            "len" => Some(StubKind::HashSetLen),
            "is_empty" => Some(StubKind::HashSetIsEmpty),
            "clear" => Some(StubKind::HashSetClear),
            "clone" if path.contains("HashSet") => Some(StubKind::HashSetClone),
            // Iterator operations (Part of #1751)
            "into_iter" => Some(StubKind::HashSetIntoIter),
            "iter" if !path.contains("into_iter") => Some(StubKind::HashSetIter),
            _ => {
                // non-enum: &str (method name)
                tracing::warn!(method, path, "unhandled HashSet method in stub lookup");
                None
            }
        }
    }

    /// Method-based ManuallyDrop helper lookup.
    ///
    /// For CHC, pre-inlined ManuallyDrop helper calls are modeled as
    /// unconstrained allocation-path extras to avoid falling through dispatch.
    pub(super) fn lookup_manuallydrop_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        match method {
            "new" => Some(StubKind::GlobalAllocImpl),
            // Deref::deref and DerefMut::deref_mut — transparent wrapper, identity in verification.
            // deref_mut appears in Vec::IntoIter paths (ManuallyDrop<Vec<T>>). Part of #2967.
            "deref" | "deref_mut" if path.contains("Deref") => Some(StubKind::GlobalAllocImpl),
            _ => {
                // non-enum: &str (method name)
                tracing::debug!(method, path, "unhandled ManuallyDrop method in stub lookup");
                None
            }
        }
    }
}
