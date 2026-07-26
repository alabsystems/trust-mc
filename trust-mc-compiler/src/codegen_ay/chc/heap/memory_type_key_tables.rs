// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Table-driven dispatch tables for `sort_from_type_key`.
//!
//! Extracted from `memory_impl_type_keys.rs` to keep that file under 500 LOC.
//! These tables replace the former 47-arm match statement with:
//! - `EXACT_TYPE_KEY_SORTS`: sorted array for O(log n) binary search on exact keys
//! - `PREFIX_TYPE_KEY_RULES`: ordered array for prefix/contains pattern matching

use super::ChcCtx;
use super::names::{self, enum_sort, struct_sort};
use super::types::{POINTER_WIDTH, bool_sort, flatten_dt_array_element, int_sort, ptr_sort};
use ay_bindings::Sort;

/// An entry mapping a literal type key string to a sort constructor.
pub(in crate::codegen_ay::chc) type TypeKeySortEntry = (&'static str, fn() -> Sort);

/// Exact type-key → sort mapping, sorted by key for binary search.
///
/// Each entry maps a literal type key string to a sort constructor.
/// The table MUST remain sorted alphabetically for `binary_search_by_key`.
pub(in crate::codegen_ay::chc) const EXACT_TYPE_KEY_SORTS: &[TypeKeySortEntry] = &[
    // IMPORTANT: this array MUST be sorted by key (byte order) for binary_search.
    // Uppercase ('A'=65) sorts before lowercase ('a'=97) in byte order.
    ("Alignment", || ptr_sort()),
    ("AllocError", bool_sort),
    // Part of #3521: ControlFlow removed — now a proper Datatype, not BV128.
    ("Global", bool_sort),
    ("Infallible", bool_sort),
    ("Layout", || Sort::bitvec(128)),
    ("LayoutError", || Sort::bitvec(128)),
    ("alloc_Global", bool_sort),
    ("alloc_Layout", || Sort::bitvec(128)),
    ("bool", bool_sort),
    ("char", || Sort::bitvec(32)),
    ("core_convert_Infallible", bool_sort),
    ("f128", || Sort::bitvec(128)),
    ("f16", || Sort::bitvec(16)),
    ("f32", || Sort::bitvec(32)),
    ("f64", || Sort::bitvec(64)),
    ("i128", || Sort::bitvec(128)),
    ("i16", || Sort::bitvec(16)),
    ("i32", || Sort::bitvec(32)),
    ("i64", || Sort::bitvec(64)),
    ("i8", || Sort::bitvec(8)),
    ("isize", || ptr_sort()),
    ("std_alloc_AllocError", bool_sort),
    ("std_alloc_Global", bool_sort),
    ("std_alloc_Layout", || Sort::bitvec(128)),
    ("std_convert_Infallible", bool_sort),
    // Part of #3521: std_ops_ControlFlow removed — now a proper Datatype.
    // Part of #3669: IndexRange is a standalone type used by array IntoIter
    // infrastructure (start, end pair). Maps to the same datatype sort as
    // translate_adt_ty (codegen_types_adt.rs:265-267).
    ("std_ops_index_range_IndexRange", || names::index_range_sort()),
    ("u128", || Sort::bitvec(128)),
    ("u16", || Sort::bitvec(16)),
    ("u32", || Sort::bitvec(32)),
    ("u64", || Sort::bitvec(64)),
    ("u8", || Sort::bitvec(8)),
    ("unit", bool_sort),
    ("usize", || ptr_sort()),
];

/// A pattern-based type key rule: if `matches(key)` returns true, `sort(key)`
/// produces the AY sort. Rules are checked in order; first match wins.
pub(in crate::codegen_ay::chc) struct PrefixTypeKeyRule {
    pub(in crate::codegen_ay::chc) matches: fn(&str) -> bool,
    pub(in crate::codegen_ay::chc) sort: fn(&str) -> Sort,
}

/// Pattern-based type-key rules, checked in priority order after exact lookup.
///
/// Order matters: more specific prefixes before less specific ones. For example,
/// `std_vec_IntoIter_` must precede the generic `IntoIter` check, and `Vec`
/// with element extraction must precede `Box` (which also starts with a capital).
pub(in crate::codegen_ay::chc) const PREFIX_TYPE_KEY_RULES: &[PrefixTypeKeyRule] = &[
    // Pointers/references: pointer-width bitvec.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("ref_") || s.starts_with("ptr_"),
        sort: |_| ptr_sort(),
    },
    // Part of #3596: unresolved generic params in non-monomorphized helper MIR
    // use a stable `param_<idx>` key so nested array/slice keys remain
    // reconstructible instead of falling back to opaque byte arrays.
    PrefixTypeKeyRule { matches: |s| s.starts_with("param_"), sort: |_| ptr_sort() },
    // Part of #3159: Foreign types (extern type) like std::ptr::metadata::VTable.
    // Foreign types are opaque and unsized; in memory they appear as pointer-width
    // addresses. Map all foreign_ keys to ptr_sort() (BV64).
    PrefixTypeKeyRule { matches: |s| s.starts_with("foreign_"), sort: |_| ptr_sort() },
    // Part of #3159: DynMetadata<T> is a wrapper around a vtable pointer.
    // In memory it is pointer-width (contains only *const VTable + PhantomData).
    // Map to ptr_sort() to avoid sort mismatches when DynMetadata is used
    // as fat-pointer metadata (expected BV64 in pointer operations).
    PrefixTypeKeyRule { matches: |s| s.starts_with("DynMetadata"), sort: |_| ptr_sort() },
    // Arrays/slices: reconstruct element sort from type key suffix.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("arr_") || s.starts_with("slice_"),
        sort: |s| {
            let elem_key =
                s.strip_prefix("arr_").or_else(|| s.strip_prefix("slice_")).unwrap_or("");
            if elem_key.is_empty() {
                Sort::array(ptr_sort(), Sort::bitvec(32))
            } else {
                let elem_sort = ChcCtx::sort_from_type_key(elem_key);
                Sort::array(ptr_sort(), elem_sort)
            }
        },
    },
    // Tuples: single-element unwraps to element sort; multi-element falls back to bv32.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("tuple_"),
        sort: |s| {
            let inner = s.strip_prefix("tuple_").unwrap_or("");
            // Empty inner or ambiguous multi-element (contains '_' but not a recognized
            // compound prefix) → bv32 fallback. Only recurse for single-element or
            // recognized compound keys (ptr_u8, arr_i32, etc.).
            if inner.is_empty() || (inner.contains('_') && !ChcCtx::is_compound_type_key(inner)) {
                Sort::bitvec(32)
            } else {
                ChcCtx::sort_from_type_key(inner)
            }
        },
    },
    // BigInt/bigint: SMT Int sort.
    PrefixTypeKeyRule {
        matches: |s| s.contains("BigInt") || s.contains("bigint"),
        sort: |_| int_sort(),
    },
    // Vec<T>: Datatype with (ptr, len, cap, data).
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("Vec") || s.contains("std_vec_Vec"),
        sort: |s| {
            let elem_sort = if let Some(suffix) = s.strip_prefix("Vec_") {
                ChcCtx::sort_from_type_key(suffix)
            } else {
                Sort::bitvec(32)
            };
            // Part of #2990: flatten DT elements to BV for PDR compatibility.
            let elem_sort = flatten_dt_array_element(elem_sort);
            // Part of #2267: Cow<str> auto-derefs to &str for name functions.
            let elem_suffix = names::sort_short_name(&elem_sort);
            let array_sort = Sort::array(ptr_sort(), elem_sort);
            struct_sort(names::vec_sort_name(&elem_suffix), names::vec_fields(array_sort))
        },
    },
    // String: Datatype with (ptr, len, cap).
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("String") || s.contains("std_string_String"),
        sort: |_| struct_sort(names::RUST_STRING_SORT, names::string_fields()),
    },
    // Box<T>: pointer-width bitvec.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("Box") || s.contains("std_boxed_Box"),
        sort: |_| ptr_sort(),
    },
    // NonNull<T>: pointer-width bitvec.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_ptr_NonNull") || s.starts_with("NonNull"),
        sort: |_| ptr_sort(),
    },
    // Unique<T>: pointer-width bitvec.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_ptr_Unique") || s.starts_with("Unique"),
        sort: |_| ptr_sort(),
    },
    // Part of #4014: Rc<T> / Weak<T> — pointer wrappers (contain NonNull<RcInner<T>>).
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_rc_Rc_") || s.starts_with("Rc_"),
        sort: |_| ptr_sort(),
    },
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_rc_Weak_") || s.starts_with("Weak_"),
        sort: |_| ptr_sort(),
    },
    // Part of #4014: RcInner<T> (RcBox) — strong(usize) + weak(usize) + value(T).
    // Memory model: use BV of (2*POINTER_WIDTH + value_width). Conservative:
    // use a wide enough BV to hold the refcounts + a pointer-width value placeholder.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_rc_RcInner"),
        sort: |_| Sort::bitvec(3 * POINTER_WIDTH),
    },
    // Part of #4014: WeakInner — internal Weak bookkeeping, pointer-width pair.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_rc_WeakInner"),
        sort: |_| Sort::bitvec(2 * POINTER_WIDTH),
    },
    // LayoutError: bv128.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_alloc_LayoutError"),
        sort: |_| Sort::bitvec(128),
    },
    // Alignment: pointer-width bitvec.
    PrefixTypeKeyRule { matches: |s| s.starts_with("std_ptr_Alignment"), sort: |_| ptr_sort() },
    // fmt infrastructure: opaque bv128.
    PrefixTypeKeyRule {
        matches: |s| {
            s.starts_with("core_fmt_rt_Argument")
                || s.starts_with("std_fmt_Argument")
                || s.starts_with("std_fmt_Arguments")
                || s.starts_with("core_fmt_Arguments")
        },
        sort: |_| Sort::bitvec(128),
    },
    // PhantomData: ZST → Bool.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("PhantomData") || s.starts_with("std_marker_PhantomData"),
        sort: |_| bool_sort(),
    },
    // RawVec<T>: Datatype with (ptr, cap).
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("RawVec") || s.contains("raw_vec_RawVec"),
        sort: |_| struct_sort("RawVec", names::rawvec_fields()),
    },
    // TryReserveError: opaque bv128.
    PrefixTypeKeyRule {
        matches: |s| {
            s.starts_with("TryReserveError") || s.starts_with("std_collections_TryReserveError")
        },
        sort: |_| Sort::bitvec(128),
    },
    // Range<T>: struct with (start, end). Part of #2323.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_ops_Range_") || s.starts_with("Range_"),
        sort: |s| {
            let inner_key = s
                .strip_prefix("std_ops_Range_")
                .or_else(|| s.strip_prefix("Range_"))
                .unwrap_or("usize");
            let elem_sort = ChcCtx::sort_from_type_key(inner_key);
            {
                let short = names::sort_short_name(&elem_sort);
                let mut name = String::with_capacity(6 + short.len());
                name.push_str("Range_");
                name.push_str(&short);
                struct_sort(name, vec![("fld_start", elem_sort.clone()), ("fld_end", elem_sort)])
            }
        },
    },
    // Option<T>: enum with None | Some(T). Part of #2323.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_option_Option_") || s.starts_with("Option_"),
        sort: |s| {
            let inner_key = s
                .strip_prefix("std_option_Option_")
                .or_else(|| s.strip_prefix("Option_"))
                .unwrap_or("usize");
            let payload_sort = ChcCtx::sort_from_type_key(inner_key);
            let option_name = names::option_sort_name(&names::sort_short_name(&payload_sort));
            enum_sort(&option_name, names::option_constructors(&option_name, payload_sort))
        },
    },
    // Coroutine types: opaque byte-array sort for heap-stored coroutines.
    // Coroutine type keys are generated by def_type_key("coro_", ...) and have
    // complex Datatype sorts (root state machine with variants) that cannot be
    // reconstructed from the string key alone. Use the same opaque byte-array
    // sort as generic ADT types. This avoids the unknown-type-key fallback
    // (which increments type_sort_fallback counter and emits UNSOUND warnings).
    // Covers: coroutine bodies, coroutine closures, coroutine witnesses.
    PrefixTypeKeyRule {
        matches: |s| {
            s.starts_with("coro_")
                || s.starts_with("coro_closure_")
                || s.starts_with("coro_witness_")
        },
        sort: |_| Sort::array(ptr_sort(), Sort::bitvec(8)),
    },
    // Closure types from def_type_key("closure_", ...) — capturing closures
    // stored on the heap. Non-capturing closures are ZST (Bool), but the
    // string-key level cannot distinguish captures. Use opaque byte-array sort
    // for heap-stored closures to avoid unknown-type-key fallback.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("closure_"),
        sort: |_| Sort::array(ptr_sort(), Sort::bitvec(8)),
    },
    // Closure types: Bool fallback. Part of #2323.
    // Exact for non-capturing closures (ZST → Bool, matches translate_ty).
    // Over-approximation for capturing closures: captured values become
    // unconstrained, which may produce false counterexamples (#2379).
    // Proper fix requires the Rust Ty (unavailable at string-key level);
    // capturing closures should be resolved by elem_sort_for_memory_array
    // before reaching this fallback.
    PrefixTypeKeyRule {
        matches: |s| s.contains("Closure") && s.starts_with("ty_"),
        sort: |_| bool_sort(),
    },
    // str (string slice): fat pointer (ptr, len, data). Part of #2323.
    // Sort name must be "Slice_bv8" to match sort_inference.rs (Fix #2379).
    PrefixTypeKeyRule {
        matches: |s| s.contains("RigidTy_Str"),
        sort: |_| {
            struct_sort(
                names::slice_sort_name("bv8"),
                vec![
                    ("fld_ptr", ptr_sort()),
                    ("fld_len", ptr_sort()),
                    ("fld_data", Sort::array(ptr_sort(), Sort::bitvec(8))),
                ],
            )
        },
    },
    // Dynamic/trait objects: fat pointer (ptr, vtable). Part of #2323.
    // Must use Dyn_Trait struct to match sort_inference.rs (Fix #2379).
    PrefixTypeKeyRule {
        matches: |s| s.contains("Dynamic") && s.starts_with("ty_"),
        sort: |_| {
            struct_sort(
                names::dyn_sort_name("Trait"),
                vec![("fld_ptr", ptr_sort()), ("fld_vtable", ptr_sort())],
            )
        },
    },
    // Slice iterators: fat pointer (ptr + end/len). Part of #2516 Step 3.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_slice_Iter_") || s.starts_with("std_slice_IterMut_"),
        sort: |_| Sort::bitvec(2 * POINTER_WIDTH),
    },
    // Vec IntoIter: 3 pointer-width fields. Part of #2516 Step 3.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_vec_IntoIter_"),
        sort: |_| Sort::bitvec(3 * POINTER_WIDTH),
    },
    // Part of #3669: Array IntoIter wraps PolymorphicIter. Memory footprint
    // is IndexRange (2 × ptr-width) + data array, approximated as a bitvec
    // for memory partitioning.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_array_IntoIter_"),
        sort: |_| Sort::bitvec(2 * POINTER_WIDTH),
    },
    // Array IntoIter internal PolymorphicIter: Range (2 × ptr-width) + data array.
    // Part of #2915: resolves unknown type key fallback for
    // `std_array_iter_iter_inner_PolymorphicIter_*` which has no layout info
    // in standalone driver mode. Memory footprint = IndexRange(start, end).
    PrefixTypeKeyRule {
        matches: |s| s.contains("PolymorphicIter"),
        sort: |_| Sort::bitvec(2 * POINTER_WIDTH),
    },
    // Hashbrown Bucket: thin pointer. Part of #2516 Step 3.
    PrefixTypeKeyRule { matches: |s| s.starts_with("hashbrown_raw_Bucket_"), sort: |_| ptr_sort() },
    // Hash collection iterators: 2-pointer width. Part of #2516 Step 3.
    PrefixTypeKeyRule {
        matches: |s| {
            (s.contains("IntoIter") || s.contains("RawIter") || s.contains("RawIterRange"))
                && (s.starts_with("hashbrown_") || s.starts_with("std_collections_"))
        },
        sort: |_| Sort::bitvec(2 * POINTER_WIDTH),
    },
    // Kani-internal iterator types. Part of #2516 Step 3.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("kani_") && s.contains("Iter"),
        sort: |_| Sort::bitvec(2 * POINTER_WIDTH),
    },
    // Core niche types. Part of #2516 Step 3.
    PrefixTypeKeyRule { matches: |s| s.contains("niche_types_"), sort: |_| ptr_sort() },
    // Result<_, TryReserveError>: bv128. Part of #2516 Step 3.
    // Part of #3738: narrowed from all Result<T,E> to only TryReserveError variants.
    // The original starts_with("std_result_Result_") matched ALL Result types,
    // forcing BV128 sort for e.g. Result<i32, ()> when stored to heap.
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_result_Result_") && s.contains("TryReserveError"),
        sort: |_| Sort::bitvec(128),
    },
    // Part of #3669: MaybeUninit<T> is a transparent wrapper — strip prefix
    // and recurse to get the inner type's sort, mirroring translate_adt_ty
    // behavior (codegen_types_adt.rs:200-206).
    PrefixTypeKeyRule {
        matches: |s| s.starts_with("std_mem_MaybeUninit_"),
        sort: |s| {
            let inner = s.strip_prefix("std_mem_MaybeUninit_").unwrap_or("");
            if inner.is_empty() { Sort::bitvec(8) } else { ChcCtx::sort_from_type_key(inner) }
        },
    },
    // Compact repr-SIMD ADT keys produced from local test newtypes such as
    // `i64x4`: flatten lane storage to the full vector bit-width.
    PrefixTypeKeyRule { matches: is_compact_simd_type_key, sort: compact_simd_type_key_sort },
    // Part of #3670: catch-all for custom user-defined ADT type keys.
    // ADT type keys start with an uppercase letter (e.g., "MyStr", "Inner").
    // Part of #4225: also matches non-std crate-prefixed ADT keys like
    // "defs_Outer_defs_Inner" where the crate name is lowercase but the
    // ADT name after the first `_` is uppercase. Without this, crate-prefixed
    // keys fall to the Phase 3 fallback which increments type_sort_fallback.
    // These custom types have no prefix table entry because their layout is
    // unknown at the string-key level (often DSTs or complex generics where
    // translate_ty and get_type_size both failed). Return the same opaque
    // byte-array sort as the fallback, but WITHOUT incrementing the
    // type_sort_fallback counter — these are expected custom ADT keys, not
    // translation failures.
    PrefixTypeKeyRule {
        matches: |s| {
            // Direct uppercase start: "MyStr", "Inner", "Outer_u8"
            s.as_bytes().first().is_some_and(|b| b.is_ascii_uppercase())
            // Crate-prefixed: "defs_Outer_Inner" — lowercase crate, `_` then uppercase ADT
            || s.bytes().zip(s.bytes().skip(1)).any(|(a, b)| a == b'_' && b.is_ascii_uppercase())
        },
        sort: |_| Sort::array(ptr_sort(), Sort::bitvec(8)),
    },
];

fn is_compact_simd_type_key(type_key: &str) -> bool {
    compact_simd_type_key_width(type_key).is_some()
}

fn compact_simd_type_key_sort(type_key: &str) -> Sort {
    compact_simd_type_key_width(type_key)
        .map(Sort::bitvec)
        .unwrap_or_else(|| Sort::array(ptr_sort(), Sort::bitvec(8)))
}

fn compact_simd_type_key_width(type_key: &str) -> Option<u32> {
    let (elem_key, lanes) = type_key.rsplit_once('x')?;
    let lane_count: u32 = lanes.parse().ok()?;
    if lane_count == 0 {
        return None;
    }
    compact_simd_elem_width(elem_key)?.checked_mul(lane_count)
}

fn compact_simd_elem_width(elem_key: &str) -> Option<u32> {
    match elem_key {
        "i8" | "u8" => Some(8),
        "i16" | "u16" | "f16" => Some(16),
        "i32" | "u32" | "f32" => Some(32),
        "i64" | "u64" | "f64" => Some(64),
        "i128" | "u128" | "f128" => Some(128),
        "isize" | "usize" => Some(POINTER_WIDTH),
        _ => None,
    }
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) fn has_prefix_type_key_rule(type_key: &str) -> bool {
    PREFIX_TYPE_KEY_RULES.iter().any(|rule| (rule.matches)(type_key))
}
