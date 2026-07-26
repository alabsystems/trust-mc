// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Intrinsic/math/alloc/fmt suffix-based stub lookup helpers for StubRegistry.
// Extracted from lookup_helpers.rs as part of #2246 decomposition.
//
// Contains: BigInt, BigRational, primitive traits, Option, Result,
// allocation, Layout, NonNull, raw pointer, formatting, panic, and UB/mem lookups.

use super::{StubKind, StubRegistry};

/// Table entry for trait-guarded method → StubKind lookup.
struct TraitStubEntry {
    method: &'static str,
    trait_guard: &'static str,
    kind: StubKind,
}

/// BigInt method → StubKind table (Part of #734, #742).
const BIGINT_STUBS: &[TraitStubEntry] = &[
    TraitStubEntry { method: "from", trait_guard: "From", kind: StubKind::BigIntFrom },
    TraitStubEntry { method: "one", trait_guard: "One>", kind: StubKind::BigIntOne },
    TraitStubEntry { method: "zero", trait_guard: "Zero>", kind: StubKind::BigIntZero },
    TraitStubEntry { method: "is_zero", trait_guard: "Zero>", kind: StubKind::BigIntIsZero },
    TraitStubEntry {
        method: "is_negative",
        trait_guard: "Signed>",
        kind: StubKind::BigIntIsNegative,
    },
    TraitStubEntry { method: "abs", trait_guard: "Signed>", kind: StubKind::BigIntAbs },
    TraitStubEntry { method: "add", trait_guard: "Add>", kind: StubKind::BigIntAdd },
    TraitStubEntry { method: "sub", trait_guard: "Sub>", kind: StubKind::BigIntSub },
    TraitStubEntry { method: "mul", trait_guard: "Mul>", kind: StubKind::BigIntMul },
    TraitStubEntry { method: "div", trait_guard: "Div>", kind: StubKind::BigIntDiv },
    TraitStubEntry { method: "rem", trait_guard: "Rem>", kind: StubKind::BigIntRem },
    TraitStubEntry { method: "neg", trait_guard: "Neg>", kind: StubKind::BigIntNeg },
    TraitStubEntry {
        method: "mul_assign",
        trait_guard: "MulAssign>",
        kind: StubKind::BigIntMulAssign,
    },
    TraitStubEntry {
        method: "add_assign",
        trait_guard: "AddAssign>",
        kind: StubKind::BigIntAddAssign,
    },
    TraitStubEntry {
        method: "sub_assign",
        trait_guard: "SubAssign>",
        kind: StubKind::BigIntSubAssign,
    },
    TraitStubEntry { method: "eq", trait_guard: "PartialEq>", kind: StubKind::BigIntEq },
    TraitStubEntry { method: "cmp", trait_guard: "Ord>", kind: StubKind::BigIntCmp },
    TraitStubEntry {
        method: "partial_cmp",
        trait_guard: "PartialOrd>",
        kind: StubKind::BigIntPartialCmp,
    },
    TraitStubEntry { method: "lt", trait_guard: "PartialOrd>", kind: StubKind::BigIntLt },
    TraitStubEntry { method: "le", trait_guard: "PartialOrd>", kind: StubKind::BigIntLe },
    TraitStubEntry { method: "gt", trait_guard: "PartialOrd>", kind: StubKind::BigIntGt },
    TraitStubEntry { method: "ge", trait_guard: "PartialOrd>", kind: StubKind::BigIntGe },
    TraitStubEntry { method: "clone", trait_guard: "Clone>", kind: StubKind::BigIntClone },
    TraitStubEntry { method: "shl", trait_guard: "Shl>", kind: StubKind::BigIntShl },
    TraitStubEntry { method: "shr", trait_guard: "Shr>", kind: StubKind::BigIntShr },
    TraitStubEntry {
        method: "shl_assign",
        trait_guard: "ShlAssign>",
        kind: StubKind::BigIntShlAssign,
    },
    TraitStubEntry {
        method: "shr_assign",
        trait_guard: "ShrAssign>",
        kind: StubKind::BigIntShrAssign,
    },
    TraitStubEntry { method: "bitand", trait_guard: "BitAnd>", kind: StubKind::BigIntBitAnd },
    TraitStubEntry { method: "bitor", trait_guard: "BitOr>", kind: StubKind::BigIntBitOr },
    TraitStubEntry { method: "bitxor", trait_guard: "BitXor>", kind: StubKind::BigIntBitXor },
];

/// BigRational method → StubKind table (Part of #911).
const BIGRATIONAL_STUBS: &[TraitStubEntry] = &[
    // "new" can appear as BigRational::new or num_rational::Rational::<BigInt>::new.
    // Since this table is only reached when the category guard passes (requiring
    // BigRational/num_rational/Ratio<BigInt in path), these broad guards are safe.
    TraitStubEntry { method: "new", trait_guard: "Ratio", kind: StubKind::BigRationalNew },
    TraitStubEntry { method: "new", trait_guard: "BigRational", kind: StubKind::BigRationalNew },
    TraitStubEntry { method: "from", trait_guard: "Ratio", kind: StubKind::BigRationalFrom },
    TraitStubEntry { method: "from", trait_guard: "BigRational", kind: StubKind::BigRationalFrom },
    TraitStubEntry { method: "add", trait_guard: "Add>", kind: StubKind::BigRationalAdd },
    TraitStubEntry { method: "sub", trait_guard: "Sub>", kind: StubKind::BigRationalSub },
    TraitStubEntry { method: "mul", trait_guard: "Mul>", kind: StubKind::BigRationalMul },
    TraitStubEntry { method: "div", trait_guard: "Div>", kind: StubKind::BigRationalDiv },
    TraitStubEntry { method: "neg", trait_guard: "Neg>", kind: StubKind::BigRationalNeg },
    TraitStubEntry { method: "eq", trait_guard: "PartialEq>", kind: StubKind::BigRationalEq },
    TraitStubEntry { method: "lt", trait_guard: "PartialOrd>", kind: StubKind::BigRationalLt },
    TraitStubEntry { method: "le", trait_guard: "PartialOrd>", kind: StubKind::BigRationalLe },
    TraitStubEntry { method: "gt", trait_guard: "PartialOrd>", kind: StubKind::BigRationalGt },
    TraitStubEntry { method: "ge", trait_guard: "PartialOrd>", kind: StubKind::BigRationalGe },
    TraitStubEntry { method: "clone", trait_guard: "Clone>", kind: StubKind::BigRationalClone },
    TraitStubEntry {
        method: "add_assign",
        trait_guard: "AddAssign>",
        kind: StubKind::BigRationalAddAssign,
    },
    TraitStubEntry {
        method: "sub_assign",
        trait_guard: "SubAssign>",
        kind: StubKind::BigRationalSubAssign,
    },
    TraitStubEntry {
        method: "mul_assign",
        trait_guard: "MulAssign>",
        kind: StubKind::BigRationalMulAssign,
    },
    TraitStubEntry {
        method: "div_assign",
        trait_guard: "DivAssign>",
        kind: StubKind::BigRationalDivAssign,
    },
];

/// Table-driven trait-guarded stub lookup: finds matching (method, trait_guard) → StubKind.
///
/// Part of #3687: Guards are matched with trailing `>` stripped so they work
/// for both canonical paths (`<T as Trait>::method`) and MIR paths
/// (`module::<impl Trait for T>::method`). The method name check prevents
/// false positives from partial trait name matches (e.g., `"Sub"` won't
/// match a `SubAssign` path because the method names differ).
fn lookup_trait_stub(
    table: &[TraitStubEntry],
    method: &str,
    path: &str,
    type_label: &str,
) -> Option<StubKind> {
    for entry in table {
        let guard = entry.trait_guard.strip_suffix('>').unwrap_or(entry.trait_guard);
        if entry.method == method && path.contains(guard) {
            return Some(entry.kind);
        }
    }
    tracing::warn!(method, path, type_label, "unhandled method in stub lookup");
    None
}

impl StubRegistry {
    /// Suffix-based BigInt stub lookup (Part of #734, #742).
    pub(super) fn lookup_bigint_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        lookup_trait_stub(BIGINT_STUBS, method, path, "BigInt")
    }

    /// Suffix-based BigRational stub lookup (Part of #911).
    /// Maps BigRational operations to SMT Real sort operations.
    pub(super) fn lookup_bigrational_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        lookup_trait_stub(BIGRATIONAL_STUBS, method, path, "BigRational")
    }

    /// Check if path is a primitive trait implementation (Part of #1240, #502, #1478).
    pub(super) fn is_primitive_trait_path(path: &str) -> bool {
        let Some(method) = Self::extract_method_name(path) else {
            return false;
        };

        // Check if method + trait context matches a primitive trait pattern
        let is_trait_method = match method {
            "eq" | "ne" => path.contains("PartialEq"),
            "lt" | "le" | "gt" | "ge" => path.contains("PartialOrd"),
            "clone" => path.contains("Clone"),
            // Use "::Ord" to avoid matching "Ordering", "Record", "Word", etc.
            // Use "::Ord" to avoid matching "Ordering", "Record", "Word", etc.
            // min/max/clamp handled via string dispatch in dispatch_chain, not StubKind.
            "cmp" => path.contains("::Ord"),
            // non-trait methods don't match — this is expected, not a gap
            _ => false, // non-enum: &str (method name)
        };

        if !is_trait_method {
            return false;
        }

        // Types with custom trait impls that shouldn't use primitive stubs.
        // Compound types (Option, Result, tuples) are excluded because their
        // derived PartialEq requires structural decomposition — fn_inline handles
        // this correctly by inlining the derived PartialEq MIR body.
        const EXCLUDED_TYPES: &[&str] = &[
            "BigInt",
            "BigUint",
            "BigRational",
            "HashMap",
            "HashSet",
            "BTreeMap",
            "BTreeSet",
            "TrustMcMap",
            "Vec",
            "String",
            "Box",
            "Option",
            "Result",
        ];
        if EXCLUDED_TYPES.iter().any(|t| path.contains(t)) {
            return false;
        }

        if path.contains("&str") || path.contains("<str") || path.contains("::str::") {
            return false;
        }

        // Tuples: both canonical trait paths (`<(T1, T2, ...) as PartialEq>::eq`)
        // and `def_path_str` impl paths (`core::tuple::<impl PartialEq for ...>::eq`)
        // require structural decomposition. The primitive cmp stub treats
        // operands as flat values, which fails for multi-field tuples (#3786).
        if path.starts_with("<(") || path.contains("tuple::<impl") {
            return false;
        }

        true
    }

    /// Lookup primitive trait method stub (Part of #1240, #502, #1478).
    /// Returns the appropriate StubKind for PartialEq, PartialOrd, Clone, or Ord trait methods.
    pub(super) fn lookup_primitive_trait(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        match method {
            "eq" if path.contains("PartialEq") => Some(StubKind::PrimitivePartialEqEq),
            "ne" if path.contains("PartialEq") => Some(StubKind::PrimitivePartialEqNe),
            "lt" if path.contains("PartialOrd") => Some(StubKind::PrimitivePartialOrdLt),
            "le" if path.contains("PartialOrd") => Some(StubKind::PrimitivePartialOrdLe),
            "gt" if path.contains("PartialOrd") => Some(StubKind::PrimitivePartialOrdGt),
            "ge" if path.contains("PartialOrd") => Some(StubKind::PrimitivePartialOrdGe),
            "clone" if path.contains("Clone") => Some(StubKind::PrimitiveClone),
            // Use "::Ord" to avoid matching "Ordering", "Record", "Word", etc.
            "cmp" if path.contains("::Ord") => Some(StubKind::OrdCmp),
            // min/max/clamp handled via string dispatch, not StubKind (Part of #4008).
            _ => {
                // non-enum: &str (method name)
                tracing::warn!(method, path, "unhandled primitive trait method in stub lookup");
                None
            }
        }
    }

    /// Method-based Option stub lookup (Part of #2130 refactor).
    /// Replaces ~20 if-else branches with extract-then-match.
    pub(super) fn lookup_option_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        match method {
            "unwrap" if !path.contains("unwrap_or") && !path.contains("unwrap_unchecked") => {
                Some(StubKind::OptionUnwrap)
            }
            "unwrap_unchecked" => Some(StubKind::OptionUnwrapUnchecked),
            "is_some_and" => Some(StubKind::OptionIsSomeAnd),
            "is_some" => Some(StubKind::OptionIsSome),
            "is_none" => Some(StubKind::OptionIsNone),
            // Match _else variants BEFORE non-else to avoid false suffix match
            "unwrap_or_else" => Some(StubKind::OptionUnwrapOrElse),
            "unwrap_or" => Some(StubKind::OptionUnwrapOr),
            "expect" => Some(StubKind::OptionExpect),
            "ok_or_else" => Some(StubKind::OptionOkOrElse),
            "ok_or" => Some(StubKind::OptionOkOr),
            "and_then" => Some(StubKind::OptionAndThen),
            // Match map_or BEFORE map to avoid false suffix match (Part of #4208)
            "map_or" => Some(StubKind::OptionMapOr),
            "map" => Some(StubKind::OptionMap),
            "take" => Some(StubKind::OptionTake),
            "copied" | "cloned" => Some(StubKind::OptionCopied),
            // Structural reference adapters are intentionally handled by MIR/CHC
            // inline fast paths rather than stub translation.
            "as_ref" | "as_mut" => None,
            _ => {
                // non-enum: &str (method name)
                tracing::warn!(method, path, "unhandled Option method in stub lookup");
                None
            }
        }
    }

    /// Method-based Result stub lookup (Part of #2130 refactor).
    /// Replaces ~20 if-else branches with extract-then-match.
    pub(super) fn lookup_result_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        match method {
            "is_ok" => Some(StubKind::ResultIsOk),
            "is_err" => Some(StubKind::ResultIsErr),
            "and_then" => Some(StubKind::ResultAndThen),
            // Match ok/err carefully: ok must not match is_ok/ok_or/ok_or_else
            "ok" => Some(StubKind::ResultOk),
            // err must not match is_err/map_err
            "err" => Some(StubKind::ResultErr),
            // Match map_err BEFORE map to avoid false suffix match
            "map_err" => Some(StubKind::ResultMapErr),
            "map" => Some(StubKind::ResultMap),
            // Match _else variants BEFORE non-else to avoid false suffix match
            "unwrap_or_else" => Some(StubKind::ResultUnwrapOrElse),
            "unwrap_or" => Some(StubKind::ResultUnwrapOr),
            "expect" => Some(StubKind::ResultExpect),
            // Match unwrap_err BEFORE unwrap to avoid false suffix match
            "unwrap_err" => Some(StubKind::ResultUnwrapErr),
            "unwrap" => Some(StubKind::ResultUnwrap),
            // Result::copied / cloned are the same pass-through shape as the
            // existing Option::copied stub: preserve the outer enum and copy
            // the payload when the representation already matches.
            "copied" | "cloned" => Some(StubKind::OptionCopied),
            _ => {
                // non-enum: &str (method name)
                tracing::warn!(method, path, "unhandled Result method in stub lookup");
                None
            }
        }
    }

    /// Method-based allocation stub lookup (Part of #2130 refactor).
    pub(super) fn lookup_alloc_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path);
        let has_allocator_trait = path.contains("Allocator");

        // These symbols do not always follow the >::method pattern.
        if Self::ends_with_any(
            path,
            &["alloc::alloc", "std::alloc::alloc", "__rust_alloc", "exchange_malloc"],
        ) || path.contains("__rust_alloc>")
        {
            return Some(StubKind::RustAlloc);
        }
        if Self::ends_with_any(
            path,
            &["alloc::alloc_zeroed", "std::alloc::alloc_zeroed", "__rust_alloc_zeroed"],
        ) || path.contains("__rust_alloc_zeroed>")
        {
            return Some(StubKind::RustAllocZeroed);
        }
        if Self::ends_with_any(path, &["alloc::dealloc", "std::alloc::dealloc", "__rust_dealloc"])
            || path.contains("__rust_dealloc>")
            || (has_allocator_trait && method == Some("deallocate"))
        {
            return Some(StubKind::RustDealloc);
        }
        if Self::ends_with_any(path, &["alloc::realloc", "std::alloc::realloc", "__rust_realloc"])
            || path.contains("__rust_realloc>")
        {
            return Some(StubKind::RustRealloc);
        }
        if path.contains("Global::alloc_impl") {
            return Some(StubKind::GlobalAllocImpl);
        }
        if path.ends_with("handle_alloc_error")
            || Self::contains_all(path, &["handle_alloc_error", "rt_error"])
        {
            return Some(StubKind::HandleAllocError);
        }
        if path.contains("__rust_no_alloc_shim_is_unstable") {
            return Some(StubKind::RustNoAllocShimIsUnstable);
        }
        if has_allocator_trait && method == Some("allocate") {
            return Some(StubKind::AllocatorAllocate);
        }
        None
    }

    /// Method-based Layout stub lookup (Part of #2130 refactor).
    pub(super) fn lookup_layout_suffix(path: &str) -> Option<StubKind> {
        // Part of #3273: Handle nested helper Layout::array::inner(element_size, align, n).
        // extract_method_name returns "inner" which is too generic; check full path instead.
        if path.ends_with("::array::inner") {
            return Some(StubKind::LayoutArrayInner);
        }
        let method = Self::extract_method_name(path)?;
        match method {
            "size" => Some(StubKind::LayoutSize),
            "align" => Some(StubKind::LayoutAlign),
            "dangling" => Some(StubKind::LayoutDangling),
            "is_size_align_valid" => Some(StubKind::LayoutIsSizeAlignValid),
            "padding_needed_for" => Some(StubKind::LayoutPaddingNeededFor),
            "array" => Some(StubKind::LayoutArray),
            "new" => Some(StubKind::LayoutNew),
            "max_size_for_align" => Some(StubKind::LayoutMaxSizeForAlign),
            "from_size_align_unchecked" => Some(StubKind::LayoutFromSizeAlignUnchecked),
            // Part of #2632: Layout methods used by hashbrown during HashMap operations
            "calculate_layout_for" => Some(StubKind::LayoutCalculateLayoutFor),
            "for_value_raw" => Some(StubKind::LayoutForValueRaw),
            "from_size_align" => Some(StubKind::LayoutFromSizeAlign),
            _ => {
                // non-enum: &str (method name)
                tracing::debug!(method, path, "unhandled Layout method in stub lookup");
                None
            }
        }
    }

    /// Method-based NonNull stub lookup (Part of #2130 refactor).
    pub(super) fn lookup_nonnull_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        match method {
            "new_unchecked" => Some(StubKind::NonNullNew),
            "new" => Some(StubKind::NonNullNew),
            "slice_from_raw_parts" => Some(StubKind::NonNullSliceFromRawParts),
            "as_non_null_ptr" => Some(StubKind::NonNullAsNonNullPtr),
            "dangling" => Some(StubKind::NonNullDangling),
            "as_mut_ptr" => Some(StubKind::NonNullAsMutPtr),
            "as_ptr" => Some(StubKind::NonNullAsPtr),
            // Part of #2632: NonNull::cast used by hashbrown during HashMap operations
            "cast" => Some(StubKind::NonNullCast),
            // Part of #2876 RC2-B: pre-inlined Vec::IntoIter internals call NonNull::{add,read}.
            "add" => Some(StubKind::PtrAdd),
            "read" => Some(StubKind::PtrRead),
            // Part of #2876 post-OI4: route ref/mut helpers through identity ptr-cast
            // semantics to avoid unconstrained nonnull-extra fallthrough.
            "as_ref" | "as_mut" | "from_ref" | "from_mut" => Some(StubKind::PtrCast),
            _ => {
                // non-enum: &str (method name)
                tracing::debug!(method, path, "unhandled NonNull method in stub lookup");
                None
            }
        }
    }

    /// Method-based raw pointer stub lookup (Part of #2130 refactor).
    /// Handles *const T and *mut T method paths.
    pub(super) fn lookup_raw_ptr_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path)?;
        match method {
            "add" => Some(StubKind::PtrAdd),
            "sub" => Some(StubKind::PtrSub),
            "write" => Some(StubKind::PtrWrite),
            "read" => Some(StubKind::PtrRead),
            "addr" => Some(StubKind::PtrAddr),
            "with_addr" => Some(StubKind::PtrWithAddr),
            "is_null" => Some(StubKind::PtrIsNull),
            "cast_const" if path.contains("mut_ptr::") => Some(StubKind::PtrCastConst),
            "cast" => Some(StubKind::PtrCast),
            // Part of #2632: wrapping pointer arithmetic used by hashbrown
            "wrapping_add" => Some(StubKind::PtrWrappingAdd),
            "wrapping_sub" => Some(StubKind::PtrWrappingSub),
            // Part of #3514: byte-level wrapping add/sub (no sizeof(T) scaling)
            "wrapping_byte_add" => Some(StubKind::PtrWrappingByteAdd),
            "wrapping_byte_sub" => Some(StubKind::PtrWrappingByteSub),
            "wrapping_offset" => Some(StubKind::PtrWrappingOffset),
            "wrapping_byte_offset" => Some(StubKind::PtrWrappingByteOffset),
            "with_metadata_of" => Some(StubKind::PtrWithMetadataOf),
            _ => {
                // non-enum: &str (method name)
                tracing::debug!(method, path, "unhandled raw pointer method in stub lookup");
                None
            }
        }
    }

    /// Method-based formatting stub lookup (Part of #2130 refactor).
    pub(super) fn lookup_fmt_suffix(path: &str) -> Option<StubKind> {
        let method = Self::extract_method_name(path);
        let is_fmt_argument = path.contains("fmt::rt::Argument");
        let is_fmt_arguments = path.contains("fmt::Arguments");

        if method == Some("new_display") && is_fmt_argument {
            return Some(StubKind::FmtArgumentNewDisplay);
        }
        if method == Some("new") && is_fmt_arguments {
            return Some(StubKind::FmtArgumentsNew);
        }
        if method == Some("from_str") && is_fmt_arguments {
            return Some(StubKind::FmtArgumentsFromStr);
        }
        if Self::contains_any(
            path,
            &["std::fmt::format", "core::fmt::format", "alloc::fmt::format"],
        ) {
            return Some(StubKind::FmtFormat);
        }
        None
    }

    /// Panic-related stub lookup (Part of #2130 refactor, extended per #2252, #3300).
    ///
    /// Two categories:
    /// - `PanicUnreachable`: genuinely unreachable panic paths (alloc error handler
    ///   under --no-malloc-may-fail). No error rule emitted.
    /// - `PanicError`: reachable panic paths — user-facing (`assert!()`, `panic!()`),
    ///   compiler-generated (`panic_nounwind`/`panic_nounwind_fmt` from checked
    ///   arithmetic overflow in `ptr.offset()` etc.). These MUST emit `→ error()`.
    pub(super) fn lookup_panic_suffix(path: &str) -> Option<StubKind> {
        // PanicUnreachable: alloc error handler — genuinely unreachable under
        // --no-malloc-may-fail. No error rule emitted.
        if Self::contains_any(path, &["__rust_alloc_error_handler"]) {
            return Some(StubKind::PanicUnreachable);
        }
        // Part of #3300: panic_nounwind/panic_nounwind_fmt are NOT unreachable.
        // The compiler uses these for checked arithmetic overflow (e.g.,
        // `checked_mul` in `ptr.offset()`) which IS reachable from user code.
        // Classifying them as PanicUnreachable silently drops overflow detection
        // paths → false PROOF. Emit error() for soundness.
        if Self::contains_any(path, &["panicking::panic_nounwind", "panic_nounwind_fmt"]) {
            return Some(StubKind::PanicError);
        }
        // Part of #2252: PanicError — user-facing panic paths from assert!()/panic!().
        // `rt::panic_fmt` is the common entry point for all user panics.
        // `panicking::panic*` variants are called by the assert!/panic! macros.
        if Self::contains_any(
            path,
            &[
                "rt::panic_fmt",
                "panicking::panic_explicit",
                "panicking::panic_display",
                "panicking::panic_fmt",
                "panicking::panic_str",
                "panicking::begin_panic",
                "panicking::assert_failed",
            ],
        ) {
            return Some(StubKind::PanicError);
        }
        // Catch-all: any remaining `panicking::panic` variant not already matched.
        // Must come after specific matches to avoid shadowing PanicUnreachable patterns.
        if Self::contains_any(path, &["panicking::panic"]) {
            return Some(StubKind::PanicError);
        }
        None
    }

    /// UB-check and mem intrinsic stub lookup (Part of #2130 refactor).
    pub(super) fn lookup_ub_mem_suffix(path: &str) -> Option<StubKind> {
        if Self::contains_any(path, &["ub_checks::check_language_ub"]) {
            return Some(StubKind::UbCheckLanguageUb);
        }
        if Self::contains_any(
            path,
            &[
                "ub_checks::maybe_is_aligned_and_not_null",
                "ub_checks::is_aligned_and_not_null",
                // Rust nightly 2025-12-03+ renamed these to shorter forms.
                // Part of #3665: raw pointer cast path triggers maybe_is_aligned.
                "ub_checks::maybe_is_aligned",
                "ub_checks::is_aligned",
            ],
        ) {
            return Some(StubKind::UbCheckMaybeIsAligned);
        }
        if Self::contains_any(
            path,
            &["ub_checks::maybe_is_nonoverlapping", "ub_checks::is_nonoverlapping"],
        ) {
            return Some(StubKind::UbCheckMaybeIsNonoverlapping);
        }
        let method = Self::extract_method_name(path);
        if method == Some("size_of")
            && (Self::contains_any(path, &["std::mem::size_of", "core::mem::size_of"])
                || Self::ends_with_any(path, &[">::size_of"]))
        {
            return Some(StubKind::MemSizeOf);
        }
        // size_of_val_raw<T: ?Sized>(*const T) — for sized T (Box<T> dealloc), same as size_of::<T>().
        // Part of #3184: Box drop path computes Layout via size_of_val_raw.
        if method == Some("size_of_val_raw")
            && Self::contains_any(
                path,
                &["std::mem::size_of_val_raw", "core::mem::size_of_val_raw"],
            )
        {
            return Some(StubKind::MemSizeOf);
        }
        if method == Some("align_of")
            && (Self::contains_any(
                path,
                &[
                    "std::mem::align_of",
                    "core::mem::align_of",
                    "std::intrinsics::align_of",
                    "core::intrinsics::align_of",
                ],
            ) || Self::ends_with_any(path, &[">::align_of"]))
        {
            return Some(StubKind::MemAlignOf);
        }
        // align_of_val_raw<T: ?Sized>(*const T) — for sized T (Box<T> dealloc), same as align_of::<T>().
        // Part of #3184: Box drop path computes Layout via align_of_val_raw.
        if method == Some("align_of_val_raw")
            && Self::contains_any(
                path,
                &["std::mem::align_of_val_raw", "core::mem::align_of_val_raw"],
            )
        {
            return Some(StubKind::MemAlignOf);
        }
        if Self::contains_any(path, &["precondition_check"]) {
            return Some(StubKind::PreconditionCheck);
        }
        // std::intrinsics::assert_inhabited — compile-time check, no-op (Part of #2916)
        if Self::contains_any(path, &["intrinsics::assert_inhabited"]) {
            return Some(StubKind::AssertInhabited);
        }
        None
    }
}
