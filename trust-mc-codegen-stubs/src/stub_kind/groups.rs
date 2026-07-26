// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! StubGroup bitmask for StubKind membership (Part of #2408). Groups map to `is_*` predicates;
//! variants can belong to multiple groups. Bitmask consumed by consistency tests (#2408 T6).
#![allow(dead_code)]

use super::StubKind;
/// Bitmask type for stub group membership. 64 bits supports up to 64 groups.
pub(crate) type StubGroupMask = u64;

// Group bit constants — ordering matches predicates.rs.
pub(crate) const SLICE_STUB: StubGroupMask = 1 << 0;
pub(crate) const OPTION_PREDICATE: StubGroupMask = 1 << 1;
pub(crate) const RESULT_PREDICATE: StubGroupMask = 1 << 2;
pub(crate) const PRIMITIVE_CLONE: StubGroupMask = 1 << 3;
pub(crate) const UNWRAP_OR: StubGroupMask = 1 << 4;
pub(crate) const UNWRAP_EXPECT: StubGroupMask = 1 << 5;
pub(crate) const UNWRAP_OR_ELSE: StubGroupMask = 1 << 6;
pub(crate) const COMBINATOR: StubGroupMask = 1 << 7;
pub(crate) const COLLECTION_PREDICATE: StubGroupMask = 1 << 8;
pub(crate) const UB_PANIC: StubGroupMask = 1 << 9;
pub(crate) const FMT: StubGroupMask = 1 << 10;
pub(crate) const VEC_CORE: StubGroupMask = 1 << 11;
pub(crate) const STRING_CORE: StubGroupMask = 1 << 12;
pub(crate) const RAWVEC: StubGroupMask = 1 << 13;
pub(crate) const TRY_RESIDUAL: StubGroupMask = 1 << 14;
pub(crate) const PTR_CAST: StubGroupMask = 1 << 15;
pub(crate) const DISPLAY_COW: StubGroupMask = 1 << 16;
pub(crate) const LAYOUT_EXTRA: StubGroupMask = 1 << 17;
pub(crate) const NONNULL_EXTRA: StubGroupMask = 1 << 18;
pub(crate) const ALLOC_EXTRA: StubGroupMask = 1 << 19;
pub(crate) const BTREESET: StubGroupMask = 1 << 20;
pub(crate) const HASHSET: StubGroupMask = 1 << 21;
pub(crate) const BTREEMAP_INTERNAL: StubGroupMask = 1 << 22;
pub(crate) const PRIMITIVE_CMP: StubGroupMask = 1 << 23;
pub(crate) const ITERATOR_ADAPTER: StubGroupMask = 1 << 24;
pub(crate) const KANI_MEM: StubGroupMask = 1 << 25;
pub(crate) const KANI_MEM_ASSUME_TRUE: StubGroupMask = 1 << 26;
pub(crate) const KANI_MEM_NOOP: StubGroupMask = 1 << 27;
pub(crate) const UB_CHECK_ASSUME_TRUE: StubGroupMask = 1 << 28;
pub(crate) const UB_CHECK_NOOP: StubGroupMask = 1 << 29;
pub(crate) const PANIC_ERROR: StubGroupMask = 1 << 30;
pub(crate) const PANIC_UNREACHABLE: StubGroupMask = 1 << 31;
pub(crate) const MEM_INTRINSIC: StubGroupMask = 1 << 32;
pub(crate) const PTR_MEMORY: StubGroupMask = 1 << 33;
pub(crate) const POINTER_UTILITY: StubGroupMask = 1 << 34;
pub(crate) const BIG_RATIONAL: StubGroupMask = 1 << 35;

impl StubKind {
    /// Returns the bitmask of all groups this stub belongs to. A variant may belong to
    /// multiple groups (e.g., `NonNullCast` belongs to both `NONNULL_EXTRA` and
    /// `POINTER_UTILITY`).
    pub(crate) const fn group_mask(self) -> StubGroupMask {
        match self {
            Self::SlicePartialEqEqual
            | Self::SliceIndexIndex
            | Self::IndexIndex
            | Self::IndexMut
            | Self::SliceGetUnchecked
            | Self::SliceIsEmpty
            | Self::SliceFirst
            | Self::SliceGet
            | Self::SlicePartitionPoint
            | Self::SliceLast
            | Self::SliceBinarySearchByKey
            | Self::SliceChunks
            | Self::SliceWindows
            | Self::MemchrMemchr => SLICE_STUB,
            // SliceAsPtr/SliceAsMutPtr have dual membership: SLICE_STUB + POINTER_UTILITY
            Self::SliceAsPtr | Self::SliceAsMutPtr => SLICE_STUB | POINTER_UTILITY,
            Self::OptionIsSome | Self::OptionIsSomeAnd | Self::OptionIsNone => OPTION_PREDICATE,
            Self::ResultIsOk | Self::ResultIsErr => RESULT_PREDICATE,
            Self::PrimitiveClone => PRIMITIVE_CLONE,
            Self::OptionUnwrapOr | Self::ResultUnwrapOr => UNWRAP_OR,
            Self::OptionUnwrap
            | Self::OptionExpect
            | Self::ResultUnwrap
            | Self::ResultExpect
            | Self::ResultUnwrapErr => UNWRAP_EXPECT,
            Self::OptionUnwrapUnchecked => UNWRAP_EXPECT,
            Self::OptionUnwrapOrElse | Self::ResultUnwrapOrElse => UNWRAP_OR_ELSE,
            Self::OptionAndThen
            | Self::OptionOkOrElse
            | Self::OptionOkOr
            | Self::OptionMap
            | Self::OptionTake
            | Self::OptionMapOr
            | Self::OptionCopied
            | Self::ResultMap
            | Self::ResultAndThen
            | Self::ResultMapErr
            | Self::ResultOk
            | Self::ResultErr => COMBINATOR,
            // VecIsEmpty has dual membership: COLLECTION_PREDICATE + VEC_CORE
            Self::VecIsEmpty => COLLECTION_PREDICATE | VEC_CORE,
            Self::VecContains
            | Self::VecEq
            | Self::StringIsEmpty
            | Self::StringContains
            | Self::StringStartsWith
            | Self::StringEndsWith
            | Self::StringIsAscii => COLLECTION_PREDICATE,
            // UB/panic variants have composite group membership
            Self::UbCheckLanguageUb => UB_PANIC | UB_CHECK_NOOP,
            Self::UbCheckMaybeIsAligned => UB_PANIC | UB_CHECK_ASSUME_TRUE,
            Self::UbCheckMaybeIsNonoverlapping => UB_PANIC | UB_CHECK_ASSUME_TRUE,
            Self::PreconditionCheck | Self::AssertInhabited => UB_PANIC | UB_CHECK_NOOP,
            Self::PanicUnreachable => UB_PANIC | PANIC_UNREACHABLE,
            Self::PanicError => UB_PANIC | PANIC_ERROR,
            Self::FmtArgumentNewDisplay
            | Self::FmtArgumentsNew
            | Self::FmtArgumentsFromStr
            | Self::FmtFormat => FMT,
            Self::VecNew
            | Self::VecWithCapacity
            | Self::VecWithCapacityIn
            | Self::VecFromElem
            | Self::VecPush
            | Self::VecReserve
            | Self::VecReserveExact
            | Self::VecShrinkToFit
            | Self::VecPop
            | Self::VecRemove
            | Self::VecLen
            | Self::VecCapacity
            | Self::VecResize
            | Self::VecSetLen
            | Self::VecClear
            | Self::VecTruncate
            | Self::VecClone
            | Self::VecDrop
            | Self::VecAsSlice
            | Self::VecAsPtr
            | Self::VecAsMutPtr
            | Self::SliceIntoVec
            | Self::VecFromSlice
            | Self::VecAppendElements
            | Self::VecFromIter
            | Self::VecExtendWith
            | Self::VecSpareCapacityMut
            | Self::VecExtendTrusted
            | Self::VecIntoBoxedSlice
            | Self::VecSwap
            | Self::VecRetain
            | Self::VecAppend
            | Self::VecLast
            | Self::VecReverse
            | Self::VecDedup
            | Self::VecSplitOff
            | Self::VecSort
            | Self::VecDrain
            | Self::VecSplice => VEC_CORE,
            Self::StringNew
            | Self::StringFrom
            | Self::StringLen
            | Self::StringPush
            | Self::StringPushStr
            | Self::StringClear
            | Self::StringClone
            | Self::StringTruncate
            | Self::StringFromUtf8Lossy
            | Self::StrFromUtf8
            | Self::IntParse
            | Self::SplitWhitespace
            | Self::SplitWhitespaceNext
            | Self::StringEq
            | Self::StringAsStr
            | Self::StringIntoBoxedStr
            | Self::StrBytesNth
            | Self::StrCharsNth => STRING_CORE,
            Self::RawVecNewIn
            | Self::RawVecCapacity
            | Self::RawVecGrowOne
            | Self::RawVecPtr
            | Self::RawVecFromNonNullIn
            | Self::RawVecDrop
            | Self::RawVecShrinkToFit => RAWVEC,
            Self::TryBranch | Self::FromResidualFromResidual => TRY_RESIDUAL,
            Self::PtrCast | Self::PtrCastConst => PTR_CAST,
            Self::CowToString | Self::DisplayToString => DISPLAY_COW,
            Self::LayoutDangling
            | Self::LayoutArray
            | Self::LayoutArrayInner
            | Self::LayoutNew
            | Self::LayoutFromSizeAlignUnchecked
            | Self::LayoutCalculateLayoutFor
            | Self::LayoutForValueRaw
            | Self::LayoutFromSizeAlign => LAYOUT_EXTRA,
            // NonNullCast has dual membership: NONNULL_EXTRA + POINTER_UTILITY
            Self::NonNullNew
            | Self::NonNullSliceFromRawParts
            | Self::NonNullAsNonNullPtr
            | Self::NonNullDangling
            | Self::NonNullAsMutPtr => NONNULL_EXTRA,
            Self::NonNullCast => NONNULL_EXTRA | POINTER_UTILITY,
            Self::AllocatorAllocate
            | Self::GlobalAllocImpl
            | Self::HandleAllocError
            | Self::RustNoAllocShimIsUnstable
            | Self::AlignmentNew
            | Self::AlignmentAsUsize
            | Self::LayoutMaxSizeForAlign
            | Self::BoxIntoRawWithAllocator
            | Self::UniqueNewUnchecked
            | Self::VecFromRawPartsIn => ALLOC_EXTRA,
            Self::BTreeSetNew
            | Self::BTreeSetInsert
            | Self::BTreeSetContains
            | Self::BTreeSetRemove
            | Self::BTreeSetLen
            | Self::BTreeSetIsEmpty
            | Self::BTreeSetClear
            | Self::BTreeSetClone
            | Self::BTreeSetIntoIter
            | Self::BTreeSetIter
            | Self::BTreeSetIterNext => BTREESET,
            Self::HashSetNew
            | Self::HashSetInsert
            | Self::HashSetContains
            | Self::HashSetRemove
            | Self::HashSetLen
            | Self::HashSetIsEmpty
            | Self::HashSetClear
            | Self::HashSetClone
            | Self::HashSetIntoIter
            | Self::HashSetIter
            | Self::HashSetIterNext => HASHSET,
            Self::BTreeMapEntry
            | Self::BTreeMapVacantInsert
            | Self::BTreeMapVacantInsertEntry
            | Self::BTreeMapOccupiedInsert
            | Self::BTreeMapOccupiedGetMut
            | Self::BTreeMapOccupiedIntoMut
            | Self::BTreeMapEntryOrInsert
            | Self::BTreeMapEntryOrInsertWith
            | Self::BTreeMapEntryOrInsertWithKey
            | Self::BTreeSearchTree
            | Self::BTreeNodeReborrow
            | Self::BTreeHandleIntoKv
            | Self::SetValZstDefault => BTREEMAP_INTERNAL,
            Self::PrimitivePartialEqEq
            | Self::PrimitivePartialEqNe
            | Self::PrimitivePartialOrdLt
            | Self::PrimitivePartialOrdLe
            | Self::PrimitivePartialOrdGt
            | Self::PrimitivePartialOrdGe
            | Self::OrdCmp
            | Self::OrdMin
            | Self::OrdMax
            | Self::OrdClamp => PRIMITIVE_CMP,
            Self::IterMap
            | Self::IterFilter
            | Self::IterFilterMap
            | Self::IterZip
            | Self::IterFold
            | Self::IterSum
            | Self::MapNext
            | Self::FilterNext
            | Self::FilterMapNext
            | Self::ZipNext
            | Self::RangeIntoIter
            | Self::RangeSpecNext
            | Self::IterFlatten
            | Self::IterCollect
            | Self::FlattenNext
            | Self::ChainNext
            | Self::IterSizeHint => ITERATOR_ADAPTER,
            // KaniMem variants: explicit-dispatch stubs get KANI_MEM only.
            // Part of #3531, #3470.
            Self::KaniMemIsPtrAligned
            | Self::KaniMemCanReadUnaligned
            | Self::KaniMemCanDereference
            | Self::KaniMemCanWrite
            | Self::KaniMemIsInbounds
            | Self::KaniMemSameAllocation => KANI_MEM,
            Self::KaniMemAssertIsInitialized => KANI_MEM | KANI_MEM_ASSUME_TRUE,
            Self::MemSizeOf | Self::MemAlignOf => MEM_INTRINSIC,
            Self::PtrAdd
            | Self::PtrSub
            | Self::PtrWrite
            | Self::PtrRead
            | Self::PtrWrappingAdd
            | Self::PtrWrappingSub
            | Self::PtrWrappingOffset
            | Self::PtrWrappingByteOffset
            | Self::PtrWrappingByteAdd
            | Self::PtrWrappingByteSub
            | Self::PtrWithMetadataOf => PTR_MEMORY,
            // NonNullCast handled above (dual membership)
            Self::NonNullAsPtr
            | Self::NonZeroGet
            | Self::PtrAddr
            | Self::PtrWithAddr
            | Self::WithoutProvenanceMut
            | Self::WithoutProvenance
            | Self::PtrNull
            | Self::PtrIsNull
            | Self::PtrIsNullRuntime
            | Self::MaybeUninitAsPtr
            | Self::CharFromU32Unchecked => POINTER_UTILITY,
            Self::BigRationalNew
            | Self::BigRationalFrom
            | Self::BigRationalAdd
            | Self::BigRationalSub
            | Self::BigRationalMul
            | Self::BigRationalDiv
            | Self::BigRationalNeg
            | Self::BigRationalEq
            | Self::BigRationalLt
            | Self::BigRationalLe
            | Self::BigRationalGt
            | Self::BigRationalGe
            | Self::BigRationalClone
            | Self::BigRationalAddAssign
            | Self::BigRationalSubAssign
            | Self::BigRationalMulAssign
            | Self::BigRationalDivAssign => BIG_RATIONAL,
            // Ungrouped — routed by dedicated detectors (bigint, hashmap, alloc)
            Self::BoxNew
            | Self::RustAlloc
            | Self::RustAllocZeroed
            | Self::RustDealloc
            | Self::RustRealloc
            | Self::LayoutSize
            | Self::LayoutAlign
            | Self::LayoutIsSizeAlignValid
            | Self::LayoutPaddingNeededFor
            | Self::BigIntFrom
            | Self::BigIntOne
            | Self::BigIntZero
            | Self::BigIntIsZero
            | Self::BigIntIsNegative
            | Self::BigIntAdd
            | Self::BigIntSub
            | Self::BigIntMul
            | Self::BigIntDiv
            | Self::BigIntRem
            | Self::BigIntNeg
            | Self::BigIntAbs
            | Self::BigIntMulAssign
            | Self::BigIntAddAssign
            | Self::BigIntSubAssign
            | Self::BigIntEq
            | Self::BigIntCmp
            | Self::BigIntPartialCmp
            | Self::BigIntLt
            | Self::BigIntLe
            | Self::BigIntGt
            | Self::BigIntGe
            | Self::BigIntClone
            | Self::BigIntShl
            | Self::BigIntShr
            | Self::BigIntShlAssign
            | Self::BigIntShrAssign
            | Self::BigIntBitAnd
            | Self::BigIntBitOr
            | Self::BigIntBitXor
            | Self::HashMapNew
            | Self::HashMapInsert
            | Self::HashMapGet
            | Self::HashMapGetMut
            | Self::HashMapContainsKey
            | Self::HashMapRemove
            | Self::HashMapLen
            | Self::HashMapIsEmpty
            | Self::HashMapClear
            | Self::HashMapClone
            | Self::HashMapDrop
            | Self::HashMapIntoIter
            | Self::HashMapIterNext
            | Self::HashMapIter
            | Self::HashMapKeys
            | Self::HashMapValues
            | Self::TrustMcMapNew
            | Self::TrustMcMapInsert
            | Self::TrustMcMapGet
            | Self::TrustMcMapContainsKey
            | Self::TrustMcMapRemove
            | Self::TrustMcMapLen
            | Self::TrustMcMapIsEmpty
            | Self::TrustMcMapClear
            | Self::TrustMcMapClone
            | Self::TrustMcMapIntoIter
            | Self::TrustMcMapIterNext
            | Self::VecIntoIter
            | Self::VecIter
            | Self::VecIterMut
            | Self::IntoIterNext
            | Self::CheckedAddUnsigned
            | Self::BTreeMapNew
            | Self::BTreeMapInsert
            | Self::BTreeMapGet
            | Self::BTreeMapGetMut
            | Self::BTreeMapContainsKey
            | Self::BTreeMapRemove
            | Self::BTreeMapLen
            | Self::BTreeMapIsEmpty
            | Self::BTreeMapClear
            | Self::BTreeMapClone
            | Self::VecExtendFromSlice
            | Self::RangeBoundsContains
            | Self::StringFromRawParts
            | Self::VecExtendRange
            | Self::VecInsert => 0,
        }
    }

    /// Check whether this stub belongs to the given group(s).
    /// Returns `true` if any bit in `group` is set in this stub's mask.
    pub(crate) const fn in_group(self, group: StubGroupMask) -> bool {
        self.group_mask() & group != 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn group_mask_matches_predicates() {
        // Slice
        assert!(StubKind::SlicePartialEqEqual.in_group(SLICE_STUB));
        assert!(!StubKind::SlicePartialEqEqual.in_group(VEC_CORE));
        // Option/Result predicates
        assert!(StubKind::OptionIsSome.in_group(OPTION_PREDICATE));
        assert!(StubKind::OptionIsSomeAnd.in_group(OPTION_PREDICATE));
        assert!(StubKind::OptionIsNone.in_group(OPTION_PREDICATE));
        assert!(!StubKind::OptionUnwrap.in_group(OPTION_PREDICATE));
        assert!(StubKind::ResultIsOk.in_group(RESULT_PREDICATE));
        assert!(!StubKind::ResultUnwrap.in_group(RESULT_PREDICATE));
        // Unwrap/expect
        assert!(StubKind::OptionUnwrap.in_group(UNWRAP_EXPECT));
        assert!(StubKind::OptionExpect.in_group(UNWRAP_EXPECT));
        assert!(StubKind::OptionUnwrapUnchecked.in_group(UNWRAP_EXPECT));
        assert!(StubKind::ResultUnwrap.in_group(UNWRAP_EXPECT));
        assert!(StubKind::ResultExpect.in_group(UNWRAP_EXPECT));
        assert!(StubKind::ResultUnwrapErr.in_group(UNWRAP_EXPECT));
        // Combinator
        assert!(StubKind::OptionAndThen.in_group(COMBINATOR));
        assert!(StubKind::ResultMapErr.in_group(COMBINATOR));
        // Collection predicates — VecIsEmpty has dual membership
        assert!(StubKind::VecIsEmpty.in_group(COLLECTION_PREDICATE));
        assert!(StubKind::VecIsEmpty.in_group(VEC_CORE));
        assert!(StubKind::StringIsEmpty.in_group(COLLECTION_PREDICATE));
        assert!(!StubKind::StringIsEmpty.in_group(STRING_CORE));
        // UB/panic — composite membership
        assert!(StubKind::UbCheckLanguageUb.in_group(UB_PANIC));
        assert!(StubKind::UbCheckLanguageUb.in_group(UB_CHECK_NOOP));
        assert!(!StubKind::UbCheckLanguageUb.in_group(UB_CHECK_ASSUME_TRUE));
        assert!(StubKind::UbCheckMaybeIsAligned.in_group(UB_PANIC));
        assert!(StubKind::UbCheckMaybeIsAligned.in_group(UB_CHECK_ASSUME_TRUE));
        assert!(StubKind::PanicError.in_group(UB_PANIC));
        assert!(StubKind::PanicError.in_group(PANIC_ERROR));
        assert!(StubKind::PanicUnreachable.in_group(PANIC_UNREACHABLE));
        // NonNullCast — dual membership (nonnull_extra + pointer_utility)
        assert!(StubKind::NonNullCast.in_group(NONNULL_EXTRA));
        assert!(StubKind::NonNullCast.in_group(POINTER_UTILITY));
        assert!(StubKind::NonNullCast.is_nonnull_extra());
        assert!(StubKind::NonNullCast.is_pointer_utility());
        // Kani mem — composite membership
        // Explicit-dispatch stubs: KANI_MEM only (Part of #3531, #3470)
        assert!(StubKind::KaniMemIsPtrAligned.in_group(KANI_MEM));
        assert!(!StubKind::KaniMemIsPtrAligned.in_group(KANI_MEM_ASSUME_TRUE));
        assert!(!StubKind::KaniMemIsPtrAligned.in_group(KANI_MEM_NOOP));
        assert!(StubKind::KaniMemCanReadUnaligned.in_group(KANI_MEM));
        assert!(!StubKind::KaniMemCanReadUnaligned.in_group(KANI_MEM_ASSUME_TRUE));
        assert!(StubKind::KaniMemCanDereference.in_group(KANI_MEM));
        assert!(!StubKind::KaniMemCanDereference.in_group(KANI_MEM_ASSUME_TRUE));
        // Assume-true stubs: KANI_MEM + KANI_MEM_ASSUME_TRUE
        assert!(StubKind::KaniMemAssertIsInitialized.in_group(KANI_MEM));
        assert!(StubKind::KaniMemAssertIsInitialized.in_group(KANI_MEM_ASSUME_TRUE));
        // Ungrouped variants return 0
        assert_eq!(StubKind::BigIntAdd.group_mask(), 0);
        assert_eq!(StubKind::HashMapNew.group_mask(), 0);
        assert_eq!(StubKind::BTreeMapNew.group_mask(), 0);
    }

    /// Verify that every `is_*` predicate agrees with `in_group`.
    #[test]
    fn predicates_consistent_with_groups() {
        type Check = (StubKind, StubGroupMask, fn(StubKind) -> bool);
        let checks: &[Check] = &[
            (StubKind::SliceIndexIndex, SLICE_STUB, StubKind::is_slice_stub),
            (StubKind::OptionIsSome, OPTION_PREDICATE, StubKind::is_option_predicate),
            (StubKind::OptionIsSomeAnd, OPTION_PREDICATE, StubKind::is_option_predicate),
            (StubKind::ResultIsOk, RESULT_PREDICATE, StubKind::is_result_predicate),
            (StubKind::PrimitiveClone, PRIMITIVE_CLONE, StubKind::is_primitive_clone),
            (StubKind::OptionUnwrapOr, UNWRAP_OR, StubKind::is_unwrap_or),
            (StubKind::OptionUnwrap, UNWRAP_EXPECT, StubKind::is_unwrap_expect),
            (StubKind::OptionUnwrapOrElse, UNWRAP_OR_ELSE, StubKind::is_unwrap_or_else),
            (StubKind::OptionAndThen, COMBINATOR, StubKind::is_combinator),
            (StubKind::VecIsEmpty, COLLECTION_PREDICATE, StubKind::is_collection_predicate),
            (StubKind::UbCheckLanguageUb, UB_PANIC, StubKind::is_ub_panic),
            (StubKind::FmtArgumentsNew, FMT, StubKind::is_fmt),
            (StubKind::VecNew, VEC_CORE, StubKind::is_vec_core),
            (StubKind::StringNew, STRING_CORE, StubKind::is_string_core),
            (StubKind::RawVecNewIn, RAWVEC, StubKind::is_rawvec),
            (StubKind::TryBranch, TRY_RESIDUAL, StubKind::is_try_residual),
            (StubKind::PtrCast, PTR_CAST, StubKind::is_ptr_cast),
            (StubKind::CowToString, DISPLAY_COW, StubKind::is_display_cow),
            (StubKind::LayoutNew, LAYOUT_EXTRA, StubKind::is_layout_extra),
            (StubKind::NonNullNew, NONNULL_EXTRA, StubKind::is_nonnull_extra),
            (StubKind::AllocatorAllocate, ALLOC_EXTRA, StubKind::is_alloc_extra),
            (StubKind::BTreeSetNew, BTREESET, StubKind::is_btreeset),
            (StubKind::HashSetNew, HASHSET, StubKind::is_hashset),
            (StubKind::BTreeMapEntry, BTREEMAP_INTERNAL, StubKind::is_btreemap_internal),
            (StubKind::PrimitivePartialEqEq, PRIMITIVE_CMP, StubKind::is_primitive_cmp),
            (StubKind::IterMap, ITERATOR_ADAPTER, StubKind::is_iterator_adapter),
            (StubKind::KaniMemIsPtrAligned, KANI_MEM, StubKind::is_kani_mem),
            (StubKind::KaniMemIsInbounds, KANI_MEM, StubKind::is_kani_mem),
            (
                StubKind::UbCheckMaybeIsAligned,
                UB_CHECK_ASSUME_TRUE,
                StubKind::is_ub_check_assume_true,
            ),
            (StubKind::UbCheckLanguageUb, UB_CHECK_NOOP, StubKind::is_ub_check_noop),
            (StubKind::PanicError, PANIC_ERROR, StubKind::is_panic_error),
            (StubKind::PanicUnreachable, PANIC_UNREACHABLE, StubKind::is_panic_unreachable),
            (StubKind::MemSizeOf, MEM_INTRINSIC, StubKind::is_mem_intrinsic),
            (StubKind::PtrAdd, PTR_MEMORY, StubKind::is_ptr_memory),
            (StubKind::NonNullAsPtr, POINTER_UTILITY, StubKind::is_pointer_utility),
            (StubKind::BigRationalNew, BIG_RATIONAL, StubKind::is_big_rational),
        ];
        for (variant, group, pred) in checks {
            assert!(variant.in_group(*group), "{variant:?} should be in group 0x{group:x}");
            assert!(pred(*variant), "{variant:?} should satisfy predicate");
        }
    }
}
