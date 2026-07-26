// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Table entries for statement stub dispatch routing.
//!
//! Keeping these lists out of `stub_dispatch.rs` prevents the dispatcher file
//! from regressing into oversized monolithic form while preserving table-driven
//! route selection.

use crate::codegen_ay::stubs::StubKind;

/// Collection BigInt stubs routed to `codegen_bigint_stub`.
pub(super) const BIGINT_STUBS: &[StubKind] = &[
    StubKind::BigIntFrom,
    StubKind::BigIntOne,
    StubKind::BigIntZero,
    StubKind::BigIntIsZero,
    StubKind::BigIntIsNegative,
    StubKind::BigIntAdd,
    StubKind::BigIntSub,
    StubKind::BigIntMul,
    StubKind::BigIntDiv,
    StubKind::BigIntRem,
    StubKind::BigIntNeg,
    StubKind::BigIntAbs,
    StubKind::BigIntMulAssign,
    StubKind::BigIntAddAssign,
    StubKind::BigIntSubAssign,
    StubKind::BigIntEq,
    StubKind::BigIntCmp,
    StubKind::BigIntPartialCmp,
    StubKind::BigIntLt,
    StubKind::BigIntLe,
    StubKind::BigIntGt,
    StubKind::BigIntGe,
    StubKind::BigIntClone,
    StubKind::BigIntShl,
    StubKind::BigIntShr,
    StubKind::BigIntShlAssign,
    StubKind::BigIntShrAssign,
    StubKind::BigIntBitAnd,
    StubKind::BigIntBitOr,
    StubKind::BigIntBitXor,
];

/// HashMap/BTreeMap family stubs routed to `codegen_hashmap_stub`.
pub(super) const HASHMAP_STUBS: &[StubKind] = &[
    StubKind::HashMapNew,
    StubKind::HashMapInsert,
    StubKind::HashMapGet,
    StubKind::HashMapGetMut,
    StubKind::HashMapContainsKey,
    StubKind::HashMapRemove,
    StubKind::HashMapLen,
    StubKind::HashMapIsEmpty,
    StubKind::HashMapClear,
    StubKind::HashMapClone,
    StubKind::HashMapDrop,
    StubKind::TrustMcMapNew,
    StubKind::TrustMcMapInsert,
    StubKind::TrustMcMapGet,
    StubKind::TrustMcMapContainsKey,
    StubKind::TrustMcMapRemove,
    StubKind::TrustMcMapLen,
    StubKind::TrustMcMapIsEmpty,
    StubKind::TrustMcMapClear,
    StubKind::TrustMcMapClone,
    StubKind::BTreeMapNew,
    StubKind::BTreeMapInsert,
    StubKind::BTreeMapGet,
    StubKind::BTreeMapGetMut,
    StubKind::BTreeMapContainsKey,
    StubKind::BTreeMapRemove,
    StubKind::BTreeMapLen,
    StubKind::BTreeMapIsEmpty,
    StubKind::BTreeMapClear,
    StubKind::BTreeMapClone,
    StubKind::HashMapIntoIter,
    StubKind::HashMapIter,
    StubKind::HashMapKeys,
    StubKind::HashMapValues,
    StubKind::TrustMcMapIntoIter,
];

/// Vec stubs routed to `codegen_vec_stub`.
pub(super) const VEC_STUBS: &[StubKind] = &[
    StubKind::VecNew,
    StubKind::VecWithCapacity,
    StubKind::VecPush,
    StubKind::VecInsert,
    StubKind::VecReserve,
    StubKind::VecReserveExact,
    StubKind::VecShrinkToFit,
    StubKind::VecPop,
    StubKind::VecRemove,
    StubKind::VecLen,
    StubKind::VecCapacity,
    StubKind::VecIsEmpty,
    StubKind::VecSetLen,
    StubKind::VecClear,
    StubKind::VecTruncate,
    StubKind::VecClone,
    StubKind::VecDrop,
    StubKind::VecContains,
    StubKind::VecEq,
    StubKind::VecAsSlice,
    StubKind::VecAsPtr,
    StubKind::VecAsMutPtr,
    StubKind::VecIntoIter,
    StubKind::VecIter,
    StubKind::VecIterMut,
    StubKind::VecFromElem,        // Part of #3494: BMC parity with CHC encoding
    StubKind::VecResize,          // Part of #3494: BMC parity with CHC encoding
    StubKind::VecExtendFromSlice, // Part of #3494: BMC parity with CHC encoding
    StubKind::SliceIntoVec,       // Part of #3494: BMC parity with CHC encoding
    StubKind::VecFromSlice,       // Part of #3673: BMC parity with CHC encoding
    StubKind::VecSplice,          // Part of #4202: Vec::splice stub
];

/// Iterator stubs routed to `codegen_iter_stub`.
pub(super) const ITER_STUBS: &[StubKind] = &[
    StubKind::IntoIterNext,
    StubKind::IterFlatten,
    StubKind::IterCollect,
    StubKind::FlattenNext,
    StubKind::HashMapIterNext,
    StubKind::TrustMcMapIterNext,
    StubKind::BTreeSetIterNext,
    StubKind::HashSetIterNext,
    StubKind::IterMap,
    StubKind::IterFilter,
    StubKind::IterFold,
    StubKind::IterSum,
    StubKind::MapNext,
    StubKind::FilterNext,
    StubKind::RangeSpecNext,
    StubKind::IterSizeHint,  // Part of #3477: BMC parity with CHC encoding
    StubKind::RangeIntoIter, // Part of #3477: Range::into_iter() identity
    StubKind::IterZip,       // Part of #3532: BMC parity with CHC encoding
    StubKind::ZipNext,       // Part of #3532: BMC parity with CHC encoding
    StubKind::IterFilterMap, // Part of #3692: BMC parity with CHC encoding
    StubKind::FilterMapNext, // Part of #3692: BMC parity with CHC encoding
    StubKind::ChainNext,     // Part of #4160: BMC parity with CHC encoding
];

/// String/display formatting stubs routed to `codegen_string_stub`.
pub(super) const STRING_STUBS: &[StubKind] = &[
    StubKind::StringNew,
    StubKind::StringFrom,
    StubKind::StringLen,
    StubKind::StringIsEmpty,
    StubKind::StringPush,
    StubKind::StringPushStr,
    StubKind::StringClear,
    StubKind::StringClone,
    StubKind::StringTruncate,
    StubKind::StringFromUtf8Lossy,
    StubKind::StrFromUtf8, // Part of #3672: BMC parity with CHC encoding
    StubKind::IntParse,    // Part of #3676: BMC parity with CHC encoding
    StubKind::StringEq,
    StubKind::StringContains,
    StubKind::StringStartsWith,
    StubKind::StringEndsWith,
    StubKind::StringIsAscii,
    StubKind::StringAsStr,
    StubKind::StringIntoBoxedStr,
    StubKind::CowToString,
    StubKind::DisplayToString,
    StubKind::FmtFormat,
];

/// BTreeSet stubs routed to `codegen_btreeset_stub`.
pub(super) const BTREESET_STUBS: &[StubKind] = &[
    StubKind::BTreeSetNew,
    StubKind::BTreeSetInsert,
    StubKind::BTreeSetContains,
    StubKind::BTreeSetRemove,
    StubKind::BTreeSetLen,
    StubKind::BTreeSetIsEmpty,
    StubKind::BTreeSetClear,
    StubKind::BTreeSetClone,
    StubKind::BTreeSetIntoIter,
    StubKind::BTreeSetIter,
];

/// HashSet stubs routed to `codegen_hashset_stub`.
pub(super) const HASHSET_STUBS: &[StubKind] = &[
    StubKind::HashSetNew,
    StubKind::HashSetInsert,
    StubKind::HashSetContains,
    StubKind::HashSetRemove,
    StubKind::HashSetLen,
    StubKind::HashSetIsEmpty,
    StubKind::HashSetClear,
    StubKind::HashSetClone,
    StubKind::HashSetIntoIter,
    StubKind::HashSetIter,
];

/// BTreeMap internals routed to `codegen_btreemap_internal_stub`.
pub(super) const BTREEMAP_INTERNAL_STUBS: &[StubKind] = &[
    StubKind::BTreeMapEntry,
    StubKind::BTreeMapVacantInsert,
    StubKind::BTreeMapVacantInsertEntry,
    StubKind::BTreeMapOccupiedInsert,
    StubKind::BTreeMapOccupiedGetMut,
    StubKind::BTreeMapOccupiedIntoMut,
    StubKind::BTreeMapEntryOrInsert,
    StubKind::BTreeMapEntryOrInsertWith,
    StubKind::BTreeMapEntryOrInsertWithKey,
    StubKind::BTreeSearchTree,
    StubKind::BTreeNodeReborrow,
    StubKind::BTreeHandleIntoKv,
];

/// Pointer/memory helper stubs routed to `try_codegen_pointer_memory_stub`.
pub(super) const POINTER_MEMORY_STUBS: &[StubKind] = &[
    StubKind::NonNullDangling,
    StubKind::NonNullAsMutPtr,
    StubKind::BoxIntoRawWithAllocator,
    StubKind::UniqueNewUnchecked,
    StubKind::VecFromRawPartsIn,
    StubKind::RawVecNewIn,
    StubKind::RawVecCapacity,
    StubKind::RawVecGrowOne,
    StubKind::RawVecPtr,
    StubKind::RawVecFromNonNullIn,
    StubKind::RawVecDrop,
    StubKind::RawVecShrinkToFit,
    StubKind::CheckedAddUnsigned,
    StubKind::SliceAsPtr,
    StubKind::SliceAsMutPtr,
];

/// Option/Result stubs routed to `try_codegen_option_result_stub`.
pub(super) const OPTION_RESULT_STUBS: &[StubKind] = &[
    StubKind::OptionUnwrapUnchecked,
    StubKind::ResultIsOk,
    StubKind::ResultIsErr,
    StubKind::OptionIsSome,
    StubKind::OptionIsSomeAnd,
    StubKind::OptionIsNone,
    StubKind::OptionUnwrapOr,
    StubKind::ResultUnwrapOr,
    StubKind::OptionExpect,
    StubKind::ResultUnwrap,
    StubKind::ResultExpect,
    StubKind::OptionUnwrapOrElse,
    StubKind::ResultUnwrapOrElse,
    StubKind::OptionAndThen,
    StubKind::OptionMap,
    StubKind::OptionOkOrElse,
    StubKind::ResultMap,
    StubKind::ResultAndThen,
    StubKind::ResultMapErr,
    StubKind::ResultOk,
    StubKind::ResultErr,
    StubKind::OptionCopied,
];

/// Variants expected to be handled before this dispatcher.
pub(super) const PREHANDLED_STUBS: &[StubKind] = &[
    StubKind::AlignmentNew,
    StubKind::AssertInhabited, // Part of #3477: handled via noop intrinsic dispatch (noop.rs)
    StubKind::AlignmentAsUsize,
    StubKind::BigRationalAdd,
    StubKind::BigRationalAddAssign,
    StubKind::BigRationalClone,
    StubKind::BigRationalDiv,
    StubKind::BigRationalDivAssign,
    StubKind::BigRationalEq,
    StubKind::BigRationalFrom,
    StubKind::BigRationalGe,
    StubKind::BigRationalGt,
    StubKind::BigRationalLe,
    StubKind::BigRationalLt,
    StubKind::BigRationalMul,
    StubKind::BigRationalMulAssign,
    StubKind::BigRationalNeg,
    StubKind::BigRationalNew,
    StubKind::BigRationalSub,
    StubKind::BigRationalSubAssign,
    StubKind::FmtArgumentNewDisplay,
    StubKind::FmtArgumentsFromStr,
    StubKind::FmtArgumentsNew,
    StubKind::FromResidualFromResidual,
    StubKind::HandleAllocError,
    StubKind::KaniMemAssertIsInitialized,
    StubKind::KaniMemCanReadUnaligned,
    StubKind::KaniMemCanDereference,
    StubKind::KaniMemCanWrite,
    StubKind::KaniMemIsInbounds,
    StubKind::KaniMemIsPtrAligned,
    StubKind::KaniMemSameAllocation,
    // MemSizeOf / MemAlignOf: moved to try_codegen_alloc_layout_stub (Part of #3141)
    StubKind::NonNullAsPtr,
    StubKind::NonZeroGet,
    StubKind::PanicError,
    StubKind::PanicUnreachable,
    StubKind::PreconditionCheck,
    StubKind::PtrAddr,
    StubKind::PtrCast,
    StubKind::PtrCastConst,
    StubKind::PtrIsNull,
    StubKind::PtrIsNullRuntime,
    StubKind::RustNoAllocShimIsUnstable,
    StubKind::SetValZstDefault,
    StubKind::UbCheckLanguageUb,
    StubKind::UbCheckMaybeIsAligned,
    StubKind::UbCheckMaybeIsNonoverlapping,
    StubKind::WithoutProvenance,
    StubKind::WithoutProvenanceMut,
];

pub(super) fn stub_in(table: &[StubKind], stub: StubKind) -> bool {
    table.contains(&stub)
}
