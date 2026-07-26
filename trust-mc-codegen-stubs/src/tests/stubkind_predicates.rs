// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// StubKind::is_*() categorization tests.
// These methods form the dispatch backbone for codegen — if a variant is in the
// wrong category, calls are silently misrouted.

use super::StubKind;

// =============================================================================
// StubKind::is_*() categorization tests (Part of proof_coverage)
//
// These methods form the dispatch backbone for codegen — if a variant is in the
// wrong category, calls are silently misrouted. Each test picks representative
// variants and confirms they match the expected category while non-members don't.
// =============================================================================

#[test]
fn stubkind_is_slice_stub() {
    assert!(StubKind::SlicePartialEqEqual.is_slice_stub());
    assert!(StubKind::SliceIndexIndex.is_slice_stub());
    assert!(StubKind::IndexIndex.is_slice_stub());
    assert!(!StubKind::VecNew.is_slice_stub());
    assert!(!StubKind::OptionIsSome.is_slice_stub());
}

#[test]
fn stubkind_is_option_predicate() {
    assert!(StubKind::OptionIsSome.is_option_predicate());
    assert!(StubKind::OptionIsSomeAnd.is_option_predicate());
    assert!(StubKind::OptionIsNone.is_option_predicate());
    assert!(!StubKind::OptionUnwrap.is_option_predicate());
    assert!(!StubKind::ResultIsOk.is_option_predicate());
}

#[test]
fn stubkind_is_result_predicate() {
    assert!(StubKind::ResultIsOk.is_result_predicate());
    assert!(StubKind::ResultIsErr.is_result_predicate());
    assert!(!StubKind::OptionIsSome.is_result_predicate());
    assert!(!StubKind::ResultUnwrap.is_result_predicate());
}

#[test]
fn stubkind_is_primitive_clone() {
    assert!(StubKind::PrimitiveClone.is_primitive_clone());
    assert!(!StubKind::VecClone.is_primitive_clone());
}

#[test]
fn stubkind_is_unwrap_or() {
    assert!(StubKind::OptionUnwrapOr.is_unwrap_or());
    assert!(StubKind::ResultUnwrapOr.is_unwrap_or());
    assert!(!StubKind::OptionUnwrap.is_unwrap_or());
    assert!(!StubKind::OptionUnwrapOrElse.is_unwrap_or());
}

#[test]
fn stubkind_is_unwrap_expect() {
    assert!(StubKind::OptionUnwrap.is_unwrap_expect());
    assert!(StubKind::OptionExpect.is_unwrap_expect());
    assert!(StubKind::OptionUnwrapUnchecked.is_unwrap_expect());
    assert!(StubKind::ResultUnwrap.is_unwrap_expect());
    assert!(StubKind::ResultExpect.is_unwrap_expect());
    assert!(!StubKind::OptionUnwrapOr.is_unwrap_expect());
    assert!(!StubKind::ResultUnwrapOrElse.is_unwrap_expect());
}

#[test]
fn stubkind_is_unwrap_or_else() {
    assert!(StubKind::OptionUnwrapOrElse.is_unwrap_or_else());
    assert!(StubKind::ResultUnwrapOrElse.is_unwrap_or_else());
    assert!(!StubKind::OptionUnwrapOr.is_unwrap_or_else());
}

#[test]
fn stubkind_is_combinator() {
    assert!(StubKind::OptionAndThen.is_combinator());
    assert!(StubKind::OptionOkOrElse.is_combinator());
    assert!(StubKind::OptionOkOr.is_combinator());
    assert!(StubKind::OptionMap.is_combinator());
    assert!(StubKind::ResultMap.is_combinator());
    assert!(StubKind::ResultAndThen.is_combinator());
    assert!(StubKind::ResultMapErr.is_combinator());
    assert!(StubKind::ResultOk.is_combinator());
    assert!(StubKind::ResultErr.is_combinator());
    assert!(!StubKind::OptionUnwrap.is_combinator());
    assert!(!StubKind::ResultUnwrap.is_combinator());
}

#[test]
fn stubkind_is_collection_predicate() {
    assert!(StubKind::VecIsEmpty.is_collection_predicate());
    assert!(StubKind::StringIsEmpty.is_collection_predicate());
    assert!(StubKind::VecContains.is_collection_predicate());
    assert!(StubKind::StringContains.is_collection_predicate());
    assert!(StubKind::StringStartsWith.is_collection_predicate());
    assert!(StubKind::StringEndsWith.is_collection_predicate());
    assert!(StubKind::StringIsAscii.is_collection_predicate());
    assert!(!StubKind::VecNew.is_collection_predicate());
    assert!(!StubKind::VecLen.is_collection_predicate());
}

#[test]
fn stubkind_is_ub_panic() {
    assert!(StubKind::UbCheckLanguageUb.is_ub_panic());
    assert!(StubKind::UbCheckMaybeIsAligned.is_ub_panic());
    assert!(StubKind::UbCheckMaybeIsNonoverlapping.is_ub_panic());
    assert!(StubKind::PreconditionCheck.is_ub_panic());
    assert!(StubKind::PanicUnreachable.is_ub_panic());
    assert!(StubKind::PanicError.is_ub_panic());
    assert!(!StubKind::VecNew.is_ub_panic());
}

#[test]
fn stubkind_is_fmt() {
    assert!(StubKind::FmtArgumentNewDisplay.is_fmt());
    assert!(StubKind::FmtArgumentsNew.is_fmt());
    assert!(StubKind::FmtArgumentsFromStr.is_fmt());
    assert!(StubKind::FmtFormat.is_fmt());
    assert!(!StubKind::PanicError.is_fmt());
}

#[test]
fn stubkind_is_vec_core() {
    assert!(StubKind::VecNew.is_vec_core());
    assert!(StubKind::VecPush.is_vec_core());
    assert!(StubKind::VecReserve.is_vec_core());
    assert!(StubKind::VecReserveExact.is_vec_core());
    assert!(StubKind::VecShrinkToFit.is_vec_core());
    assert!(StubKind::VecPop.is_vec_core());
    assert!(StubKind::VecLen.is_vec_core());
    assert!(StubKind::VecClone.is_vec_core());
    assert!(StubKind::VecDrop.is_vec_core());
    assert!(StubKind::VecAsSlice.is_vec_core());
    assert!(StubKind::VecIsEmpty.is_vec_core()); // dual membership: COLLECTION_PREDICATE + VEC_CORE
    assert!(!StubKind::VecContains.is_vec_core());
    assert!(!StubKind::StringNew.is_vec_core());
}

#[test]
fn stubkind_is_string_core() {
    assert!(StubKind::StringNew.is_string_core());
    assert!(StubKind::StringFrom.is_string_core());
    assert!(StubKind::StringLen.is_string_core());
    assert!(StubKind::StringPush.is_string_core());
    assert!(StubKind::StringClone.is_string_core());
    assert!(StubKind::StringEq.is_string_core());
    assert!(StubKind::StringAsStr.is_string_core());
    assert!(StubKind::StringIntoBoxedStr.is_string_core());
    assert!(StubKind::IntParse.is_string_core());
    assert!(StubKind::SplitWhitespace.is_string_core());
    assert!(StubKind::SplitWhitespaceNext.is_string_core());
    assert!(!StubKind::StringIsEmpty.is_string_core());
    assert!(!StubKind::VecNew.is_string_core());
}

#[test]
fn stubkind_is_rawvec() {
    assert!(StubKind::RawVecNewIn.is_rawvec());
    assert!(StubKind::RawVecCapacity.is_rawvec());
    assert!(StubKind::RawVecGrowOne.is_rawvec());
    assert!(StubKind::RawVecPtr.is_rawvec());
    assert!(StubKind::RawVecShrinkToFit.is_rawvec());
    assert!(!StubKind::VecNew.is_rawvec());
}

#[test]
fn stubkind_is_try_residual() {
    assert!(StubKind::TryBranch.is_try_residual());
    assert!(StubKind::FromResidualFromResidual.is_try_residual());
    assert!(!StubKind::ResultUnwrap.is_try_residual());
}

#[test]
fn stubkind_is_ptr_cast() {
    assert!(StubKind::PtrCast.is_ptr_cast());
    assert!(StubKind::PtrCastConst.is_ptr_cast());
    assert!(!StubKind::PtrAdd.is_ptr_cast());
}

#[test]
fn stubkind_is_display_cow() {
    assert!(StubKind::CowToString.is_display_cow());
    assert!(StubKind::DisplayToString.is_display_cow());
    assert!(!StubKind::StringFrom.is_display_cow());
}

#[test]
fn stubkind_is_layout_extra() {
    assert!(StubKind::LayoutDangling.is_layout_extra());
    assert!(StubKind::LayoutArray.is_layout_extra());
    assert!(StubKind::LayoutArrayInner.is_layout_extra());
    assert!(StubKind::LayoutNew.is_layout_extra());
    assert!(StubKind::LayoutFromSizeAlign.is_layout_extra());
    assert!(!StubKind::AllocatorAllocate.is_layout_extra());
}

#[test]
fn stubkind_is_nonnull_extra() {
    assert!(StubKind::NonNullNew.is_nonnull_extra());
    assert!(StubKind::NonNullSliceFromRawParts.is_nonnull_extra());
    assert!(StubKind::NonNullDangling.is_nonnull_extra());
    assert!(StubKind::NonNullCast.is_nonnull_extra());
    assert!(!StubKind::NonNullAsPtr.is_nonnull_extra());
}

#[test]
fn stubkind_is_alloc_extra() {
    assert!(StubKind::AllocatorAllocate.is_alloc_extra());
    assert!(StubKind::GlobalAllocImpl.is_alloc_extra());
    assert!(StubKind::HandleAllocError.is_alloc_extra());
    assert!(StubKind::UniqueNewUnchecked.is_alloc_extra());
    assert!(!StubKind::LayoutNew.is_alloc_extra());
}

#[test]
fn stubkind_is_btreeset() {
    assert!(StubKind::BTreeSetNew.is_btreeset());
    assert!(StubKind::BTreeSetInsert.is_btreeset());
    assert!(StubKind::BTreeSetContains.is_btreeset());
    assert!(StubKind::BTreeSetIterNext.is_btreeset());
    assert!(!StubKind::HashSetNew.is_btreeset());
}

#[test]
fn stubkind_is_hashset() {
    assert!(StubKind::HashSetNew.is_hashset());
    assert!(StubKind::HashSetInsert.is_hashset());
    assert!(StubKind::HashSetContains.is_hashset());
    assert!(StubKind::HashSetIterNext.is_hashset());
    assert!(!StubKind::BTreeSetNew.is_hashset());
}

#[test]
fn stubkind_is_btreemap_internal() {
    assert!(StubKind::BTreeMapEntry.is_btreemap_internal());
    assert!(StubKind::BTreeMapVacantInsert.is_btreemap_internal());
    assert!(StubKind::BTreeSearchTree.is_btreemap_internal());
    assert!(StubKind::SetValZstDefault.is_btreemap_internal());
    assert!(!StubKind::BTreeSetNew.is_btreemap_internal());
}

#[test]
fn stubkind_is_primitive_cmp() {
    assert!(StubKind::PrimitivePartialEqEq.is_primitive_cmp());
    assert!(StubKind::PrimitivePartialEqNe.is_primitive_cmp());
    assert!(StubKind::PrimitivePartialOrdLt.is_primitive_cmp());
    assert!(StubKind::OrdCmp.is_primitive_cmp());
    assert!(StubKind::OrdMin.is_primitive_cmp());
    assert!(StubKind::OrdMax.is_primitive_cmp());
    assert!(StubKind::OrdClamp.is_primitive_cmp());
    assert!(!StubKind::OptionIsSome.is_primitive_cmp());
}

#[test]
fn stubkind_is_iterator_adapter() {
    assert!(StubKind::IterMap.is_iterator_adapter());
    assert!(StubKind::IterFilter.is_iterator_adapter());
    assert!(StubKind::IterFilterMap.is_iterator_adapter());
    assert!(StubKind::IterZip.is_iterator_adapter());
    assert!(StubKind::IterFold.is_iterator_adapter());
    assert!(StubKind::IterSum.is_iterator_adapter());
    assert!(StubKind::MapNext.is_iterator_adapter());
    assert!(StubKind::FilterNext.is_iterator_adapter());
    assert!(StubKind::FilterMapNext.is_iterator_adapter());
    assert!(StubKind::ZipNext.is_iterator_adapter());
    assert!(StubKind::RangeSpecNext.is_iterator_adapter());
    assert!(StubKind::IterFlatten.is_iterator_adapter());
    assert!(StubKind::IterCollect.is_iterator_adapter());
    assert!(StubKind::FlattenNext.is_iterator_adapter());
    assert!(!StubKind::IntoIterNext.is_iterator_adapter());
}

#[test]
fn stubkind_is_kani_mem() {
    assert!(StubKind::KaniMemIsPtrAligned.is_kani_mem());
    assert!(StubKind::KaniMemIsInbounds.is_kani_mem());
    assert!(StubKind::KaniMemAssertIsInitialized.is_kani_mem());
    assert!(StubKind::KaniMemCanReadUnaligned.is_kani_mem());
    assert!(StubKind::KaniMemCanDereference.is_kani_mem());
    assert!(!StubKind::PtrRead.is_kani_mem());
}

#[test]
fn stubkind_is_kani_mem_assume_true() {
    assert!(StubKind::KaniMemAssertIsInitialized.is_kani_mem_assume_true());
    // KaniMemIsPtrAligned, KaniMemCanReadUnaligned, KaniMemCanDereference,
    // and KaniMemIsInbounds now have explicit dispatch branches and are no
    // longer in assume-true fallback handling (Part of #3531, #3470, #4249).
    assert!(!StubKind::KaniMemIsInbounds.is_kani_mem_assume_true());
    assert!(!StubKind::KaniMemIsPtrAligned.is_kani_mem_assume_true());
    assert!(!StubKind::KaniMemCanReadUnaligned.is_kani_mem_assume_true());
    assert!(!StubKind::KaniMemCanDereference.is_kani_mem_assume_true());
}

#[test]
fn stubkind_is_kani_mem_noop() {
    // All kani_mem stubs are now assume-true; noop returns false for all.
    assert!(!StubKind::KaniMemAssertIsInitialized.is_kani_mem_noop());
    assert!(!StubKind::KaniMemIsPtrAligned.is_kani_mem_noop());
}

#[test]
fn stubkind_is_ub_check_assume_true() {
    assert!(StubKind::UbCheckMaybeIsAligned.is_ub_check_assume_true());
    assert!(StubKind::UbCheckMaybeIsNonoverlapping.is_ub_check_assume_true());
    assert!(!StubKind::UbCheckLanguageUb.is_ub_check_assume_true());
}

#[test]
fn stubkind_is_ub_check_noop() {
    assert!(StubKind::UbCheckLanguageUb.is_ub_check_noop());
    assert!(StubKind::PreconditionCheck.is_ub_check_noop());
    assert!(StubKind::AssertInhabited.is_ub_check_noop());
    assert!(!StubKind::UbCheckMaybeIsAligned.is_ub_check_noop());
}

#[test]
fn stubkind_is_panic_error() {
    assert!(StubKind::PanicError.is_panic_error());
    assert!(!StubKind::PanicUnreachable.is_panic_error());
}

#[test]
fn stubkind_is_panic_unreachable() {
    assert!(StubKind::PanicUnreachable.is_panic_unreachable());
    assert!(!StubKind::PanicError.is_panic_unreachable());
}

#[test]
fn stubkind_is_mem_intrinsic() {
    assert!(StubKind::MemSizeOf.is_mem_intrinsic());
    assert!(StubKind::MemAlignOf.is_mem_intrinsic());
    assert!(!StubKind::PtrRead.is_mem_intrinsic());
}

#[test]
fn stubkind_is_ptr_memory() {
    assert!(StubKind::PtrAdd.is_ptr_memory());
    assert!(StubKind::PtrSub.is_ptr_memory());
    assert!(StubKind::PtrWrite.is_ptr_memory());
    assert!(StubKind::PtrRead.is_ptr_memory());
    assert!(StubKind::PtrWrappingAdd.is_ptr_memory());
    assert!(!StubKind::PtrCast.is_ptr_memory());
    assert!(!StubKind::NonNullAsPtr.is_ptr_memory());
}

#[test]
fn stubkind_is_pointer_utility() {
    assert!(StubKind::NonNullAsPtr.is_pointer_utility());
    assert!(StubKind::NonZeroGet.is_pointer_utility());
    assert!(StubKind::PtrAddr.is_pointer_utility());
    assert!(StubKind::PtrIsNull.is_pointer_utility());
    assert!(!StubKind::PtrAdd.is_pointer_utility());
    assert!(!StubKind::PtrRead.is_pointer_utility());
}

#[test]
fn stubkind_is_big_rational() {
    assert!(StubKind::BigRationalNew.is_big_rational());
    assert!(StubKind::BigRationalAdd.is_big_rational());
    assert!(StubKind::BigRationalEq.is_big_rational());
    assert!(StubKind::BigRationalClone.is_big_rational());
    assert!(!StubKind::VecNew.is_big_rational());
}
