// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for uninit_visitor module: intrinsic skip classification and deref removal.

use super::assign_analysis::try_remove_topmost_deref;
use super::intrinsic_skip::can_skip_intrinsic;
use crate::intrinsics::Intrinsic;
use rustc_public::mir::Local;
use rustc_public::mir::{Place, ProjectionElem};

// =========================================================================
// can_skip_intrinsic tests
//
// The function returns true for intrinsics that have no memory
// initialization side effects, and false for everything else.
// =========================================================================

#[test]
fn test_skip_arithmetic_overflow_intrinsics() {
    assert!(can_skip_intrinsic(&Intrinsic::AddWithOverflow));
    assert!(can_skip_intrinsic(&Intrinsic::SubWithOverflow));
    assert!(can_skip_intrinsic(&Intrinsic::MulWithOverflow));
}

#[test]
fn test_skip_bit_manipulation_intrinsics() {
    assert!(can_skip_intrinsic(&Intrinsic::Bitreverse));
    assert!(can_skip_intrinsic(&Intrinsic::Bswap));
    assert!(can_skip_intrinsic(&Intrinsic::Ctlz));
    assert!(can_skip_intrinsic(&Intrinsic::CtlzNonZero));
    assert!(can_skip_intrinsic(&Intrinsic::Ctpop));
    assert!(can_skip_intrinsic(&Intrinsic::Cttz));
    assert!(can_skip_intrinsic(&Intrinsic::CttzNonZero));
    assert!(can_skip_intrinsic(&Intrinsic::RotateLeft));
    assert!(can_skip_intrinsic(&Intrinsic::RotateRight));
}

#[test]
fn test_skip_float_intrinsics() {
    assert!(can_skip_intrinsic(&Intrinsic::CeilF32));
    assert!(can_skip_intrinsic(&Intrinsic::CeilF64));
    assert!(can_skip_intrinsic(&Intrinsic::FloorF32));
    assert!(can_skip_intrinsic(&Intrinsic::FloorF64));
    assert!(can_skip_intrinsic(&Intrinsic::SqrtF32));
    assert!(can_skip_intrinsic(&Intrinsic::SqrtF64));
    assert!(can_skip_intrinsic(&Intrinsic::SinF32));
    assert!(can_skip_intrinsic(&Intrinsic::CosF64));
    assert!(can_skip_intrinsic(&Intrinsic::ExpF32));
    assert!(can_skip_intrinsic(&Intrinsic::LogF64));
    assert!(can_skip_intrinsic(&Intrinsic::PowF32));
    assert!(can_skip_intrinsic(&Intrinsic::TruncF64));
    assert!(can_skip_intrinsic(&Intrinsic::RoundF32));
    assert!(can_skip_intrinsic(&Intrinsic::FabsF64));
    assert!(can_skip_intrinsic(&Intrinsic::CopySignF32));
    assert!(can_skip_intrinsic(&Intrinsic::FmafF64));
}

#[test]
fn test_skip_fast_math_intrinsics() {
    assert!(can_skip_intrinsic(&Intrinsic::FaddFast));
    assert!(can_skip_intrinsic(&Intrinsic::FsubFast));
    assert!(can_skip_intrinsic(&Intrinsic::FmulFast));
    assert!(can_skip_intrinsic(&Intrinsic::FdivFast));
}

#[test]
fn test_skip_wrapping_arithmetic() {
    assert!(can_skip_intrinsic(&Intrinsic::WrappingAdd));
    assert!(can_skip_intrinsic(&Intrinsic::WrappingMul));
    assert!(can_skip_intrinsic(&Intrinsic::WrappingSub));
    assert!(can_skip_intrinsic(&Intrinsic::SaturatingAdd));
    assert!(can_skip_intrinsic(&Intrinsic::SaturatingSub));
}

#[test]
fn test_skip_pointer_comparison_intrinsics() {
    assert!(can_skip_intrinsic(&Intrinsic::PtrGuaranteedCmp));
    assert!(can_skip_intrinsic(&Intrinsic::PtrOffsetFrom));
    assert!(can_skip_intrinsic(&Intrinsic::PtrOffsetFromUnsigned));
    assert!(can_skip_intrinsic(&Intrinsic::SizeOfVal));
}

#[test]
fn test_skip_simd_intrinsics() {
    assert!(can_skip_intrinsic(&Intrinsic::SimdAdd));
    assert!(can_skip_intrinsic(&Intrinsic::SimdAnd));
    assert!(can_skip_intrinsic(&Intrinsic::SimdEq));
    assert!(can_skip_intrinsic(&Intrinsic::SimdExtract));
    assert!(can_skip_intrinsic(&Intrinsic::SimdInsert));
    assert!(can_skip_intrinsic(&Intrinsic::SimdMul));
    assert!(can_skip_intrinsic(&Intrinsic::SimdShuffle("test".into())));
    assert!(can_skip_intrinsic(&Intrinsic::SimdXor));
}

#[test]
fn test_skip_atomic_fences() {
    assert!(can_skip_intrinsic(&Intrinsic::AtomicFence));
    assert!(can_skip_intrinsic(&Intrinsic::AtomicSingleThreadFence));
}

#[test]
fn test_skip_misc_safe_intrinsics() {
    assert!(can_skip_intrinsic(&Intrinsic::AlignOfVal));
    assert!(can_skip_intrinsic(&Intrinsic::Assume));
    assert!(can_skip_intrinsic(&Intrinsic::BlackBox));
    assert!(can_skip_intrinsic(&Intrinsic::Breakpoint));
    assert!(can_skip_intrinsic(&Intrinsic::DiscriminantValue));
    assert!(can_skip_intrinsic(&Intrinsic::ExactDiv));
    assert!(can_skip_intrinsic(&Intrinsic::Forget));
    assert!(can_skip_intrinsic(&Intrinsic::IsValStaticallyKnown));
    assert!(can_skip_intrinsic(&Intrinsic::Likely));
    assert!(can_skip_intrinsic(&Intrinsic::Unlikely));
    assert!(can_skip_intrinsic(&Intrinsic::RawEq));
    assert!(can_skip_intrinsic(&Intrinsic::UncheckedDiv));
    assert!(can_skip_intrinsic(&Intrinsic::UncheckedRem));
    assert!(can_skip_intrinsic(&Intrinsic::VtableSize));
    assert!(can_skip_intrinsic(&Intrinsic::VtableAlign));
    assert!(can_skip_intrinsic(&Intrinsic::AssertInhabited));
    assert!(can_skip_intrinsic(&Intrinsic::AssertMemUninitializedValid));
    assert!(can_skip_intrinsic(&Intrinsic::AssertZeroValid));
}

#[test]
fn test_no_skip_memory_intrinsics() {
    // These interact with memory initialization and must NOT be skipped.
    assert!(!can_skip_intrinsic(&Intrinsic::Copy));
    assert!(!can_skip_intrinsic(&Intrinsic::VolatileLoad));
    assert!(!can_skip_intrinsic(&Intrinsic::VolatileStore));
    assert!(!can_skip_intrinsic(&Intrinsic::VolatileCopyMemory));
    assert!(!can_skip_intrinsic(&Intrinsic::VolatileCopyNonOverlappingMemory));
    assert!(!can_skip_intrinsic(&Intrinsic::WriteBytes));
    assert!(!can_skip_intrinsic(&Intrinsic::Transmute));
    assert!(!can_skip_intrinsic(&Intrinsic::TypedSwap));
    assert!(!can_skip_intrinsic(&Intrinsic::UnalignedVolatileLoad));
    assert!(!can_skip_intrinsic(&Intrinsic::CompareBytes));
}

#[test]
fn test_no_skip_atomic_memory_intrinsics() {
    // Atomic load/store/RMW operations interact with memory.
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicLoad));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicStore));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicXchg));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicCxchg));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicCxchgWeak));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicXadd));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicXsub));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicAnd));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicOr));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicXor));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicNand));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicMax));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicMin));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicUmax));
    assert!(!can_skip_intrinsic(&Intrinsic::AtomicUmin));
}

#[test]
fn test_no_skip_unimplemented() {
    let op =
        Intrinsic::Unimplemented { name: "test".into(), issue_link: "http://example.com".into() };
    assert!(!can_skip_intrinsic(&op));
}

#[test]
fn test_no_skip_simd_bitmask() {
    // SimdBitmask is NOT in the skip list (it's not in the SIMD group).
    assert!(!can_skip_intrinsic(&Intrinsic::SimdBitmask));
}

// =========================================================================
// try_remove_topmost_deref tests
// =========================================================================

#[test]
fn test_remove_deref_from_single_deref() {
    let place = Place { local: 5usize.into(), projection: vec![ProjectionElem::Deref] };
    let result = try_remove_topmost_deref(&place);
    assert!(result.is_some());
    let stripped = result.expect("deref should be removed");
    assert_eq!(stripped.local, place.local);
    assert!(stripped.projection.is_empty());
}

#[test]
fn test_remove_deref_from_compound_projection() {
    // Use Deref+Deref to avoid Ty::bool_ty() which needs compiler TLV.
    let place = Place {
        local: 3usize.into(),
        projection: vec![ProjectionElem::Deref, ProjectionElem::Deref],
    };
    let result = try_remove_topmost_deref(&place);
    assert!(result.is_some());
    let stripped = result.expect("topmost deref should be removed");
    assert_eq!(stripped.projection.len(), 1);
}

#[test]
fn test_remove_deref_empty_projection() {
    let place = Place { local: 1usize.into(), projection: vec![] };
    assert!(try_remove_topmost_deref(&place).is_none());
}

#[test]
fn test_remove_deref_non_deref_last_projection() {
    // Index(Local) doesn't require compiler TLV, unlike Field which needs Ty.
    let place =
        Place { local: 2usize.into(), projection: vec![ProjectionElem::Index(0usize.into())] };
    assert!(try_remove_topmost_deref(&place).is_none());
}

#[test]
fn test_remove_deref_preserves_local() {
    let local: Local = 99usize.into();
    let place = Place { local, projection: vec![ProjectionElem::Deref] };
    let result = try_remove_topmost_deref(&place).expect("deref should be removed");
    assert_eq!(result.local, local);
}
