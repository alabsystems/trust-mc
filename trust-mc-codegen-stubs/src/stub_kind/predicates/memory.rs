// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::StubKind;

impl StubKind {
    pub const fn is_try_residual(self) -> bool {
        matches!(self, Self::TryBranch | Self::FromResidualFromResidual)
    }

    pub const fn is_ptr_cast(self) -> bool {
        matches!(self, Self::PtrCast | Self::PtrCastConst)
    }

    pub const fn is_layout_extra(self) -> bool {
        matches!(
            self,
            Self::LayoutDangling
                | Self::LayoutArray
                | Self::LayoutArrayInner
                | Self::LayoutNew
                | Self::LayoutFromSizeAlignUnchecked
                | Self::LayoutCalculateLayoutFor
                | Self::LayoutForValueRaw
                | Self::LayoutFromSizeAlign
        )
    }

    pub const fn is_nonnull_extra(self) -> bool {
        matches!(
            self,
            Self::NonNullNew
                | Self::NonNullSliceFromRawParts
                | Self::NonNullAsNonNullPtr
                | Self::NonNullDangling
                | Self::NonNullAsMutPtr
                | Self::NonNullCast
        )
    }

    /// Part of #4249: Returns true for stubs that produce pointers with
    /// concrete obj_ids assigned by the allocation codegen. These are
    /// allocation entry points where the CHC heap model assigns a fresh
    /// obj_id, so the returned pointer is fully constrained.
    pub const fn is_known_alloc_producer(self) -> bool {
        matches!(
            self,
            Self::RustAlloc
                | Self::RustAllocZeroed
                | Self::RustRealloc
                | Self::BoxNew
                | Self::AllocatorAllocate
        )
    }

    pub const fn is_alloc_extra(self) -> bool {
        matches!(
            self,
            Self::AllocatorAllocate
                | Self::GlobalAllocImpl
                | Self::HandleAllocError
                | Self::RustNoAllocShimIsUnstable
                | Self::AlignmentNew
                | Self::AlignmentAsUsize
                | Self::LayoutMaxSizeForAlign
                | Self::BoxIntoRawWithAllocator
                | Self::UniqueNewUnchecked
                | Self::VecFromRawPartsIn
        )
    }

    pub const fn is_kani_mem(self) -> bool {
        matches!(
            self,
            Self::KaniMemIsPtrAligned
                | Self::KaniMemIsInbounds
                | Self::KaniMemAssertIsInitialized
                | Self::KaniMemCanReadUnaligned
                | Self::KaniMemCanDereference
                | Self::KaniMemCanWrite
                | Self::KaniMemSameAllocation
        )
    }

    pub const fn is_kani_mem_assume_true(self) -> bool {
        matches!(self, Self::KaniMemAssertIsInitialized)
    }

    /// No kani_mem stubs currently use noop semantics.
    /// Retained for partition exhaustiveness checking.
    pub const fn is_kani_mem_noop(self) -> bool {
        false
    }

    /// RangeBounds::contains — over-approximate as true (Part of #3470).
    /// Sound: assumes value is in range; relaxes constraints.
    pub const fn is_range_bounds_contains(self) -> bool {
        matches!(self, Self::RangeBoundsContains)
    }

    pub const fn is_ub_check_assume_true(self) -> bool {
        matches!(self, Self::UbCheckMaybeIsAligned | Self::UbCheckMaybeIsNonoverlapping)
    }

    pub const fn is_ub_check_noop(self) -> bool {
        matches!(self, Self::UbCheckLanguageUb | Self::PreconditionCheck | Self::AssertInhabited)
    }

    pub const fn is_panic_error(self) -> bool {
        matches!(self, Self::PanicError)
    }

    pub const fn is_panic_unreachable(self) -> bool {
        matches!(self, Self::PanicUnreachable)
    }

    pub const fn is_mem_intrinsic(self) -> bool {
        matches!(self, Self::MemSizeOf | Self::MemAlignOf)
    }

    pub const fn is_ptr_memory(self) -> bool {
        matches!(
            self,
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
                | Self::PtrWithMetadataOf
        )
    }

    pub const fn is_pointer_utility(self) -> bool {
        matches!(
            self,
            Self::NonNullAsPtr
                | Self::NonZeroGet
                | Self::PtrAddr
                | Self::PtrWithAddr
                | Self::WithoutProvenanceMut
                | Self::WithoutProvenance
                | Self::PtrNull
                | Self::PtrIsNull
                | Self::PtrIsNullRuntime
                | Self::NonNullCast
                | Self::MaybeUninitAsPtr
                | Self::CharFromU32Unchecked
                | Self::SliceAsPtr
                | Self::SliceAsMutPtr
        )
    }
}
