// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Intrinsic classification for memory initialization analysis.
//!
//! Determines which intrinsics can be safely skipped during uninit memory checking
//! (those with no memory initialization side effects).

use crate::intrinsics::Intrinsic;

/// Determines if the intrinsic has no memory initialization related function and hence can be
/// safely skipped.
pub(super) fn can_skip_intrinsic(intrinsic: &Intrinsic) -> bool {
    match intrinsic {
        Intrinsic::AddWithOverflow
        | Intrinsic::AlignOfVal
        | Intrinsic::ArithOffset
        | Intrinsic::AssertInhabited
        | Intrinsic::AssertMemUninitializedValid
        | Intrinsic::AssertZeroValid
        | Intrinsic::Assume
        | Intrinsic::Bitreverse
        | Intrinsic::BlackBox
        | Intrinsic::Breakpoint
        | Intrinsic::Bswap
        | Intrinsic::CeilF32
        | Intrinsic::CeilF64
        | Intrinsic::CopySignF32
        | Intrinsic::CopySignF64
        | Intrinsic::CosF32
        | Intrinsic::CosF64
        | Intrinsic::Ctlz
        | Intrinsic::CtlzNonZero
        | Intrinsic::Ctpop
        | Intrinsic::Cttz
        | Intrinsic::CttzNonZero
        | Intrinsic::DiscriminantValue
        | Intrinsic::ExactDiv
        | Intrinsic::Exp2F32
        | Intrinsic::Exp2F64
        | Intrinsic::ExpF32
        | Intrinsic::ExpF64
        | Intrinsic::FabsF32
        | Intrinsic::FabsF64
        | Intrinsic::FaddFast
        | Intrinsic::FdivFast
        | Intrinsic::FloorF32
        | Intrinsic::FloorF64
        | Intrinsic::FmafF32
        | Intrinsic::FmafF64
        | Intrinsic::FmulFast
        | Intrinsic::Forget
        | Intrinsic::FsubFast
        | Intrinsic::IsValStaticallyKnown
        | Intrinsic::Likely
        | Intrinsic::Log10F32
        | Intrinsic::Log10F64
        | Intrinsic::Log2F32
        | Intrinsic::Log2F64
        | Intrinsic::LogF32
        | Intrinsic::LogF64
        | Intrinsic::MaxNumF32
        | Intrinsic::MaxNumF64
        | Intrinsic::MinNumF32
        | Intrinsic::MinNumF64
        | Intrinsic::MulWithOverflow
        | Intrinsic::PowF32
        | Intrinsic::PowF64
        | Intrinsic::PowIF32
        | Intrinsic::PowIF64
        | Intrinsic::RawEq
        | Intrinsic::RotateLeft
        | Intrinsic::RotateRight
        | Intrinsic::RoundF32
        | Intrinsic::RoundF64
        | Intrinsic::SaturatingAdd
        | Intrinsic::SaturatingSub
        | Intrinsic::SinF32
        | Intrinsic::SinF64
        | Intrinsic::SqrtF32
        | Intrinsic::SqrtF64
        | Intrinsic::SubWithOverflow
        | Intrinsic::TruncF32
        | Intrinsic::TruncF64
        | Intrinsic::UncheckedDiv
        | Intrinsic::UncheckedRem
        | Intrinsic::Unlikely
        | Intrinsic::VtableSize
        | Intrinsic::VtableAlign
        | Intrinsic::WrappingAdd
        | Intrinsic::WrappingMul
        | Intrinsic::WrappingSub => {
            /* Intrinsics that do not interact with memory initialization. */
            true
        }
        Intrinsic::PtrGuaranteedCmp
        | Intrinsic::PtrOffsetFrom
        | Intrinsic::PtrOffsetFromUnsigned
        | Intrinsic::SizeOfVal => {
            /* AFAICS from the documentation, none of those require the pointer arguments to be actually initialized. */
            true
        }
        Intrinsic::SimdAdd
        | Intrinsic::SimdAnd
        | Intrinsic::SimdDiv
        | Intrinsic::SimdRem
        | Intrinsic::SimdEq
        | Intrinsic::SimdExtract
        | Intrinsic::SimdGe
        | Intrinsic::SimdGt
        | Intrinsic::SimdInsert
        | Intrinsic::SimdLe
        | Intrinsic::SimdLt
        | Intrinsic::SimdMul
        | Intrinsic::SimdNe
        | Intrinsic::SimdOr
        | Intrinsic::SimdShl
        | Intrinsic::SimdShr
        | Intrinsic::SimdShuffle(_)
        | Intrinsic::SimdSub
        | Intrinsic::SimdXor => {
            /* SIMD operations */
            true
        }
        Intrinsic::AtomicFence | Intrinsic::AtomicSingleThreadFence => {
            /* Atomic fences */
            true
        }
        // Intrinsics that interact with memory initialization — cannot skip.
        Intrinsic::AlignOf
        | Intrinsic::AtomicAnd
        | Intrinsic::AtomicCxchg
        | Intrinsic::AtomicCxchgWeak
        | Intrinsic::AtomicLoad
        | Intrinsic::AtomicMax
        | Intrinsic::AtomicMin
        | Intrinsic::AtomicNand
        | Intrinsic::AtomicOr
        | Intrinsic::AtomicStore
        | Intrinsic::AtomicUmax
        | Intrinsic::AtomicUmin
        | Intrinsic::AtomicXadd
        | Intrinsic::AtomicXchg
        | Intrinsic::AtomicXor
        | Intrinsic::AtomicXsub
        | Intrinsic::CompareBytes
        | Intrinsic::Copy
        | Intrinsic::FloatToIntUnchecked
        | Intrinsic::RetagBoxToRaw
        | Intrinsic::RoundTiesEvenF32
        | Intrinsic::RoundTiesEvenF64
        | Intrinsic::SimdBitmask
        | Intrinsic::SizeOf
        | Intrinsic::Transmute
        | Intrinsic::TypedSwap
        | Intrinsic::UnalignedVolatileLoad
        | Intrinsic::VolatileCopyMemory
        | Intrinsic::VolatileCopyNonOverlappingMemory
        | Intrinsic::VolatileLoad
        | Intrinsic::VolatileStore
        | Intrinsic::WriteBytes
        | Intrinsic::Unimplemented { .. } => {
            /* Memory-interacting or unimplemented intrinsics — cannot skip. */
            false
        }
    }
}
