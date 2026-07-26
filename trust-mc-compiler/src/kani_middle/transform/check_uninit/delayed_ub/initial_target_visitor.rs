// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! This module contains the visitor responsible for collecting initial analysis targets for delayed
//! UB instrumentation.

use crate::{
    intrinsics::Intrinsic,
    kani_middle::transform::check_uninit::ty_layout::tys_layout_equal_to_size,
};
use rustc_public::{
    mir::{
        Body, CastKind, LocalDecl, MirVisitor, NonDivergingIntrinsic, Operand, Place, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind,
        alloc::GlobalAlloc,
        mono::{Instance, InstanceKind, StaticDef},
        visit::Location,
    },
    ty::{ConstantKind, RigidTy, TyKind},
};

/// Pointer, write through which might trigger delayed UB.
pub(crate) enum AnalysisTarget {
    Place(Place),
    Static(StaticDef),
}

/// Visitor that finds initial analysis targets for delayed UB instrumentation. For our purposes,
/// analysis targets are *pointers* to places reading and writing from which should be tracked.
pub(crate) struct InitialTargetVisitor {
    body: Body,
    targets: Vec<AnalysisTarget>,
}

impl InitialTargetVisitor {
    pub(crate) fn new(body: Body) -> Self {
        Self { body, targets: vec![] }
    }

    pub(crate) fn into_targets(self) -> Vec<AnalysisTarget> {
        self.targets
    }

    pub(crate) fn push_operand(&mut self, operand: &Operand) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.targets.push(AnalysisTarget::Place(place.clone()));
            }
            Operand::Constant(constant) => {
                // Extract the static from the constant.
                if let ConstantKind::Allocated(allocation) = constant.const_.kind() {
                    for (_, prov) in &allocation.provenance.ptrs {
                        if let GlobalAlloc::Static(static_def) = GlobalAlloc::from(prov.0) {
                            self.targets.push(AnalysisTarget::Static(static_def));
                        }
                    }
                }
            }
        }
    }
}

/// We implement MirVisitor to facilitate target finding, we look for:
/// - pointer casts where pointees have different padding;
/// - calls to `copy`-like intrinsics.
impl MirVisitor for InitialTargetVisitor {
    fn visit_rvalue(&mut self, rvalue: &Rvalue, location: Location) {
        if let Rvalue::Cast(kind, operand, ty) = rvalue {
            let operand_ty = operand
                .ty(self.body.locals())
                .expect("operand should have valid type in body locals");
            match kind {
                CastKind::Transmute | CastKind::PtrToPtr => {
                    let operand_ty_kind = operand_ty.kind();
                    let from_ty = match operand_ty_kind
                        .rigid()
                        .expect("pointer cast operand should have rigid type")
                    {
                        RigidTy::RawPtr(ty, _) | RigidTy::Ref(_, ty, _) => Some(ty),
                        _ => None, // external enum: RigidTy
                    };
                    let ty_kind = ty.kind();
                    let to_ty = match ty_kind
                        .rigid()
                        .expect("pointer cast target should have rigid type")
                    {
                        RigidTy::RawPtr(ty, _) | RigidTy::Ref(_, ty, _) => Some(ty),
                        _ => None, // external enum: RigidTy
                    };
                    if let (Some(from_ty), Some(to_ty)) = (from_ty, to_ty)
                        && !tys_layout_equal_to_size(from_ty, to_ty)
                    {
                        self.push_operand(operand);
                    }
                }
                _ => {} // external enum: CastKind
            }
        }
        self.super_rvalue(rvalue, location);
    }

    fn visit_statement(&mut self, stmt: &Statement, location: Location) {
        if let StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(copy)) =
            &stmt.kind
        {
            self.push_operand(&copy.dst);
        }
        self.super_statement(stmt, location);
    }

    fn visit_terminator(&mut self, term: &Terminator, location: Location) {
        if let TerminatorKind::Call { func, args, .. } = &term.kind {
            let instance = try_resolve_instance(self.body.locals(), func)
                .expect("should resolve function instance for call terminator");
            if instance.kind == InstanceKind::Intrinsic {
                match Intrinsic::from_instance(&instance) {
                    Intrinsic::Copy => {
                        // Here, `dst` is the second argument.
                        self.push_operand(&args[1]);
                    }
                    Intrinsic::VolatileCopyMemory | Intrinsic::VolatileCopyNonOverlappingMemory => {
                        // Here, `dst` is the first argument.
                        self.push_operand(&args[0]);
                    }
                    // All other Intrinsic variants don't involve
                    // copy/write targets — no action needed. Explicit arms
                    // ensure the compiler catches new variants.
                    Intrinsic::AddWithOverflow
                    | Intrinsic::AlignOf
                    | Intrinsic::AlignOfVal
                    | Intrinsic::ArithOffset
                    | Intrinsic::AssertInhabited
                    | Intrinsic::AssertMemUninitializedValid
                    | Intrinsic::AssertZeroValid
                    | Intrinsic::Assume
                    | Intrinsic::AtomicAnd
                    | Intrinsic::AtomicCxchg
                    | Intrinsic::AtomicCxchgWeak
                    | Intrinsic::AtomicFence
                    | Intrinsic::AtomicLoad
                    | Intrinsic::AtomicMax
                    | Intrinsic::AtomicMin
                    | Intrinsic::AtomicNand
                    | Intrinsic::AtomicOr
                    | Intrinsic::AtomicSingleThreadFence
                    | Intrinsic::AtomicStore
                    | Intrinsic::AtomicUmax
                    | Intrinsic::AtomicUmin
                    | Intrinsic::AtomicXadd
                    | Intrinsic::AtomicXchg
                    | Intrinsic::AtomicXor
                    | Intrinsic::AtomicXsub
                    | Intrinsic::Bitreverse
                    | Intrinsic::BlackBox
                    | Intrinsic::Breakpoint
                    | Intrinsic::Bswap
                    | Intrinsic::CeilF32
                    | Intrinsic::CeilF64
                    | Intrinsic::CompareBytes
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
                    | Intrinsic::FloatToIntUnchecked
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
                    | Intrinsic::PtrGuaranteedCmp
                    | Intrinsic::PtrOffsetFrom
                    | Intrinsic::PtrOffsetFromUnsigned
                    | Intrinsic::RawEq
                    | Intrinsic::RetagBoxToRaw
                    | Intrinsic::RotateLeft
                    | Intrinsic::RotateRight
                    | Intrinsic::RoundF32
                    | Intrinsic::RoundF64
                    | Intrinsic::RoundTiesEvenF32
                    | Intrinsic::RoundTiesEvenF64
                    | Intrinsic::SaturatingAdd
                    | Intrinsic::SaturatingSub
                    | Intrinsic::SinF32
                    | Intrinsic::SinF64
                    | Intrinsic::SimdAdd
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
                    | Intrinsic::SimdXor
                    | Intrinsic::SimdBitmask
                    | Intrinsic::SizeOf
                    | Intrinsic::SizeOfVal
                    | Intrinsic::SqrtF32
                    | Intrinsic::SqrtF64
                    | Intrinsic::SubWithOverflow
                    | Intrinsic::Transmute
                    | Intrinsic::TruncF32
                    | Intrinsic::TruncF64
                    | Intrinsic::TypedSwap
                    | Intrinsic::UnalignedVolatileLoad
                    | Intrinsic::UncheckedDiv
                    | Intrinsic::UncheckedRem
                    | Intrinsic::Unlikely
                    | Intrinsic::VolatileLoad
                    | Intrinsic::VolatileStore
                    | Intrinsic::VtableSize
                    | Intrinsic::VtableAlign
                    | Intrinsic::WrappingAdd
                    | Intrinsic::WrappingMul
                    | Intrinsic::WrappingSub
                    | Intrinsic::WriteBytes
                    | Intrinsic::Unimplemented { .. } => {}
                }
            }
        }
        self.super_terminator(term, location);
    }
}

/// Try retrieving instance for the given function operand.
fn try_resolve_instance(locals: &[LocalDecl], func: &Operand) -> Result<Instance, String> {
    let ty = func.ty(locals).expect("function operand should have valid type in locals");
    match ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => {
            Ok(Instance::resolve(def, &args).expect("should resolve FnDef instance"))
        }
        _ => Err(format!(
            // external enum: TyKind
            "trust_mc was not able to resolve the instance of the function operand `{ty:?}`. Currently, memory initialization checks in presence of function pointers and vtable calls are not supported. For more information about planned support, see https://github.com/model-checking/kani/issues/3300."
        )),
    }
}
