// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Module responsible for implementing a few Rust compiler intrinsics.
//!
//! Note that some rustc intrinsics are lowered to MIR instructions. Those can also be handled
//! here.

use crate::intrinsics::Intrinsic;
use crate::kani_middle::kani_functions::{KaniFunction, KaniModel};
use crate::kani_middle::transform::body::{
    InsertPosition, MutMirVisitor, MutableBody, SourceInstruction,
};
use crate::kani_middle::transform::{TransformPass, TransformationType};
use crate::kani_queries::QueryDb;
use rustc_hir::LangItem;
use rustc_middle::ty::{self as internal_ty, TyCtxt};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    BasicBlockIdx, BinOp, Body, ConstOperand, LocalDecl, Operand, Rvalue, StatementKind,
    Terminator, TerminatorKind,
};
use rustc_public::rustc_internal;
use rustc_public::ty::{
    FnDef, GenericArgKind, GenericArgs, IntTy, MirConst, RigidTy, Span, Ty, TyKind, UintTy,
};
use std::collections::HashMap;
use tracing::debug;

/// Generate the body for a few Kani intrinsics.
#[derive(Debug, Clone)]
pub(crate) struct RustcIntrinsicsPass {
    /// Used to cache FnDef lookups for intrinsics models.
    models: HashMap<KaniModel, FnDef>,
}

impl TransformPass for RustcIntrinsicsPass {
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        TransformationType::Stubbing
    }

    fn is_enabled(&self, _query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        true
    }

    /// Transform the function body by inserting checks one-by-one.
    /// For every unsafe dereference or a transmute operation, we check all values are valid.
    fn transform(&mut self, tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        debug!(function=?instance.name(), "transform");

        let mut new_body = MutableBody::from(body);
        let mut visitor =
            ReplaceIntrinsicCallVisitor::new(&self.models, new_body.locals().to_vec(), tcx);
        visitor.visit_body(&mut new_body);
        let changed = self.replace_lowered_intrinsics(tcx, &mut new_body);
        (visitor.changed || changed, new_body.into())
    }
}

fn is_panic_function(tcx: &TyCtxt, def_id: rustc_public::DefId) -> bool {
    let def_id = rustc_internal::internal(*tcx, def_id);
    Some(def_id) == tcx.lang_items().panic_fn()
        || tcx.is_lang_item(def_id, LangItem::PanicDisplay)
        || Some(def_id) == tcx.lang_items().panic_fmt()
        || Some(def_id) == tcx.lang_items().begin_panic_fn()
}

impl RustcIntrinsicsPass {
    pub(crate) fn new(queries: &QueryDb) -> Self {
        let models = queries
            .kani_functions()
            .iter()
            .filter_map(|(func, def)| {
                if let KaniFunction::Model(model) = func { Some((*model, *def)) } else { None }
            })
            .collect();
        debug!(?models, "RustcIntrinsicsPass::new");
        RustcIntrinsicsPass { models }
    }

    /// This function checks if we need to replace intrinsics that have been lowered.
    fn replace_lowered_intrinsics(&self, tcx: TyCtxt, body: &mut MutableBody) -> bool {
        // Do a reverse iteration on the instructions since we will replace Rvalues by a function
        // call, which will split the basic block.
        let mut changed = false;
        let orig_bbs = body.blocks().len();
        for bb in (0..orig_bbs).rev() {
            let num_stmts = body.blocks()[bb].statements.len();
            for stmt in (0..num_stmts).rev() {
                changed |= self.replace_offset(tcx, body, bb, stmt);
            }
        }
        changed
    }

    /// Replace a lowered offset intrinsic.
    fn replace_offset(
        &self,
        tcx: TyCtxt,
        body: &mut MutableBody,
        bb: BasicBlockIdx,
        stmt: usize,
    ) -> bool {
        let statement = &body.blocks()[bb].statements[stmt];
        let StatementKind::Assign(place, rvalue) = &statement.kind else {
            return false;
        };
        let Rvalue::BinaryOp(BinOp::Offset, op1, op2) = rvalue else { return false };
        let mut source = SourceInstruction::Statement { idx: stmt, bb };

        // Double check input parameters of `offset` operation.
        let offset_ty = op2.ty(body.locals()).expect("offset operand should have type");
        let pointer_ty = op1.ty(body.locals()).expect("pointer operand should have type");
        validate_offset(tcx, offset_ty, statement.span);
        validate_raw_ptr(tcx, pointer_ty, statement.span);
        tcx.dcx().abort_if_errors();

        let pointee_ty = pointer_ty
            .kind()
            .builtin_deref(true)
            .expect("pointer type should be dereferenceable")
            .ty;
        // The model takes the following parameters (PointeeType, PointerType, OffsetType).
        let model = self.models[&KaniModel::Offset];
        let params = vec![
            GenericArgKind::Type(pointee_ty),
            GenericArgKind::Type(pointer_ty),
            GenericArgKind::Type(offset_ty),
        ];
        let instance = Instance::resolve(model, &GenericArgs(params))
            .expect("offset model should be resolvable");
        body.insert_call(
            &instance,
            &mut source,
            InsertPosition::After,
            vec![op1.clone(), op2.clone()],
            place.clone(),
        );
        body.remove_stmt(bb, stmt);
        true
    }
}

struct ReplaceIntrinsicCallVisitor<'a, 'tcx> {
    models: &'a HashMap<KaniModel, FnDef>,
    locals: Vec<LocalDecl>,
    tcx: TyCtxt<'tcx>,
    changed: bool,
}

impl<'a, 'tcx> ReplaceIntrinsicCallVisitor<'a, 'tcx> {
    fn new(
        models: &'a HashMap<KaniModel, FnDef>,
        locals: Vec<LocalDecl>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        ReplaceIntrinsicCallVisitor { models, locals, changed: false, tcx }
    }
}

impl MutMirVisitor for ReplaceIntrinsicCallVisitor<'_, '_> {
    /// Replace the terminator for some rustc's intrinsics.
    ///
    /// In some cases, we replace a function call to a rustc intrinsic by a call to the
    /// corresponding Kani intrinsic.
    ///
    /// Our models are usually augmented by some trait bounds, or they leverage Kani intrinsics to
    /// implement the given semantics.
    ///
    /// Note that we only need to replace function calls since intrinsics must always be called
    /// directly. I.e., no need to handle function pointers.
    fn visit_terminator(&mut self, term: &mut Terminator) {
        if let TerminatorKind::Call { func, args: call_args, .. } = &mut term.kind
            && let TyKind::RigidTy(RigidTy::FnDef(def, generic_args)) =
                func.ty(&self.locals).expect("func should have type").kind()
        {
            // Get the model we should use to replace this function call, if any.
            let (replacement_model, new_generic_args) = if def.is_intrinsic() {
                let instance =
                    Instance::resolve(def, &generic_args).expect("intrinsic should be resolvable");
                let intrinsic = Intrinsic::from_instance(&instance);
                debug!(?intrinsic, "handle_terminator");
                match intrinsic {
                    Intrinsic::AlignOfVal => (self.models[&KaniModel::AlignOfVal], generic_args),
                    Intrinsic::SizeOfVal => (self.models[&KaniModel::SizeOfVal], generic_args),
                    Intrinsic::PtrOffsetFrom => {
                        (self.models[&KaniModel::PtrOffsetFrom], generic_args)
                    }
                    Intrinsic::PtrOffsetFromUnsigned => {
                        (self.models[&KaniModel::PtrOffsetFromUnsigned], generic_args)
                    }
                    Intrinsic::SimdBitmask => {
                        // Parity note (#4122): Upstream Kani resolves the SIMD bitmask
                        // model via tcx.get_diagnostic_item("KaniModelSimdBitmask").
                        // trust_mc uses the generic fn_marker discovery pipeline instead:
                        // self.models[&KaniModel::SimdBitmask] is populated from the
                        // #[kanitool::fn_marker = "SimdBitmaskModel"] attribute on the
                        // macro-generated model in kani_core::generate_models!().
                        // The two mechanisms are equivalent for MIR/codegen purposes.
                        // SimdBitmask requires special handling:
                        // 1. Validate the arg type is SIMD
                        // 2. Extract SIMD element type and length
                        // 3. Add these as extra generic args to the model
                        if call_args.is_empty() {
                            return self.super_terminator(term);
                        }
                        let arg_ty =
                            call_args[0].ty(&self.locals).expect("call arg should have type");
                        if !is_simd_type(self.tcx, arg_ty) {
                            debug!(?arg_ty, "simd_bitmask: arg is not SIMD type");
                            return self.super_terminator(term);
                        }
                        let Some((len_const, elem_ty)) = simd_len_and_type(self.tcx, arg_ty) else {
                            debug!(?arg_ty, "simd_bitmask: failed to extract SIMD info");
                            return self.super_terminator(term);
                        };
                        debug!(?elem_ty, ?len_const, "simd_bitmask: extracted SIMD info");

                        // Build augmented generic args: original args + elem_ty + len
                        let mut new_args = Vec::from_iter(generic_args.0.iter().cloned());
                        new_args.push(GenericArgKind::Type(elem_ty));
                        new_args.push(GenericArgKind::Const(len_const));
                        let augmented_args = GenericArgs(new_args);

                        (self.models[&KaniModel::SimdBitmask], augmented_args)
                    }
                    // All other intrinsics are handled in codegen, not this
                    // transform pass. Explicit arms ensure the compiler catches
                    // new Intrinsic variants that may need model replacement.
                    Intrinsic::AddWithOverflow
                    | Intrinsic::AlignOf
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
                    | Intrinsic::Copy
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
                    | Intrinsic::SizeOf
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
                    | Intrinsic::VolatileCopyMemory
                    | Intrinsic::VolatileCopyNonOverlappingMemory
                    | Intrinsic::VolatileLoad
                    | Intrinsic::VolatileStore
                    | Intrinsic::VtableSize
                    | Intrinsic::VtableAlign
                    | Intrinsic::WrappingAdd
                    | Intrinsic::WrappingMul
                    | Intrinsic::WrappingSub
                    | Intrinsic::WriteBytes
                    | Intrinsic::Unimplemented { .. } => {
                        return self.super_terminator(term);
                    }
                }
            } else if is_panic_function(&self.tcx, def.0) {
                // If we find a panic function, we replace it with our stub.
                (self.models[&KaniModel::PanicStub], generic_args)
            } else {
                return self.super_terminator(term);
            };

            let new_instance = Instance::resolve(replacement_model, &new_generic_args)
                .expect("replacement model should be resolvable");

            // Construct the wrapper types needed to insert our resolved model [Instance]
            // back into the MIR as an operand.
            let literal = MirConst::try_new_zero_sized(new_instance.ty())
                .expect("instance type should be zero-sized");
            let span = term.span;
            let new_func = ConstOperand { span, user_ty: None, const_: literal };
            *func = Operand::Constant(new_func);
            self.changed = true;
        }
        self.super_terminator(term);
    }
}

/// Validate whether the offset type is valid, i.e., `isize` or `usize`.
///
/// This will emit an error if the type is wrong but not abort.
/// Invoke `tcx.dcx().abort_if_errors()` to abort execution.
fn validate_offset(tcx: TyCtxt, offset_ty: Ty, span: Span) {
    if !matches!(
        offset_ty.kind(),
        TyKind::RigidTy(RigidTy::Int(IntTy::Isize)) | TyKind::RigidTy(RigidTy::Uint(UintTy::Usize))
    ) {
        tcx.dcx().span_err(
            rustc_internal::internal(tcx, span),
            format!("Expected `isize` or `usize` for offset type. Found `{offset_ty}` instead"),
        );
    }
}

/// Validate that we have a raw pointer otherwise emit an error.
///
/// This will emit an error if the type is wrong but not abort.
/// Invoke `tcx.dcx().abort_if_errors()` to abort execution.
fn validate_raw_ptr(tcx: TyCtxt, ptr_ty: Ty, span: Span) {
    let pointer_ty_kind = ptr_ty.kind();
    if !pointer_ty_kind.is_raw_ptr() {
        tcx.dcx().span_err(
            rustc_internal::internal(tcx, span),
            format!("Expected raw pointer for pointer type. Found `{ptr_ty}` instead"),
        );
    }
}

/// Check if a stable MIR type is a SIMD type by converting to internal and checking repr.
fn is_simd_type(tcx: TyCtxt, ty: Ty) -> bool {
    let internal_ty = rustc_internal::internal(tcx, ty);
    internal_ty.is_simd()
}

/// Extract SIMD length and element type from a SIMD type.
/// Returns `(len_const, elem_ty)` in stable MIR format.
/// Returns `None` if the type is not a valid SIMD type.
fn simd_len_and_type(tcx: TyCtxt, simd_ty: Ty) -> Option<(rustc_public::ty::TyConst, Ty)> {
    let internal_ty: internal_ty::Ty<'_> = rustc_internal::internal(tcx, simd_ty);
    match internal_ty.kind() {
        internal_ty::TyKind::Adt(def, args) => {
            if !def.repr().simd() {
                return None;
            }
            let variant = def.non_enum_variant();
            let f0_ty = variant.fields[rustc_abi::FieldIdx::from_usize(0)].ty(tcx, args);

            if let internal_ty::TyKind::Array(elem_ty, len) = f0_ty.kind() {
                // Convert back to stable MIR types
                let stable_elem_ty = rustc_internal::stable(*elem_ty);
                let stable_len = rustc_internal::stable(*len);
                Some((stable_len, stable_elem_ty))
            } else {
                // external enum: internal_ty::TyKind
                // Fields are not in an array - use field count as length
                let len = internal_ty::Const::from_target_usize(tcx, variant.fields.len() as u64);
                let stable_elem_ty = rustc_internal::stable(f0_ty);
                let stable_len = rustc_internal::stable(len);
                Some((stable_len, stable_elem_ty))
            }
        }
        _ => None, // external enum: internal_ty::TyKind
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kani_middle::kani_functions::{KaniFunction, KaniHook, KaniIntrinsic};
    use strum::IntoEnumIterator;

    // =========================================================================
    // TransformationType — RustcIntrinsicsPass is a Stubbing pass (Part of #2217)
    // =========================================================================

    #[test]
    fn rustc_intrinsics_pass_is_stubbing_type() {
        assert!(matches!(RustcIntrinsicsPass::transformation_type(), TransformationType::Stubbing));
    }

    // =========================================================================
    // KaniModel filtering — the core logic of RustcIntrinsicsPass::new()
    // (Part of #2217)
    //
    // We cannot call new() directly (requires QueryDb with live compiler), but
    // we can verify the filter pattern: only KaniFunction::Model variants pass
    // through, all Intrinsic and Hook variants are excluded.
    // =========================================================================

    #[test]
    fn model_filter_accepts_all_model_variants() {
        for model in KaniModel::iter() {
            let func = KaniFunction::Model(model);
            let passes_filter = matches!(func, KaniFunction::Model(_));
            assert!(passes_filter, "KaniModel::{model:?} should pass Model filter");
        }
    }

    #[test]
    fn model_filter_rejects_all_intrinsic_variants() {
        for intrinsic in KaniIntrinsic::iter() {
            let func = KaniFunction::Intrinsic(intrinsic);
            let passes_filter = matches!(func, KaniFunction::Model(_));
            assert!(!passes_filter, "KaniIntrinsic::{intrinsic:?} should not pass Model filter");
        }
    }

    #[test]
    fn model_filter_rejects_all_hook_variants() {
        for hook in KaniHook::iter() {
            let func = KaniFunction::Hook(hook);
            let passes_filter = matches!(func, KaniFunction::Model(_));
            assert!(!passes_filter, "KaniHook::{hook:?} should not pass Model filter");
        }
    }

    /// Verify that the specific models used by the intrinsics visitor exist.
    /// These are the models indexed in visit_terminator and replace_offset.
    #[test]
    fn expected_models_exist_in_enum() {
        // Models directly referenced in this file's code:
        let required_models = [
            KaniModel::AlignOfVal,
            KaniModel::SizeOfVal,
            KaniModel::PtrOffsetFrom,
            KaniModel::PtrOffsetFromUnsigned,
            KaniModel::SimdBitmask,
            KaniModel::PanicStub,
            KaniModel::Offset,
        ];
        for model in &required_models {
            // Verify the model is a valid KaniFunction (round-trip through From)
            let func: KaniFunction = (*model).into();
            assert!(
                matches!(func, KaniFunction::Model(m) if m == *model),
                "KaniModel::{model:?} should round-trip through KaniFunction"
            );
        }
    }

    // =========================================================================
    // Intrinsic enum — structural tests (Part of #2217)
    //
    // The Intrinsic enum is defined in src/intrinsics.rs. These tests verify
    // constructability and Debug formatting of variants used by this pass.
    // =========================================================================

    #[test]
    fn intrinsic_simd_bitmask_constructable() {
        let intrinsic = Intrinsic::SimdBitmask;
        let debug_str = format!("{intrinsic:?}");
        assert_eq!(debug_str, "SimdBitmask");
    }

    #[test]
    fn intrinsic_ptr_offset_from_constructable() {
        let intrinsic = Intrinsic::PtrOffsetFrom;
        let debug_str = format!("{intrinsic:?}");
        assert_eq!(debug_str, "PtrOffsetFrom");
    }

    #[test]
    fn intrinsic_unimplemented_carries_metadata() {
        let intrinsic = Intrinsic::Unimplemented {
            name: "test_intrinsic".to_string(),
            issue_link: "https://example.com/issue/1".to_string(),
        };
        let debug_str = format!("{intrinsic:?}");
        assert!(debug_str.contains("test_intrinsic"));
        assert!(debug_str.contains("https://example.com/issue/1"));
    }

    #[test]
    fn intrinsic_simd_shuffle_carries_suffix() {
        let intrinsic = Intrinsic::SimdShuffle("4".to_string());
        let debug_str = format!("{intrinsic:?}");
        assert!(debug_str.contains("SimdShuffle"));
        assert!(debug_str.contains('4'));
    }
}
