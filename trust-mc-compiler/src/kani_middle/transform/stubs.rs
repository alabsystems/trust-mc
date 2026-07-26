// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! This module contains code related to the MIR-to-MIR pass that performs the
//! stubbing of functions and methods.
use crate::kani_middle::codegen_units::Stubs;
use crate::kani_middle::stubbing::validate_stub_const;
use crate::kani_middle::transform::body::{
    InsertPosition, MutMirVisitor, MutableBody, SourceInstruction,
};
use crate::kani_middle::transform::{TransformPass, TransformationType};
use crate::kani_queries::QueryDb;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::visit::{Location, MirVisitor};
use rustc_public::mir::{
    Body, ConstOperand, LocalDecl, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    Terminator, TerminatorKind, UnOp,
};
use rustc_public::rustc_internal;
use rustc_public::ty::{FnDef, GenericArgKind, GenericArgs, MirConst, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, CrateDefType};
use std::collections::HashMap;
use std::fmt::Debug;
use tracing::{debug, trace};

/// Replace the body of a function that is stubbed by the other.
///
/// This pass will replace the entire body, and it should only be applied to stubs
/// that have a body.
#[derive(Debug, Clone)]
pub(crate) struct FnStubPass {
    stubs: Stubs,
}

impl TransformPass for FnStubPass {
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        TransformationType::Stubbing
    }

    fn is_enabled(&self, query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        query_db.args().stubbing_enabled && !self.stubs.is_empty()
    }

    /// Transform the function body by replacing it with the stub body.
    fn transform(&mut self, tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        trace!(function=?instance.name(), "transform");
        let ty = instance.ty();
        if let TyKind::RigidTy(RigidTy::FnDef(fn_def, args)) = ty.kind()
            && let Some(replace) = self.stubs.get(&fn_def)
        {
            let new_instance =
                Instance::resolve(*replace, &args).expect("stub replacement should be resolvable");
            debug!(from=?instance.name(), to=?new_instance.name(), "FnStubPass::transform");
            if let Some(body) = FnStubValidator::validate(tcx, (fn_def, *replace), new_instance) {
                return (true, body);
            }
        }
        (false, body)
    }
}

impl FnStubPass {
    /// Build the pass with non-extern function stubs.
    pub(crate) fn new(all_stubs: &Stubs) -> FnStubPass {
        let stubs = all_stubs
            .iter()
            .filter_map(|(from, to)| (has_body(*from) && has_body(*to)).then_some((*from, *to)))
            .collect::<HashMap<_, _>>();
        FnStubPass { stubs }
    }
}

/// Replace the body of a function that is stubbed by the other.
///
/// This pass will replace the function call, since one of the functions do not have a body to
/// replace.
#[derive(Debug, Clone)]
pub(crate) struct ExternFnStubPass {
    stubs: Stubs,
}

impl TransformPass for ExternFnStubPass {
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        TransformationType::Stubbing
    }

    fn is_enabled(&self, query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        query_db.args().stubbing_enabled && !self.stubs.is_empty()
    }

    /// Search for calls to extern functions that should be stubbed.
    ///
    /// We need to find function calls and function pointers.
    /// We should replace this with a visitor once rustc_public includes a mutable one.
    fn transform(&mut self, _tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        trace!(function=?instance.name(), "transform");
        let mut new_body = MutableBody::from(body);
        let changed = false;
        let locals = new_body.locals().to_vec();
        let mut visitor = ExternFnStubVisitor { changed, locals, stubs: &self.stubs };
        visitor.visit_body(&mut new_body);
        (visitor.changed, new_body.into())
    }
}

impl ExternFnStubPass {
    /// Build the pass with the extern function stubs.
    ///
    /// This will cover any case where the stub doesn't have a body.
    pub(crate) fn new(all_stubs: &Stubs) -> ExternFnStubPass {
        let stubs = all_stubs
            .iter()
            .filter_map(|(from, to)| (!has_body(*from) || !has_body(*to)).then_some((*from, *to)))
            .collect::<HashMap<_, _>>();
        ExternFnStubPass { stubs }
    }
}

/// Reconstruct user stubs for methods that rustc lowered away before normal
/// call-site stubbing can see them.
///
/// The motivating case is `<[T]>::len`: rustc's `LowerSliceLenCalls` turns
/// calls into `Rvalue::Len(place)`, leaving no `TerminatorKind::Call` for
/// `FnStubPass` or `ExternFnStubPass` to rewrite. When the active harness has
/// `#[kani::stub(<[T]>::len, replacement)]`, insert a call to `replacement`
/// before the lowered `Len` assignment and turn the lowered assignment into a
/// no-op copy of the replacement result.
#[derive(Debug, Clone)]
pub(crate) struct LoweredMethodStubPass {
    slice_len_stubs: Vec<FnDef>,
}

impl TransformPass for LoweredMethodStubPass {
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        TransformationType::Stubbing
    }

    fn is_enabled(&self, query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        query_db.args().stubbing_enabled && !self.slice_len_stubs.is_empty()
    }

    fn transform(&mut self, _tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        trace!(function=?instance.name(), "LoweredMethodStubPass::transform");
        let mut new_body = MutableBody::from(body);
        let mut changed = false;
        let original_blocks = new_body.blocks().len();
        for bb_idx in (0..original_blocks).rev() {
            let stmt_count = new_body.blocks()[bb_idx].statements.len();
            for stmt_idx in (0..stmt_count).rev() {
                let Some(rewrite) = self.lowered_len_rewrite(&new_body, bb_idx, stmt_idx) else {
                    continue;
                };
                debug!(
                    bb_idx,
                    stmt_idx,
                    replacement = %rewrite.instance.name(),
                    "LoweredMethodStubPass: restoring user stub for lowered slice len"
                );
                let noop = StatementKind::Assign(
                    rewrite.destination.clone(),
                    Rvalue::Use(Operand::Copy(rewrite.destination.clone())),
                );
                new_body.replace_statement_kind(bb_idx, stmt_idx, noop);
                let mut source = SourceInstruction::Statement { bb: bb_idx, idx: stmt_idx };
                new_body.insert_call(
                    &rewrite.instance,
                    &mut source,
                    InsertPosition::Before,
                    vec![rewrite.receiver],
                    rewrite.destination,
                );
                changed = true;
            }
        }
        (changed, new_body.into())
    }
}

impl LoweredMethodStubPass {
    pub(crate) fn new(all_stubs: &Stubs) -> Self {
        let slice_len_stubs: Vec<FnDef> = all_stubs
            .iter()
            .filter_map(|(from, to)| is_slice_len_def(*from).then_some(*to))
            .collect();
        Self { slice_len_stubs }
    }

    fn lowered_len_rewrite(
        &self,
        body: &MutableBody,
        bb_idx: usize,
        stmt_idx: usize,
    ) -> Option<LenRewrite> {
        let stmt = &body.blocks()[bb_idx].statements[stmt_idx];
        let StatementKind::Assign(destination, rvalue) = &stmt.kind else {
            return None;
        };
        let (elem_ty, receiver) = match rvalue {
            Rvalue::Len(place) => (
                lowered_slice_len_elem_ty(place, body.locals())?,
                lowered_slice_len_receiver(place)?,
            ),
            Rvalue::UnaryOp(UnOp::PtrMetadata, operand) => (
                ptr_metadata_slice_len_elem_ty(operand, body.locals())?,
                copyable_receiver(operand)?,
            ),
            _ => return None,
        };
        let instance = self.resolve_slice_len_replacement(elem_ty)?;
        Some(LenRewrite { destination: destination.clone(), receiver, instance })
    }

    fn resolve_slice_len_replacement(&self, elem_ty: Ty) -> Option<Instance> {
        let typed_args = GenericArgs(vec![GenericArgKind::Type(elem_ty)]);
        let empty_args = GenericArgs(vec![]);
        self.slice_len_stubs.iter().find_map(|replacement| {
            Instance::resolve(*replacement, &typed_args)
                .or_else(|_| Instance::resolve(*replacement, &empty_args))
                .ok()
        })
    }
}

struct LenRewrite {
    destination: Place,
    receiver: Operand,
    instance: Instance,
}

fn is_slice_len_def(def: FnDef) -> bool {
    if !def.name().ends_with("::len") {
        return false;
    }
    let Some(fn_sig) = def.ty().kind().fn_sig() else {
        return false;
    };
    let sig = fn_sig.skip_binder();
    let Some(receiver) = sig.inputs().first() else {
        return false;
    };
    matches!(
        receiver.kind(),
        TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Slice(_)))
    )
}

fn lowered_slice_len_elem_ty(place: &Place, locals: &[LocalDecl]) -> Option<Ty> {
    let ty = place.ty(locals).ok()?;
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Slice(elem_ty)) => Some(elem_ty),
        _ => None,
    }
}

fn lowered_slice_len_receiver(place: &Place) -> Option<Operand> {
    if !matches!(place.projection.last(), Some(ProjectionElem::Deref)) {
        return None;
    }
    let mut receiver = place.clone();
    receiver.projection.pop();
    Some(Operand::Copy(receiver))
}

fn ptr_metadata_slice_len_elem_ty(operand: &Operand, locals: &[LocalDecl]) -> Option<Ty> {
    let receiver_ty = operand.ty(locals).ok()?;
    let TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) = receiver_ty.kind()
    else {
        return None;
    };
    match inner.kind() {
        TyKind::RigidTy(RigidTy::Slice(elem_ty)) => Some(elem_ty),
        _ => None,
    }
}

fn copyable_receiver(operand: &Operand) -> Option<Operand> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(Operand::Copy(place.clone())),
        Operand::Constant(_) => None,
    }
}

fn has_body(def: FnDef) -> bool {
    def.body().is_some()
}

/// Validate that the body of the stub is valid for the given instantiation
struct FnStubValidator<'a, 'tcx> {
    stub: (FnDef, FnDef),
    tcx: TyCtxt<'tcx>,
    locals: &'a [LocalDecl],
    is_valid: bool,
}

impl FnStubValidator<'_, '_> {
    fn validate(tcx: TyCtxt, stub: (FnDef, FnDef), new_instance: Instance) -> Option<Body> {
        if validate_stub_const(tcx, new_instance) {
            let body = new_instance.body().expect("stub instance should have body");
            let mut validator =
                FnStubValidator { stub, tcx, locals: body.locals(), is_valid: true };
            validator.visit_body(&body);
            validator.is_valid.then_some(body)
        } else {
            None
        }
    }
}

impl MirVisitor for FnStubValidator<'_, '_> {
    fn visit_operand(&mut self, op: &Operand, loc: Location) {
        let op_ty = op.ty(self.locals).expect("operand should have type");
        if let TyKind::RigidTy(RigidTy::FnDef(def, args)) = op_ty.kind()
            && Instance::resolve(def, &args).is_err()
        {
            self.is_valid = false;
            let callee = def.name();
            let receiver_ty = args.0[0].expect_ty();
            let sep = callee.rfind("::").expect("callee name should contain ::");
            let trait_ = &callee[..sep];
            self.tcx.dcx().span_err(
                rustc_internal::internal(self.tcx, loc.span()),
                format!(
                    "`{}` doesn't implement \
                                        `{}`. The function `{}` \
                                        cannot be stubbed by `{}` due to \
                                        generic bounds not being met. Callee: {}",
                    receiver_ty,
                    trait_,
                    self.stub.0.name(),
                    self.stub.1.name(),
                    callee,
                ),
            );
        }
    }
}

struct ExternFnStubVisitor<'a> {
    changed: bool,
    locals: Vec<LocalDecl>,
    stubs: &'a Stubs,
}

impl MutMirVisitor for ExternFnStubVisitor<'_> {
    fn visit_terminator(&mut self, term: &mut Terminator) {
        // Replace direct calls
        if let TerminatorKind::Call { func, .. } = &mut term.kind
            && let TyKind::RigidTy(RigidTy::FnDef(def, args)) =
                func.ty(&self.locals).expect("func should have type").kind()
            && let Some(new_def) = self.stubs.get(&def)
        {
            let instance =
                Instance::resolve(*new_def, &args).expect("stub replacement should be resolvable");
            let literal = MirConst::try_new_zero_sized(instance.ty())
                .expect("instance type should be zero-sized");
            let span = term.span;
            let new_func = ConstOperand { span, user_ty: None, const_: literal };
            *func = Operand::Constant(new_func);
            self.changed = true;
        }
        self.super_terminator(term);
    }

    fn visit_operand(&mut self, operand: &mut Operand) {
        let func_ty = operand.ty(&self.locals).expect("operand should have type");
        if let TyKind::RigidTy(RigidTy::FnDef(orig_def, args)) = func_ty.kind()
            && let Some(new_def) = self.stubs.get(&orig_def)
        {
            let Operand::Constant(ConstOperand { span, .. }) = operand else {
                unreachable!("operand with FnDef type must be Operand::Constant, got Copy/Move");
            };
            let instance = Instance::resolve_for_fn_ptr(*new_def, &args)
                .expect("stub replacement for fn ptr should be resolvable");
            let literal = MirConst::try_new_zero_sized(instance.ty())
                .expect("instance type should be zero-sized");
            let new_func = ConstOperand { span: *span, user_ty: None, const_: literal };
            *operand = Operand::Constant(new_func);
            self.changed = true;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fn_stub_pass_transformation_type_is_stubbing() {
        assert_eq!(FnStubPass::transformation_type(), TransformationType::Stubbing);
    }

    #[test]
    fn test_extern_fn_stub_pass_transformation_type_is_stubbing() {
        assert_eq!(ExternFnStubPass::transformation_type(), TransformationType::Stubbing);
    }

    #[test]
    fn test_fn_stub_pass_new_empty_stubs() {
        let empty: Stubs = HashMap::new();
        let pass = FnStubPass::new(&empty);
        assert!(pass.stubs.is_empty());
    }

    #[test]
    fn test_extern_fn_stub_pass_new_empty_stubs() {
        let empty: Stubs = HashMap::new();
        let pass = ExternFnStubPass::new(&empty);
        assert!(pass.stubs.is_empty());
    }

    #[test]
    fn test_fn_stub_pass_debug() {
        let empty: Stubs = HashMap::new();
        let pass = FnStubPass::new(&empty);
        let dbg = format!("{:?}", pass);
        assert!(dbg.contains("FnStubPass"));
    }

    #[test]
    fn test_extern_fn_stub_pass_debug() {
        let empty: Stubs = HashMap::new();
        let pass = ExternFnStubPass::new(&empty);
        let dbg = format!("{:?}", pass);
        assert!(dbg.contains("ExternFnStubPass"));
    }
}
