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

/// Rewrite every CALL SITE of a stubbed function into a call of its stub
/// (`#[kani::stub(f, g)]`: `f(x)` becomes `g(x)`), and every `f` fn-item
/// operand into `g`.
///
/// Kani's own pass did this only for the pairs `FnStubPass` cannot serve (the
/// original or the stub has no body) and left every other call site naming
/// `f`, whose BODY `FnStubPass` replaces. That is the same program only for a
/// consumer that runs `f`'s transformed body. trust-mc's encoders do not
/// always: both lanes model standard-library functions by the path the call
/// site names (`Option::unwrap`, `u8::wrapping_add`, `mem::forget`, the
/// known-call and no-op tables, ...) and never fetch the body. So
/// `#[kani::stub(u8::wrapping_add, stub)]` with a panicking stub proved clean,
/// and a stub that makes `unwrap` total left a certified Genuine
/// counterexample on `None` (`tools/soundness-duals/stub_modelled_std_dual.rs`).
/// Rewriting the call site makes every path-keyed handler see the stub, a
/// function none of them claims, which is then inlined or walked as the
/// unit's own code. `FnStubPass` still replaces the original's body, for the
/// calls no call site names (a virtual call, drop glue).
///
/// A call resolves through the stub map in two steps
/// ([`stubbed_callee_instance`]): the callee `def` itself, then the instance a
/// trait-method call resolves to (`Clone::clone` on `Foo` runs
/// `<Foo as Clone>::clone`, which the unit may stub).
///
/// The CHC walker fetches most callee bodies RAW, outside this pipeline; it
/// applies the same rewrite through `CalleeBody::callee_body`
/// ([`crate::kani_middle::transform::stub_aware_instance_body`]).
#[derive(Debug, Clone)]
pub(crate) struct CallSiteStubPass {
    stubs: Stubs,
}

impl TransformPass for CallSiteStubPass {
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

    /// Search for calls to stubbed functions and fn-item operands naming them.
    fn transform(&mut self, _tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        trace!(function=?instance.name(), "transform");
        rewrite_stubbed_call_sites(body, &self.stubs)
    }
}

impl CallSiteStubPass {
    /// Build the pass with every stub of the unit.
    pub(crate) fn new(all_stubs: &Stubs) -> CallSiteStubPass {
        CallSiteStubPass { stubs: all_stubs.clone() }
    }
}

/// [`CallSiteStubPass`] on one body, outside the pipeline: returns whether a
/// call site or operand was rewritten, and the body.
pub(crate) fn rewrite_stubbed_call_sites(body: Body, stubs: &Stubs) -> (bool, Body) {
    if stubs.is_empty() {
        return (false, body);
    }
    let mut new_body = MutableBody::from(body);
    let locals = new_body.locals().to_vec();
    let mut visitor = CallSiteStubVisitor { changed: false, locals, stubs };
    visitor.visit_body(&mut new_body);
    (visitor.changed, new_body.into())
}

/// The instance a call of `def` with `args` runs when the unit stubs it: the
/// stub's, resolved at the stubbed function's own generic arguments. The call
/// is resolved first and the stub map is consulted for the function the call
/// RUNS, exactly as `FnStubPass` keys on the resolved instance: a
/// trait-method call that resolves to a stubbed impl item is stubbed, and a
/// trait default method the unit stubs (`#[kani::stub(Tr::m, s)]`) is not
/// applied to an impl that overrides it. `def` itself is consulted only when
/// the call does not resolve (a polymorphic body). `None` when nothing is
/// stubbed (or the stub does not resolve, which the stub validation reports
/// as a compile error). `for_fn_ptr` resolves for a reified fn-item operand.
pub(crate) fn stubbed_callee_instance(
    stubs: &Stubs,
    def: FnDef,
    args: &GenericArgs,
    for_fn_ptr: bool,
) -> Option<Instance> {
    let resolve = |def: FnDef, args: &GenericArgs| {
        if for_fn_ptr { Instance::resolve_for_fn_ptr(def, args) } else { Instance::resolve(def, args) }
    };
    let (orig, stub_instance) = match resolve(def, args) {
        Ok(instance) => {
            let TyKind::RigidTy(RigidTy::FnDef(resolved, resolved_args)) = instance.ty().kind()
            else {
                return None;
            };
            let new_def = stubs.get(&resolved)?;
            (resolved, resolve(*new_def, &resolved_args).ok()?)
        }
        Err(_) => (def, resolve(*stubs.get(&def)?, args).ok()?),
    };
    stub_instance_is_valid(orig, stub_instance).then_some(stub_instance)
}

thread_local! {
    /// [`stub_instance_is_valid`]'s answers, one per stub instance, so each
    /// invalid stub is reported once.
    static STUB_INSTANCE_VALIDITY: std::cell::RefCell<HashMap<Instance, bool>> =
        std::cell::RefCell::new(HashMap::new());
}

/// Does the stub instance `stub_instance`, replacing `orig`, pass Kani's stub
/// validation (`FnStubValidator`: its constants evaluate at these generic
/// arguments and every call in it resolves)? `FnStubPass` replaces a body
/// only with a valid stub and reports an invalid one as a compile error; a
/// call site is rewritten, and a raw fetch applies the stub, on the same
/// terms. Fetching an invalid stub's body ICEs in `rustc_public`'s body
/// builder (`tests/expected/issue-2589/issue_2589.rs`: `stub::<String>`
/// with an unmet `T: Dummy` bound evaluating `T::TRUE`). A stub without a
/// body (an extern replacement) is not validated, as Kani's
/// `ExternFnStubPass` never did. Runs in the compiler's implicit context,
/// where every pipeline pass and codegen fetch runs.
fn stub_instance_is_valid(orig: FnDef, stub_instance: Instance) -> bool {
    if !stub_instance.has_body() {
        return true;
    }
    if let Some(known) = STUB_INSTANCE_VALIDITY.with(|cache| cache.borrow().get(&stub_instance).copied())
    {
        return known;
    }
    let TyKind::RigidTy(RigidTy::FnDef(stub_def, _)) = stub_instance.ty().kind() else {
        return false;
    };
    let valid = rustc_middle::ty::tls::with(|tcx| {
        FnStubValidator::validate(tcx, (orig, stub_def), stub_instance).is_some()
    });
    STUB_INSTANCE_VALIDITY.with(|cache| cache.borrow_mut().insert(stub_instance, valid));
    valid
}

/// `instance`'s MIR as a unit stubbing `unit_stubs` runs it
/// (`kani_middle::transform::stub_aware_instance_body`): the stub's body for a
/// stubbed instance (`FnStubPass`), with every call site and lowered method
/// the unit stubs rewritten ([`apply_call_site_stubs`]). The raw body when
/// `unit_stubs` is `None`.
pub(crate) fn unit_instance_body(unit_stubs: Option<&Stubs>, instance: &Instance) -> Option<Body> {
    let Some(unit_stubs) = unit_stubs else {
        return instance.body();
    };
    let body = match stub_replacement_instance(unit_stubs, instance) {
        // The renamed-float-intrinsic rule of `CalleeBody` holds for the stub too.
        Some(stub_instance) if crate::intrinsics::is_modelled_renamed_intrinsic(&stub_instance) => {
            return None;
        }
        Some(stub_instance) => stub_instance.body()?,
        None => instance.body()?,
    };
    Some(apply_call_site_stubs(unit_stubs, body))
}

/// [`unit_instance_body`] for a polymorphic def.
pub(crate) fn unit_def_body(unit_stubs: Option<&Stubs>, def: &FnDef) -> Option<Body> {
    let Some(unit_stubs) = unit_stubs else {
        return def.body();
    };
    let body = match unit_stubs.get(def) {
        Some(stub_def) => stub_def.body()?,
        None => def.body()?,
    };
    Some(apply_call_site_stubs(unit_stubs, body))
}

/// `CallSiteStubPass` and `LoweredMethodStubPass` on one body.
pub(crate) fn apply_call_site_stubs(unit_stubs: &Stubs, body: Body) -> Body {
    let (_, body) = rewrite_stubbed_call_sites(body, unit_stubs);
    let (_, body) = LoweredMethodStubPass::new(unit_stubs).rewrite(body);
    body
}

/// The stub instance `FnStubPass` gives `instance` the body of: `Some` when
/// the unit stubs the function `instance` is an item of.
pub(crate) fn stub_replacement_instance(stubs: &Stubs, instance: &Instance) -> Option<Instance> {
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = instance.ty().kind() else {
        return None;
    };
    let new_def = stubs.get(&def)?;
    let stub_instance = Instance::resolve(*new_def, &args).ok()?;
    stub_instance_is_valid(def, stub_instance).then_some(stub_instance)
}

/// Reconstruct user stubs for methods that rustc lowered away before normal
/// call-site stubbing can see them.
///
/// The motivating case is `<[T]>::len`: rustc's `LowerSliceLenCalls` turns
/// calls into `Rvalue::Len(place)`, leaving no `TerminatorKind::Call` for
/// `FnStubPass` or `CallSiteStubPass` to rewrite. When the active harness has
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
        self.rewrite(body)
    }
}

impl LoweredMethodStubPass {
    /// The pass on one body, outside the pipeline (the CHC walker's raw
    /// fetches, `stub_aware_instance_body`).
    pub(crate) fn rewrite(&self, body: Body) -> (bool, Body) {
        if self.slice_len_stubs.is_empty() {
            return (false, body);
        }
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
                    rvalue_use!(Rvalue::Use(Operand::Copy(rewrite.destination.clone()))),
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
        #[cfg(trust_toolchain)]
        Operand::RuntimeChecks(_) => None,
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

struct CallSiteStubVisitor<'a> {
    changed: bool,
    locals: Vec<LocalDecl>,
    stubs: &'a Stubs,
}

impl MutMirVisitor for CallSiteStubVisitor<'_> {
    fn visit_terminator(&mut self, term: &mut Terminator) {
        // Replace direct calls
        if let TerminatorKind::Call { func, .. } = &mut term.kind
            && let Ok(func_ty) = func.ty(&self.locals)
            && let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind()
            && let Some(instance) = stubbed_callee_instance(self.stubs, def, &args, false)
            && let Ok(literal) = MirConst::try_new_zero_sized(instance.ty())
        {
            let span = mir_span!(term);
            let new_func = ConstOperand { span, user_ty: None, const_: literal };
            *func = Operand::Constant(new_func);
            self.changed = true;
        }
        self.super_terminator(term);
    }

    fn visit_operand(&mut self, operand: &mut Operand) {
        // A fn item reified or passed as a value. Only a constant names the
        // function: a copy of a local of fn-item type reads the constant this
        // visitor rewrote where the local was assigned.
        let Operand::Constant(ConstOperand { span, .. }) = operand else {
            return;
        };
        let span = *span;
        if let Ok(func_ty) = operand.ty(&self.locals)
            && let TyKind::RigidTy(RigidTy::FnDef(orig_def, args)) = func_ty.kind()
            && let Some(instance) = stubbed_callee_instance(self.stubs, orig_def, &args, true)
            && let Ok(literal) = MirConst::try_new_zero_sized(instance.ty())
        {
            let new_func = ConstOperand { span, user_ty: None, const_: literal };
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
    fn test_call_site_stub_pass_transformation_type_is_stubbing() {
        assert_eq!(CallSiteStubPass::transformation_type(), TransformationType::Stubbing);
    }

    #[test]
    fn test_fn_stub_pass_new_empty_stubs() {
        let empty: Stubs = HashMap::new();
        let pass = FnStubPass::new(&empty);
        assert!(pass.stubs.is_empty());
    }

    #[test]
    fn test_call_site_stub_pass_new_empty_stubs() {
        let empty: Stubs = HashMap::new();
        let pass = CallSiteStubPass::new(&empty);
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
    fn test_call_site_stub_pass_debug() {
        let empty: Stubs = HashMap::new();
        let pass = CallSiteStubPass::new(&empty);
        let dbg = format!("{:?}", pass);
        assert!(dbg.contains("CallSiteStubPass"));
    }
}
