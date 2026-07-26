// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! This module contains code related to the MIR-to-MIR pass to enable contracts.
use crate::args::ReachabilityType;
use crate::kani_middle::attributes::KaniAttributes;
use crate::kani_middle::codegen_units::CodegenUnit;
use crate::kani_middle::kani_functions::{KaniHook, KaniIntrinsic, KaniModel};
use crate::kani_middle::transform::body::{InsertPosition, MutableBody, SourceInstruction};
use crate::kani_middle::transform::contracts_frame;
use crate::kani_middle::transform::{TransformPass, TransformationType};
use crate::kani_queries::QueryDb;
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    Body, ConstOperand, Operand, Rvalue, StatementKind, Terminator, TerminatorKind,
    VarDebugInfoContents,
};
use rustc_public::rustc_internal;
use rustc_public::ty::{ClosureDef, FnDef, MirConst, RigidTy, TyKind, TypeAndMut, UintTy};
use rustc_span::Symbol;
use std::collections::HashSet;
use std::fmt::Debug;
use tracing::{debug, trace};

/// Check if we can replace calls to any_modifies or write_any.
///
/// This pass will replace the entire body, and it should only be applied to stubs
/// that have a body.
///
/// write_any is replaced with one of write_any_slim, write_any_slice, or write_any_str
/// depending on what the type of the input it
///
/// any_modifies is replaced with any
#[derive(Debug, Clone)]
pub(crate) struct AnyModifiesPass {
    kani_any: Option<FnDef>,
    kani_any_modifies: Option<FnDef>,
    kani_write_any: Option<FnDef>,
    kani_write_any_slim: Option<FnDef>,
    kani_write_any_slice: Option<FnDef>,
    kani_write_any_str: Option<FnDef>,
    target_fn: Option<String>,
}

impl TransformPass for AnyModifiesPass {
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
        // Only enable for contract verification harnesses (proof_for_contract).
        // This prevents applying contract-specific transformations to non-contract harnesses.
        query_db.args().unstable_features.iter().any(|f| f == "function-contracts")
            && self.kani_any.is_some()
            && self.target_fn.is_some()
    }

    /// Transform the function body by replacing it with the stub body.
    fn transform(&mut self, tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        trace!(function=?instance.name(), "AnyModifiesPass::transform");

        if instance.def.def_id()
            == self.kani_any.expect("kani_any must be set when enabled").def_id()
        {
            // Ensure kani::any is valid.
            self.any_body(tcx, body)
        } else if instance.ty().kind().is_closure() {
            // Replace any modifies occurrences. They should only happen in the contract closures.
            self.replace_any_modifies(body)
        } else {
            (false, body)
        }
    }
}

impl AnyModifiesPass {
    /// Build the pass with non-extern function stubs.
    pub(crate) fn new(tcx: TyCtxt, queries: &QueryDb, unit: &CodegenUnit) -> AnyModifiesPass {
        let kani_fns = queries.kani_functions();
        let kani_any = kani_fns.get(&KaniModel::Any.into()).copied();
        let kani_any_modifies = kani_fns.get(&KaniIntrinsic::AnyModifies.into()).copied();
        let kani_write_any = kani_fns.get(&KaniIntrinsic::WriteAny.into()).copied();
        let kani_write_any_slim = kani_fns.get(&KaniModel::WriteAnySlim.into()).copied();
        let kani_write_any_slice = kani_fns.get(&KaniModel::WriteAnySlice.into()).copied();
        let kani_write_any_str = kani_fns.get(&KaniModel::WriteAnyStr.into()).copied();
        let target_fn = if let Some(harness) = unit.harnesses.first() {
            let attributes = KaniAttributes::for_instance(tcx, *harness);
            attributes
                .proof_for_contract()
                .map(|symbol| symbol.expect("proof_for_contract symbol").as_str().to_string())
        } else {
            None
        };
        AnyModifiesPass {
            kani_any,
            kani_any_modifies,
            kani_write_any,
            kani_write_any_slim,
            kani_write_any_slice,
            kani_write_any_str,
            target_fn,
        }
    }

    /// Replace calls to `any_modifies` by calls to `any`.
    fn replace_any_modifies(&self, mut body: Body) -> (bool, Body) {
        let mut changed = false;
        let locals = body.locals().to_vec();
        for bb in &mut body.blocks {
            let TerminatorKind::Call { func, args, .. } = &mut bb.terminator.kind else {
                continue;
            };
            if let TyKind::RigidTy(RigidTy::FnDef(def, instance_args)) =
                func.ty(&locals).expect("func type for any_modifies").kind()
                && Some(def) == self.kani_any_modifies
            {
                let instance =
                    Instance::resolve(self.kani_any.expect("kani_any set"), &instance_args)
                        .expect("resolve kani_any instance");
                let literal = MirConst::try_new_zero_sized(instance.ty())
                    .expect("zero-sized const for kani_any");
                let span = bb.terminator.span;
                let new_func = ConstOperand { span, user_ty: None, const_: literal };
                *func = Operand::Constant(new_func);
                changed = true;
            }

            // if this is a valid kani::write_any function
            let func_ty = func.ty(&locals).expect("func type for write_any");
            if let TyKind::RigidTy(RigidTy::FnDef(def, instance_args)) = func_ty.kind()
                && Some(def) == self.kani_write_any
                && args.len() == 1
                && let Some(fn_sig) = func_ty.kind().fn_sig()
                && let Some(first_input_ty) = fn_sig.skip_binder().inputs().first()
                && let Some(TypeAndMut { ty: internal_type, mutability: _ }) =
                    first_input_ty.kind().builtin_deref(true)
            {
                // case on the type of the input
                if let TyKind::RigidTy(RigidTy::Slice(_)) = internal_type.kind() {
                    //if the input is a slice, use write_any_slice
                    let instance = Instance::resolve(
                        self.kani_write_any_slice.expect("write_any_slice set"),
                        &instance_args,
                    )
                    .expect("resolve write_any_slice");
                    let literal = MirConst::try_new_zero_sized(instance.ty())
                        .expect("zero-sized const for write_any_slice");
                    let span = bb.terminator.span;
                    let new_func = ConstOperand { span, user_ty: None, const_: literal };
                    *func = Operand::Constant(new_func);
                } else if let TyKind::RigidTy(RigidTy::Str) = internal_type.kind() {
                    //if the input is a str, use write_any_str
                    let instance = Instance::resolve(
                        self.kani_write_any_str.expect("write_any_str set"),
                        &instance_args,
                    )
                    .expect("resolve write_any_str");
                    let literal = MirConst::try_new_zero_sized(instance.ty())
                        .expect("zero-sized const for write_any_str");
                    let span = bb.terminator.span;
                    let new_func = ConstOperand { span, user_ty: None, const_: literal };
                    *func = Operand::Constant(new_func);
                } else {
                    //otherwise, use write_any_slim
                    let instance = Instance::resolve(
                        self.kani_write_any_slim.expect("write_any_slim set"),
                        &instance_args,
                    )
                    .expect("resolve write_any_slim");
                    let literal = MirConst::try_new_zero_sized(instance.ty())
                        .expect("zero-sized const for write_any_slim");
                    let span = bb.terminator.span;
                    let new_func = ConstOperand { span, user_ty: None, const_: literal };
                    *func = Operand::Constant(new_func);
                }
                changed = true;
            }
        }
        (changed, body)
    }

    /// Check if T::Arbitrary requirement for `kani::any()` is met after replacement.
    ///
    /// If it T does not implement arbitrary, generate error and delete body to interrupt analysis.
    fn any_body(&self, tcx: TyCtxt, mut body: Body) -> (bool, Body) {
        let mut valid = true;
        let locals = body.locals().to_vec();
        for bb in &mut body.blocks {
            let TerminatorKind::Call { func, .. } = &mut bb.terminator.kind else {
                continue;
            };
            if let TyKind::RigidTy(RigidTy::FnDef(def, args)) =
                func.ty(&locals).expect("func type in any_body").kind()
            {
                match Instance::resolve(def, &args) {
                    Ok(_) => {}
                    Err(e) => {
                        valid = false;
                        debug!(?e, "AnyModifiesPass::any_body failed");
                        let receiver_ty = args.0[0].expect_ty();
                        let msg = if let Some(target_fn) = &self.target_fn {
                            format!(
                                "`{receiver_ty}` doesn't implement `kani::Arbitrary`.\
                                        Please, check `{}` contract.",
                                target_fn,
                            )
                        } else {
                            format!("`{receiver_ty}` doesn't implement `kani::Arbitrary`.")
                        };
                        tcx.dcx()
                            .struct_span_err(rustc_internal::internal(tcx, bb.terminator.span), msg)
                            .with_help(
                                "All objects in the modifies clause must implement the Arbitrary. \
                                 The return type must also implement the Arbitrary trait if you \
                                 are checking recursion or using verified stub.",
                            )
                            .emit();
                    }
                }
            }
        }
        if valid {
            (true, body)
        } else {
            let mut new_body = MutableBody::from(body);
            new_body.clear_body(TerminatorKind::Unreachable);
            (true, new_body.into())
        }
    }
}

/// This pass will transform functions annotated with contracts based on the harness configuration.
///
/// Functions with contract will always follow the same structure:
///
/// ```text
/// #[kanitool::recursion_check = "__kani_recursion_check_modify"]
/// #[kanitool::checked_with = "__kani_check_modify"]
/// #[kanitool::replaced_with = "__kani_replace_modify"]
/// #[kanitool::asserted_with = "__kani_assert_modify"]
/// #[kanitool::modifies_wrapper = "__kani_modifies_modify"]
/// fn name_fn(ptr: &mut u32) {
///     #[kanitool::fn_marker = "kani_register_contract"]
///     pub const fn kani_register_contract<T, F: FnOnce() -> T>(f: F) -> T {
///         kani::panic("internal error: entered unreachable code: ")
///     }
///     let kani_contract_mode = kani::internal::mode();
///     match kani_contract_mode {
///         kani::internal::RECURSION_CHECK => {
///             #[kanitool::is_contract_generated(recursion_check)]
///             let mut __kani_recursion_check_name_fn = || { /* recursion check body */ };
///             kani_register_contract(__kani_recursion_check_modify)
///         }
///         kani::internal::REPLACE => {
///             #[kanitool::is_contract_generated(replace)]
///             let mut __kani_replace_name_fn = || { /* replace body */ };
///             kani_register_contract(__kani_replace_name_fn)
///         }
///         kani::internal::SIMPLE_CHECK => {
///             #[kanitool::is_contract_generated(check)]
///             let mut __kani_check_name_fn = || { /* check body */ };
///             kani_register_contract(__kani_check_name_fn)
///         }
///         kani::internal::ASSERT => {
///             #[kanitool::is_contract_generated(assert)]
///             let mut __kani_check_name_fn = || { /* assert body */ };
///             kani_register_contract(__kani_assert_name_fn)
///         }
///         _ => { /* original body */ } // non-enum: doc example
///     }
/// }
/// ```
///
/// This pass will perform the following operations:
/// 1. For functions with contract that are not being used for check or replacement:
///    - Set `kani_contract_mode` to the value ORIGINAL.
///    - Replace the generated closures body with unreachable.
/// 2. For functions with contract that are being used:
///    - Set `kani_contract_mode` to the value corresponding to the expected usage.
///    - Replace the non-used generated closures body with unreachable.
/// 3. Replace the body of `kani_register_contract` by `kani::internal::run_contract_fn` to
///    invoke the closure.
#[derive(Debug, Default, Clone)]
pub(crate) struct FunctionWithContractPass {
    /// Function that is being checked, if any.
    check_fn: Option<FnDef>,
    /// Functions that should be stubbed by their contract.
    replace_fns: HashSet<FnDef>,
    /// Should we interpret contracts as assertions? (true iff the no-assert-contracts option is not passed)
    assert_contracts: bool,
    /// Functions annotated with contract attributes will contain contract closures even if they
    /// are not to be used in this harness.
    /// In order to avoid bringing unnecessary logic, we clear their body.
    unused_closures: HashSet<ClosureDef>,
    /// Cache KaniRunContract function used to implement contracts.
    run_contract_fn: Option<FnDef>,
    /// FC-06: the modifies-wrapper closure of the checked function, resolved
    /// when the checked function's body is transformed. Its body gets
    /// instrumented with modifies-frame markers (see `contracts_frame`).
    check_wrapper_closure: Option<ClosureDef>,
    /// FC-06: `kani::internal::modifies_frame_enter` hook.
    frame_enter_fn: Option<FnDef>,
    /// FC-06: `kani::internal::modifies_frame_exit` hook.
    frame_exit_fn: Option<FnDef>,
}

impl TransformPass for FunctionWithContractPass {
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

    /// Transform the function body by replacing it with the stub body.
    fn transform(&mut self, tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        trace!(function=?instance.name(), "FunctionWithContractPass::transform");
        match instance.ty().kind().rigid().expect("rigid type for contract transform") {
            RigidTy::FnDef(def, args) => {
                if let Some(mode) = self.contract_mode(tcx, *def) {
                    self.mark_unused(tcx, *def, &body, mode);
                    let new_body = self.set_mode(tcx, body, mode);
                    (true, new_body)
                } else if KaniAttributes::for_instance(tcx, instance).fn_marker()
                    == Some(Symbol::intern("kani_register_contract"))
                {
                    let run =
                        Instance::resolve(self.run_contract_fn.expect("run_contract_fn set"), args)
                            .expect("resolve run_contract_fn");
                    (true, run.body().expect("run_contract body"))
                } else {
                    // Not a contract annotated function
                    (false, body)
                }
            }
            RigidTy::Closure(def, _args) => {
                if self.unused_closures.contains(def) {
                    // Delete body and mark it as unreachable.
                    let mut new_body = MutableBody::from(body);
                    new_body.clear_body(TerminatorKind::Unreachable);
                    (true, new_body.into())
                } else if Some(*def) == self.check_wrapper_closure
                    && let (Some(enter_fn), Some(exit_fn)) =
                        (self.frame_enter_fn, self.frame_exit_fn)
                {
                    // FC-06: instrument the checked function's modifies wrapper
                    // with frame markers so the backend can enforce the
                    // declared assignable footprint.
                    contracts_frame::instrument_wrapper_body(enter_fn, exit_fn, body)
                } else {
                    // Not a contract annotated function
                    (false, body)
                }
            }
            _ => {
                // external enum: RigidTy
                /* static variables case */
                (false, body)
            }
        }
    }
}

impl FunctionWithContractPass {
    /// Build the pass by collecting stubbed and verified functions.
    #[rustfmt::skip] // Keep compact — file at 500-line limit
    pub(crate) fn new(tcx: TyCtxt, queries: &QueryDb, unit: &CodegenUnit) -> FunctionWithContractPass {
        if let Some(harness) = unit.harnesses.first() {
            let (check_fn, replace_fns) = {
                let harness_generic_args = harness.args().0;
                // Manual harnesses have no arguments, so if there are generic arguments,
                // we know this is an automatic harness
                if matches!(queries.args().reachability_analysis, ReachabilityType::AllFns)
                    && !harness_generic_args.is_empty()
                {
                    let kind = harness.args().0[0].expect_ty().kind();
                    let (fn_to_verify_def, _) = kind.fn_def().expect("fn_def for auto harness");
                    // For automatic harnesses, the target is the function to verify,
                    // and stubs are empty.
                    (Some(fn_to_verify_def), HashSet::default())
                } else {
                    let attrs = KaniAttributes::for_instance(tcx, *harness);
                    let check_fn = attrs.interpret_for_contract_attribute();
                    let replace_fns: HashSet<_> =
                        attrs.interpret_stub_verified_attribute().into_iter().collect();
                    (check_fn, replace_fns)
                }
            };
            let run_contract_fn =
                queries.kani_functions().get(&KaniModel::RunContract.into()).copied();
            assert!(run_contract_fn.is_some(), "Failed to find trust_mc run contract function");
            FunctionWithContractPass {
                check_fn,
                replace_fns,
                assert_contracts: !queries.args().no_assert_contracts,
                unused_closures: Default::default(),
                run_contract_fn,
                check_wrapper_closure: None,
                frame_enter_fn: queries
                    .kani_functions()
                    .get(&KaniHook::ModifiesFrameEnter.into())
                    .copied(),
                frame_exit_fn: queries
                    .kani_functions()
                    .get(&KaniHook::ModifiesFrameExit.into())
                    .copied(),
            }
        } else {
            // If reachability mode is PubFns or Tests, we just remove any contract logic.
            // Note that in this path there is no proof harness.
            FunctionWithContractPass::default()
        }
    }

    /// Functions with contract have the following structure:
    /// ```text
    /// fn original([self], args*) {
    ///    let kani_contract_mode = kani::internal::mode(); // ** Replace this call
    ///    match kani_contract_mode {
    ///        kani::internal::RECURSION_CHECK => {
    ///            let closure = |/*args*/|{ /*body*/};
    ///            kani_register_contract(closure) // ** Replace this call
    ///        }
    ///        kani::internal::REPLACE => {
    ///            // same as above
    ///        }
    ///        kani::internal::SIMPLE_CHECK => {
    ///            // same as above
    ///        }
    ///        kani::internal::ASSERT => {
    ///            // same as above
    ///        }
    ///        _ => { /* original code */} // non-enum: doc example
    ///    }
    /// }
    /// ```
    /// See function `handle_untouched` inside `kani_macros`.
    ///
    /// Thus, we need to:
    /// 1. Initialize `kani_contract_mode` variable to the value corresponding to the mode.
    ///
    /// Thus replace this call:
    /// ```text
    ///    let kani_contract_mode = kani::internal::mode(); // ** Replace this call
    /// ```
    /// by:
    /// ```text
    ///    let kani_contract_mode = mode_const;
    ///    goto bbX;
    /// ```
    /// 2. Replace `kani_register_contract` by the call to the closure.
    fn set_mode(&self, tcx: TyCtxt, body: Body, mode: ContractMode) -> Body {
        debug!(?mode, "set_mode");
        let mut new_body = MutableBody::from(body);
        let (mut mode_call, ret, target) = new_body
            .blocks()
            .iter()
            .enumerate()
            .find_map(|(bb_idx, bb)| {
                if let TerminatorKind::Call { func, target, destination, .. } = &bb.terminator.kind
                {
                    let (callee, _) = func
                        .ty(new_body.locals())
                        .expect("func type in set_mode")
                        .kind()
                        .fn_def()?;
                    let marker = KaniAttributes::for_def_id(tcx, callee.def_id()).fn_marker();
                    if marker.is_some_and(|s| s.as_str() == "kani_contract_mode") {
                        return Some((
                            SourceInstruction::Terminator { bb: bb_idx },
                            destination.clone(),
                            target.expect("call target"),
                        ));
                    }
                }
                None
            })
            .expect("find kani_contract_mode call");

        let span = mode_call.span(new_body.blocks());
        // Capture the mode local before `ret` is consumed by `assign_to`.
        let ret_local = ret.local;
        let ret_proj_empty = ret.projection.is_empty();
        let mode_const = new_body.new_uint_operand(mode as _, UintTy::U8, span);
        new_body.assign_to(ret, Rvalue::Use(mode_const), &mut mode_call, InsertPosition::Before);
        new_body.replace_terminator(
            &mode_call,
            Terminator { kind: TerminatorKind::Goto { target }, span },
        );

        // G3 fix: `ret` (the contract mode) is now a compile-time constant, but
        // the downstream `SwitchInt` that dispatches on it — and its dead arms,
        // including the bare-Original arm that inlines the REAL function body —
        // still survive. BMC codegen does not reliably prune those unsat arms
        // (it is receiver-type dependent), so the dead real body's
        // un-inlinable calls leak as `Call terminator` fallbacks and demote any
        // `stub_verified` consumer (e.g. aterm's parser_never_panics, where the
        // dead arm is process_byte_inner's 18-call VTE dispatch). Constant-fold
        // the mode `SwitchInt` to a direct `Goto` to the selected arm so every
        // other arm becomes statically unreachable and is never codegen'd. This
        // is semantics-preserving: it is exactly the branch the switch would
        // take at runtime for the now-constant mode.
        if ret_proj_empty {
            // Locals whose value is (a copy of) the mode constant.
            let mut alias: HashSet<usize> = HashSet::new();
            alias.insert(ret_local);
            let mut changed = true;
            while changed {
                changed = false;
                for bb in new_body.blocks() {
                    for stmt in &bb.statements {
                        if let StatementKind::Assign(dest, Rvalue::Use(op)) = &stmt.kind
                            && let Operand::Copy(src) | Operand::Move(src) = op
                            && src.projection.is_empty()
                            && dest.projection.is_empty()
                            && alias.contains(&src.local)
                            && !alias.contains(&dest.local)
                        {
                            alias.insert(dest.local);
                            changed = true;
                        }
                    }
                }
            }
            let mode_val = mode as u128;
            let fold = new_body.blocks().iter().enumerate().find_map(|(bb_idx, bb)| {
                if let TerminatorKind::SwitchInt { discr, targets } = &bb.terminator.kind
                    && let Operand::Copy(p) | Operand::Move(p) = discr
                    && p.projection.is_empty()
                    && alias.contains(&p.local)
                {
                    let selected = targets
                        .branches()
                        .find(|(v, _)| *v == mode_val)
                        .map(|(_, t)| t)
                        .unwrap_or_else(|| targets.otherwise());
                    return Some((bb_idx, selected, bb.terminator.span));
                }
                None
            });
            if let Some((bb_idx, selected, sw_span)) = fold {
                new_body.replace_terminator(
                    &SourceInstruction::Terminator { bb: bb_idx },
                    Terminator { kind: TerminatorKind::Goto { target: selected }, span: sw_span },
                );
            }
        }

        new_body.into()
    }

    /// Return which contract mode to use for this function if any.
    /// Note that the Check and Replace modes take precedence over the Assert mode.
    /// This precedence ensures that a given `target` of a proof_for_contract(target) or stub_verified(target)
    /// use their Check or Replace closures, respectively, rather than the Assert closure.
    fn contract_mode(&self, tcx: TyCtxt, fn_def: FnDef) -> Option<ContractMode> {
        let kani_attributes = KaniAttributes::for_def_id(tcx, fn_def.def_id());
        kani_attributes.has_contract().then(|| {
            if self.check_fn == Some(fn_def) {
                if kani_attributes.has_recursion() {
                    ContractMode::RecursiveCheck
                } else {
                    ContractMode::SimpleCheck
                }
            } else if self.replace_fns.contains(&fn_def) {
                ContractMode::Replace
            } else if self.assert_contracts {
                ContractMode::Assert
            } else {
                ContractMode::Original
            }
        })
    }

    /// Select any unused closure for body deletion.
    fn mark_unused(&mut self, tcx: TyCtxt, fn_def: FnDef, body: &Body, mode: ContractMode) {
        let contract = KaniAttributes::for_def_id(tcx, fn_def.def_id())
            .contract_attributes()
            .expect("contract attributes for mark_unused");
        let recursion_closure = find_closure(tcx, fn_def, body, contract.recursion_check.as_str());
        let check_closure = find_closure(tcx, fn_def, body, contract.checked_with.as_str());
        let replace_closure = find_closure(tcx, fn_def, body, contract.replaced_with.as_str());
        let assert_closure = find_closure(tcx, fn_def, body, contract.asserted_with.as_str());
        match mode {
            ContractMode::Original => {
                // No contract instrumentation needed. Add all closures to the list of unused.
                self.unused_closures.insert(recursion_closure);
                self.unused_closures.insert(check_closure);
                self.unused_closures.insert(replace_closure);
                self.unused_closures.insert(assert_closure);
            }
            ContractMode::RecursiveCheck => {
                self.unused_closures.insert(replace_closure);
                self.unused_closures.insert(check_closure);
                self.unused_closures.insert(assert_closure);
                // FC-06: enforce the modifies clause of the checked function.
                self.check_wrapper_closure =
                    contracts_frame::resolve_modifies_wrapper(tcx, fn_def, body, &contract, true);
            }
            ContractMode::SimpleCheck => {
                self.unused_closures.insert(replace_closure);
                self.unused_closures.insert(recursion_closure);
                self.unused_closures.insert(assert_closure);
                // FC-06: enforce the modifies clause of the checked function.
                self.check_wrapper_closure =
                    contracts_frame::resolve_modifies_wrapper(tcx, fn_def, body, &contract, false);
            }
            ContractMode::Replace => {
                self.unused_closures.insert(recursion_closure);
                self.unused_closures.insert(check_closure);
                self.unused_closures.insert(assert_closure);
            }
            ContractMode::Assert => {
                self.unused_closures.insert(recursion_closure);
                self.unused_closures.insert(check_closure);
                self.unused_closures.insert(replace_closure);
            }
        }
    }
}

/// Enumeration that store the value of which implementation should be selected.
///
/// Keep the discriminant values in sync with `kani::internal::mode`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum ContractMode {
    Original = 0,
    RecursiveCheck = 1,
    SimpleCheck = 2,
    Replace = 3,
    Assert = 4,
}

fn find_closure(tcx: TyCtxt, fn_def: FnDef, body: &Body, name: &str) -> ClosureDef {
    body.var_debug_info
        .iter()
        .find_map(|var_info| {
            if var_info.name.as_str() == name {
                let ty = match &var_info.value {
                    VarDebugInfoContents::Place(place) => {
                        place.ty(body.locals()).expect("place type in find_closure")
                    }
                    VarDebugInfoContents::Const(const_op) => const_op.ty(),
                };
                if let TyKind::RigidTy(RigidTy::Closure(def, _args)) = ty.kind() {
                    return Some(def);
                }
            }
            None
        })
        .unwrap_or_else(|| {
            tcx.sess.dcx().err(format!(
                "Failed to find contract closure `{name}` in function `{}`",
                fn_def.name()
            ));
            tcx.sess.dcx().abort_if_errors();
            unreachable!(
                "abort_if_errors should have terminated after emitting contract closure error"
            )
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kani_middle::attributes;
    use rustc_public::{CompilerError, run_with_tcx};
    use std::fs;
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU64, Ordering};
    use tempfile::TempDir;

    const WRITE_ANY_TRANSFORM_SOURCE: &str = r#"#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani_internal {
    #[inline(never)]
    #[kanitool::fn_marker = "WriteAnyIntrinsic"]
    pub unsafe fn write_any<T: ?Sized>(_pointer: *mut T) {}
}

mod kani_models {
    #[inline(never)]
    #[kanitool::fn_marker = "WriteAnySlimModel"]
    pub unsafe fn write_any_slim<T>(_pointer: *mut T) {}

    #[inline(never)]
    #[kanitool::fn_marker = "WriteAnySliceModel"]
    pub unsafe fn write_any_slice<T>(_pointer: *mut [T]) {}

    #[inline(never)]
    #[kanitool::fn_marker = "WriteAnyStrModel"]
    pub unsafe fn write_any_str(_pointer: *mut str) {}
}

pub fn probe_write_any_slice() {
    let mut data = [0_u32; 2];
    unsafe {
        let slice: &mut [u32] = &mut data;
        kani_internal::write_any::<[u32]>(slice as *mut [u32]);
    }
}
"#;

    fn with_test_tcx_for_source<F>(source: &str, callback: F)
    where
        F: for<'tcx> FnOnce(TyCtxt<'tcx>) + Send,
    {
        static CRATE_COUNTER: AtomicU64 = AtomicU64::new(0);

        let temp_dir = TempDir::new().expect("create temp dir");
        let src_path: PathBuf = temp_dir.path().join("lib.rs");
        fs::write(&src_path, source).expect("write test source");

        let unique_id = CRATE_COUNTER.fetch_add(1, Ordering::SeqCst);
        let crate_name = format!("contracts_transform_test_crate_{unique_id}");
        let out_dir = temp_dir.path().join("out");
        fs::create_dir_all(&out_dir).expect("create output dir");

        let args = vec![
            "rustc".to_string(),
            src_path.to_string_lossy().into_owned(),
            "--crate-type=lib".to_string(),
            format!("--crate-name={crate_name}"),
            "--out-dir".to_string(),
            out_dir.to_string_lossy().into_owned(),
            "--edition=2024".to_string(),
            "-C".to_string(),
            "opt-level=0".to_string(),
            "-Z".to_string(),
            "inline-mir=no".to_string(),
            "-Z".to_string(),
            "mir-opt-level=0".to_string(),
        ];
        let result = run_with_tcx!(&args, |tcx| {
            callback(tcx);
            std::ops::ControlFlow::<(), ()>::Continue(())
        });
        assert!(
            result.is_ok() || matches!(result, Err(CompilerError::Skipped)),
            "rustc_public run failed: {result:?}"
        );
    }

    fn find_instance_by_suffix(tcx: TyCtxt<'_>, suffix: &str) -> Instance {
        rustc_public::all_local_items()
            .into_iter()
            .find_map(|item| {
                let def_id = rustc_internal::internal(tcx, item.def_id());
                tcx.def_path_str(def_id)
                    .ends_with(suffix)
                    .then(|| Instance::try_from(item).ok())
                    .flatten()
            })
            .expect("missing item with requested suffix")
    }

    fn find_fn_def_by_marker(marker: &str) -> FnDef {
        rustc_public::all_local_items()
            .into_iter()
            .find_map(|item| {
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) = item.ty().kind() else {
                    return None;
                };
                (attributes::fn_marker(def).as_deref() == Some(marker)).then_some(def)
            })
            .unwrap_or_else(|| panic!("missing marker-tagged function {marker}"))
    }

    fn collect_call_markers(body: &Body) -> Vec<String> {
        body.blocks
            .iter()
            .filter_map(|block| {
                let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                    return None;
                };
                let Ok(func_ty) = func.ty(body.locals()) else { return None };
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind() else {
                    return None;
                };
                attributes::fn_marker(def).map(|marker| marker.to_string())
            })
            .collect()
    }

    // ContractMode discriminants must match kani::internal::mode constants.
    // If these change, contract dispatch will silently break.
    #[test]
    fn test_contract_mode_discriminant_original() {
        assert_eq!(ContractMode::Original as u8, 0);
    }

    #[test]
    fn test_contract_mode_discriminant_recursive_check() {
        assert_eq!(ContractMode::RecursiveCheck as u8, 1);
    }

    #[test]
    fn test_contract_mode_discriminant_simple_check() {
        assert_eq!(ContractMode::SimpleCheck as u8, 2);
    }

    #[test]
    fn test_contract_mode_discriminant_replace() {
        assert_eq!(ContractMode::Replace as u8, 3);
    }

    #[test]
    fn test_contract_mode_discriminant_assert() {
        assert_eq!(ContractMode::Assert as u8, 4);
    }

    #[test]
    fn test_contract_mode_all_variants_distinct() {
        let modes = [
            ContractMode::Original,
            ContractMode::RecursiveCheck,
            ContractMode::SimpleCheck,
            ContractMode::Replace,
            ContractMode::Assert,
        ];
        for (i, a) in modes.iter().enumerate() {
            for (j, b) in modes.iter().enumerate() {
                if i == j {
                    assert_eq!(a, b);
                } else {
                    assert_ne!(a, b, "variants {i} and {j} should differ");
                }
            }
        }
    }

    #[test]
    fn test_contract_mode_copy() {
        let mode = ContractMode::SimpleCheck;
        let copied = mode;
        assert_eq!(mode, copied);
    }

    #[test]
    fn test_contract_mode_debug_format() {
        let dbg = format!("{:?}", ContractMode::RecursiveCheck);
        assert!(dbg.contains("RecursiveCheck"), "Debug should include variant name");
    }

    #[test]
    fn test_function_with_contract_pass_default_has_no_check_fn() {
        let pass = FunctionWithContractPass::default();
        assert!(pass.check_fn.is_none());
        assert!(pass.replace_fns.is_empty());
        assert!(!pass.assert_contracts);
        assert!(pass.unused_closures.is_empty());
        assert!(pass.run_contract_fn.is_none());
    }

    #[test]
    fn test_function_with_contract_pass_transformation_type_is_stubbing() {
        assert_eq!(FunctionWithContractPass::transformation_type(), TransformationType::Stubbing);
    }

    #[test]
    fn test_function_with_contract_pass_default_is_enabled() {
        let pass = FunctionWithContractPass::default();
        let dbg = format!("{:?}", pass);
        assert!(dbg.contains("FunctionWithContractPass"));
    }

    #[test]
    fn test_any_modifies_pass_transformation_type_is_stubbing() {
        assert_eq!(AnyModifiesPass::transformation_type(), TransformationType::Stubbing);
    }

    #[test]
    fn test_any_modifies_pass_rewrites_write_any_slice_intrinsic_to_slice_model() {
        with_test_tcx_for_source(WRITE_ANY_TRANSFORM_SOURCE, |tcx| {
            let instance = find_instance_by_suffix(tcx, "probe_write_any_slice");
            let body = instance.body().expect("probe_write_any_slice body");
            let pass = AnyModifiesPass {
                target_fn: None,
                kani_any_modifies: None,
                kani_any: None,
                kani_write_any: Some(find_fn_def_by_marker("WriteAnyIntrinsic")),
                kani_write_any_slim: Some(find_fn_def_by_marker("WriteAnySlimModel")),
                kani_write_any_slice: Some(find_fn_def_by_marker("WriteAnySliceModel")),
                kani_write_any_str: Some(find_fn_def_by_marker("WriteAnyStrModel")),
            };

            let (changed, transformed) = pass.replace_any_modifies(body);
            assert!(changed, "write_any::<[T]> should be rewritten by AnyModifiesPass");
            let markers = collect_call_markers(&transformed);
            assert!(
                markers.iter().any(|marker| marker == "WriteAnySliceModel"),
                "transformed body should call WriteAnySliceModel, got {markers:?}"
            );
            assert!(
                !markers.iter().any(|marker| marker == "WriteAnyIntrinsic"),
                "transformed body should not keep the WriteAnyIntrinsic call, got {markers:?}"
            );
        });
    }
}
