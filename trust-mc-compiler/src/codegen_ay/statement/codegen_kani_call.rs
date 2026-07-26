// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Kani intrinsic dispatch (converted from include!() per #2595).
// Kani marker-based intrinsic dispatch.
// Name-based function dispatch is in codegen_kani_iter.rs (#2246).

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::chc::quantifier_encoding::{
    ClosureBodyResult, QUANTIFIER_UNROLL_LIMIT, extract_constant_bounds,
    resolve_quantifier_closure_body, translate_closure_body_as_expr,
};
use crate::codegen_ay::chc::{ChcConfig, ChcCtx};
use crate::codegen_ay::statement::dispatch::CallDispatchOutcome;
use crate::codegen_ay::types::ptr_sort;
use crate::kani_middle::attributes;
use crate::kani_middle::kani_functions::{
    KaniFunction, KaniHook, KaniIntrinsic, KaniModel, try_get_kani_function,
};
use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    AggregateKind, BasicBlockIdx, Operand, Place, Rvalue, StatementKind, Terminator,
};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Try to codegen a kani intrinsic call.
    ///
    /// Handles Kani-specific intrinsics like `kani::any`, `kani::assume`, `kani::assert`.
    /// Returns an explicit dispatch outcome so handled divergence and fallthrough
    /// cannot be confused with a family miss.
    ///
    /// REQUIRES: func resolves to a valid function (FnDef)
    /// ENSURES: On Continue(bb), kani call handled, continue to bb
    /// ENSURES: On Diverge, kani call handled, diverges (no successors)
    /// ENSURES: kani::assume adds path constraint, kani::assert adds violation
    /// ENSURES: kani::any_raw creates fresh symbolic variable with model query
    /// ENSURES: On Miss, func is not a recognized Kani intrinsic (caller handles)
    pub(super) fn try_codegen_kani_call(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        term: &Terminator,
    ) -> CallDispatchOutcome {
        // Get the function type once — reused for FnDef check and closure shim
        // fallback. Avoids the format!("{:?}", ty) allocation that previously ran
        // on every Call terminator (Part of #2267).
        let Some(func_ty) = func.ty(self.body.locals()).into_option() else {
            return CallDispatchOutcome::Miss;
        };
        let (fn_def, fn_args) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return CallDispatchOutcome::Miss, // external enum: TyKind
        };

        // Resolve the function to an Instance to check instance kind and get fn_marker.
        let instance_opt = Instance::resolve(fn_def, &fn_args).into_option();
        let fn_marker = instance_opt
            .as_ref()
            .and_then(|instance| attributes::fn_marker(instance.def))
            .or_else(|| attributes::fn_marker(fn_def));

        // First try marker-based lookup
        if let Some(ref marker) = fn_marker
            && let Some(kani_fn) = try_get_kani_function(marker)
        {
            debug!(?kani_fn, "AY codegen kani intrinsic");
            return match kani_fn {
                KaniFunction::Hook(KaniHook::AnyRaw) => {
                    self.codegen_kani_any_raw(destination);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::Assume) => {
                    self.codegen_kani_assume(args);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::Assert) => {
                    // Part of #4217: In prove_safety_only mode, user assertions
                    // become assumptions (no violation emitted).
                    if self.ctx.config.prove_safety_only {
                        self.codegen_kani_assume(args);
                    } else {
                        // Kani assert-assume semantics: assert(cond) THEN
                        // assume(cond), so code after a failed assert is
                        // path-constrained (UNREACHABLE, not SUCCESS). The
                        // assume half is ordered (suffix-scoped) so it cannot
                        // mask this assert's own violation or earlier ones.
                        self.codegen_kani_assert(args);
                        self.codegen_kani_assume_ordered(args);
                    }
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::Cover) => {
                    self.codegen_kani_cover(args);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::ValueView) => {
                    self.codegen_kani_value_view(args, destination);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::Panic) => {
                    // Part of #4217: Skip panic violations in prove_safety_only mode.
                    if !self.ctx.config.prove_safety_only {
                        self.record_violation_guarded(Expr::bool_const(true), "panic");
                    }
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::UnsupportedCheck) => {
                    self.record_violation_guarded(Expr::bool_const(true), "unsupported_check");
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::SafetyCheck) => {
                    self.codegen_kani_assert(args);
                    self.codegen_kani_assume(args);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::SafetyCheckNoAssume) => {
                    self.codegen_kani_assert(args);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::UntrackedDeref) => {
                    if !args.is_empty()
                        && let Some(val) = self.codegen_operand(&args[0])
                    {
                        let base_name = self.ssa_base_name(destination);
                        self.env_update(base_name, val);
                    }
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::InitContracts) => {
                    CallDispatchOutcome::from_handled_target(target)
                }
                // FC-06: modifies frame markers are only enforced by the CHC
                // backend; BMC treats them as control-flow no-ops.
                KaniFunction::Hook(KaniHook::ModifiesFrameEnter | KaniHook::ModifiesFrameExit) => {
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::Check) => {
                    // Part of #4217: Check is a user assertion variant — suppress
                    // in prove_safety_only mode, convert to assume.
                    if self.ctx.config.prove_safety_only {
                        self.codegen_kani_assume(args);
                    } else {
                        self.codegen_kani_assert(args);
                    }
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Model(KaniModel::RunContract)
                | KaniFunction::Model(KaniModel::RunLoopContract) => {
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Model(KaniModel::PanicStub) => {
                    // Part of #4217: PanicStub comes from user assert!() failures —
                    // suppress in prove_safety_only mode.
                    if !self.ctx.config.prove_safety_only {
                        self.record_violation_guarded(Expr::bool_const(true), "panic_stub");
                    }
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Model(KaniModel::Any)
                | KaniFunction::Intrinsic(KaniIntrinsic::AnyModifies) => {
                    self.codegen_kani_any_raw(destination);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Intrinsic(KaniIntrinsic::FloatToIntInRange) => {
                    self.codegen_float_to_int_in_range(&fn_args, args, destination);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Intrinsic(KaniIntrinsic::CheckedSizeOf) => {
                    self.codegen_checked_size_or_align(args, destination, true);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Intrinsic(KaniIntrinsic::CheckedAlignOf) => {
                    self.codegen_checked_size_or_align(args, destination, false);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Intrinsic(KaniIntrinsic::IsInitialized) => {
                    let base_name = self.ssa_base_name(destination);
                    let _ssa_name = self.ssa_name_from_base(&base_name, true);
                    self.env_update(base_name, Expr::bool_const(true));
                    debug!("codegen IsInitialized: over-approximating as true");
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Intrinsic(KaniIntrinsic::ValidValue) => {
                    let base_name = self.ssa_base_name(destination);
                    let _ssa_name = self.ssa_name_from_base(&base_name, true);
                    self.env_update(base_name, Expr::bool_const(true));
                    debug!("codegen ValidValue: over-approximating as true");
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::IsAllocated) => {
                    let base_name = self.ssa_base_name(destination);
                    let _ssa_name = self.ssa_name_from_base(&base_name, true);

                    let ptr_expr = if !args.is_empty() {
                        self.codegen_operand(&args[0]).unwrap_or_else(|| {
                            let name = self.ctx.fresh_name("ay_is_alloc_ptr");
                            self.ctx.declare_var(&name, ptr_sort())
                        })
                    } else {
                        let name = self.ctx.fresh_name("ay_is_alloc_ptr");
                        self.ctx.declare_var(&name, ptr_sort())
                    };

                    let size_expr =
                        if args.len() > 1 { self.codegen_operand(&args[1]) } else { None };

                    let is_allocated = self.ctx.heap_is_allocated(ptr_expr, size_expr);
                    self.env_update(base_name, is_allocated);
                    debug!("codegen IsAllocated: using heap model lookup with size check");
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::PointerObject) => {
                    let base_name = self.ssa_base_name(destination);
                    let _ssa_name = self.ssa_name_from_base(&base_name, true);

                    let ptr_expr = if !args.is_empty() {
                        self.codegen_operand(&args[0]).unwrap_or_else(|| {
                            let name = self.ctx.fresh_name("ay_ptr_obj_arg");
                            self.ctx.declare_var(&name, ptr_sort())
                        })
                    } else {
                        let name = self.ctx.fresh_name("ay_ptr_obj_arg");
                        self.ctx.declare_var(&name, ptr_sort())
                    };

                    let object_id = self.ctx.heap_pointer_object(ptr_expr);
                    self.env_update(base_name, object_id);
                    debug!("codegen PointerObject: using heap model (ptr / HEAP_STRIDE)");
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::PointerOffset) => {
                    let base_name = self.ssa_base_name(destination);
                    let _ssa_name = self.ssa_name_from_base(&base_name, true);

                    let ptr_expr = if !args.is_empty() {
                        self.codegen_operand(&args[0]).unwrap_or_else(|| {
                            let name = self.ctx.fresh_name("ay_ptr_off_arg");
                            self.ctx.declare_var(&name, ptr_sort())
                        })
                    } else {
                        let name = self.ctx.fresh_name("ay_ptr_off_arg");
                        self.ctx.declare_var(&name, ptr_sort())
                    };

                    let offset = self.ctx.heap_pointer_offset(ptr_expr);
                    self.env_update(base_name, offset);
                    debug!("codegen PointerOffset: using heap model (ptr % HEAP_STRIDE)");
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Model(KaniModel::AlignOfVal) => {
                    debug!("codegen KaniModel::AlignOfVal");
                    CallDispatchOutcome::from_handled_target(self.codegen_align_of_val(
                        args,
                        destination,
                        target,
                    ))
                }
                KaniFunction::Model(KaniModel::SizeOfVal) => {
                    debug!("codegen KaniModel::SizeOfVal");
                    CallDispatchOutcome::from_handled_target(self.codegen_size_of_val(
                        args,
                        destination,
                        target,
                    ))
                }
                KaniFunction::Model(KaniModel::PtrOffsetFrom) => {
                    debug!("codegen KaniModel::PtrOffsetFrom");
                    CallDispatchOutcome::from_handled_target(self.codegen_ptr_offset_from(
                        args,
                        destination,
                        target,
                        false,
                    ))
                }
                KaniFunction::Model(KaniModel::PtrOffsetFromUnsigned) => {
                    debug!("codegen KaniModel::PtrOffsetFromUnsigned");
                    CallDispatchOutcome::from_handled_target(self.codegen_ptr_offset_from(
                        args,
                        destination,
                        target,
                        true,
                    ))
                }
                KaniFunction::Model(KaniModel::Offset) => {
                    // Part of #2912: Handle ptr::offset(ptr, count) model function.
                    // Kani rewrites core::ptr::offset to this model. The function
                    // computes ptr + count * sizeof(T). This is essential for
                    // IntoIter::next() which uses ptr::offset to advance the
                    // read pointer.
                    debug!("codegen KaniModel::Offset");
                    CallDispatchOutcome::from_handled_target(self.codegen_model_offset(
                        args,
                        destination,
                        target,
                        &instance_opt,
                    ))
                }
                // MEMUB-24/25/27: Is*PtrInitialized — real verdicts from the
                // scalar shadow-memory state under `-Z uninit-checks`
                // (still `true` when the flag is off or the shape is
                // untranslatable — the pre-MEMUB #3311 behavior).
                KaniFunction::Model(
                    model @ (KaniModel::IsPtrInitialized
                    | KaniModel::IsStrPtrInitialized
                    | KaniModel::IsSliceChunkPtrInitialized
                    | KaniModel::IsSlicePtrInitialized),
                ) => {
                    self.codegen_shadow_mem_is(model, args, destination);
                    CallDispatchOutcome::from_handled_target(target)
                }
                // Part of #3912: BMC parity for KaniModel::SimdBitmask.
                // CHC already has a dedicated encoder; this brings the BMC
                // statement path to parity.
                KaniFunction::Model(KaniModel::SimdBitmask) => {
                    self.codegen_simd_bitmask_model(func, args, destination);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Model(KaniModel::WriteAnySlim) => {
                    if !self.codegen_kani_write_any_slim(args) {
                        let location = format!("{:?} ({:?})", term.span, kani_fn);
                        self.ctx.unsupported_with_fallback("trust_mc intrinsic", location);
                    }
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Intrinsic(KaniIntrinsic::WriteAny) => {
                    let is_dst = args
                        .first()
                        .and_then(|arg| arg.ty(self.body.locals()).into_option())
                        .is_some_and(|ty| {
                            matches!(
                                ty.kind(),
                                TyKind::RigidTy(RigidTy::RawPtr(pointee, _)
                                    | RigidTy::Ref(_, pointee, _))
                                    if matches!(
                                        pointee.kind(),
                                        TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str)
                                    )
                            )
                        });
                    if is_dst || !self.codegen_kani_write_any_slim(args) {
                        let location = format!("{:?} ({:?})", term.span, kani_fn);
                        self.ctx.unsupported_with_fallback("trust_mc intrinsic", location);
                    }
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Hook(KaniHook::Exists | KaniHook::Forall) => {
                    let is_forall = matches!(kani_fn, KaniFunction::Hook(KaniHook::Forall));
                    if self.codegen_kani_bounded_quantifier(func, args, destination, is_forall) {
                        debug!(is_forall, "BMC kani quantifier hook -> unrolled expression");
                    } else {
                        let location = format!("{:?} ({:?})", term.span, kani_fn);
                        self.ctx.unsupported_with_fallback("trust_mc intrinsic", location);
                    }
                    CallDispatchOutcome::from_handled_target(target)
                }
                // MEMUB-24/25/27: shadow-memory writes are real guarded updates
                // of the ctx-level scalar shadow state under `-Z uninit-checks`
                // (no-ops when the flag is off — the #4101 behavior, avoiding
                // spurious fallback counts).
                KaniFunction::Model(KaniModel::InitializeMemoryInitializationState) => {
                    self.codegen_shadow_mem_initialize();
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Model(
                    model @ (KaniModel::SetPtrInitialized
                    | KaniModel::SetSliceChunkPtrInitialized
                    | KaniModel::SetSlicePtrInitialized
                    | KaniModel::SetStrPtrInitialized),
                ) => {
                    self.codegen_shadow_mem_set(model, args);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Model(
                    model @ (KaniModel::CopyInitState | KaniModel::CopyInitStateSingle),
                ) => {
                    self.codegen_shadow_mem_copy(model, &fn_args, args);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Model(KaniModel::StoreArgument) => {
                    self.codegen_shadow_mem_store_argument(args);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Model(KaniModel::LoadArgument) => {
                    self.codegen_shadow_mem_load_argument(&fn_args, args);
                    CallDispatchOutcome::from_handled_target(target)
                }
                KaniFunction::Model(KaniModel::AlignOfDynObject)
                | KaniFunction::Model(KaniModel::SizeOfDynObject)
                | KaniFunction::Model(KaniModel::SizeOfSliceObject)
                | KaniFunction::Model(KaniModel::WriteAnySlice)
                | KaniFunction::Model(KaniModel::WriteAnyStr)
                | KaniFunction::Intrinsic(KaniIntrinsic::AutomaticHarness) => {
                    let location = format!("{:?} ({:?})", term.span, kani_fn);
                    self.ctx.unsupported_with_fallback("trust_mc intrinsic", location);
                    CallDispatchOutcome::from_handled_target(target)
                }
            };
        }

        // Delegate to name-based dispatch for non-marker functions.
        // Part of #3317: Use def_path_str (full crate-qualified path) as fallback
        // instead of fn_def.0.name() (short name). Short names lack crate prefixes,
        // which bypasses the namespace guards that protect against false-positive
        // routing of user functions to Kani model handlers.
        let fn_name = self.resolve_callee_path(func).unwrap_or_else(|| {
            let internal_def_id = rustc_internal::internal(self.ctx.tcx, fn_def.def_id());
            self.ctx.tcx.def_path_str(internal_def_id)
        });
        self.try_codegen_named_call(&fn_name, &instance_opt, func, args, destination, target)
    }

    fn codegen_kani_bounded_quantifier(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        is_forall: bool,
    ) -> bool {
        if args.len() < 3 {
            return false;
        }

        let Some(lower) = self.codegen_operand(&args[0]) else {
            return false;
        };
        let Some(upper) = self.codegen_operand(&args[1]) else {
            return false;
        };
        let lower = self.resolve_concrete_expr(&lower);
        let upper = self.resolve_concrete_expr(&upper);
        let Some((lower_val, upper_val, bv_width)) = extract_constant_bounds(&lower, &upper) else {
            return false;
        };
        let range_size = upper_val.saturating_sub(lower_val);
        if range_size > QUANTIFIER_UNROLL_LIMIT {
            return false;
        }

        let caller_locals = self.body.locals();
        let Some(closure_body) = resolve_quantifier_closure_body(func, &caller_locals) else {
            return false;
        };
        let captures = self.extract_bmc_quantifier_captures(&args[2]);

        let mut chc_ctx = ChcCtx::new(
            self.ctx.tcx,
            self.body,
            self.ctx.current_fn_name().to_owned(),
            ChcConfig::default(),
        );

        let mut predicates = Vec::with_capacity(range_size as usize);
        let mut safety_guards = Vec::new();
        for i in lower_val..upper_val {
            let qvar = if let Some(width) = bv_width {
                Expr::bitvec_const(i, width)
            } else {
                Expr::int_const(i)
            };
            let Some(ClosureBodyResult { pred, no_panic_guard }) =
                translate_closure_body_as_expr(&mut chc_ctx, &closure_body, &qvar, &captures, 0)
            else {
                return false;
            };
            predicates.push(pred);
            if let Some(guard) = no_panic_guard {
                safety_guards.push(guard);
            }
        }

        let quantifier_result = if predicates.is_empty() {
            Expr::bool_const(is_forall)
        } else {
            predicates
                .into_iter()
                .reduce(|lhs, rhs| if is_forall { lhs.and(rhs) } else { lhs.or(rhs) })
                .unwrap_or_else(|| Expr::bool_const(is_forall))
        };

        let expr = if safety_guards.is_empty() {
            quantifier_result
        } else {
            safety_guards
                .into_iter()
                .reduce(|lhs, rhs| lhs.and(rhs))
                .expect("invariant: safety_guards is non-empty")
                .and(quantifier_result)
        };

        let base_name = self.ssa_base_name(destination);
        self.env_update(base_name, expr);
        true
    }

    fn extract_bmc_quantifier_captures(&mut self, closure_operand: &Operand) -> Vec<Expr> {
        let closure_local = match closure_operand {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        };
        if let Some(closure_local) = closure_local {
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(place, rvalue) = &stmt.kind
                        && place.local == closure_local
                        && place.projection.is_empty()
                        && let Rvalue::Aggregate(AggregateKind::Closure(_, _), fields) = rvalue
                    {
                        return fields
                            .iter()
                            .filter_map(|field| self.translate_bmc_quantifier_capture(field))
                            .collect();
                    }
                }
            }
        }

        let Some(closure_expr) = self.codegen_operand(closure_operand) else {
            return Vec::new();
        };
        let closure_expr = self.resolve_concrete_expr(&closure_expr);
        if let ay_bindings::ExprValue::DatatypeConstructor { args, .. } = closure_expr.value() {
            return args.clone();
        }

        let Some(dt) = closure_expr.sort().datatype_sort() else {
            return Vec::new();
        };
        let Some(constructor) = dt.constructors.first() else {
            return Vec::new();
        };
        constructor
            .fields
            .iter()
            .map(|field| {
                closure_expr.clone().field_select(&dt.name, &field.name, field.sort.clone())
            })
            .collect()
    }

    fn translate_bmc_quantifier_capture(&mut self, operand: &Operand) -> Option<Expr> {
        if let Operand::Copy(place) | Operand::Move(place) = operand
            && place.projection.is_empty()
        {
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(ref_place, rvalue) = &stmt.kind
                        && ref_place.local == place.local
                        && ref_place.projection.is_empty()
                        && let Rvalue::Ref(_, _, inner_place) = rvalue
                    {
                        let inner_operand = Operand::Copy(inner_place.clone());
                        let expr = self.codegen_operand(&inner_operand)?;
                        return Some(self.resolve_concrete_expr(&expr));
                    }
                }
            }
        }

        let expr = self.codegen_operand(operand)?;
        Some(self.resolve_concrete_expr(&expr))
    }
}
