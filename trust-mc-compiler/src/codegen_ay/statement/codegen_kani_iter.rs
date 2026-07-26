// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Iterator/closure/special function call handlers (converted from include!() per #2595).
// Iterator, closure, and special function call handlers extracted from
// codegen_kani_call.rs (#2246).
//
// Handles fn_name-based dispatch for:
// - IndexRange (zero_to, new_unchecked, next_unchecked)
// - PolymorphicIter (new_unchecked, len, next)
// - ExactSizeIterator::len
// - IntoIterator::into_iter (arrays)
// - Iterator::next
// - ManuallyDrop::new
// - SliceIndex::index
// - FnOnce::call_once, Fn::call, FnMut::call_mut
// - Option::map

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::names::struct_sort;
use crate::codegen_ay::statement::dispatch::CallDispatchOutcome;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Record a BMC violation for the compile-time type-validity assertions
    /// `assert_inhabited` / `assert_zero_valid` / `assert_mem_uninitialized_valid`
    /// when rustc definitively proves the target type is invalid for the
    /// requirement. A pure no-op for satisfiable / undecidable / parametric
    /// types, so `mem::zeroed::<u32>()` is never flagged. Mirrors the CHC
    /// `codegen_assert_validity` handler.
    fn maybe_emit_assert_validity_violation(&mut self, instance: &Instance, intrinsic_name: &str) {
        let Some(requirement) =
            crate::kani_middle::type_validity::validity_requirement_for_intrinsic(intrinsic_name)
        else {
            return;
        };
        let Some(ty) = instance
            .args()
            .0
            .iter()
            .find_map(|arg| if let GenericArgKind::Type(t) = arg { Some(*t) } else { None })
        else {
            return;
        };
        if matches!(ty.kind(), TyKind::Param(_)) {
            return;
        }
        if crate::kani_middle::type_validity::assert_requirement_definitely_violated(
            self.ctx.tcx,
            ty,
            requirement,
        ) {
            debug!(intrinsic_name, "BMC: assert_* type-validity violated — recording violation");
            self.record_violation_guarded(Expr::bool_const(true), "assert_type_validity");
        }
    }

    /// Try to codegen a function call by name-based dispatch.
    ///
    /// This handles known library functions that are not tagged with Kani markers
    /// but need special codegen treatment: iterators, closures, trait methods, etc.
    ///
    /// Returns an explicit dispatch outcome so handled calls cannot collapse
    /// back into the same `None` shape as a miss.
    ///
    /// REQUIRES: fn_name is the resolved callee path or def name
    /// REQUIRES: instance_opt is the resolved Instance if available
    #[allow(clippy::collapsible_if)]
    pub(super) fn try_codegen_named_call(
        &mut self,
        fn_name: &str,
        instance_opt: &Option<Instance>,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> CallDispatchOutcome {
        // Check for InstanceKind::Intrinsic - direct calls to core::intrinsics::*
        if let Some(instance) = instance_opt
            && matches!(instance.kind, InstanceKind::Intrinsic)
            && let Some(intrinsic_name) = instance.intrinsic_name()
        {
            debug!("AY codegen: handling InstanceKind::Intrinsic: {}", intrinsic_name);
            // Compile-time type-validity assertions (assert_inhabited /
            // assert_zero_valid / assert_mem_uninitialized_valid): record a UB
            // violation when rustc proves the type is invalid, then fall through
            // to the existing no-op handler for control flow. Parity with CHC.
            self.maybe_emit_assert_validity_violation(instance, &intrinsic_name);
            let outcome =
                self.try_codegen_std_intrinsic(&intrinsic_name, args, destination, target);
            if !matches!(outcome, CallDispatchOutcome::Miss) {
                return outcome;
            }
        }

        // Fallback: check by function name for known unmarked kani functions
        debug!("try_codegen_named_call: fn_name = {:?}", fn_name);
        if fn_name.contains("kani::")
            && (fn_name.contains("any_raw_internal") || fn_name.contains("any_raw_array"))
        {
            debug!("AY codegen: handling unmarked kani function {}", fn_name);
            self.codegen_kani_any_raw(destination);
            return CallDispatchOutcome::from_handled_target(target);
        }
        if fn_name.contains("kani::") && fn_name.contains("Arbitrary") && fn_name.contains("::any")
        {
            debug!("AY codegen: handling Arbitrary::any impl {}", fn_name);
            self.codegen_kani_any_raw(destination);
            return CallDispatchOutcome::from_handled_target(target);
        }
        if fn_name.contains("kani::")
            && (fn_name.contains("kani_force_fn_once_with_args")
                || fn_name.contains("kani_force_fn_once"))
        {
            if let Some(closure_expr) = args.first().and_then(|arg| self.codegen_operand(arg)) {
                self.assign_value_to_place(destination, closure_expr);
            } else {
                self.codegen_symbolic_result(destination);
            }
            return CallDispatchOutcome::from_handled_target(target);
        }
        if fn_name.contains("kani::") && fn_name.contains("kani_register_contract") {
            return CallDispatchOutcome::from_handled_target(self.codegen_closure_call(
                func,
                args,
                destination,
                target,
            ));
        }

        // Handle std library intrinsics
        let outcome = self.try_codegen_std_intrinsic(fn_name, args, destination, target);
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }

        // #468: Handle iterator functions for arrays with known bounds.
        if fn_name.contains("ExactSizeIterator")
            && fn_name.contains("::len")
            && !args.is_empty()
            && let Some(iter_ty) = args[0].ty(self.body.locals()).into_option()
            && let Some(array_len) = Self::extract_array_iter_len(iter_ty)
        {
            debug!("codegen ExactSizeIterator::len: array length = {}", array_len);
            let base_name = self.ssa_base_name(destination);
            let len_expr = Expr::bitvec_const(array_len as u128, POINTER_WIDTH);
            self.env_update(base_name, len_expr);
            return CallDispatchOutcome::from_handled_target(target);
        }

        // #468: IndexRange helpers for array iterators.
        if fn_name.contains("IndexRange") && fn_name.contains("zero_to") {
            debug!("MATCHED IndexRange::zero_to");
            if let Some(end_expr) = args.first().and_then(|arg| self.codegen_operand(arg))
                && let Some(range_ty) = destination.ty(self.body.locals()).into_option()
            {
                let zero_expr = Expr::bitvec_const(
                    0u128,
                    end_expr.sort().bitvec_width().unwrap_or(POINTER_WIDTH),
                );
                if let Some(range_expr) = self.build_index_range_expr(range_ty, zero_expr, end_expr)
                {
                    debug!("IndexRange::zero_to: SUCCESS");
                    let base_name = self.ssa_base_name(destination);
                    self.env_update(base_name, range_expr);
                    return CallDispatchOutcome::from_handled_target(target);
                }
            }
        }

        if fn_name.contains("IndexRange")
            && fn_name.contains("new_unchecked")
            && args.len() >= 2
            && let (Some(start_expr), Some(end_expr)) =
                (self.codegen_operand(&args[0]), self.codegen_operand(&args[1]))
            && let Some(range_ty) = destination.ty(self.body.locals()).into_option()
            && let Some(range_expr) = self.build_index_range_expr(range_ty, start_expr, end_expr)
        {
            let base_name = self.ssa_base_name(destination);
            self.env_update(base_name, range_expr);
            return CallDispatchOutcome::from_handled_target(target);
        }

        // #468: Handle IndexRange::next_unchecked
        if fn_name.contains("IndexRange") && fn_name.contains("next_unchecked") {
            debug!("MATCHED IndexRange::next_unchecked");
            if let Some(arg0) = args.first() {
                if let Some((range_base, range_sort)) = self.get_ref_pointee_sort(arg0)
                    && let Some(range_expr) = self.env_lookup(&range_base).cloned()
                {
                    if range_expr.sort().is_datatype() {
                        let start_expr =
                            range_expr.clone().field_select("IndexRange", "fld_start", ptr_sort());
                        let end_expr = range_expr.field_select("IndexRange", "fld_end", ptr_sort());
                        let base_name = self.ssa_base_name(destination);
                        let one = Expr::bitvec_const(1u128, POINTER_WIDTH);
                        let new_start = start_expr.clone().bvadd(one);
                        self.env_update(base_name, start_expr);
                        let cons_name =
                            range_sort.datatype_default_constructor().unwrap_or("IndexRange_mk");
                        let updated_range = Expr::datatype_constructor(
                            "IndexRange",
                            cons_name,
                            vec![new_start, end_expr],
                            range_sort.clone(),
                        );
                        self.env_update(range_base, updated_range);
                        debug!("IndexRange::next_unchecked: SUCCESS");
                        return CallDispatchOutcome::from_handled_target(target);
                    }
                }
            }
        }

        // #468: Handle ExactSizeIterator::len for IndexRange
        if fn_name.contains("ExactSizeIterator") && fn_name.contains("::len") {
            debug!("MATCHED ExactSizeIterator::len");
            if let Some(arg0) = args.first() {
                if let Some(arg_ty) = arg0.ty(self.body.locals()).into_option() {
                    let mut inner_ty = arg_ty;
                    while let TyKind::RigidTy(RigidTy::Ref(_, next_ty, _)) = inner_ty.kind() {
                        inner_ty = next_ty;
                    }
                    if let TyKind::RigidTy(RigidTy::Adt(def, _)) = inner_ty.kind()
                        && def.trimmed_name() == "IndexRange"
                        && let Some((range_base, _)) = self.get_ref_pointee_sort(arg0)
                        && let Some(range_expr) = self.env_lookup(&range_base).cloned()
                    {
                        if range_expr.sort().is_datatype() {
                            let start_expr = range_expr.clone().field_select(
                                "IndexRange",
                                "fld_start",
                                ptr_sort(),
                            );
                            let end_expr =
                                range_expr.field_select("IndexRange", "fld_end", ptr_sort());
                            let len_expr = end_expr.bvsub(start_expr);
                            let base_name = self.ssa_base_name(destination);
                            self.env_update(base_name, len_expr);
                            debug!("ExactSizeIterator::len: SUCCESS");
                            return CallDispatchOutcome::from_handled_target(target);
                        }
                    }
                }
            }
        }

        if fn_name.contains("PolymorphicIter") && fn_name.contains("new_unchecked") {
            debug!("MATCHED PolymorphicIter::new_unchecked");
            if args.len() >= 2
                && let (Some(alive_expr), Some(data_expr)) =
                    (self.codegen_operand(&args[0]), self.codegen_operand(&args[1]))
                && let Some(iter_ty) = destination.ty(self.body.locals()).into_option()
                && let Some(iter_expr) =
                    self.build_polymorphic_iter_expr(iter_ty, alive_expr, data_expr)
            {
                debug!("PolymorphicIter::new_unchecked: SUCCESS");
                let base_name = self.ssa_base_name(destination);
                self.env_update(base_name, iter_expr);
                return CallDispatchOutcome::from_handled_target(target);
            }
        }

        if fn_name.contains("IntoIter")
            && (fn_name.contains("unsize_mut") || fn_name.contains("unsize"))
            && let Some(arg0) = args.first()
            && let Operand::Copy(place) | Operand::Move(place) = arg0
        {
            let ref_base = self.ssa_base_name(place);
            if let Some(pointee_base) = self.ref_pointees.get(ref_base.as_str()).cloned() {
                let inner_base = crate::codegen_ay::names::indexed_field_name(&pointee_base, 0);
                let dest_base = self.ssa_base_name(destination);
                self.ref_pointees.insert(
                    std::sync::Arc::from(dest_base),
                    std::sync::Arc::from(inner_base.as_str()),
                );
                if self.env_lookup(&inner_base).is_none()
                    && let Some(intoiter_expr) = self.env_lookup(&pointee_base).cloned()
                    && let Some(intoiter_ty) = place.ty(self.body.locals()).into_option()
                    && let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = intoiter_ty.kind()
                    && let TyKind::RigidTy(RigidTy::Adt(def, args)) = inner.kind()
                {
                    let adt_name = Self::adt_sort_name(def, &args);
                    if let Some(concrete_ty) =
                        Self::resolve_generic_ty(def.variants()[0].fields()[0].ty(), &args)
                        && let Some(inner_sort) = Self::infer_sort_from_ty(concrete_ty)
                    {
                        if intoiter_expr.sort().is_datatype() {
                            let inner_expr =
                                intoiter_expr.field_select(adt_name, "fld_inner", inner_sort);
                            self.env_update(inner_base, inner_expr);
                        }
                    }
                }
                return CallDispatchOutcome::from_handled_target(target);
            }
        }

        if fn_name.contains("PolymorphicIter")
            && fn_name.contains("::len")
            && let Some((iter_base, iter_ty)) = self.iter_base_from_operand(args.first())
            && let Some(iter_expr) = self.env_lookup(&iter_base).cloned()
            && let Some(len_expr) = self.polymorphic_iter_len_expr(&iter_expr, iter_ty)
        {
            let base_name = self.ssa_base_name(destination);
            self.env_update(base_name, len_expr);
            return CallDispatchOutcome::from_handled_target(target);
        }

        if fn_name.contains("PolymorphicIter")
            && fn_name.contains("::next")
            && let Some((iter_base, iter_ty)) = self.iter_base_from_operand(args.first())
            && let Some(iter_expr) = self.env_lookup(&iter_base).cloned()
            && let Some((next_expr, updated_iter)) =
                self.polymorphic_iter_next_expr(&iter_expr, iter_ty, destination)
        {
            self.env_update(iter_base, updated_iter);
            let base_name = self.ssa_base_name(destination);
            self.env_update(base_name, next_expr);
            return CallDispatchOutcome::from_handled_target(target);
        }

        // #468: Handle ManuallyDrop::new - identity function.
        if fn_name.contains("ManuallyDrop")
            && fn_name.contains("::new")
            && let Some(arg) = args.first()
            && let Some(arg_expr) = self.codegen_operand(arg)
        {
            debug!("codegen ManuallyDrop::new: passing through {:?}", arg_expr.sort());
            let base_name = self.ssa_base_name(destination);
            self.env_update(base_name, arg_expr);
            return CallDispatchOutcome::from_handled_target(target);
        }

        // #468: Handle IntoIterator::into_iter for arrays.
        if fn_name.contains("IntoIterator")
            && fn_name.contains("into_iter")
            && let Some(arg) = args.first()
            && let Some(arg_ty) = arg.ty(self.body.locals()).into_option()
        {
            if let TyKind::RigidTy(RigidTy::Array(elem_ty, const_len)) = arg_ty.kind()
                && let Some(len) = const_len.eval_target_usize().into_option()
            {
                debug!("codegen IntoIterator::into_iter for [{}; {}]", elem_ty, len);
                if let Some(dest_ty) = destination.ty(self.body.locals()).into_option()
                    && let Some(iter_expr) =
                        self.build_array_into_iter_expr(dest_ty, arg, elem_ty, len)
                {
                    let base_name = self.ssa_base_name(destination);
                    self.env_update(base_name, iter_expr);
                    return CallDispatchOutcome::from_handled_target(target);
                }
            }
        }

        // #468: Handle Iterator::next trait method.
        if fn_name.contains("Iterator")
            && fn_name.contains("::next")
            && !fn_name.contains("PolymorphicIter")
            && let Some((iter_base, iter_ty)) = self.iter_base_from_operand(args.first())
        {
            let inner_ty = match iter_ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, args))
                    if def.0.name().contains("ManuallyDrop") =>
                {
                    args.0
                        .iter()
                        .find_map(|arg| {
                            if let rustc_public::ty::GenericArgKind::Type(ty) = arg {
                                Some(*ty)
                            } else {
                                None
                            }
                        })
                        .unwrap_or(iter_ty)
                }
                _ => iter_ty, // external enum: TyKind
            };
            if let Some(iter_expr) = self.env_lookup(&iter_base).cloned()
                && let Some((next_expr, updated_iter)) =
                    self.polymorphic_iter_next_expr(&iter_expr, inner_ty, destination)
            {
                self.env_update(iter_base, updated_iter);
                let base_name = self.ssa_base_name(destination);
                self.env_update(base_name, next_expr);
                return CallDispatchOutcome::from_handled_target(target);
            }
        }

        // #408: Handle SliceIndex::index for ZST elements.
        if fn_name.contains("SliceIndex") && fn_name.contains("::index") {
            if let Some(dest_ty) = destination.ty(self.body.locals()).into_option() {
                let is_zst_result = match dest_ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => Self::is_zst_type(inner),
                    _ => Self::is_zst_type(dest_ty), // external enum: TyKind
                };
                if is_zst_result {
                    debug!("codegen SliceIndex::index: ZST result, returning phantom value");
                    let base_name = self.ssa_base_name(destination);
                    let unit_sort = struct_sort("Unit", Vec::<(&str, Sort)>::new());
                    // Constructor name is always "Unit_mk" per struct_type convention.
                    let unit_value =
                        Expr::datatype_constructor("Unit", "Unit_mk", vec![], unit_sort);
                    self.env_update(base_name, unit_value);
                    return CallDispatchOutcome::from_handled_target(target);
                }
            }
        }

        // #478: Handle FnOnce::call_once for closure invocation.
        // Part of #3317: namespace guard — FnOnce is in core::ops::function.
        if fn_name.contains("ops::") && fn_name.contains("FnOnce") && fn_name.contains("call_once")
        {
            debug!("MATCHED FnOnce::call_once");
            return CallDispatchOutcome::from_handled_target(self.codegen_closure_call(
                func,
                args,
                destination,
                target,
            ));
        }

        // Also handle Fn::call and FnMut::call_mut
        // Part of #3317: namespace guard — Fn/FnMut are in core::ops::function.
        if fn_name.contains("ops::")
            && ((fn_name.contains("::Fn") && fn_name.contains("::call"))
                || (fn_name.contains("FnMut") && fn_name.contains("call_mut")))
        {
            debug!("AY codegen: handling Fn/FnMut closure call");
            return CallDispatchOutcome::from_handled_target(self.codegen_closure_call(
                func,
                args,
                destination,
                target,
            ));
        }

        // #478: Handle Option::map
        // Part of #3317: namespace guard — Option is in core::option.
        if fn_name.contains("core::") && fn_name.contains("Option") && fn_name.contains("::map") {
            debug!("AY codegen: handling Option::map");
            return CallDispatchOutcome::from_handled_target(self.codegen_option_map(
                args,
                destination,
                target,
            ));
        }

        // Sound bounded-unroll of Iterator::all / Iterator::any (replaces the
        // unsupported-call HAVOC that skipped the predicate closure entirely).
        // The handler is fail-closed: it preserves the prior over-approximation
        // (and demotes) whenever it cannot soundly unroll. See
        // `codegen_iter_all_any`.
        // Match the terminal method token robustly: monomorphized callee paths
        // appear as `<Slice::Iter<..> as ..Iterator>::all` (i.e. `Iterator>::all`)
        // as well as the trait path `..Iterator::all`, so key off the last `::`
        // segment (with any generic suffix stripped) plus an `Iterator` marker.
        let iter_method = if fn_name.contains("Iterator") {
            fn_name
                .rsplit("::")
                .next()
                .map(|m| m.split(['<', '(']).next().unwrap_or(m).trim_end_matches('>'))
        } else {
            None
        };
        if iter_method == Some("all") {
            debug!(%fn_name, "AY codegen: handling Iterator::all via sound bounded unroll");
            return CallDispatchOutcome::from_handled_target(self.codegen_iter_all_any(
                args,
                destination,
                target,
                true,
            ));
        }
        if iter_method == Some("any") {
            debug!(%fn_name, "AY codegen: handling Iterator::any via sound bounded unroll");
            return CallDispatchOutcome::from_handled_target(self.codegen_iter_all_any(
                args,
                destination,
                target,
                false,
            ));
        }

        // Not a recognized function
        if fn_name.contains("exchange") || fn_name.contains("alloc::alloc") {
            debug!("try_codegen_named_call: returning None for fn_name={}", fn_name);
        }
        CallDispatchOutcome::Miss
    }
}
