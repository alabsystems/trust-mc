// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Kani hook/intrinsic call handling for CHC codegen.
//!
//! Thin dispatcher for `KaniHook` variants. Per-group handlers are in
//! `codegen_call_kani_hooks.rs`. Kani model functions (`any`, `offset`,
//! `simd_bitmask`) are in `codegen_call_kani_model.rs`.

use ay_bindings::Expr;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::debug;

use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_kani_model::CallKaniModel;
use super::codegen_rules::CodegenRules;
use super::{ChcCtx, KaniHook, KaniIntrinsic, KaniModel};
use crate::codegen_ay::float_range_check::{
    eval_float_in_int_range, extract_const_float, trace_local_const_float,
};
use crate::codegen_ay::types::{
    POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, int_ty_to_bitvec_width,
    uint_ty_to_bitvec_width,
};
use crate::kani_middle::abi::LayoutOf;

/// Extension trait for Kani hook/intrinsic/model call handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallKani {
    fn codegen_call_kani_hook(&mut self, dcx: &DispatchCallContext<'_>, kani_hook: KaniHook);

    fn codegen_call_kani_intrinsic(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        kani_intrinsic: KaniIntrinsic,
    );
}

impl<'tcx, 'body> CallKani for ChcCtx<'tcx, 'body> {
    /// Dispatch kani hooks to per-group handlers in `codegen_call_kani_hooks.rs`.
    fn codegen_call_kani_hook(&mut self, dcx: &DispatchCallContext<'_>, kani_hook: KaniHook) {
        match kani_hook {
            KaniHook::Assert | KaniHook::Check => self.hook_assert_check(dcx),
            KaniHook::Assume => self.hook_assume(dcx),
            KaniHook::SafetyCheck => self.hook_safety_check(dcx),
            KaniHook::SafetyCheckNoAssume => self.hook_safety_check_no_assume(dcx),
            KaniHook::Panic => self.hook_panic(dcx),
            KaniHook::UnsupportedCheck => self.hook_unsupported_check(dcx),
            KaniHook::IsAllocated => self.hook_is_allocated(dcx),
            KaniHook::PointerObject => self.hook_pointer_object(dcx),
            KaniHook::PointerOffset => self.hook_pointer_offset(dcx),
            KaniHook::AnyRaw => self.hook_any_raw(dcx),
            KaniHook::Forall | KaniHook::Exists => self.hook_quantifier(dcx, kani_hook),
            KaniHook::Cover => self.hook_cover(dcx),
            KaniHook::InitContracts | KaniHook::ValueView | KaniHook::UntrackedDeref => {
                self.hook_noop_transition(dcx, "kani_hook::noop")
            }
            // FC-06: modifies frame markers (contract CHECK mode).
            KaniHook::ModifiesFrameEnter => self.hook_modifies_frame_enter(dcx),
            KaniHook::ModifiesFrameExit => {
                self.hook_noop_transition(dcx, "kani_hook::modifies_frame_exit")
            }
        }
    }

    // Quantifier encoding (build_quantifier_expr, binop_to_expr, closure helpers)
    // moved to chc/quantifier_encoding.rs as proper module — Part of #2306.

    /// Handle Kani intrinsics (IsInitialized, ValidValue, CheckedSizeOf, CheckedAlignOf).
    ///
    /// Part of #1229: IsInitialized and ValidValue are over-approximated as true.
    /// CheckedSizeOf/CheckedAlignOf are handled by MIR transforms and should
    /// not normally appear, but we handle them as nondet for safety.
    fn codegen_call_kani_intrinsic(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        kani_intrinsic: KaniIntrinsic,
    ) {
        let bb_idx = dcx.bb_idx;
        let func = dcx.func;
        let destination = dcx.destination;
        let target = dcx.target;
        let from_app = dcx.from_app;
        let stmt_constraints = dcx.stmt_constraints;
        let modified_locals = dcx.modified_locals;
        match kani_intrinsic {
            // Part of #1229: IsInitialized — over-approximate as always true.
            // Sound: assumes all memory is initialized; may miss uninitialized-memory bugs
            // but prevents false positives in can_dereference / can_read_unaligned.
            KaniIntrinsic::IsInitialized | KaniIntrinsic::ValidValue => {
                self.emit_dest_constrained_to_true(dcx, "IsInitialized");
            }
            // Part of #3212: CheckedSizeOf/CheckedAlignOf — constrain to concrete
            // Some(value) for sized types. MIR transforms should lower these but
            // when the call is not inlined, the intrinsic dispatch sees them.
            KaniIntrinsic::CheckedSizeOf | KaniIntrinsic::CheckedAlignOf => {
                let is_size = matches!(kani_intrinsic, KaniIntrinsic::CheckedSizeOf);
                self.emit_checked_size_or_align(dcx, is_size);
            }
            // Part of #3840: float_to_int_in_range — concrete fast path, nondet fallback.
            KaniIntrinsic::FloatToIntInRange => {
                if let Some(result) = self.try_eval_float_to_int_in_range(dcx) {
                    self.emit_dest_constrained_to_bool(dcx, result, "FloatToIntInRange");
                    return;
                }
                // Symbolic fallback: nondet boolean.
                let dest_local: usize = destination.local;
                if let Some(target) = target {
                    let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                    self.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
                } else {
                    self.record_diverging_call_drop(
                        func,
                        Some(bb_idx),
                        "kani_intrinsic::FloatToIntInRange",
                        None,
                    );
                }
            }
            // Other intrinsics — nondet destination (MIR transforms handle most of these).
            KaniIntrinsic::WriteAny => {
                if let Some(model) = self.write_any_intrinsic_model(dcx) {
                    debug!(
                        "WriteAnyIntrinsic fallback routed to {:?} for pointer side effect",
                        model
                    );
                    self.codegen_call_kani_model(dcx, model);
                    return;
                }
                self.emit_intrinsic_nondet_destination(dcx, "kani_intrinsic::WriteAny");
            }
            KaniIntrinsic::AnyModifies | KaniIntrinsic::AutomaticHarness => {
                // Fail-close for `any_modifies::<T>()` where T dereferences to
                // `str`: upstream Kani rejects these at compile time (`&str`
                // does not implement Arbitrary) and trust-mc has no arbitrary
                // `str` model (mirrors the WriteAnyStr fail-close above). A
                // plain nondet fat pointer here feeds the imprecise str-eq
                // lane and can vacuously satisfy return-value assertions
                // (false-Safe channel unmasked by the Shape A resolver fix).
                if matches!(kani_intrinsic, KaniIntrinsic::AnyModifies)
                    && Self::intrinsic_type_arg_derefs_to_str(func, self.body.locals())
                {
                    self.record_sound_fallback_reason("kani_any_modifies_str_unsupported");
                }
                self.emit_intrinsic_nondet_destination(dcx, "kani_intrinsic::nondet");
            }
        }
    }

    // codegen_call_kani_model and extract_simd_bitmask_lanes moved to
    // codegen_call_kani_model.rs per #2408 (500 LOC decomposition target).
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Whether the callee's first generic type argument dereferences (through
    /// any chain of Ref/RawPtr) to `str`. Used to fail-close `any_modifies`
    /// on `str`-backed types that have no arbitrary-value model.
    fn intrinsic_type_arg_derefs_to_str(
        func: &rustc_public::mir::Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        use rustc_public::ty::GenericArgKind;
        let Ok(func_ty) = func.ty(locals) else { return false };
        let TyKind::RigidTy(RigidTy::FnDef(_, args)) = func_ty.kind() else {
            return false;
        };
        let Some(GenericArgKind::Type(mut ty)) = args.0.first().cloned() else {
            return false;
        };
        for _ in 0..4 {
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Str) => return true,
                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => ty = inner,
                _ => return false,
            }
        }
        false
    }

    fn write_any_intrinsic_model(&self, dcx: &DispatchCallContext<'_>) -> Option<KaniModel> {
        let pointer_arg = dcx.args.first()?;
        let pointer_ty = pointer_arg.ty(self.body.locals()).ok()?;
        let pointee_ty = match pointer_ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _))
            | TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
            _ => return None,
        };
        match pointee_ty.kind() {
            TyKind::RigidTy(RigidTy::Slice(_)) => Some(KaniModel::WriteAnySlice),
            TyKind::RigidTy(RigidTy::Str) => Some(KaniModel::WriteAnyStr),
            _ => Some(KaniModel::WriteAnySlim),
        }
    }

    fn emit_intrinsic_nondet_destination(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        site: &'static str,
    ) {
        let bb_idx = dcx.bb_idx;
        let func = dcx.func;
        let destination = dcx.destination;
        let target = dcx.target;
        let from_app = dcx.from_app;
        let stmt_constraints = dcx.stmt_constraints;
        let modified_locals = dcx.modified_locals;

        let dest_local: usize = destination.local;
        if let Some(target) = target {
            let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
            // Part of #112 Direction 2 step 3: bound nondet output to BV range.
            let mut bounds = self.int_lift_nondet_bounds(dest_local);
            // Part of #3470: Constrain char outputs to valid Unicode scalar values.
            bounds.extend(self.char_nondet_bounds(dest_local));
            // #47: bind each nondet `X__out` head var to a declared FRESH
            // universal variable. Semantically a no-op (the fresh var is
            // unconstrained), but it keeps the out var syntactically
            // CONSTRAINED: chc_const_prop's propagate_to_unconstrained_out_vars
            // assumes "unconstrained __out == identity pass-through" and would
            // otherwise silently UN-HAVOC the destination whenever the incoming
            // value is constant (observed as a false proof on the loop-contract
            // rule's havoc of a constant-initialized loop counter).
            bounds.extend(self.nondet_out_binding_constraints(dest_local));
            if bounds.is_empty() {
                self.emit_goto_rule(from_app, *target, &new_output_args, stmt_constraints);
            } else {
                self.emit_goto_rule_extra(
                    from_app,
                    *target,
                    &new_output_args,
                    stmt_constraints,
                    bounds,
                );
            }
        } else {
            self.record_diverging_call_drop(func, Some(bb_idx), site, None);
        }
    }

    /// #47: `(= X__out __havoc_N)` binding constraints for a nondet
    /// destination (one per flattened field slot), with `__havoc_N` declared
    /// as a fresh universal variable. See `emit_intrinsic_nondet_destination`.
    fn nondet_out_binding_constraints(&mut self, dest_local: usize) -> Vec<Expr> {
        use super::super::codegen_ctx::globals::chc_fresh_name;
        let Some(base_idx) = self.try_state_idx_for_local(dest_local) else {
            return Vec::new();
        };
        let n_fields = if self.flatten.flattened_tuple_locals.contains(&dest_local) {
            self.flattened_field_count(dest_local)
        } else {
            1
        };
        let mut constraints = Vec::with_capacity(n_fields);
        for idx in base_idx..base_idx + n_fields {
            let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(idx) else {
                break;
            };
            let fresh_name = chc_fresh_name("__havoc");
            self.vc.add_var(trust_mc_core::chc::VarDecl {
                name: fresh_name.clone().into(),
                sort: out_sort.clone(),
            });
            let out_var = Expr::var(&**out_name, out_sort.clone());
            constraints.push(out_var.eq(Expr::var(fresh_name, out_sort.clone())));
        }
        constraints
    }

    /// Constrain a call destination to `true` and emit a goto rule.
    /// Part of #3311, #1229: sound over-approximation for Is*Initialized/ValidValue.
    pub(in crate::codegen_ay::chc) fn emit_dest_constrained_to_true(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        site: &'static str,
    ) {
        let dest_local = dcx.destination.local;
        let dest_vec_idx = self.state_idx_for_local(dest_local);
        if let Some(target) = dcx.target {
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
            let dest_var =
                Expr::var(&*self.state_var_mgr.output_state_vars[dest_vec_idx].0, out_sort.clone());
            let eq = self.make_coerced_eq_constraint(
                &dest_var,
                Expr::bool_const(true),
                &out_sort,
                dest_local,
                site,
            );
            self.emit_goto_rule_extra(
                dcx.from_app,
                *target,
                &new_output_args,
                dcx.stmt_constraints,
                eq,
            );
        } else {
            self.record_diverging_call_drop(dcx.func, Some(dcx.bb_idx), site, None);
        }
    }

    /// Handle CheckedSizeOf/CheckedAlignOf intrinsics with concrete values for
    /// sized types and vtable-based values for dyn-trait DSTs. The destination is
    /// `Option<usize>`, which is flattened to `(is_some: Bool, value: BV64)` state
    /// variables.
    ///
    /// Part of #3212: BMC path already handled this via `codegen_checked_size_or_align`
    /// in `intrinsics/memory.rs`, but the CHC path left these as nondet. For sized
    /// pointee types, the nondet `Option<usize>` can be `None`, causing `is_inbounds`
    /// and `is_ptr_aligned` to return false, producing spurious CTREX in `can_write`.
    ///
    /// Part of #3445: For unsized pointee types with trait tails, `abi_align` gives
    /// only the sized prefix alignment. Use vtable metadata ITE for correct values.
    fn emit_checked_size_or_align(&mut self, dcx: &DispatchCallContext<'_>, is_size: bool) {
        let dest_local = dcx.destination.local;

        // Extract pointee type from the pointer argument.
        let pointee_ty = dcx.args.first().and_then(|arg| {
            let ty = arg.ty(self.body.locals()).ok()?;
            match ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
                | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Some(pointee),
                _ => None,
            }
        });

        // Determine the value expression and optional overflow flag.
        // For most cases (sized, dyn-trait, alignment), overflow is impossible.
        // For slice-tail size, overflow is possible and must produce None.
        // Part of #3445: checked_size_with_overflow CTREX fix.
        let value_and_overflow: Option<(Expr, Option<Expr>)> = pointee_ty.and_then(|pointee| {
            let layout = LayoutOf::new(pointee);
            if layout.is_sized() {
                // Sized type: use compile-time constant, no overflow possible.
                let val =
                    if is_size { layout.size_of()? as u128 } else { layout.align_of()? as u128 };
                Some((Expr::bitvec_const(val, POINTER_WIDTH), None))
            } else if layout.has_trait_tail() {
                // Part of #3445: dyn-trait tail — use vtable metadata ITE, no overflow.
                self.compute_checked_dyn_val(dcx, &layout, is_size).map(|v| (v, None))
            } else if layout.has_slice_tail() {
                if is_size {
                    // Part of #3445: slice-tail size with overflow detection.
                    self.compute_checked_slice_size(dcx, &layout)
                        .map(|(val, overflow)| (val, Some(overflow)))
                } else {
                    // Slice tail alignment is compile-time known, no overflow.
                    let val = layout.align_of()? as u128;
                    Some((Expr::bitvec_const(val, POINTER_WIDTH), None))
                }
            } else {
                None
            }
        });

        if let Some((val_expr, overflow_expr)) = value_and_overflow {
            // Destination is flattened Option<usize>: (fld0=is_some: Bool, fld1=value: BV64).
            // Part of #3631: use shared helper for flattened field emission.
            // Replaces manual fld0/fld1 constraint construction that was missing
            // flattened_field_env updates entirely.
            if let Some(target) = dcx.target {
                let is_some = match &overflow_expr {
                    None => Expr::bool_const(true),
                    Some(overflow) => overflow.clone().not(),
                };
                let field_values = vec![
                    Some(self.reshape_flattened_bool_field_for_call(dest_local, 0, is_some)),
                    Some(val_expr),
                ];
                if self.emit_flattened_call_fields(
                    dest_local,
                    &field_values,
                    dcx.from_app,
                    *target,
                    dcx.modified_locals,
                    dcx.stmt_constraints,
                ) {
                    let kind = if is_size { "size" } else { "align" };
                    let has_overflow = overflow_expr.is_some();
                    debug!(
                        dest_local,
                        kind,
                        has_overflow,
                        "CHC checked_{}: Option(expr) for pointee (#3212/#3445/#3631)",
                        kind,
                    );
                    return;
                }
            }
        }

        // Fallback: nondet destination for unsized/foreign types or non-flattened dest.
        let kind = if is_size { "size" } else { "align" };
        debug!(dest_local, kind, "CHC checked_{}: nondet fallback (#3212)", kind);
        if let Some(target) = dcx.target {
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            let mut bounds = self.int_lift_nondet_bounds(dest_local);
            // Part of #3470: Constrain char outputs to valid Unicode scalar values.
            bounds.extend(self.char_nondet_bounds(dest_local));
            if bounds.is_empty() {
                self.emit_goto_rule(dcx.from_app, *target, &new_output_args, dcx.stmt_constraints);
            } else {
                self.emit_goto_rule_extra(
                    dcx.from_app,
                    *target,
                    &new_output_args,
                    dcx.stmt_constraints,
                    bounds,
                );
            }
        } else {
            let site = if is_size {
                "kani_intrinsic::checked_size"
            } else {
                "kani_intrinsic::checked_align"
            };
            self.record_diverging_call_drop(dcx.func, Some(dcx.bb_idx), site, None);
        }
    }

    /// Compute size/align for dyn-trait DSTs via vtable metadata ITE chain.
    /// Used by `emit_checked_size_or_align` for `CheckedSizeOf`/`CheckedAlignOf`
    /// on pointee types with trait tails. Part of #3445.
    fn compute_checked_dyn_val(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        layout: &LayoutOf,
        is_size: bool,
    ) -> Option<Expr> {
        if self.vtable_type_metadata.is_empty() {
            return None;
        }
        let vtable_disc = super::codegen_call_kani_model_dyn::extract_vtable_disc_from_ptr_arg(
            self,
            dcx.args,
            dcx.modified_locals,
        )?;
        let dyn_align = super::codegen_call_kani_model_dyn::build_vtable_metadata_ite(
            self,
            &vtable_disc,
            false,
        );
        let head_align = Expr::bitvec_const(layout.align_of_head() as u64, POINTER_WIDTH);
        // align = max(dyn_align, head_align)
        let align = Expr::ite(dyn_align.clone().bvugt(head_align.clone()), dyn_align, head_align);

        if !is_size {
            debug!("compute_checked_dyn_val: align via vtable ITE (#3445)");
            return Some(align);
        }
        // Size: compute aligned total = (dyn_size + head_size) rounded up to align.
        let dyn_size =
            super::codegen_call_kani_model_dyn::build_vtable_metadata_ite(self, &vtable_disc, true);
        let head_size = Expr::bitvec_const(layout.size_of_head() as u64, POINTER_WIDTH);
        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let total = dyn_size.bvadd(head_size);
        let adjust = total.bvadd(align.clone().bvsub(one));
        let adjusted_size = adjust.bvand(zero.bvsub(align));
        debug!("compute_checked_dyn_val: size via vtable ITE (#3445)");
        Some(adjusted_size)
    }

    /// Compute size for slice-tail DSTs: round_up(elem_size * len + head_size, align).
    /// Uses compile-time layout constants + runtime slice length from fat pointer metadata.
    /// Part of #3445.
    /// Compute slice-tail size with overflow detection.
    ///
    /// Returns `(adjusted_size, any_overflow)` where `any_overflow` is a Bool
    /// expression that is true when the size computation overflows. This matches
    /// the semantics of `codegen_size_of_slice_object` in codegen_call_kani_model_dst.rs.
    ///
    /// Part of #3445: checked_size_with_overflow CTREX fix.
    fn compute_checked_slice_size(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        layout: &LayoutOf,
    ) -> Option<(Expr, Expr)> {
        let elem_ty = layout.unsized_tail_elem_ty()?;
        let elem_size_val = LayoutOf::new(elem_ty).size_of()? as u64;
        let head_size_val = layout.size_of_head() as u64;
        let align_val = layout.align_of()? as u64;

        // Extract slice length from the fat pointer argument.
        let len = super::codegen_call_kani_model_dst::extract_fat_ptr_len(
            self,
            dcx.args,
            dcx.modified_locals,
        )?;
        let len = coerce_bitvec_width_safe(len, POINTER_WIDTH, SignExtension::ZeroExtend);

        let elem_size = Expr::bitvec_const(elem_size_val, POINTER_WIDTH);
        let head_size = Expr::bitvec_const(head_size_val, POINTER_WIDTH);
        let align = Expr::bitvec_const(align_val, POINTER_WIDTH);
        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);

        // Compute slice_sz = elem_size * len
        let slice_sz = elem_size.clone().bvmul(len.clone());

        // Overflow check 1: multiplication overflow (elem_size * len wraps)
        let mul_overflow = elem_size
            .clone()
            .eq(zero.clone())
            .not()
            .and(len.eq(zero.clone()).not())
            .and(slice_sz.clone().bvult(elem_size));

        // Compute total = slice_sz + head_size
        let total = slice_sz.clone().bvadd(head_size);

        // Overflow check 2: addition overflow (slice_sz + head_size wraps)
        let sum_overflow = total.clone().bvult(slice_sz);

        // Compute adjust = total + (align - 1)
        let align_sub_1 = align.clone().bvsub(one);
        let adjust = total.clone().bvadd(align_sub_1);

        // Overflow check 3: alignment adjustment overflow
        let adjust_overflow = adjust.clone().bvult(total);

        // adjusted_size = adjust & align.wrapping_neg()
        let align_neg = zero.bvsub(align);
        let adjusted_size = adjust.bvand(align_neg);

        // Overflow check 4: isize::MAX overflow
        let isize_max = Expr::bitvec_const(i64::MAX as u64, POINTER_WIDTH);
        let size_overflow = adjusted_size.clone().bvugt(isize_max);

        // Combined overflow
        let any_overflow = mul_overflow.or(sum_overflow).or(adjust_overflow).or(size_overflow);

        debug!(
            elem_size_val,
            head_size_val, align_val, "compute_checked_slice_size with overflow checks (#3445)"
        );
        Some((adjusted_size, any_overflow))
    }

    /// Constrain a call destination to a specific boolean value and emit a goto rule.
    /// Part of #3840: concrete float_to_int_in_range evaluation.
    fn emit_dest_constrained_to_bool(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        value: bool,
        site: &'static str,
    ) {
        let dest_local = dcx.destination.local;
        let dest_vec_idx = self.state_idx_for_local(dest_local);
        if let Some(target) = dcx.target {
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
            let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
            let dest_var =
                Expr::var(&*self.state_var_mgr.output_state_vars[dest_vec_idx].0, out_sort.clone());
            let eq = self.make_coerced_eq_constraint(
                &dest_var,
                Expr::bool_const(value),
                &out_sort,
                dest_local,
                site,
            );
            self.emit_goto_rule_extra(
                dcx.from_app,
                *target,
                &new_output_args,
                dcx.stmt_constraints,
                eq,
            );
        } else {
            self.record_diverging_call_drop(dcx.func, Some(dcx.bb_idx), site, None);
        }
    }

    /// Try to evaluate `float_to_int_in_range` at codegen time from MIR constants.
    /// Part of #3840: concrete fast path for the CHC encoding.
    fn try_eval_float_to_int_in_range(&self, dcx: &DispatchCallContext<'_>) -> Option<bool> {
        // Extract Float and Int types from function generic args.
        let func_ty = dcx.func.ty(self.body.locals()).ok()?;
        let fn_args = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(_, args)) => args,
            _ => return None,
        };
        let (float_ty, int_ty) = match (fn_args.0.first(), fn_args.0.get(1)) {
            (Some(GenericArgKind::Type(ft)), Some(GenericArgKind::Type(it))) => (*ft, *it),
            _ => return None,
        };

        // Extract concrete float value from the first argument.
        // MIR often passes the float via Move/Copy of a local, not as an inline
        // constant. Try direct constant extraction first, then trace through
        // the local's assignment to find the original constant.
        let operand = dcx.args.first()?;
        let (value_f64, mantissa_bits) = extract_const_float(operand, &float_ty)
            .or_else(|| trace_local_const_float(&self.body.blocks, operand, &float_ty))?;

        // Determine target integer width and signedness.
        let (width, signed) = match int_ty.kind() {
            TyKind::RigidTy(RigidTy::Int(it)) => (int_ty_to_bitvec_width(it), true),
            TyKind::RigidTy(RigidTy::Uint(ut)) => (uint_ty_to_bitvec_width(ut), false),
            _ => return None,
        };

        let result = eval_float_in_int_range(value_f64, mantissa_bits, width, signed);
        if let Some(r) = result {
            debug!(
                "CHC float_to_int_in_range: {:?} -> {:?}, concrete = {} (#3840)",
                float_ty, int_ty, r
            );
        }
        result
    }
}
