// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Semantic Layout construction for LayoutNew/LayoutForValueRaw/LayoutArray/LayoutFromSizeAlign{,Unchecked}.
//! Part of #2408 S1: codegen_call_misc decomposition.

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};
use crate::kani_middle::abi::LayoutOf;

use super::super::ChcCtx;
use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_rules::CodegenRules;
use super::super::stubs_option_helpers::OptionHelpers;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Semantic Layout construction for LayoutNew/LayoutForValueRaw/LayoutArray/LayoutFromSizeAlign{,Unchecked}.
    /// Constructs bv128 = concat(size:bv64, align:bv64) using compile-time type info.
    /// Part of #1739 (Bug 1: Layout left fully symbolic by unconstrained stub).
    pub(in crate::codegen_ay::chc) fn codegen_call_layout_semantic_impl(
        &mut self,
        func: &Operand,
        cx: &ChcCallContext<'_>,
    ) {
        let stub = cx.stub;
        let args = cx.args;
        let destination = cx.destination;
        let target = cx.target;
        let from_app = cx.from_app;
        let stmt_constraints = cx.stmt_constraints;
        let modified_locals = cx.modified_locals;
        let dest_local: usize = destination.local;

        // Extract T's compile-time size and align from the function's generic args.
        // LayoutNew<T>(), LayoutForValueRaw<T>(), and LayoutArray<T>(n) have T as the first generic arg.
        let func_ty = func.ty(self.body.locals()).ok();
        let (type_size, type_align) = {
            let mut result: Option<(u64, u64)> = None;
            let mut is_dyn_unsized = false;
            let mut found_type_arg = false;
            if let Some(ty) = func_ty {
                if let TyKind::RigidTy(RigidTy::FnDef(_, fn_args)) = ty.kind()
                    && let Some(GenericArgKind::Type(element_ty)) = fn_args.0.first()
                {
                    found_type_arg = true;
                    // Try compile-time layout for sized types.
                    if element_ty.layout().is_ok() {
                        let layout = LayoutOf::new(*element_ty);
                        if let (Some(size), Some(align)) = (layout.size_of(), layout.align_of()) {
                            result = Some((size as u64, align as u64));
                        }
                    }
                    // Part of #3159: For unsized dyn Trait types, use vtable_type_metadata
                    // to get the concrete type's actual layout. Without this, dyn Trait
                    // types fall through to the (8, 8) default, causing dealloc size
                    // mismatches: alloc records the concrete type's size (e.g. 12) but
                    // dealloc expects pointer-width (8).
                    // Part of #3347: Check vtable_type_metadata first (correct
                    // vtable_id→layout entries from translation pass), then fall
                    // back to predeclared_concrete_layouts (from pre-declaration
                    // pass, before vtable IDs are assigned).
                    if result.is_none()
                        && matches!(element_ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)))
                    {
                        if let Some((_, &(size, align))) = self.vtable_type_metadata.iter().next() {
                            result = Some((size, align));
                        } else if let Some(&(size, align)) =
                            self.predeclared_concrete_layouts.first()
                        {
                            result = Some((size, align));
                        } else {
                            is_dyn_unsized = true;
                        }
                    }
                }
            }
            // Part of #3589: Catch-all for unresolved unsized layouts.
            // ADTs containing dyn Trait parameters (e.g., Outer<dyn Identity>)
            // are unsized but don't match the TyKind::Dynamic(..) check at L68.
            // Without this, result falls through to the (8, 8) default,
            // causing false CTREX from dealloc size mismatch.
            // Guard: only trigger when we found a type arg but couldn't resolve
            // its layout. Stubs that take explicit args (LayoutFromSizeAlign*,
            // LayoutArrayInner) have no generic type param and must reach their
            // match arms instead of short-circuiting to unconstrained fallback.
            if result.is_none() && found_type_arg {
                is_dyn_unsized = true;
            }
            // Part of #3589: For LayoutForValueRaw on unsized types, compute
            // the layout dynamically using obj_size[obj_id] from the pointer
            // argument. This matches what the alloc recorded, so the dealloc
            // size-match check passes instead of producing false CTREX.
            // Falls back to unconstrained if the pointer arg can't be resolved.
            if is_dyn_unsized && result.is_none() {
                if matches!(stub, StubKind::LayoutForValueRaw) {
                    let ptr_resolved = args
                        .first()
                        .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals))
                        .and_then(|ptr| self.split_pointer(&ptr));
                    if let Some((obj_id_expr, _offset)) = ptr_resolved {
                        let obj_size_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(32));
                        let obj_size_in = Expr::var("obj_size", obj_size_sort);
                        let dynamic_size = obj_size_in.select(obj_id_expr);
                        let size_64 =
                            coerce_bitvec_width_safe(dynamic_size, 64, SignExtension::ZeroExtend);
                        let align_64 = Expr::bitvec_const(1i64, 64);
                        let layout_bv128 = size_64.concat(align_64);

                        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                            let eq = self.make_coerced_eq_constraint(
                                &dest_var,
                                layout_bv128,
                                dest_var.sort(),
                                dest_local,
                                "layout_for_value_raw_dyn",
                            );
                            if eq.is_some() {
                                self.mark_heap_metadata_read();
                                let new_output_args =
                                    self.build_output_args(modified_locals, &[dest_local]);
                                let extras: Vec<Expr> = eq.into_iter().collect();
                                self.emit_goto_rule_extra(
                                    from_app,
                                    target,
                                    &new_output_args,
                                    stmt_constraints,
                                    extras,
                                );
                                return;
                            }
                        }
                    }
                }
                // Fallback: leave destination unconstrained (sound over-approximation).
                // Part of #3159: Hardcoding (8, 8) causes false CTREX.
                emit_sound_fallback_goto(
                    self,
                    from_app,
                    target,
                    modified_locals,
                    &[dest_local],
                    stmt_constraints,
                );
                return;
            }
            result.unwrap_or((8, 8))
        };

        // Part of #3408: overflow guard for checked_mul in Layout::array.
        // When set, Ok path only fires when no overflow (sound).
        let mut overflow_guard: Option<Expr> = None;
        let layout_bv128 = match stub {
            StubKind::LayoutNew | StubKind::LayoutForValueRaw => {
                // Layout::new::<T>() / Layout::for_value_raw::<T>()
                // -> concat(size_of::<T>(), align_of::<T>())
                // for_value_raw has the same semantics for Sized types (Part of #3184).
                Expr::bitvec_const(type_size, 64).concat(Expr::bitvec_const(type_align, 64))
            }
            StubKind::LayoutArray => {
                // Layout::array::<T>(n) -> concat(size_of::<T>() * n, align_of::<T>())
                // Count `n` is the first call argument (confirmed: alloc_layout.rs:192).
                let count_expr = args
                    .first()
                    .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals));
                if let Some(n) = count_expr {
                    let size_per = Expr::bitvec_const(type_size, 64);
                    let n_coerced = coerce_bitvec_width_safe(n, 64, SignExtension::ZeroExtend);
                    // Part of #2992: Post-coercion BV check — non-BV count causes
                    // sort mismatch in bvmul.
                    if n_coerced.sort().bitvec_width().is_none() {
                        warn!(sort = ?n_coerced.sort(), "LayoutArray: non-BV count after coercion (#2992)");
                        // Non-BV count — translation failure (Part of #3123).
                        emit_sound_fallback_goto(
                            self,
                            from_app,
                            target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                        );
                        return;
                    }
                    let total_size = size_per.bvmul(n_coerced.clone());
                    // Part of #3408: Rust Layout::array uses checked_mul.
                    // Guard Ok path: total_size / size == n (no wrapping).
                    if type_size > 0 {
                        overflow_guard = Some(
                            total_size
                                .clone()
                                .bvudiv(Expr::bitvec_const(type_size, 64))
                                .eq(n_coerced),
                        );
                    }
                    total_size.concat(Expr::bitvec_const(type_align, 64))
                } else {
                    // LayoutArray count arg not translatable (Part of #3123).
                    emit_sound_fallback_goto(
                        self,
                        from_app,
                        target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                    return;
                }
            }
            StubKind::LayoutArrayInner => {
                // Part of #3273: Layout::array::inner(element_size, align, n)
                // Unlike LayoutArray which gets T from generics, inner() takes raw usize args.
                // Part of #3677: Handle both 3-arg (elem_size, align, n) and 2-arg
                // (packed_layout, n) calling conventions. When MIR inlines
                // Layout::array, the call may pass a packed Layout as arg0.
                let (elem_size_expr, align_expr, n) = if args.len() >= 3 {
                    // 3-arg form: (elem_size, align, n)
                    let es = args.first().and_then(|arg| {
                        self.translate_operand_with_modified(arg, modified_locals)
                            .or_else(|| self.resolve_layout_operand_expr(arg, modified_locals))
                    });
                    let al = args.get(1).and_then(|arg| {
                        self.translate_operand_with_modified(arg, modified_locals)
                            .or_else(|| self.resolve_layout_operand_expr(arg, modified_locals))
                    });
                    let ct = args.get(2).and_then(|arg| {
                        self.translate_operand_with_modified(arg, modified_locals)
                            .or_else(|| self.resolve_layout_operand_expr(arg, modified_locals))
                    });
                    (es, al, ct)
                } else if args.len() == 2 {
                    // 2-arg form: (packed_layout, n) — extract size/align from bv128.
                    // Part of #3677: resolve_layout_operand_expr handles pointer deref
                    // + layout cache recovery; translate_operand alone short-circuits.
                    let layout_expr = args
                        .first()
                        .and_then(|arg| self.resolve_layout_operand_expr(arg, modified_locals));
                    let ct = args.get(1).and_then(|arg| {
                        self.translate_operand_with_modified(arg, modified_locals)
                            .or_else(|| self.resolve_layout_operand_expr(arg, modified_locals))
                    });
                    if let Some((size, align)) =
                        layout_expr.and_then(Self::extract_layout_size_align)
                    {
                        (Some(size), Some(align), ct)
                    } else {
                        (None, None, ct)
                    }
                } else {
                    (None, None, None)
                };
                if let (Some(elem_size_expr), Some(align_expr), Some(n)) =
                    (elem_size_expr, align_expr, n)
                {
                    let elem_size_64 =
                        coerce_bitvec_width_safe(elem_size_expr, 64, SignExtension::ZeroExtend);
                    let align_64 =
                        coerce_bitvec_width_safe(align_expr, 64, SignExtension::ZeroExtend);
                    let n_64 = coerce_bitvec_width_safe(n, 64, SignExtension::ZeroExtend);
                    if elem_size_64.sort().bitvec_width().is_none()
                        || n_64.sort().bitvec_width().is_none()
                    {
                        warn!("LayoutArrayInner: non-BV args after coercion");
                        emit_sound_fallback_goto(
                            self,
                            from_app,
                            target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                        );
                        return;
                    }
                    let total_size = elem_size_64.clone().bvmul(n_64.clone());
                    // Part of #3408: overflow detection for runtime elem_size.
                    // size_nonzero => (total / size == n) — no wrapping.
                    let zero = Expr::bitvec_const(0u128, 64);
                    let size_nonzero = elem_size_64.clone().eq(zero).not();
                    let no_wrap = total_size.clone().bvudiv(elem_size_64).eq(n_64);
                    overflow_guard = Some(size_nonzero.implies(no_wrap));
                    total_size.concat(align_64)
                } else {
                    emit_sound_fallback_goto(
                        self,
                        from_app,
                        target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                    return;
                }
            }
            StubKind::LayoutFromSizeAlignUnchecked => {
                // Layout::from_size_align_unchecked(size, align)
                let size_expr = args
                    .first()
                    .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals));
                let align_expr = args
                    .get(1)
                    .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals));
                if let (Some(s), Some(a)) = (size_expr, align_expr) {
                    let s64 = coerce_bitvec_width_safe(s, 64, SignExtension::ZeroExtend);
                    let a64 = coerce_bitvec_width_safe(a, 64, SignExtension::ZeroExtend);
                    // Part of #2992: Post-coercion BV check — non-BV sort causes
                    // sort mismatch in concat.
                    if s64.sort().bitvec_width().is_none() || a64.sort().bitvec_width().is_none() {
                        warn!(
                            size_sort = ?s64.sort(),
                            align_sort = ?a64.sort(),
                            "LayoutFromSizeAlignUnchecked: non-BV after coercion (#2992)"
                        );
                        // Non-BV after coercion — translation failure (Part of #3123).
                        emit_sound_fallback_goto(
                            self,
                            from_app,
                            target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                        );
                        return;
                    }
                    s64.concat(a64)
                } else {
                    // LayoutFromSizeAlignUnchecked args not translatable (Part of #3123).
                    emit_sound_fallback_goto(
                        self,
                        from_app,
                        target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                    return;
                }
            }
            StubKind::LayoutFromSizeAlign => {
                // Layout::from_size_align(size, align) -> Result<Layout, LayoutError>
                // Checked variant: validity-guarded then delegates to unchecked
                // constructor semantics. Part of #3641.
                let size_expr = args
                    .first()
                    .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals));
                let align_expr = args
                    .get(1)
                    .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals));
                if let (Some(s), Some(a)) = (size_expr, align_expr) {
                    let s64 = coerce_bitvec_width_safe(s, 64, SignExtension::ZeroExtend);
                    let a64 = coerce_bitvec_width_safe(a, 64, SignExtension::ZeroExtend);
                    if s64.sort().bitvec_width().is_none() || a64.sort().bitvec_width().is_none() {
                        warn!(
                            size_sort = ?s64.sort(),
                            align_sort = ?a64.sort(),
                            "LayoutFromSizeAlign: non-BV after coercion (Part of #3641)"
                        );
                        emit_sound_fallback_goto(
                            self,
                            from_app,
                            target,
                            modified_locals,
                            &[dest_local],
                            stmt_constraints,
                        );
                        return;
                    }
                    // Build validity guard matching Rust's Layout::from_size_align.
                    let validity = self.layout_size_align_validity_expr(s64.clone(), a64.clone());
                    if let Some(valid) = validity {
                        overflow_guard = Some(valid);
                    }
                    s64.concat(a64)
                } else {
                    emit_sound_fallback_goto(
                        self,
                        from_app,
                        target,
                        modified_locals,
                        &[dest_local],
                        stmt_constraints,
                    );
                    return;
                }
            }
            _ => {
                // Unreachable: only stubs matching `is_semantic` in codegen_call_dispatch_misc
                // are routed here. Non-semantic layout stubs (LayoutDangling,
                // LayoutCalculateLayoutFor) go to codegen_call_unconstrained_stub instead.
                // Defensive fallback: leave destination nondet (sound over-approximation).
                emit_sound_fallback_goto(
                    self,
                    from_app,
                    target,
                    modified_locals,
                    &[dest_local],
                    stmt_constraints,
                );
                return;
            }
        };

        // Part of #3107, #3641: Cache concrete Layout sizes for downstream reuse
        // (alloc_zeroed window bounding, realloc layout-pair recovery).
        // Extract concrete (size, align) from the packed bv128 when both halves
        // are compile-time constants. Covers LayoutNew, LayoutForValueRaw,
        // LayoutArray (constant count), LayoutFromSizeAlign{,Unchecked} with
        // concrete args.
        if matches!(stub, StubKind::LayoutNew | StubKind::LayoutForValueRaw) {
            // Type-derived layouts are always concrete.
            self.known_layout_sizes.insert(dest_local, (type_size, type_align));
        } else if let ExprValue::BvConcat(hi, lo) = layout_bv128.value() {
            // Try to extract concrete values from dynamically-computed layouts.
            if let (
                ExprValue::BitVecConst { value: size_val, .. },
                ExprValue::BitVecConst { value: align_val, .. },
            ) = (hi.value(), lo.value())
            {
                if let (Ok(s), Ok(a)) = (u64::try_from(size_val), u64::try_from(align_val)) {
                    self.known_layout_sizes.insert(dest_local, (s, a));
                }
            }
        }

        let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
            debug!(dest_local, "CHC: layout_semantic dest not in state map — sound over-approx");
            self.record_sound_fallback_reason("state_idx_missing_layout_semantic_dest");
            emit_sound_fallback_goto(
                self,
                from_app,
                target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
            return;
        };

        // Layout::array often lowers to a flattened Result local:
        //   fld0 = is_ok, fld1 = Layout payload.
        // Constrain both fields so unwrap() does not read an unconstrained payload.
        //
        // Some mem-track pipelines expose flattened fld0/fld1 slots without
        // registering `dest_local` in `flattened_tuple_locals`, so detect by
        // adjacent output-var naming as a fallback.
        if matches!(
            stub,
            StubKind::LayoutArray | StubKind::LayoutArrayInner | StubKind::LayoutFromSizeAlign
        ) {
            let looks_flattened_result = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx)
                .zip(self.state_var_mgr.output_state_vars.get(dest_vec_idx + 1))
                .is_some_and(|((name0, _), (name1, _))| {
                    name0.contains("_fld0") && name1.contains("_fld1")
                });

            if looks_flattened_result {
                let field_count = if self.flatten.flattened_tuple_locals.contains(&dest_local) {
                    self.flattened_field_count(dest_local)
                } else {
                    2
                };
                let mut field_values = Vec::with_capacity(field_count);
                field_values.push(Some(layout_bv128.clone()));
                field_values.push(Some(layout_bv128.clone()));
                field_values.extend((2..field_count).map(|_| None));

                // Part of #2486: collect extras instead of stmt_constraints.to_vec().
                let mut extra_constraints: Vec<Expr> = Vec::new();
                if self.constrain_flattened_fields_for_call(
                    dest_local,
                    &field_values,
                    &mut extra_constraints,
                ) {
                    for i in 1..field_count {
                        self.mark_state_var_modified(dest_vec_idx + i);
                    }
                    // Part of #3677: `dest_vec_idx + i` is a raw state slot, not a
                    // MIR local. Routing it through `extra_dests` can alias an
                    // unrelated later local whose MIR index happens to match the
                    // slot number, flipping that local to `__out` with no
                    // constraint. Mark the raw slots directly instead.
                    self.mark_state_var_modified(dest_vec_idx);
                    let new_output_args = self.build_output_args(modified_locals, &[]);
                    // Part of #3408: add overflow guard so Ok path only fires without overflow.
                    extra_constraints.extend(overflow_guard);
                    self.emit_goto_rule_extra(
                        from_app,
                        target,
                        &new_output_args,
                        stmt_constraints,
                        extra_constraints,
                    );
                    return;
                }
            }
        }

        // Constrain destination to the concrete layout value.
        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            let mut rhs_expr = layout_bv128;

            // Layout::array returns Result<Layout, LayoutError>. When MIR has not
            // inlined unwrap(), destination is a Result datatype, so wrap the
            // semantic layout payload in Result::Ok(...) instead of assigning raw
            // bv128 and silently dropping the constraint.
            // Part of #2631: Find Ok constructor by predicate (supports scoped names).
            if matches!(
                stub,
                StubKind::LayoutArray | StubKind::LayoutArrayInner | StubKind::LayoutFromSizeAlign
            ) && let Some(dt) = dest_var.sort().datatype_sort()
                && let Some(ok_ctor) = dt
                    .constructors
                    .iter()
                    .find(|ctor| crate::codegen_ay::names::is_ok_constructor(&ctor.name))
                && let Some(ok_payload) = ok_ctor.fields.first()
                && ok_ctor.fields.len() == 1
                && let Some(coerced_payload) =
                    self.coerce_value_to_sort(rhs_expr.clone(), &ok_payload.sort, false)
            {
                rhs_expr = Expr::datatype_constructor(
                    &dt.name,
                    &ok_ctor.name,
                    vec![coerced_payload],
                    dest_var.sort().clone(),
                );
            }

            let eq = self.make_coerced_eq_constraint(
                &dest_var,
                rhs_expr,
                dest_var.sort(),
                dest_local,
                "codegen_call_layout_semantic",
            );
            if eq.is_some() {
                let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                // Part of #3408: add overflow guard so Ok path only fires without overflow.
                let extras: Vec<Expr> = eq.into_iter().chain(overflow_guard).collect();
                self.emit_goto_rule_extra(
                    from_app,
                    target,
                    &new_output_args,
                    stmt_constraints,
                    extras,
                );
                return;
            }
        }
        // Layout constraint push failed — translation failure (Part of #3123).
        emit_sound_fallback_goto(
            self,
            from_app,
            target,
            modified_locals,
            &[dest_local],
            stmt_constraints,
        );
    }
}
