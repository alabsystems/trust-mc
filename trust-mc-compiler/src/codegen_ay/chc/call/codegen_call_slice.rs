// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC slice stub codegen with backend parity (Part of #408).
//! Array-select semantics, bounds guards, ZST handling for SliceIndexIndex/IndexIndex.
//! Range-based subslice indexing is in codegen_call_slice_range.rs (Part of #3327).
//!
//! Query stubs (SliceIsEmpty, SliceFirst) are in codegen_call_slice_query.rs.
//! Get/RangeFull stubs are in codegen_call_slice_get.rs (Part of #4130).

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use super::codegen_expr_signedness::arg_signedness_or_fallback;
use crate::codegen_ay::shared::SignednessFallbackKind;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto_prebuilt};
use super::codegen_call_misc::CallMisc;
use super::codegen_rules::CodegenRules;

/// Extension trait for CHC slice call handling.
pub(in crate::codegen_ay::chc) trait CallSlice {
    fn codegen_call_slice_stub_parity(&mut self, cx: &ChcCallContext<'_>);
}

impl<'tcx, 'body> CallSlice for ChcCtx<'tcx, 'body> {
    fn codegen_call_slice_stub_parity(&mut self, cx: &ChcCallContext<'_>) {
        self.codegen_call_slice_stub_parity_impl(cx);
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Slice stub implementation with statement-backend parity.
    ///
    /// - `SlicePartialEqEqual`: delegates to existing equality path (unchanged).
    /// - `SliceIndexIndex` / `IndexIndex`: replaces unconstrained fallback with:
    ///   1. Operand type inspection for ZST element detection
    ///   2. Array-select when the resolved value has Array sort
    ///   3. Datatype `fld_data` extraction for Vec/Slice backing arrays
    ///   4. Bounds guard emission (index >= length -> violation)
    ///   5. Constrained symbolic fallback only when source cannot be resolved
    pub(in crate::codegen_ay::chc) fn codegen_call_slice_stub_parity_impl(
        &mut self,
        cx: &ChcCallContext<'_>,
    ) {
        let dest_local: usize = cx.destination.local;
        let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);

        match cx.stub {
            StubKind::SlicePartialEqEqual => {
                // Delegate to existing equality path — unchanged from primitive_ops.
                self.codegen_call_slice_eq_impl(cx, dest_local, &new_output_args);
            }
            StubKind::SliceIndexIndex | StubKind::IndexIndex | StubKind::SliceGetUnchecked => {
                // output_args built inside impl — late state vars may be added. Part of #2970.
                self.codegen_call_slice_index_impl(cx, dest_local);
                // Contract-modifies REPLACE lane: record the read-side index
                // context so `write_any_slim` can havoc `modifies(&v[i])`
                // targets through the collection lane. Stored in a separate
                // map (`collection_index_refs`) that deref-store handlers
                // never consult.
                self.register_index_read_tracking(cx.args, cx.modified_locals, dest_local);
            }
            StubKind::IndexMut => {
                // Part of #3348: IndexMut reuses IndexIndex path for bounds guard and select,
                // then registers the dest for deferred Vec store propagation.
                self.codegen_call_slice_index_impl(cx, dest_local);
                self.register_index_mut_tracking(cx.args, cx.modified_locals, dest_local);
            }
            StubKind::SliceIsEmpty => {
                // Part of #3713: slice::is_empty — returns len == 0.
                self.codegen_call_slice_is_empty_impl(cx, dest_local, &new_output_args);
            }
            StubKind::SliceFirst => {
                // Part of #3768: slice::first — returns first element or None.
                self.codegen_call_slice_first_impl(cx, dest_local, &new_output_args);
            }
            StubKind::SliceGet => {
                // Part of #4174: slice::get — checked element access returning Option<&T>.
                self.codegen_call_slice_get_impl(cx, dest_local, &new_output_args);
            }
            StubKind::SlicePartitionPoint => {
                // Part of #4202: partition_point returns 0..=len.
                // Constrained symbolic result in [0, len] (mirrors BMC path).
                self.codegen_call_slice_partition_point_impl(cx, dest_local, &new_output_args);
            }
            StubKind::SliceLast => {
                // Part of #4208: slice::last — sound over-approximation (unconstrained dest).
                debug!("codegen_call_slice: SliceLast — sound fallback");
                emit_sound_fallback_goto_prebuilt(
                    self,
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                );
            }
            StubKind::SliceBinarySearchByKey => {
                // Part of #4208: binary_search_by_key — sound over-approximation.
                debug!("codegen_call_slice: SliceBinarySearchByKey — sound fallback");
                emit_sound_fallback_goto_prebuilt(
                    self,
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                );
            }
            StubKind::SliceChunks | StubKind::SliceWindows => {
                // Part of #4208: chunks/windows — sound over-approximation.
                debug!(?cx.stub, "codegen_call_slice: chunks/windows — sound fallback");
                emit_sound_fallback_goto_prebuilt(
                    self,
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                );
            }
            _other => {
                // partial dispatch: StubKind
                warn!(?_other, "codegen_call_slice_stub_parity: unexpected stub");
                emit_sound_fallback_goto_prebuilt(
                    self,
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                );
            }
        }
    }

    /// Handle `SlicePartialEqEqual` — compare resolved referent values.
    ///
    /// Same logic as the prior implementation in `primitive_ops.rs`.
    fn codegen_call_slice_eq_impl(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        new_output_args: &[Expr],
    ) {
        let args = cx.args;
        let target = cx.target;
        let from_app = cx.from_app;
        let stmt_constraints = cx.stmt_constraints;
        let modified_locals = cx.modified_locals;

        // ZST slice equality is value-semantic length equality. This mirrors
        // the statement backend and avoids unconstrained call results for
        // `[(); N]` equality lowered through `SlicePartialEq::equal`.
        if let Some(eq_expr) = self.try_zst_slice_eq_expr(args, modified_locals) {
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    eq_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_slice::SlicePartialEqEqual(zst)",
                );
                if eq.is_some() {
                    self.emit_goto_rule_extra(
                        from_app,
                        target,
                        new_output_args,
                        stmt_constraints,
                        eq,
                    );
                    return;
                }
            }
        }

        // Part of #3495: Provenance-based shortcut for subslice equality.
        // If both args share the same const_ref_values backing array AND the
        // same subslice_offset, they reference identical data → emit `true`.
        if let Some(eq_expr) = self.try_slice_eq_via_provenance(args) {
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    eq_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_slice::SlicePartialEqEqual(provenance)",
                );
                if eq.is_some() {
                    self.emit_goto_rule_extra(
                        from_app,
                        target,
                        new_output_args,
                        stmt_constraints,
                        eq,
                    );
                    return;
                }
            }
        }

        let lhs_backing =
            args.first().and_then(|arg| self.resolve_slice_backing(arg, modified_locals));
        let rhs_backing =
            args.get(1).and_then(|arg| self.resolve_slice_backing(arg, modified_locals));

        if let (Some(lhs), Some(rhs)) = (&lhs_backing, &rhs_backing) {
            if let Some(eq_expr) = self.build_precise_slice_eq(lhs, rhs) {
                if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                    let eq = self.make_coerced_eq_constraint(
                        &dest_var,
                        eq_expr,
                        dest_var.sort(),
                        dest_local,
                        "codegen_call_slice::SlicePartialEqEqual(backing)",
                    );
                    if eq.is_some() {
                        self.emit_goto_rule_extra(
                            from_app,
                            target,
                            new_output_args,
                            stmt_constraints,
                            eq,
                        );
                        return;
                    }
                }
            }
        }

        let lhs = args.first().and_then(|arg| self.resolve_raw_eq_referent(arg, modified_locals));
        let rhs = args.get(1).and_then(|arg| self.resolve_raw_eq_referent(arg, modified_locals));

        if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
            let eq_expr = if *lhs.sort() == *rhs.sort() {
                lhs.eq(rhs)
            } else if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
                let Some(lhs_w) = lhs.sort().bitvec_width() else {
                    warn!("CHC fallback: slice_eq lhs bitvec sort without width");
                    emit_sound_fallback_goto_prebuilt(
                        self,
                        from_app,
                        target,
                        new_output_args,
                        stmt_constraints,
                    );
                    return;
                };
                let Some(rhs_w) = rhs.sort().bitvec_width() else {
                    warn!("CHC fallback: slice_eq rhs bitvec sort without width");
                    emit_sound_fallback_goto_prebuilt(
                        self,
                        from_app,
                        target,
                        new_output_args,
                        stmt_constraints,
                    );
                    return;
                };
                // Task #69 step 5: length-blind width coercion is fail-open.
                // When the flattened widths DIFFER, the slices have different
                // byte counts, and the padded comparison can report "equal"
                // for slices of different lengths (zext([1u8]) == [1u8, 0]).
                // Require a CONST-resolvable length pair and conjoin
                // lhs_len == rhs_len (the length conjunct of the
                // build_precise_slice_eq shape, const-folded here). Symbolic
                // or unresolvable lengths fall through to the MARKED fallback:
                // conjoining a symbolic length equality with the padded
                // compare could report false-unequal on really-equal slices,
                // which would false-prove `assert!(a != b)`.
                if lhs_w != rhs_w {
                    let lhs_len = self.resolve_const_slice_eq_len(args, 0, modified_locals);
                    let rhs_len = self.resolve_const_slice_eq_len(args, 1, modified_locals);
                    match (lhs_len, rhs_len) {
                        (Some(ll), Some(rl)) if ll != rl => {
                            // Length conjunct is definitely false → unequal.
                            debug!(
                                fn_name = %self.fn_name,
                                ll, rl, "CHC slice_eq: width+length mismatch → const false (#69)"
                            );
                            Expr::bool_const(false)
                        }
                        _ => {
                            warn!(
                                fn_name = %self.fn_name,
                                lhs_w,
                                rhs_w,
                                "CHC slice_eq: width mismatch without const length pair; MARKED fallback (#69)"
                            );
                            emit_sound_fallback_goto_prebuilt(
                                self,
                                from_app,
                                target,
                                new_output_args,
                                stmt_constraints,
                            );
                            return;
                        }
                    }
                } else {
                    let target_width = lhs_w.max(rhs_w);
                    // Part of #2976: derive signedness from operand type for BV widening.
                    let signed = args
                        .first()
                        .map(|arg| {
                            arg_signedness_or_fallback(
                                arg,
                                self.body.locals(),
                                "slice_eq",
                                SignednessFallbackKind::Comparison,
                            )
                        })
                        .unwrap_or(false);
                    let lhs = coerce_bitvec_width_safe(
                        lhs,
                        target_width,
                        SignExtension::for_signedness(signed),
                    );
                    let rhs = coerce_bitvec_width_safe(
                        rhs,
                        target_width,
                        SignExtension::for_signedness(signed),
                    );
                    lhs.eq(rhs)
                }
            } else if let Some(rhs_coerced) = Self::reinterpret_fixed_layout_expr(&rhs, lhs.sort())
            {
                // Part of #3951: BV→Array coercion for slice literal vs Vec data.
                lhs.eq(rhs_coerced)
            } else if let Some(lhs_coerced) = Self::reinterpret_fixed_layout_expr(&lhs, rhs.sort())
            {
                // Part of #3951: symmetric case — Array→BV coercion.
                lhs_coerced.eq(rhs)
            } else {
                warn!(
                    fn_name = %self.fn_name,
                    lhs_sort = ?lhs.sort(),
                    rhs_sort = ?rhs.sort(),
                    "CHC: slice equality sort mismatch; fallback"
                );
                emit_sound_fallback_goto_prebuilt(
                    self,
                    from_app,
                    target,
                    new_output_args,
                    stmt_constraints,
                );
                return;
            };

            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    eq_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_slice::SlicePartialEqEqual",
                );
                if eq.is_some() {
                    self.emit_goto_rule_extra(
                        from_app,
                        target,
                        new_output_args,
                        stmt_constraints,
                        eq,
                    );
                    return;
                }
            }
        }

        // Fallback: unresolved or incompatible slice equality.
        warn!(
            fn_name = %self.fn_name,
            "CHC: slice equality unresolved; fallback"
        );
        emit_sound_fallback_goto_prebuilt(
            self,
            from_app,
            target,
            new_output_args,
            stmt_constraints,
        );
    }

    /// Task #69 step 5: resolve a CONST element count for a slice-eq operand.
    ///
    /// Chain: static `[T; N]` length → registered subslice_len (direct or one
    /// ref_targets hop) → shared sidecar chain (`resolve_slice_arg_length`).
    /// Only constant-foldable lengths are returned — the width-mismatch
    /// equality path must not conjoin symbolic lengths (see call site).
    fn resolve_const_slice_eq_len(
        &self,
        args: &[Operand],
        arg_idx: usize,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<u128> {
        use ay_bindings::ExprValue;

        let arg = args.get(arg_idx)?;
        let len_expr = self
            .static_slice_len_from_operand(arg)
            .or_else(|| {
                let local = match arg {
                    Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                    _ => None,
                }?;
                self.ref_resolution.subslice_len.get(&local).cloned().or_else(|| {
                    let rt = self.ref_resolution.ref_targets.get(&local)?;
                    if rt.projections.is_empty() {
                        self.ref_resolution.subslice_len.get(&rt.local).cloned()
                    } else {
                        None
                    }
                })
            })
            .or_else(|| self.resolve_slice_arg_length(args, arg_idx, modified_locals))?;
        match len_expr.value() {
            ExprValue::BitVecConst { value, .. } | ExprValue::IntConst(value) => {
                u128::try_from(value).ok()
            }
            _ => None,
        }
    }

    /// Handle `SlicePartitionPoint` — returns a `usize` in `[0, len]`. Part of #4202.
    ///
    /// The real `partition_point` performs a binary search returning the first
    /// index where the predicate is false (range `0..=len`). We model this as
    /// a fresh symbolic `usize` constrained to `[0, len]`, which is a sound
    /// over-approximation: the solver explores all possible return values in
    /// the valid range. This mirrors the BMC-path encoding in `statement/slice.rs`.
    ///
    /// Uses the same 5-strategy length resolution chain as `SliceIsEmpty`:
    /// 1. Static `[T; N]` length from operand type
    /// 2. `subslice_len` for known subslices
    /// 3. `translate_ptr_metadata` for `&[T]` / fat-pointer slice receivers
    /// 4. direct `fld_len` read from a resolved slice datatype local
    /// 5. `resolve_slice_arg_length` (sidecar, slice_to_vec_local, iter tracking)
    /// Falls back to unconstrained symbolic (still sound, just less precise).
    fn codegen_call_slice_partition_point_impl(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        new_output_args: &[Expr],
    ) {
        let args = cx.args;

        // Create fresh symbolic result variable.
        let fresh_result = super::declare_pending_var(
            super::chc_fresh_name("__partition_point"),
            Sort::bitvec(POINTER_WIDTH),
        );

        // Resolve length using the same 5-strategy chain as SliceIsEmpty.
        let len_expr = args.first().and_then(|receiver| {
            let local = match receiver {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                _ => None,
            };

            // Strategy 1: Static array length from type.
            let receiver_ty = receiver.ty(self.body.locals()).ok();
            let pointee_ty = receiver_ty.and_then(|ty| match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => Some(inner),
                _ => None,
            });
            if let Some(pointee) = pointee_ty {
                if let TyKind::RigidTy(RigidTy::Array(_, const_len)) = pointee.kind() {
                    if let Ok(n) = const_len.eval_target_usize() {
                        return Some(Expr::bitvec_const(n as u128, POINTER_WIDTH));
                    }
                }
            }

            // Strategy 2: subslice_len metadata.
            if let Some(l) = local {
                if let Some(len) = self.ref_resolution.subslice_len.get(&l).cloned() {
                    return Some(len);
                }
            }

            // Strategy 3: use the wide-pointer metadata path for `&[T]`.
            if let Some(len) = self.translate_ptr_metadata(receiver, cx.modified_locals) {
                return Some(len.into_expr());
            }

            // Strategy 4: read `fld_len` from the resolved slice referent.
            if let Some(expr) = self.resolve_ref_or_const_referent(receiver, cx.modified_locals) {
                let expr_for_sort = expr.clone();
                let expr_sort = expr_for_sort.sort();
                if let Some(dt_name) = expr_sort.datatype_name()
                    && let Some(len_sort) = Self::get_dt_field_sort(&expr_for_sort, "fld_len")
                {
                    return Some(expr.field_select(dt_name, "fld_len", len_sort));
                }
            }

            // Strategy 5: resolve_slice_arg_length (sidecar + ref_targets + vec mappings).
            self.resolve_slice_arg_length(args, 0, cx.modified_locals)
        });

        let mut extra_constraints = Vec::new();

        if let Some(len) = len_expr {
            // Constrain result to [0, len]. Since bitvec is unsigned, result >= 0
            // is trivially true; we only need result <= len.
            extra_constraints.push(fresh_result.clone().bvule(len));
            debug!(
                fn_name = %self.fn_name,
                dest_local,
                "CHC SlicePartitionPoint: constrained result in [0, len]"
            );
        } else {
            // Length unresolved — result is unconstrained (still sound).
            debug!(
                fn_name = %self.fn_name,
                dest_local,
                "CHC SlicePartitionPoint: length unresolved; unconstrained result"
            );
            self.record_sound_fallback_reason("slice_partition_point_len_unresolved");
        }

        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            let eq = self.make_coerced_eq_constraint(
                &dest_var,
                fresh_result,
                dest_var.sort(),
                dest_local,
                "codegen_call_slice::SlicePartitionPoint",
            );
            if eq.is_some() {
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    new_output_args,
                    cx.stmt_constraints,
                    extra_constraints.into_iter().chain(eq),
                );
                return;
            }
        }

        // Destination unresolved — sound fallback.
        debug!(
            fn_name = %self.fn_name,
            dest_local,
            "CHC SlicePartitionPoint: destination unresolved; fallback"
        );
        emit_sound_fallback_goto_prebuilt(
            self,
            cx.from_app,
            cx.target,
            new_output_args,
            cx.stmt_constraints,
        );
    }

    // SliceIsEmpty and SliceFirst live in codegen_call_slice_query.rs.
    // SliceGet and RangeFull identity live in codegen_call_slice_get.rs.
    // Scalar-index lowering lives in codegen_call_slice_index.rs.
    // Helper methods (split_chc_slice_index_args, chc_slice_elem_ty,
    // is_zst_type_for_slice, coerce_to_pointer_width, chc_array_length,
    // get_dt_field_sort, register_index_mut_tracking) are in
    // codegen_call_slice_helpers.rs (extracted per #3348, file size limit).
}
