// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Nondet-value, quantifier, and validity-bound Kani hook handlers.
//!
//! Extracted from `codegen_call_kani_hooks.rs` for size management.
//! Covers `AnyRaw` (nondeterministic values with memory mirroring),
//! `Forall`/`Exists` (quantifier encoding), and validity-constraint
//! helpers for unit-enum discriminants and `char` outputs.

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::Place;
use rustc_public::ty::{AdtKind, RigidTy, TyKind};
use tracing::{debug, warn};

use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{
    CallCoerce, emit_sound_fallback_goto, emit_sound_fallback_goto_extra,
};
use super::codegen_rules::CodegenRules;
use super::quantifier_encoding::QuantifierEncoding;
use super::{ChcCtx, KaniHook};
use crate::args::ChcTrackLevel;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle `KaniHook::AnyRaw`: nondeterministic value (like kani::any()).
    ///
    /// Part of #3222: mirrors memory store from `KaniModel::Any` so that
    /// raw-pointer dereferences read the same symbolic value. Without this,
    /// `let x = kani::any(); let p = &x; assert!(*p == x)` fails because
    /// the memory load returns an independent unconstrained value.
    pub(in crate::codegen_ay::chc) fn hook_any_raw(&mut self, dcx: &DispatchCallContext<'_>) {
        let dest_local: usize = dcx.destination.local;
        if let Some(target) = dcx.target {
            let is_zst =
                super::codegen_call_kani_model_dst::is_zst_ty(self.body.locals()[dest_local].ty);
            if is_zst {
                let dest_ty = self.body.locals()[dest_local].ty;
                debug!("kani::any_raw() on ZST type, emitting canonical deterministic value");
                let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
                    self.record_sound_fallback_reason("state_idx_missing_hook_any_raw_zst");
                    emit_sound_fallback_goto(
                        self,
                        dcx.from_app,
                        *target,
                        dcx.modified_locals,
                        &[dest_local],
                        dcx.stmt_constraints,
                    );
                    return;
                };
                let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
                else {
                    self.record_sound_fallback_reason("output_slot_missing_hook_any_raw_zst");
                    emit_sound_fallback_goto(
                        self,
                        dcx.from_app,
                        *target,
                        dcx.modified_locals,
                        &[dest_local],
                        dcx.stmt_constraints,
                    );
                    return;
                };
                let Some(canonical_zst) =
                    super::codegen_call_kani_model_zst::canonical_zst_expr(dest_ty)
                else {
                    self.record_sound_fallback_reason("canonical_zst_expr_missing_hook_any_raw");
                    emit_sound_fallback_goto(
                        self,
                        dcx.from_app,
                        *target,
                        dcx.modified_locals,
                        &[dest_local],
                        dcx.stmt_constraints,
                    );
                    return;
                };
                let dest_var = Expr::var(&*out_name, out_sort.clone());
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    canonical_zst,
                    &out_sort,
                    dest_local,
                    "kani_hook::AnyRaw::canonical_zst",
                );
                let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    dcx.from_app,
                    *target,
                    &new_output_args,
                    dcx.stmt_constraints,
                    eq,
                );
                return;
            }

            let mut extra_constraints = Vec::new();

            // Mem-level: mirror the nondet value into memory so that
            // subsequent raw-pointer dereferences read the assigned value.
            if !is_zst && self.track_level >= ChcTrackLevel::Mem {
                // Part of #3768: graceful fallback instead of panic on unregistered locals
                if let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) {
                    let store_constraint =
                        self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned().and_then(
                            |(out_name, out_sort)| {
                                let dest_var = Expr::var(&*out_name, out_sort);
                                let local_place = Place { local: dest_local, projection: vec![] };
                                let addr_expr = self
                                    .translate_ref_to_address(&local_place, dcx.modified_locals)?;
                                let local_ty = self.body.locals()[dest_local].ty;
                                self.build_memory_store(addr_expr, dest_var, local_ty)
                            },
                        );
                    if let Some(store_constraint) = store_constraint {
                        extra_constraints.push(store_constraint);
                    }
                } else {
                    self.record_sound_fallback_reason("state_idx_missing_hook_any_raw");
                }

                // Call-terminator handlers bypass encode_block_statements,
                // so flush heap side effects explicitly.
                extra_constraints.append(&mut self.heap_state.pending_updates);
                extra_constraints
                    .append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
                let pending_checks: Vec<_> = self.heap_state.pending_checks.drain(..).collect();
                for check in pending_checks {
                    self.emit_error_rule_for_condition(
                        dcx.from_app,
                        check,
                        dcx.stmt_constraints,
                        dcx.bb_idx,
                    );
                }
            }

            // Part of #112 Direction 2 step 3: bound nondet output to BV range.
            extra_constraints.extend(self.int_lift_nondet_bounds(dest_local));
            // Part of #3041: Constrain unit enum discriminants to valid range.
            extra_constraints.extend(self.unit_enum_discriminant_bounds(dest_local));
            // Part of #3470: Constrain char outputs to valid Unicode scalar values.
            extra_constraints.extend(self.char_nondet_bounds(dest_local));

            // Build output args after heap side effects so modified memory
            // arrays are routed to their __out vars.
            let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);

            if extra_constraints.is_empty() {
                self.emit_goto_rule(dcx.from_app, *target, &new_output_args, dcx.stmt_constraints);
            } else {
                self.emit_goto_rule_extra(
                    dcx.from_app,
                    *target,
                    &new_output_args,
                    dcx.stmt_constraints,
                    extra_constraints,
                );
            }
        } else {
            self.record_diverging_call_drop(dcx.func, Some(dcx.bb_idx), "kani_hook::AnyRaw", None);
        }
    }

    /// Build discriminant bound constraints for unit enum destinations.
    ///
    /// For unit enums (all variants have no fields), the sort is BV32. Without
    /// bounds, `kani::any()` produces an unconstrained BV32 that can take values
    /// outside the valid discriminant range, causing the SwitchInt default arm
    /// to fire as a spurious CTREX. This constrains `out < num_variants`.
    /// Part of #3041.
    pub(in crate::codegen_ay::chc) fn unit_enum_discriminant_bounds(
        &self,
        dest_local: usize,
    ) -> Option<Expr> {
        let ty = self.body.locals()[dest_local].ty;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
            return None;
        };
        if def.kind() != AdtKind::Enum {
            return None;
        }
        let variants = def.variants();
        let is_unit_enum = variants.iter().all(|v| v.fields().is_empty());
        if !is_unit_enum || variants.len() <= 1 {
            return None;
        }
        let num_variants = variants.len();

        let vec_idx = self.try_state_idx_for_local(dest_local)?;
        let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx)?;
        // Only constrain BV sorts (unit enums are encoded as BV32/BV64).
        let bv_width = out_sort.bitvec_width()?;
        let out_var = Expr::var(&**out_name, out_sort.clone());

        // Missed-bug F fix: constrain the nondet output to the enum's actual
        // discriminant VALUE set {d0..dn-1}, not the variant-INDEX range [0, n).
        // A unit enum is read back by `Rvalue::Discriminant` as its raw stored
        // VALUE, and SwitchInt cases are discriminant VALUES; bounding to the index
        // range was only correct for identity-discriminant enums. For explicit
        // discriminants (e.g. `enum E { A=10, B=20, C=30 }` or signed `repr` enums
        // like `Ordering`) the old `out < num_variants` left `kani::any::<E>()` in
        // the WRONG space — casts (`e as u8`) read the index and every SwitchInt
        // case went dead. Pinning to the value set keeps a valid nondet enum's
        // selector inside the case set, so the exhaustive `otherwise -> Unreachable`
        // arm stays UNSAT without the (now-removed) exhaustiveness gate, while a
        // transmuted INVALID value — which never flows through this bound —
        // correctly reaches the Unreachable error edge.
        let internal_def = rustc_public::rustc_internal::internal(self.tcx, def);
        let mut membership: Option<Expr> = None;
        for i in 0..num_variants {
            let discr = internal_def
                .discriminant_for_variant(self.tcx, rustc_abi::VariantIdx::from_usize(i));
            let dv = crate::codegen_ay::chc::codegen_stmt_aggregate_adt::sign_extend_discr_val(
                discr.val, discr.ty, self.tcx, bv_width,
            );
            let eq = out_var.clone().eq(Expr::bitvec_const(dv, bv_width));
            membership = Some(match membership {
                None => eq,
                Some(acc) => acc.or(eq),
            });
        }
        debug!(
            dest_local,
            num_variants,
            bv_width,
            "unit_enum_discriminant_bounds: out ∈ valid discriminant values"
        );
        // `membership` is always Some here (num_variants > 1 checked above); the
        // index-range bound is a defensive fallback that never regresses soundness.
        Some(
            membership.unwrap_or_else(|| {
                out_var.bvult(Expr::bitvec_const(num_variants as u64, bv_width))
            }),
        )
    }

    /// Build validity constraints for `char` nondet outputs.
    ///
    /// Rust `char` is a Unicode scalar value: `[0, 0xD7FF] ∪ [0xE000, 0x10FFFF]`.
    /// Without this constraint, `kani::any::<char>()` produces an unconstrained
    /// BV32 that can be a surrogate (0xD800–0xDFFF) or above 0x10FFFF.
    /// The `-Z valid-value-checks` flag then inserts MIR validity checks that
    /// fail (producing CTREX or UNKNOWN) because the char may be invalid.
    ///
    /// Part of #3470.
    pub(in crate::codegen_ay::chc) fn char_nondet_bounds(&self, dest_local: usize) -> Option<Expr> {
        let ty = self.body.locals()[dest_local].ty;
        if ty.kind().is_char() {
            let vec_idx = self.try_state_idx_for_local(dest_local)?;
            let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx)?;
            let out_var = Expr::var(&**out_name, out_sort.clone());
            return Self::build_char_validity_constraint(out_var, out_sort, dest_local, "scalar");
        }

        // Part of #3930: For structs with char fields, constrain each char field.
        // When `kani::any::<Struct>()` is dispatched as KaniModel::Any without
        // inlining the Arbitrary impl, `kani::assume(is_valid_char)` inside
        // `<char as Arbitrary>::any()` is never processed. We must add the char
        // constraint for each char-typed field.
        self.struct_char_field_nondet_bounds(dest_local, ty)
    }

    /// Part of #3930: Constrain char-typed fields in struct nondet outputs.
    fn struct_char_field_nondet_bounds(
        &self,
        dest_local: usize,
        ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let fields_with_args = match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let variants = def.variants();
                if variants.len() != 1 {
                    return None;
                }
                variants[0].fields().iter().map(|f| f.ty_with_args(&args)).collect::<Vec<_>>()
            }
            TyKind::RigidTy(RigidTy::Tuple(elems)) => elems,
            _ => return None,
        };

        let char_field_indices: Vec<usize> = fields_with_args
            .iter()
            .enumerate()
            .filter(|(_, fty)| fty.kind().is_char())
            .map(|(i, _)| i)
            .collect();

        if char_field_indices.is_empty() {
            return None;
        }

        let vec_idx = self.try_state_idx_for_local(dest_local)?;
        let mut combined = Expr::bool_const(true);

        if self.flatten.flattened_tuple_locals.contains(&dest_local) {
            // Flattened: each field is a separate state var at vec_idx + field_idx
            for &field_idx in &char_field_indices {
                let slot = vec_idx + field_idx;
                if let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(slot) {
                    let out_var = Expr::var(&**out_name, out_sort.clone());
                    if let Some(constraint) = Self::build_char_validity_constraint(
                        out_var,
                        out_sort,
                        dest_local,
                        &format!("flattened_field_{field_idx}"),
                    ) {
                        combined = combined.and(constraint);
                    }
                }
            }
        } else {
            // Datatype: single state var, extract fields with DatatypeSelector
            let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx)?;
            if !out_sort.is_datatype() {
                return None;
            }
            let root_expr = Expr::var(&**out_name, out_sort.clone());
            for &field_idx in &char_field_indices {
                if let Some(field_expr) = Self::datatype_field_select(&root_expr, field_idx, None) {
                    let field_sort = field_expr.sort().clone();
                    if let Some(constraint) = Self::build_char_validity_constraint(
                        field_expr,
                        &field_sort,
                        dest_local,
                        &format!("dt_field_{field_idx}"),
                    ) {
                        combined = combined.and(constraint);
                    }
                }
            }
        }

        // Only return a constraint if we actually constrained something
        if matches!(combined.value(), ExprValue::BoolConst(true)) { None } else { Some(combined) }
    }

    fn build_char_validity_constraint(
        out_var: Expr,
        out_sort: &ay_bindings::Sort,
        dest_local: usize,
        label: &str,
    ) -> Option<Expr> {
        if let Some(bv_width) = out_sort.bitvec_width() {
            let low_range = out_var.clone().bvule(Expr::bitvec_const(0xD7FFu64, bv_width));
            let high_lower = out_var.clone().bvuge(Expr::bitvec_const(0xE000u64, bv_width));
            let high_upper = out_var.bvule(Expr::bitvec_const(0x10FFFFu64, bv_width));
            let valid = low_range.or(high_lower.and(high_upper));
            debug!(
                dest_local,
                label, "char_nondet_bounds: Unicode scalar constraint (BV{bv_width})"
            );
            Some(valid)
        } else if out_sort.is_int() {
            let low_range = out_var.clone().int_le(Expr::int_const(0xD7FFi64));
            let high_lower = out_var.clone().int_ge(Expr::int_const(0xE000i64));
            let high_upper = out_var.int_le(Expr::int_const(0x10FFFFi64));
            let valid = low_range.or(high_lower.and(high_upper));
            debug!(dest_local, label, "char_nondet_bounds: Unicode scalar constraint (Int)");
            Some(valid)
        } else {
            None
        }
    }

    /// Handle `KaniHook::Forall | KaniHook::Exists`: encode quantifier expression.
    pub(in crate::codegen_ay::chc) fn hook_quantifier(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        kani_hook: KaniHook,
    ) {
        let bb_idx = dcx.bb_idx;
        let dest_local: usize = dcx.destination.local;

        if let Some(target) = dcx.target {
            // Part of #3768: graceful fallback instead of panic on unregistered locals
            let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
                self.record_sound_fallback_reason("state_idx_missing_hook_quantifier");
                emit_sound_fallback_goto(
                    self,
                    dcx.from_app,
                    *target,
                    dcx.modified_locals,
                    &[dest_local],
                    dcx.stmt_constraints,
                );
                return;
            };
            let mut sound_fallback = false;
            let is_forall = matches!(kani_hook, KaniHook::Forall);
            let eq = if let Some(quant_expr) = self.build_quantifier_expr(
                dcx.func,
                dcx.args,
                dcx.modified_locals,
                bb_idx,
                is_forall,
            ) {
                let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
                let dest_var = Expr::var(
                    &*self.state_var_mgr.output_state_vars[dest_vec_idx].0,
                    out_sort.clone(),
                );
                let site = if is_forall {
                    "codegen_call_kani_hook::Forall"
                } else {
                    "codegen_call_kani_hook::Exists"
                };
                self.make_coerced_eq_constraint(&dest_var, quant_expr, &out_sort, dest_local, site)
            } else {
                // Part of #3099: reclassified from record_fallback() (DEMOTED).
                // Destination left nondet = sound over-approximation: verification
                // must prove the assertion for ALL possible values of the result,
                // which is strictly more conservative than the intended quantifier.
                warn!(?bb_idx, "quantifier encoding failed; dest unconstrained (nondet)");
                sound_fallback = true;
                None
            };
            if sound_fallback {
                emit_sound_fallback_goto_extra(
                    self,
                    dcx.from_app,
                    *target,
                    dcx.modified_locals,
                    &[dest_local],
                    dcx.stmt_constraints,
                    eq,
                );
            } else {
                let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    dcx.from_app,
                    *target,
                    &new_output_args,
                    dcx.stmt_constraints,
                    eq,
                );
            }
        } else {
            self.record_diverging_call_drop(
                dcx.func,
                Some(bb_idx),
                "kani_hook::Forall_Exists",
                None,
            );
        }
    }
}
