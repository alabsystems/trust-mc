// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vtable intrinsic constraining for CHC codegen.
//!
//! Handles `vtable_size` and `vtable_align` intrinsics by building constrained
//! ITE chains over known concrete type metadata, instead of leaving the result
//! unconstrained. The metadata is collected at Unsize coercion sites (see
//! `codegen_stmt_rvalue_ref/`) where the concrete type's layout is known.
//!
//! Part of #3159: DynTrait category recovery — vtable metadata constraining.

use ay_bindings::{Expr, Sort};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::CallEmitContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Which vtable intrinsic is being called. Part of #3159.
#[derive(Debug, Clone, Copy)]
pub(in crate::codegen_ay::chc) enum VtableIntrinsicKind {
    Size,
    Align,
}

/// Extension trait for vtable intrinsic constraining on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallVtableIntrinsic {
    fn try_constrain_vtable_intrinsic(
        &mut self,
        kind: VtableIntrinsicKind,
        bb_idx: usize,
        ecx: &CallEmitContext<'_>,
    ) -> bool;
}

impl<'tcx, 'body> CallVtableIntrinsic for ChcCtx<'tcx, 'body> {
    /// Constrain vtable_size/vtable_align to concrete type metadata.
    ///
    /// Builds an ITE chain over `vtable_type_metadata` entries:
    ///   `ite(arg == disc_0, metadata_0, ite(arg == disc_1, metadata_1, unconstrained))`
    ///
    /// The vtable pointer argument in our CHC encoding IS the discriminant BV64 value
    /// (assigned at Unsize coercion sites). This maps directly to the vtable_type_metadata
    /// table populated by `try_translate_dyn_trait_coercion`.
    ///
    /// Part of #3367: DynMetadata::size_of/align_of methods pass `self` (DynMetadata
    /// value) rather than a raw vtable pointer. When the argument can't be translated
    /// (e.g., DynMetadata type not in CHC sort system), fall back to direct metadata
    /// lookup from vtable_type_metadata without the ITE discriminant chain.
    fn try_constrain_vtable_intrinsic(
        &mut self,
        kind: VtableIntrinsicKind,
        bb_idx: usize,
        ecx: &CallEmitContext<'_>,
    ) -> bool {
        // Translate the vtable pointer argument (first arg) to a AY expression.
        // Part of #3367: try resolve_ref_operand as fallback for DynMetadata &self args.
        let vtable_arg = ecx.args.first().and_then(|op| {
            self.translate_operand_with_modified(op, ecx.modified_locals)
                .or_else(|| self.resolve_ref_operand(op, ecx.modified_locals))
        });

        // Build constrained expression from vtable metadata.
        // Part of #3794: when vtable_type_metadata has entries, the vtable arg
        // at runtime can only be one of the registered discriminant values.
        // Use exact value (1 entry) or ITE + membership constraint (N entries).
        let (result, membership_constraint) = if let Some(vtable_arg) = vtable_arg {
            if self.vtable_type_metadata.is_empty() {
                // No registered vtable entries — unconstrained symbolic (sound).
                self.record_sound_fallback_reason("vtable_ite_no_entries");
                (
                    super::declare_pending_var(
                        super::chc_fresh_name("__vtable_meta"),
                        Sort::bitvec(POINTER_WIDTH),
                    ),
                    None,
                )
            } else if self.vtable_type_metadata.len() == 1 {
                // Part of #3794: Single registered concrete type — return exact value.
                // The vtable discriminant can only be this one value, so no ITE needed.
                let &(size, align) = self
                    .vtable_type_metadata
                    .values()
                    .next()
                    .expect("invariant: len() == 1 checked above");
                let value = match kind {
                    VtableIntrinsicKind::Size => size,
                    VtableIntrinsicKind::Align => align,
                };
                debug!(
                    kind = ?kind,
                    value,
                    "vtable intrinsic: single registered type, using exact value (bb{})",
                    bb_idx
                );
                (Expr::bitvec_const(value as u128, POINTER_WIDTH), None)
            } else {
                // Multiple registered types — build ITE chain with membership constraint.
                // Part of #3794: Add disjunction that vtable_arg is one of the registered IDs.
                // This makes the encoding exact rather than over-approximate.
                let mut ite_result = super::declare_pending_var(
                    super::chc_fresh_name("__vtable_meta"),
                    Sort::bitvec(POINTER_WIDTH),
                );
                let mut membership_clauses = Vec::new();
                for (&vtable_id, &(size, align)) in &self.vtable_type_metadata {
                    let value = match kind {
                        VtableIntrinsicKind::Size => size,
                        VtableIntrinsicKind::Align => align,
                    };
                    let cond =
                        vtable_arg.clone().eq(Expr::bitvec_const(vtable_id as u128, POINTER_WIDTH));
                    membership_clauses.push(cond.clone());
                    let val_expr = Expr::bitvec_const(value as u128, POINTER_WIDTH);
                    ite_result = Expr::ite(cond, val_expr, ite_result);
                }
                // Constrain vtable_arg to be one of the registered IDs.
                let membership = membership_clauses
                    .into_iter()
                    .reduce(|a, b| a.or(b))
                    .expect("vtable_type_metadata is non-empty");
                (ite_result, Some(membership))
            }
        } else {
            // Part of #3367: argument translation failed (DynMetadata type not in CHC
            // sort system). Use direct metadata from vtable_type_metadata without ITE.
            // If all concrete types agree on the value, use it directly (exact).
            // If they disagree, use unconstrained (sound over-approximation).
            if self.vtable_type_metadata.is_empty() {
                return false;
            }
            let mut values_iter =
                self.vtable_type_metadata.values().map(|&(size, align)| match kind {
                    VtableIntrinsicKind::Size => size,
                    VtableIntrinsicKind::Align => align,
                });
            let first_value =
                values_iter.next().expect("vtable_entries is non-empty (checked above)");
            let all_agree = values_iter.all(|v| v == first_value);
            let result_expr = if all_agree {
                Expr::bitvec_const(first_value as u128, POINTER_WIDTH)
            } else {
                // Part of #3447: Multiple concrete types disagree on metadata
                // and the vtable argument is untranslatable — unconstrained
                // symbolic is a sound over-approximation.
                self.record_sound_fallback_reason("vtable_noarg_disagree");
                super::declare_pending_var(
                    super::chc_fresh_name("__vtable_meta_noarg"),
                    Sort::bitvec(POINTER_WIDTH),
                )
            };
            debug!(
                kind = ?kind,
                entries = self.vtable_type_metadata.len(),
                all_agree,
                "vtable intrinsic: arg untranslatable, using direct metadata (bb{})",
                bb_idx
            );
            (result_expr, None)
        };

        // Constrain destination = result.
        let dest_local = ecx.destination.local;
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            return false;
        };
        let Some(eq) = self.make_coerced_eq_constraint(
            &dest_var,
            result,
            dest_var.sort(),
            dest_local,
            "vtable_intrinsic_constrained",
        ) else {
            return false;
        };

        let new_output_args = self.build_output_args(ecx.modified_locals, &[dest_local]);
        // Part of #3794: include vtable membership constraint if present.
        let mut constraints: Vec<Expr> = vec![eq];
        if let Some(membership) = membership_constraint {
            constraints.push(membership);
        }
        self.emit_goto_rule_extra(
            ecx.from_app,
            ecx.target,
            &new_output_args,
            ecx.stmt_constraints,
            constraints,
        );
        debug!(
            kind = ?kind,
            metadata_entries = self.vtable_type_metadata.len(),
            "modeled vtable intrinsic as constrained ITE (bb{})",
            bb_idx
        );
        true
    }
}
