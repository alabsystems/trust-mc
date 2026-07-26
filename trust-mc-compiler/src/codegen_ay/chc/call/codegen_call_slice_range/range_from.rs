// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC RangeFrom slice indexing.
//! Part of #3495, #3981.

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::{debug, warn};

use crate::codegen_ay::types::POINTER_WIDTH;
use trust_mc_core::chc::{Rule, RuleBody};

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_coerce::emit_sound_fallback_goto;
use super::super::{ChcCtx, RelationApp, chc_fresh_name, declare_pending_var};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn codegen_call_slice_range_from_index(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        slice_arg: &Operand,
        index_arg: &Operand,
    ) {
        let target = cx.target;
        let from_app = cx.from_app;
        let stmt_constraints = cx.stmt_constraints;
        let modified_locals = cx.modified_locals;

        let range_local = Self::operand_local(index_arg);
        let start_expr = match range_local {
            Some(local_idx) => match self.resolve_range_field_from_local(
                local_idx,
                0,
                &["start", "fld_start"],
                modified_locals,
            ) {
                Some(s) => s,
                None => {
                    debug!(
                        fn_name = %self.fn_name,
                        "CHC slice range_from: cannot extract RangeFrom.start; fallback"
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
            },
            None => {
                debug!(
                    fn_name = %self.fn_name,
                    "CHC slice range_from: index not a bare local; fallback"
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
        };

        let Some(start_bv) = self.coerce_to_pointer_width(start_expr) else {
            warn!(fn_name = %self.fn_name, "CHC slice range_from: start coerce failed; fallback");
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

        let slice_backing = self.resolve_slice_backing(slice_arg, modified_locals);
        let effective_start =
            slice_backing.as_ref().map(|backing| backing.offset.clone().bvadd(start_bv.clone()));

        let error_app = RelationApp::new("error", Vec::new());
        if let Some(ref backing) = slice_backing {
            let oob = start_bv.clone().bvugt(backing.len.clone());
            let body =
                RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, [oob]);
            self.vc.add_rule(Rule::new(body, error_app));
        }

        if let (Some(backing), Some(effective_start)) = (&slice_backing, &effective_start) {
            self.ref_resolution.const_ref_values.insert(dest_local, backing.data.clone());
            self.ref_resolution.subslice_offset.insert(dest_local, effective_start.clone());

            let subslice_len = backing.len.clone().bvsub(start_bv);
            self.ref_resolution.subslice_len.insert(dest_local, subslice_len);

            debug!(
                fn_name = %self.fn_name,
                dest_local,
                "CHC slice range_from: registered subslice data/offset/len in side tables"
            );
        }

        const MAX_SUBSLICE_ELEMS: usize = 32;

        let elem_ty = self.chc_slice_elem_ty(slice_arg);
        let source_inner = slice_backing.as_ref().map(|backing| backing.data.clone());

        if source_inner.is_none() || elem_ty.is_none() {
            debug!(
                fn_name = %self.fn_name,
                source_resolved = source_inner.is_some(),
                elem_ty_resolved = elem_ty.is_some(),
                "CHC slice range_from: source inner array not resolved; sound fallback"
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
        let source_inner = source_inner.expect("invariant: None case returned above");
        let elem_ty = elem_ty.expect("invariant: None case returned above");
        let inner_arr_sort = source_inner.sort().clone();
        let effective_start =
            effective_start.expect("invariant: source_inner resolution requires slice backing");

        self.record_aggregate_gap("slice_range_from_subslice_rebase");
        let shifted_base_name = chc_fresh_name("__subslice_from_base");
        let mut shifted = declare_pending_var(shifted_base_name, inner_arr_sort.clone());

        for i in 0..MAX_SUBSLICE_ELEMS {
            let idx = Expr::bitvec_const(i as i128, POINTER_WIDTH);
            let src_idx = effective_start.clone().bvadd(idx.clone());
            let elem = source_inner.clone().select(src_idx);
            shifted = shifted.store(idx, elem);
        }

        let Some(mat) =
            self.materialize_subslice_type_array(shifted, inner_arr_sort.clone(), elem_ty, None)
        else {
            warn!(fn_name = %self.fn_name, "CHC slice range_from: alloc ID overflow; fallback");
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

        // RangeFrom-specific: seed per-element memory entries.
        self.seed_subslice_element_memory(
            &mat.fresh_addr,
            &source_inner,
            &effective_start,
            elem_ty,
            &inner_arr_sort,
            &mat.elem_key,
            MAX_SUBSLICE_ELEMS,
        );

        self.emit_subslice_destination(
            cx,
            dest_local,
            mat.fresh_addr,
            "codegen_call_slice::SliceIndex_RangeFrom_subslice",
            "codegen_call_slice_range_from::fat_ptr_len",
        );
    }
}
