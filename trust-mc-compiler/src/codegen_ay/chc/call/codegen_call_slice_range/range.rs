// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC Range/RangeInclusive slice indexing.
//! Part of #3495, #3551, #3981.

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::{debug, warn};

use crate::codegen_ay::types::POINTER_WIDTH;
use trust_mc_core::chc::{Rule, RuleBody};

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_coerce::emit_sound_fallback_goto;
use super::super::codegen_call_slice_helpers::{
    ResolvedSliceBacking, SLICE_BACKING_REBASE_MAX_ELEMS,
};
use super::super::{ChcCtx, RelationApp};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn codegen_call_slice_range_index(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        slice_arg: &Operand,
        index_arg: &Operand,
        inclusive: bool,
    ) {
        let target = cx.target;
        let from_app = cx.from_app;
        let stmt_constraints = cx.stmt_constraints;
        let modified_locals = cx.modified_locals;

        let range_local = Self::operand_local(index_arg);
        let (start_expr, end_expr) = match range_local {
            Some(local_idx) => {
                match self.resolve_range_bounds_from_local(local_idx, modified_locals) {
                    Some(bounds) => bounds,
                    None => {
                        debug!(
                            fn_name = %self.fn_name,
                            "CHC slice range: cannot extract Range fields; fallback"
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
                }
            }
            None => {
                debug!(
                    fn_name = %self.fn_name,
                    "CHC slice range: index not a bare local; fallback"
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
            warn!(fn_name = %self.fn_name, "CHC slice range: start coerce failed; fallback");
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
        let Some(end_bv) = self.coerce_to_pointer_width(end_expr) else {
            warn!(fn_name = %self.fn_name, "CHC slice range: end coerce failed; fallback");
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

        // Bounds guard: start > end -> error (reversed range).
        let reversed = start_bv.clone().bvugt(end_bv.clone());
        let error_app = RelationApp::new("error", Vec::new());
        let body =
            RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, [reversed]);
        self.vc.add_rule(Rule::new(body, error_app.clone()));

        // OOB bounds guard.
        let slice_backing = self.resolve_slice_backing(slice_arg, modified_locals);
        if slice_backing.is_none() {
            let sl = match slice_arg {
                Operand::Copy(p) | Operand::Move(p) => Some((p.local, p.projection.len())),
                _ => None,
            };
            tracing::debug!(
                fn_name = %self.fn_name,
                ?sl,
                "slice range backing resolution failed for Range index"
            );
        }
        let effective_start =
            slice_backing.as_ref().map(|backing| backing.offset.clone().bvadd(start_bv.clone()));
        if let Some(ref backing) = slice_backing {
            let oob = if inclusive {
                end_bv.clone().bvuge(backing.len.clone())
            } else {
                end_bv.clone().bvugt(backing.len.clone())
            };
            let body =
                RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, [oob]);
            self.vc.add_rule(Rule::new(body, error_app));
        }

        // Register subslice data in side tables.
        if let (Some(backing), Some(effective_start)) = (&slice_backing, &effective_start) {
            self.ref_resolution.const_ref_values.insert(dest_local, backing.data.clone());
            self.ref_resolution.subslice_offset.insert(dest_local, effective_start.clone());

            let subslice_len = if inclusive {
                end_bv.bvsub(start_bv).bvadd(Expr::bitvec_const(1, POINTER_WIDTH))
            } else {
                end_bv.bvsub(start_bv)
            };
            self.ref_resolution.subslice_len.insert(dest_local, subslice_len);

            debug!(
                fn_name = %self.fn_name,
                dest_local,
                inclusive,
                "CHC slice range: registered subslice data/offset/len in side tables"
            );
        } else {
            debug!(
                fn_name = %self.fn_name,
                "CHC slice range: source not resolved; subslice data not registered"
            );
        }

        // Mem-level: build shifted inner array via rebase.
        let elem_ty = self.chc_slice_elem_ty(slice_arg);
        let Some(backing) = slice_backing.as_ref() else {
            debug!(
                fn_name = %self.fn_name,
                source_resolved = false,
                elem_ty_resolved = elem_ty.is_some(),
                "CHC slice range: source inner array not resolved; sound fallback"
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
        };
        let Some(elem_ty) = elem_ty else {
            debug!(
                fn_name = %self.fn_name,
                source_resolved = true,
                elem_ty_resolved = false,
                "CHC slice range: source inner array not resolved; sound fallback"
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
        };
        let inner_arr_sort = backing.data.sort().clone();
        let effective_start =
            effective_start.expect("invariant: source resolution requires slice backing");

        if backing.data.sort() != &inner_arr_sort
            || !Self::is_zero_pointer_width_bitvec(&effective_start)
        {
            self.record_aggregate_gap("slice_range_sort_or_offset_mismatch");
        }
        // Part of #3979: Use effective_start (accumulated offset) as rebase origin.
        // For subslice-of-subslice, backing.offset is only the first range's offset.
        // effective_start = backing.offset + start_bv, giving the correct absolute
        // position in the underlying array.
        let rebase_backing = ResolvedSliceBacking {
            data: backing.data.clone(),
            len: backing.len.clone(),
            offset: effective_start,
        };
        let Some(shifted) = self.rebase_slice_backing_to_zero_based_array(
            &rebase_backing,
            &inner_arr_sort,
            "__subslice_base",
            SLICE_BACKING_REBASE_MAX_ELEMS,
        ) else {
            debug!(
                fn_name = %self.fn_name,
                "CHC slice range: failed to rebase backing array; sound fallback"
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
        };

        // Part of #4030: source-derived address preserves pointer identity
        // for fat pointer comparison (e.g., &array[0..2] vs &array[0..4]
        // share the same data pointer when start offsets match).
        let mut addr_override = self.resolve_subslice_source_addr(
            slice_arg,
            &rebase_backing.offset,
            elem_ty,
            modified_locals,
        );

        // Strategy 3: cache lookup by (provenance_local, start_const).
        // Covers heap allocations (Box deref) where source address resolution
        // fails but identical subslice operations should share a data pointer.
        let cache_key = self.subslice_cache_key(slice_arg, &rebase_backing.offset);
        if addr_override.is_none() {
            if let Some(key) = &cache_key {
                addr_override = self.ref_resolution.subslice_addr_cache.get(key).cloned();
            }
        }

        // Shared tail: type-array materialization + destination emission.
        let Some(mat) =
            self.materialize_subslice_type_array(shifted, inner_arr_sort, elem_ty, addr_override)
        else {
            warn!(fn_name = %self.fn_name, "CHC slice range: alloc ID overflow; fallback");
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

        // Cache the address for future subslice operations from the same source.
        if let Some(key) = cache_key {
            self.ref_resolution
                .subslice_addr_cache
                .entry(key)
                .or_insert_with(|| mat.fresh_addr.clone());
        }

        self.emit_subslice_destination(
            cx,
            dest_local,
            mat.fresh_addr,
            "codegen_call_slice::SliceIndex_Range_subslice",
            "codegen_call_slice_range::fat_ptr_len",
        );
    }
}
