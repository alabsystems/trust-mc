// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Metadata propagation for pointer offset call results.

use ay_bindings::Expr;
use rustc_public::mir::Operand;

use super::ChcCtx;
use crate::codegen_ay::types::POINTER_WIDTH;

enum PtrOffsetMetadataDirection {
    Add,
    Sub,
    Signed,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn propagate_ptr_add_result_metadata(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
    ) {
        self.propagate_ptr_offset_result_metadata_from_args(
            dest_local,
            args,
            modified_locals,
            PtrOffsetMetadataDirection::Add,
        );
    }

    pub(in crate::codegen_ay::chc) fn propagate_ptr_sub_result_metadata(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
    ) {
        self.propagate_ptr_offset_result_metadata_from_args(
            dest_local,
            args,
            modified_locals,
            PtrOffsetMetadataDirection::Sub,
        );
    }

    pub(in crate::codegen_ay::chc) fn propagate_signed_ptr_offset_result_metadata(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
    ) {
        self.propagate_ptr_offset_result_metadata_from_args(
            dest_local,
            args,
            modified_locals,
            PtrOffsetMetadataDirection::Signed,
        );
    }

    fn propagate_ptr_offset_result_metadata_from_args(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
        direction: PtrOffsetMetadataDirection,
    ) {
        let Some(src_local) = args.first().and_then(|arg| match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        }) else {
            self.clear_ptr_offset_metadata(dest_local);
            return;
        };

        let delta =
            args.get(1)
                .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals))
                .and_then(|expr| match direction {
                    PtrOffsetMetadataDirection::Add => Self::const_usize_from_expr(&expr)
                        .and_then(|count| i128::try_from(count).ok()),
                    PtrOffsetMetadataDirection::Sub => Self::const_usize_from_expr(&expr)
                        .and_then(|count| i128::try_from(count).ok())
                        .and_then(|count| count.checked_neg()),
                    PtrOffsetMetadataDirection::Signed => Self::const_isize_from_expr(&expr),
                });

        self.propagate_ptr_offset_result_metadata_from_parts(dest_local, src_local, delta);
    }

    pub(in crate::codegen_ay::chc) fn propagate_ptr_offset_result_metadata_from_parts(
        &mut self,
        dest_local: usize,
        src_local: usize,
        delta: Option<i128>,
    ) {
        // PROVENANCE (allocation id) is invariant under pointer offset
        // arithmetic — for ANY delta, const or symbolic — so carry
        // known_alloc_ids from the base to the result. This keeps the offset
        // alloc-bound check's metadata side-channel alive on derived pointers
        // (ptr.add(k).sub(1), offset(other_ptr, i)). SCOPED to promoted-const
        // allocations: for heap/stack ids the provenance demotion is the
        // load-bearing fail-closed net over still-missing models (uninit
        // shadow memory) — carrying those ids resolved alloc-to-slice's UB
        // harness into a false Safe.
        if let Some(obj_id) = self
            .known_alloc_ids
            .get(&src_local)
            .copied()
            .filter(|&id| self.is_promoted_const_obj_id(id))
        {
            self.known_alloc_ids.insert(dest_local, obj_id);
        } else {
            self.known_alloc_ids.remove(&dest_local);
        }

        // Symbolic step (delta unknown at compile time): the destination's
        // referent element is statically unknown, so element-precise tracking
        // (ref_targets / const_ref_values / subslice_*) cannot be carried
        // over. Keeping the source's backing-array view here made derefs of
        // `base.add(sym_i)` resolve through an offset-less array select —
        // reads compared the raw split-pointer address against element
        // indices, matched nothing, and returned the default lane: a silent
        // false proof on OOB harnesses and a false CTREX on in-bounds ones.
        // Clearing forces the deref onto the address-based memory path where
        // heap_access_checks emits real bounds obligations.
        if delta.is_none() {
            self.clear_ptr_offset_metadata(dest_local);
            return;
        }

        let mut shifted_ref_projection = false;
        let mut shifted_const_value = None;

        if let Some(mut ref_target) = self.ref_resolution.ref_targets.get(&src_local).cloned() {
            shifted_ref_projection = delta.is_some_and(|delta| {
                self.shift_ref_target_constant_index(
                    ref_target.local,
                    &mut ref_target.projections,
                    delta,
                )
            });
            if shifted_ref_projection {
                shifted_const_value = self.const_array_element_for_ref_target(&ref_target);
            }
            self.ref_resolution.ref_targets.insert(dest_local, ref_target);
            self.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
        } else {
            self.ref_resolution.ref_targets.remove(&dest_local);
            self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
        }

        if let Some(value) = self.ref_resolution.const_ref_values.get(&src_local).cloned() {
            self.ref_resolution.const_ref_values.insert(dest_local, value);
        } else if let Some(value) = shifted_const_value {
            self.ref_resolution.const_ref_values.insert(dest_local, value);
        } else {
            self.ref_resolution.const_ref_values.remove(&dest_local);
        }

        if let Some(len) = self.ref_resolution.subslice_len.get(&src_local).cloned() {
            self.ref_resolution.subslice_len.insert(dest_local, len);
        } else {
            self.ref_resolution.subslice_len.remove(&dest_local);
        }

        if shifted_ref_projection {
            self.ref_resolution.subslice_offset.remove(&dest_local);
            return;
        }

        let base_offset = self
            .ref_resolution
            .subslice_offset
            .get(&src_local)
            .and_then(Self::const_usize_from_expr)
            .unwrap_or(0);
        let offset = delta.and_then(|delta| Self::apply_signed_metadata_offset(base_offset, delta));
        if let Some(offset) = offset {
            self.ref_resolution
                .subslice_offset
                .insert(dest_local, Expr::bitvec_const(offset as u64, POINTER_WIDTH));
        } else {
            self.ref_resolution.subslice_offset.remove(&dest_local);
            self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
        }
    }
}
