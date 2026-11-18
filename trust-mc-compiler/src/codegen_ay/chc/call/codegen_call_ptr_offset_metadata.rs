// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Metadata propagation for pointer offset call results.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
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
    /// A constant wrapping chain into a fixed integer array keeps its root.
    /// Its element view comes from the complete definition chain, not from
    /// adding to metadata that may have been dropped by an earlier OOB step.
    /// Other roots and unresolved displacements keep the existing refusal.
    pub(in crate::codegen_ay::chc) fn propagate_wrapping_array_pointer_metadata(
        &mut self,
        dest_local: usize,
        args: &[Operand],
    ) {
        use rustc_public::ty::{RigidTy, TyKind};

        let exact = (|| {
            if self.int_lift || POINTER_WIDTH != 64 {
                return None;
            }
            let (Operand::Copy(source) | Operand::Move(source)) = args.first()? else {
                return None;
            };
            if !source.projection.is_empty() {
                return None;
            }
            let target = self.ref_resolution.ref_targets.get(&source.local)?.clone();
            if !target.projections.is_empty() {
                return None;
            }
            let target_ty = self.resolve_body_ty(self.body.locals().get(target.local)?.ty);
            let TyKind::RigidTy(RigidTy::Array(element, _)) = target_ty.kind() else {
                return None;
            };
            let element = self.resolve_body_ty(element);
            if !matches!(element.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_))) {
                return None;
            }
            let source_ty = self.resolve_body_ty(args[0].ty(self.body.locals()).ok()?);
            let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) = source_ty.kind() else {
                return None;
            };
            if self.resolve_body_ty(pointee) != element {
                return None;
            }
            let element_bytes = i128::try_from(self.get_type_size(element)?).ok()?;
            let len = i128::try_from(self.get_array_length(target_ty)?).ok()?;
            if element_bytes == 0 || len.checked_mul(element_bytes)? > i128::from(u32::MAX) {
                return None;
            }
            let displacement = self.native_array_pointer_byte_offset(dest_local, &target)?;
            // This element view covers only a small exact displacement. Far
            // wrapping steps retain their existing full-address model and
            // refusal; its 64-bit residue is not an array element index.
            let displacement = i128::from(i32::try_from(displacement).ok()?);
            Some((target, displacement, element_bytes, len))
        })();

        self.clear_ptr_offset_metadata(dest_local);
        self.ref_resolution.const_memory_provenance.remove(&dest_local);
        self.known_stack_addr_exprs.remove(&dest_local);
        let Some((target, displacement, element_bytes, len)) = exact else {
            return;
        };
        // Retain the allocation for its span/lifetime checks even outside it.
        // An OOB pointer receives no element value or forwarded-array view.
        self.ref_resolution.ref_targets.insert(dest_local, target);
        if displacement >= 0 && displacement % element_bytes == 0 {
            let index = displacement / element_bytes;
            if index <= len {
                self.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
                self.ref_resolution
                    .subslice_offset
                    .insert(dest_local, Expr::bitvec_const(index as u64, POINTER_WIDTH));
            }
        }
    }

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
            self.ref_resolution.const_memory_provenance.remove(&dest_local);
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
        // arithmetic — for ANY delta, const or symbolic — which keeps the
        // offset alloc-bound check's metadata side-channel alive on derived
        // pointers (ptr.add(k).sub(1), offset(other_ptr, i)). SCOPED to
        // constant-memory allocations: for heap/stack ids the provenance
        // demotion is the load-bearing fail-closed net over still-missing
        // models (uninit shadow memory) — carrying those ids resolved
        // alloc-to-slice's UB harness into a false Safe.
        //
        // But a `known_alloc_ids` entry carries an implicit offset of ZERO: it
        // is read back as the deref base `concat(obj, 0)`. So the id rides in
        // `known_alloc_ids` only through a KNOWN ZERO delta; any other delta
        // records it as provenance only (`const_memory_provenance`), which
        // names no address.
        let src_known = self
            .known_alloc_ids
            .get(&src_local)
            .copied()
            .filter(|&id| self.is_const_memory_obj_id(id));
        let src_provenance = src_known
            .or_else(|| self.ref_resolution.const_memory_provenance.get(&src_local).copied())
            .or_else(|| self.ref_resolution.const_ref_objects.get(&src_local).map(|o| o.obj_id));
        self.known_alloc_ids.remove(&dest_local);
        self.ref_resolution.const_memory_provenance.remove(&dest_local);
        match (src_known, src_provenance) {
            (Some(obj_id), _) if delta == Some(0) => {
                self.known_alloc_ids.insert(dest_local, obj_id);
            }
            (_, Some(obj_id)) => {
                self.ref_resolution.const_memory_provenance.insert(dest_local, obj_id);
            }
            _ => {}
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

        let src_elem_bytes = self.body.locals().get(src_local).and_then(|decl| {
            match self.resolve_body_ty(decl.ty).kind() {
                rustc_public::ty::TyKind::RigidTy(
                    rustc_public::ty::RigidTy::RawPtr(inner, _)
                    | rustc_public::ty::RigidTy::Ref(_, inner, _),
                ) => self.get_type_size(inner).and_then(|s| u64::try_from(s).ok()),
                _ => None,
            }
        });
        if let Some(mut ref_target) = self.ref_resolution.ref_targets.get(&src_local).cloned() {
            shifted_ref_projection = delta.is_some_and(|delta| {
                self.shift_ref_target_constant_index(
                    ref_target.local,
                    &mut ref_target.projections,
                    delta,
                    src_elem_bytes,
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

        // D10: a value fact describes exactly one window. It is copied only
        // through a known zero delta (or re-indexed, for an array fact), and
        // re-decoded at the moved window otherwise (`moved_const_value_fact`).
        let known_delta = delta.unwrap_or(0);
        if let Some(value) = self.moved_const_value_fact(src_local, dest_local, known_delta) {
            self.ref_resolution.const_ref_values.insert(dest_local, value);
        } else if let Some(value) = shifted_const_value {
            self.ref_resolution.const_ref_values.insert(dest_local, value);
        } else {
            self.ref_resolution.const_ref_values.remove(&dest_local);
        }
        match self.moved_const_ref_object(src_local, known_delta) {
            Some(object) => {
                self.ref_resolution.const_ref_objects.insert(dest_local, object);
            }
            None => {
                self.ref_resolution.const_ref_objects.remove(&dest_local);
            }
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
