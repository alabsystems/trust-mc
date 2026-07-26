// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! DST field-ref string backing resolution.
//!
//! Handles the MIR pattern `_local = &(*_parent).field` where `field: str`,
//! used by custom DSTs with str fields. Traces through the parent struct
//! to resolve the string backing with field-offset adjustment.
//!
//! Part of #4118: custom DST string backing.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};

use crate::codegen_ay::types::POINTER_WIDTH;

use super::super::super::ChcCtx;
use super::codegen_call_string_backing::StringBacking;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Part of #4118: resolve backing for an `&str` local created from a Ref
    /// to a `str` field of a custom DST.
    ///
    /// Detects the MIR pattern:
    ///   `_local = &(*_parent).field` where `field: str`
    ///
    /// When found, computes the field byte offset, resolves the parent local's
    /// string backing (tracing through Calls via the first argument if needed),
    /// and returns a `StringBacking` with the offset adjusted by the field
    /// position.
    pub(super) fn resolve_string_backing_from_str_field_ref(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<StringBacking> {
        // Step 1: Find `_local = &(*_parent).field` where `field: str`.
        let (source_local, field_idx, parent_ty) = self.find_str_field_ref_source(local)?;
        tracing::debug!(
            local,
            source_local,
            field_idx,
            ?parent_ty,
            "[#4118] found str field ref pattern"
        );

        // Step 2: Compute field byte offset.
        let field_offset = self.get_field_offset(parent_ty, field_idx)?;
        tracing::debug!(field_offset, "[#4118] computed field offset");
        let field_offset_expr = Expr::bitvec_const(field_offset as u128, POINTER_WIDTH);

        // Step 3: Resolve the parent local's string backing.
        let parent_backing = self
            .resolve_string_backing_local(source_local, modified_locals)
            .or_else(|| {
                let resolved = self.resolve_provenance_local(source_local);
                if resolved != source_local {
                    self.resolve_string_backing_local(resolved, modified_locals)
                } else {
                    None
                }
            })
            .or_else(|| {
                self.resolve_string_backing_from_call_first_arg(source_local, modified_locals)
            })?;

        // Step 4: Return backing with offset adjusted by field position.
        let adjusted_offset = parent_backing.offset.bvadd(field_offset_expr);
        let len =
            self.ref_resolution.subslice_len.get(&local).cloned().unwrap_or(parent_backing.len);

        Some(StringBacking { data: parent_backing.data, len, offset: adjusted_offset })
    }

    /// Scan MIR for `_local = &(*_source).field` where `field: str`.
    /// Returns `(source_local, field_index, parent_type)`.
    fn find_str_field_ref_source(
        &self,
        local: usize,
    ) -> Option<(usize, usize, rustc_public::ty::Ty)> {
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if lhs.local != local || !lhs.projection.is_empty() {
                    continue;
                }
                let (Rvalue::Ref(_, _, ref_place) | Rvalue::AddressOf(_, ref_place)) = rhs else {
                    continue;
                };
                if ref_place.projection.len() == 2
                    && matches!(ref_place.projection[0], ProjectionElem::Deref)
                {
                    if let ProjectionElem::Field(field_idx, field_ty) = &ref_place.projection[1] {
                        if matches!(field_ty.kind(), TyKind::RigidTy(RigidTy::Str)) {
                            let parent_ref_ty = self.body.locals().get(ref_place.local)?.ty;
                            let parent_ty = match parent_ref_ty.kind() {
                                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                                | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
                                _ => parent_ref_ty,
                            };
                            return Some((ref_place.local, *field_idx, parent_ty));
                        }
                    }
                }
            }
        }
        None
    }

    /// Part of #4118: When a local was produced by a Call terminator, trace
    /// through the first argument to resolve string backing.
    fn resolve_string_backing_from_call_first_arg(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<StringBacking> {
        for bb_data in &self.body.blocks {
            let TerminatorKind::Call { args, destination, .. } = &bb_data.terminator.kind else {
                continue;
            };
            if destination.local != local {
                continue;
            }
            let (Operand::Copy(place) | Operand::Move(place)) = args.first()? else {
                return None;
            };
            let arg_local = if place.projection.is_empty() {
                place.local
            } else {
                continue;
            };

            let resolved_arg = self.resolve_provenance_local(arg_local);
            tracing::debug!(
                local,
                arg_local,
                resolved_arg,
                "[#4118] tracing call first arg for backing"
            );

            if let Some(backing) = self.resolve_string_backing_local(resolved_arg, modified_locals)
            {
                return Some(backing);
            }
            if resolved_arg != arg_local {
                if let Some(backing) = self.resolve_string_backing_local(arg_local, modified_locals)
                {
                    return Some(backing);
                }
            }
        }
        None
    }
}
