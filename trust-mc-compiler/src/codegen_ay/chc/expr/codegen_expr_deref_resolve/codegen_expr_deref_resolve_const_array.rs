// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Const-ref array index resolution for MIR deref places.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::ProjectionElem;
use tracing::debug;

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

use super::super::ChcCtx;
use super::super::codegen_stmt_projection::FieldProjection;
use super::super::constant_index_offset;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(super) fn try_resolve_const_array_deref_index(
        &mut self,
        local_idx: usize,
        val: &Expr,
        remaining: &[ProjectionElem],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if !val.sort().is_array() {
            return None;
        }

        let (index_expr, rest): (Expr, &[ProjectionElem]) = match remaining {
            [ProjectionElem::Index(idx_local), rest @ ..] => {
                let raw = self.resolve_local_expr(*idx_local, modified_locals)?;
                (coerce_bitvec_width_safe(raw, POINTER_WIDTH, SignExtension::ZeroExtend), rest)
            }
            [ProjectionElem::ConstantIndex { offset, min_length, from_end }, rest @ ..] => {
                // #from_end needs the slice's runtime length -> fail closed (projection_path.rs)
                let Some(actual_offset) = constant_index_offset(*offset, *min_length, *from_end)
                else {
                    return None;
                };
                (Expr::bitvec_const(actual_offset as u128, POINTER_WIDTH), rest)
            }
            _ => return None,
        };

        let pointee_ty = Self::deref_pointee_ty(self.body.locals()[local_idx].ty)?;
        if let Some(len_expr) =
            self.ref_resolution.subslice_len.get(&local_idx).cloned().or_else(|| {
                self.get_array_length(pointee_ty)
                    .map(|array_len| Expr::bitvec_const(array_len as u128, POINTER_WIDTH))
            })
        {
            self.heap_state.pending_checks.push(index_expr.clone().bvult(len_expr));
        }

        let elem_ty = self.get_array_element_ty(pointee_ty);
        let effective_index =
            if let Some(offset) = self.ref_resolution.subslice_offset.get(&local_idx).cloned() {
                index_expr.bvadd(offset)
            } else {
                index_expr
            };
        let mut current = val.clone().select(effective_index);
        if let Some(ty) = elem_ty {
            current = self.try_unflatten_bv_to_datatype(current, ty);
        }

        if rest.is_empty() {
            debug!(local_idx, "CHC: resolved const array deref+index via const_ref_values");
            return Some(current);
        }

        if rest.iter().all(|p| matches!(p, ProjectionElem::Field(..))) {
            let field_selections: Vec<FieldProjection> = rest
                .iter()
                .filter_map(|p| {
                    if let ProjectionElem::Field(idx, ty) = p {
                        Some(FieldProjection {
                            field_idx: *idx,
                            cons_idx: None,
                            field_ty: Some(*ty),
                        })
                    } else {
                        None
                    }
                })
                .collect();
            if let Some(result) = Self::apply_field_selections(current, &field_selections) {
                debug!(
                    local_idx,
                    n_fields = field_selections.len(),
                    "CHC: resolved const array deref+index+field via const_ref_values"
                );
                return Some(result);
            }
        }

        None
    }
}
