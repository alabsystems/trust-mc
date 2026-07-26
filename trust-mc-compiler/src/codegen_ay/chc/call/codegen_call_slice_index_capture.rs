// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{AggregateKind, Operand, Place, ProjectionElem, StatementKind};
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve `Vec` backing arrays through closure-capture reference chains.
    ///
    /// When a closure captures a `Vec` by reference (`|| a[0] + 2`), slice
    /// lowering often sees a raw pointer-typed capture field instead of a
    /// directly resolvable `Vec` local. This helper follows the closure
    /// aggregate assignment and `ref_targets` metadata back to the original
    /// captured `Vec`, then recovers its `fld_data` array.
    pub(super) fn try_resolve_closure_captured_vec_data(
        &mut self,
        slice_arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let slice_local = match slice_arg {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return None,
        };
        let ref_target = self.ref_resolution.ref_targets.get(&slice_local)?;

        let field_idx = ref_target.projections.iter().find_map(|proj| match proj {
            ProjectionElem::Field(idx, _) => Some(*idx),
            _ => None,
        })?;
        let capture_local = ref_target.local;

        let captured_operand = self.body.blocks.iter().find_map(|block| {
            block.statements.iter().find_map(|stmt| {
                if let StatementKind::Assign(
                    place,
                    rustc_public::mir::Rvalue::Aggregate(AggregateKind::Closure(_, _), fields),
                ) = &stmt.kind
                    && place.local == capture_local
                    && place.projection.is_empty()
                {
                    fields.get(field_idx).cloned()
                } else {
                    None
                }
            })
        })?;

        let captured_ref_local = match &captured_operand {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return None,
        };

        let vec_ref_target = self.ref_resolution.ref_targets.get(&captured_ref_local)?;
        if !vec_ref_target.projections.is_empty() {
            return None;
        }
        let vec_local = vec_ref_target.local;

        if let Some(expr) = self.ref_resolution.const_ref_values.get(&vec_local)
            && expr.sort().is_array()
        {
            debug!(
                slice_local,
                capture_local,
                vec_local,
                "slice_index: resolved Vec data via closure capture -> const_ref_values (#4003)"
            );
            return Some(expr.clone());
        }

        let target_place = Place { local: vec_local, projection: vec![] };
        let resolved = self.translate_place_with_modified(&target_place, modified_locals)?;
        if resolved.sort().is_array() {
            debug!(
                slice_local,
                capture_local,
                vec_local,
                "slice_index: resolved Vec data via closure capture -> state var (#4003)"
            );
            return Some(resolved);
        }

        if let Some(data_sort) = Self::get_dt_field_sort(&resolved, "fld_data")
            && let Some(dt_name) = resolved.sort().datatype_name().map(|s| s.to_string())
        {
            debug!(
                slice_local,
                capture_local,
                vec_local,
                "slice_index: resolved Vec fld_data via closure capture -> DT (#4003)"
            );
            return Some(resolved.field_select(&dt_name, "fld_data", data_sort));
        }

        None
    }
}
