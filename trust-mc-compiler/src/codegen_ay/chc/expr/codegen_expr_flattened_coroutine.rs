// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Coroutine-root projection handling for flattened locals.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use tracing::warn;

use super::ChcCtx;
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_ctx::record_translation_drop_site_reason_for_fn;
use super::codegen_types::CodegenTypes;

pub(super) enum FlattenedCoroutineRootProjection {
    NotApplicable,
    Translated(Expr),
    Failed,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolves field projections on flattened coroutine roots through the
    /// coroutine-root datatype view. MIR field indices on coroutine roots refer
    /// to direct fields or variant views, not to flattened leaf slots.
    pub(super) fn translate_flattened_coroutine_root_projection(
        &self,
        place: &Place,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> FlattenedCoroutineRootProjection {
        if place.projection.is_empty() {
            return FlattenedCoroutineRootProjection::NotApplicable;
        }

        let has_field =
            place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Field(..)));
        if !has_field {
            return FlattenedCoroutineRootProjection::NotApplicable;
        }

        let Some(local_decl) = self.body.locals().get(local_idx) else {
            return FlattenedCoroutineRootProjection::NotApplicable;
        };
        let local_ty = self
            .resolve_inline_local_ty(self.body, local_idx)
            .unwrap_or_else(|| self.resolve_body_ty(local_decl.ty));
        let Some(local_sort) = Self::translate_ty(local_ty) else {
            return FlattenedCoroutineRootProjection::NotApplicable;
        };
        if !crate::codegen_ay::types::is_coroutine_root_sort(&local_sort) {
            return FlattenedCoroutineRootProjection::NotApplicable;
        }

        let supported_projection_chain = place.projection.iter().all(|proj| {
            matches!(
                proj,
                ProjectionElem::Downcast(_)
                    | ProjectionElem::Field(..)
                    | ProjectionElem::OpaqueCast(_)
                    | ProjectionElem::Index(_)
                    | ProjectionElem::ConstantIndex { .. }
                    | ProjectionElem::Subslice { .. }
            )
        });
        if !supported_projection_chain {
            self.record_flattened_coroutine_root_projection_drop(local_idx, place);
            return FlattenedCoroutineRootProjection::Failed;
        }

        let Some(root) = self.reconstruct_flattened_root(local_idx, modified_locals) else {
            self.record_flattened_coroutine_root_projection_drop(local_idx, place);
            return FlattenedCoroutineRootProjection::Failed;
        };
        let projections: Vec<_> = place
            .projection
            .iter()
            .filter(|proj| !matches!(proj, ProjectionElem::OpaqueCast(_)))
            .cloned()
            .collect();
        let Some(expr) =
            self.translate_place_field_index(&projections, root, Some(local_ty), modified_locals)
        else {
            self.record_flattened_coroutine_root_projection_drop(local_idx, place);
            return FlattenedCoroutineRootProjection::Failed;
        };
        FlattenedCoroutineRootProjection::Translated(expr)
    }

    fn record_flattened_coroutine_root_projection_drop(&self, local_idx: usize, place: &Place) {
        self.diagnostics.place_translation_drop.inc();
        record_translation_drop_site_reason_for_fn(
            &self.fn_name,
            "flattened_projection_unsupported",
        );
        warn!(
            local_idx,
            projections = ?place.projection,
            "translate_place: unsupported coroutine-root projection on flattened local"
        );
    }
}
