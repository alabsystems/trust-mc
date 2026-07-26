// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Projection-path decoding helpers for CHC statement encoding.

use rustc_public::mir::ProjectionElem;
use tracing::warn;

use crate::rustc_public_bridge::IndexedVal;

use super::super::codegen_ctx::diagnostics::{CellCounter, ChcDiagnostics};

/// A field projection extracted from MIR projection elements.
///
/// Carries field type information needed for marker field detection.
/// Used by `apply_field_selections` and `apply_projection_update` to handle
/// ZST marker fields (like PhantomData) which are represented as compact scalars
/// but should be no-ops for field access.
///
/// Note: `field_ty` is Optional to support unit tests that run outside the
/// rustc_public context, where TLV (thread-local variable) is not initialized.
#[derive(Clone, Copy)]
pub(in crate::codegen_ay::chc) struct FieldProjection {
    /// Field index within the struct/variant
    pub(in crate::codegen_ay::chc) field_idx: usize,
    /// Constructor index for enum variants (from Downcast projection)
    pub(in crate::codegen_ay::chc) cons_idx: Option<usize>,
    /// Field type - used to check if this is a ZST marker field.
    /// `None` skips marker detection (used by unit tests outside rustc_public context
    /// to avoid TLV.is_set panics).
    pub(in crate::codegen_ay::chc) field_ty: Option<rustc_public::ty::Ty>,
}

/// Compute actual array index for a ConstantIndex projection.
/// MIR's `from_end` flag counts backwards from `min_length`.
///
/// Part of #3329: extracted from 7 duplicate instances across 6 files.
#[inline]
pub(in crate::codegen_ay::chc) fn constant_index_offset(
    offset: u64,
    min_length: u64,
    from_end: bool,
) -> u64 {
    if from_end { min_length.saturating_sub(offset) } else { offset }
}

/// Policy for non-Field/Downcast projections encountered during collection.
///
/// Part of #3329: unifies `collect_field_projections_with_downcast` and
/// `extract_field_projections` into a single function with configurable
/// error handling.
pub(in crate::codegen_ay::chc) enum UnknownProjectionPolicy<'a> {
    /// Stop collecting and return what we have so far.
    Break,
    /// Skip unknown projections, continue collecting.
    Skip,
    /// Return empty Vec, increment diagnostic counter, and warn.
    ReturnEmpty(&'a ChcDiagnostics),
}

/// Collects FieldProjection entries from a projection slice, tracking
/// Downcast variants as constructor indices on the subsequent Field.
///
/// The `on_unknown` policy controls behavior when a non-Downcast/Field
/// projection is encountered:
/// - `Break`: stop and return collected-so-far (for LHS slices)
/// - `Skip`: silently skip (for ref_target projections)
/// - `ReturnEmpty`: bail with diagnostics (for strict extraction)
///
/// Part of #3329: unified from `collect_field_projections_with_downcast`
/// and `extract_field_projections`.
#[track_caller]
pub(in crate::codegen_ay::chc) fn collect_field_projections(
    projections: &[ProjectionElem],
    on_unknown: UnknownProjectionPolicy<'_>,
) -> Vec<FieldProjection> {
    let mut projs = Vec::new();
    let mut pending_cons_idx: Option<usize> = None;
    for p in projections {
        match p {
            ProjectionElem::Downcast(variant_idx) => {
                pending_cons_idx = Some(variant_idx.to_index());
            }
            ProjectionElem::Field(idx, ty) => {
                projs.push(FieldProjection {
                    field_idx: *idx,
                    cons_idx: pending_cons_idx.take(),
                    field_ty: Some(*ty),
                });
            }
            _ => match &on_unknown {
                UnknownProjectionPolicy::Break => break,
                UnknownProjectionPolicy::Skip => {}
                UnknownProjectionPolicy::ReturnEmpty(diagnostics) => {
                    let caller = std::panic::Location::caller();
                    diagnostics.unsupported_field_projection.inc();
                    warn!(
                        caller = %format_args!("{}:{}", caller.file(), caller.line()),
                        ?p,
                        ?projections,
                        "collect_field_projections: unsupported projection"
                    );
                    return Vec::new();
                }
            },
        }
    }
    projs
}
