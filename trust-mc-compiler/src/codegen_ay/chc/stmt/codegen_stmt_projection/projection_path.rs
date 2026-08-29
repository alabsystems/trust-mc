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

/// Compute the actual element index for a `ConstantIndex` projection.
///
/// Returns `None` when the index CANNOT be determined statically; every caller
/// must fail closed on `None` (drop the transition / return `NotApplicable` /
/// record a fallback). Never substitute a default — that is the defect this
/// signature exists to prevent.
///
/// # Why `from_end` cannot be answered here
///
/// `min_length` is the **pattern's** minimum length, NOT the slice's runtime
/// length, so `min_length - offset` is simply the wrong cell. MIR settles which
/// inputs reach this branch:
///
/// ```text
/// match a { [.., x] => .. }      a: &mut [i64]     ->  (*_1)[-1 of 1]  from_end
/// match a { [_, .., x] => .. }   a: &mut [i64]     ->  (*_1)[-1 of 2]  from_end
/// match a { [.., x] => .. }      a: &mut [i64; 4]  ->  (*_1)[3 of 4]   direct
/// ```
///
/// Arrays lower to a **direct index** and never set `from_end`, so this branch
/// is reachable only for slices — where the runtime length lives in fat-pointer
/// metadata that this helper does not receive. It was previously computed as
/// `min_length.saturating_sub(offset)`, which PROVED `a[0] == 99` for
/// `match a { [.., x] => *x = 99 }` while refuting the true `a[3] == 99`.
///
/// The read lane (`chc/heap/memory_impl_addr.rs`) follows this rule too: it uses
/// a fixed array length or unanimous MIR provenance for an array-backed slice,
/// and returns `None` when that authority is absent or conflicting. See
/// `tools/soundness-duals/constant_index_from_end_dual.rs`.
///
/// Part of #3329: extracted from 7 duplicate instances across 6 files.
#[inline]
pub(in crate::codegen_ay::chc) fn constant_index_offset(
    offset: u64,
    _min_length: u64,
    from_end: bool,
) -> Option<u64> {
    if from_end { None } else { Some(offset) }
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

#[cfg(test)]
mod constant_index_offset_tests {
    use super::constant_index_offset;

    /// `from_end: false` — MIR already gives the real index. Arrays lower this
    /// way (`(*_1)[3 of 4]`), so this is the ONLY arm arrays ever take.
    #[test]
    fn direct_index_is_the_offset() {
        assert_eq!(constant_index_offset(3, 4, false), Some(3));
        assert_eq!(constant_index_offset(0, 4, false), Some(0));
    }

    /// `from_end: true` reaches this helper only for SLICES, whose runtime
    /// length is not an argument here. It must refuse rather than guess.
    ///
    /// Regression guard for a CONFIRMED FALSE PROOF: this used to return
    /// `min_length.saturating_sub(offset)`, which PROVED `a[0] == 99` for
    /// `fn f(a: &mut [i64]) { match a { [.., x] => *x = 99, _ => {} } }` while
    /// refuting the true `a[3] == 99`. `min_length` is the PATTERN's minimum
    /// (1, 2, 3 ... for `[.., x]`, `[_, .., x]`, `[_, _, .., x]`), never the
    /// slice's length — so the old formula produced 0, 1, 2 where every case
    /// should yield `len - 1`.
    #[test]
    fn from_end_refuses_to_guess() {
        for (offset, min_length) in [(1u64, 1u64), (1, 2), (1, 3), (2, 5)] {
            assert_eq!(
                constant_index_offset(offset, min_length, true),
                None,
                "from_end must fail closed (offset={offset}, min_length={min_length}); \
                 returning min_length-offset here is a false proof"
            );
        }
    }

    /// The old formula's saturating subtraction silently produced 0 — a VALID
    /// index — when `offset > min_length`. Failing closed removes that class.
    #[test]
    fn from_end_never_saturates_to_a_valid_index() {
        assert_eq!(constant_index_offset(9, 2, true), None);
    }
}
