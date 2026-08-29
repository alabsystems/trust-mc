// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! References that point INTO a collection element.
//!
//! `_r = &((*_e).f1.f2…)` where `_e` came from `Index::index` /
//! `IndexMut::index_mut` is NOT a fresh heap address — it is a LOCATION in the
//! collection's value lane, the same lane the direct read `v[0].base.0`
//! resolves through.
//!
//! Before this module the Mem-level ref encoder minted a symbolic address for
//! such a place (`ref_address.rs`), because `_e` is a CALL destination and so
//! has neither a `ref_target` nor a `mir_provable_referent_local` for the
//! decl-time `collect_numeric_ref_targets` pass to resolve. Reads through the
//! minted address then landed in a type-indexed memory array
//! (`_main_mem_u64`) that `Vec::push` never wrote — push stores into the Vec
//! datatype's `fld_data` — so the value compared was a free variable and true
//! assertions were refuted. `Vectors/sort_by_key.rs` reported a counterexample
//! for `regions[0].guest_base == GuestAddress(0)` on a ONE-element Vec.
//!
//! `collection_index_refs` / `collection_mut_refs` already carry the
//! `(collection_local, index_expr)` context; they are populated at
//! call-codegen time, i.e. AFTER the decl-time ref-target pass has run, so the
//! resolution point has to be the USE site rather than a bigger Pass 2. This
//! module is that resolution point: [`ChcCtx::register_collection_elem_field_ref`]
//! records the projection at the `Rvalue::Ref` statement, and
//! [`ChcCtx::resolve_collection_elem_field_ref_value`] rebuilds the value as
//! `field_f2(field_f1(select(fld_data(c), i)))` at the read.
//!
//! Fail-closed rule: when the element location cannot be built, the resolver
//! records a fail-closing sound-fallback and declines. It never invents a
//! value and never blesses the minted address as a place to read from.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use tracing::debug;

use super::super::ChcCtx;
use crate::codegen_ay::chc::codegen_ctx::types::{
    CollectionElemFieldRef, CollectionMutRef, CollectionProjectionKind,
};
use crate::codegen_ay::provenance::Val;
use crate::rustc_public_bridge::IndexedVal;

/// Vec datatype field index for the backing data array (`fld_data`).
const VEC_FLD_DATA: usize = 3;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Record `dest = &((*base).f1.f2…)` when `base` denotes a collection
    /// element, so the use site can read through the collection's value lane
    /// instead of the address the Mem-level ref lane is about to mint.
    ///
    /// Only a leading `Deref` followed by pure field/downcast projections is
    /// recorded. Anything else (a nested `Index`, a subslice) is declined
    /// rather than approximated — an unrecorded local simply keeps the existing
    /// behaviour.
    pub(in crate::codegen_ay::chc) fn register_collection_elem_field_ref(
        &mut self,
        dest_local: Option<usize>,
        place: &Place,
    ) {
        let Some(dest) = dest_local else {
            return;
        };
        if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            return;
        }
        let base = place.local;
        // The base is either already a recorded element projection (chained
        // `&(*_r).f`) or the `Index`/`IndexMut` destination itself.
        let (base_ref_local, mut elem_fields) =
            if let Some(existing) = self.ref_resolution.collection_elem_field_refs.get(&base) {
                (existing.base_ref_local, existing.elem_fields.clone())
            } else if self.ref_resolution.collection_index_refs.contains_key(&base) {
                (base, Vec::new())
            } else {
                // READ-ONLY `Index::index` results only. A `&mut` element reference
                // (`collection_mut_refs`) is deliberately excluded: its STORE side
                // is routed into `fld_data` by `handle_collection_mut_ref_store`
                // only for the index_mut destination ITSELF, so adding a read lane
                // for copies of it would split the two — a store through the copy
                // would land in memory while the read came back from `fld_data`,
                // and a stale read can PROVE a false post-condition. Read-only
                // element references cannot be written through at all, so no such
                // split is possible for them.
                return;
            };

        let mut pending_cons: Option<usize> = None;
        for proj in &place.projection[1..] {
            match proj {
                ProjectionElem::Field(idx, _) => elem_fields.push((*idx, pending_cons.take())),
                ProjectionElem::Downcast(variant) => {
                    pending_cons = Some(IndexedVal::to_index(variant));
                }
                _ => return, // external enum: ProjectionElem — not a field path.
            }
        }

        debug!(
            fn_name = %self.fn_name,
            dest,
            base_ref_local,
            ?elem_fields,
            "CHC: recorded reference into collection element (value lane, not an address)"
        );
        self.ref_resolution
            .collection_elem_field_refs
            .insert(dest, CollectionElemFieldRef { base_ref_local, elem_fields });
    }

    /// Read the VALUE denoted by a reference into a collection element.
    ///
    /// Returns `None` when `local` is not such a reference (the caller then
    /// carries on unchanged). When it IS one but the element location cannot be
    /// built, this records a fail-closing sound fallback before returning
    /// `None`, so a harness that ends up reading the minted address reports
    /// UNDETERMINED rather than a fabricated counterexample.
    pub(in crate::codegen_ay::chc) fn resolve_collection_elem_field_ref_value(
        &mut self,
        local: usize,
        extra_fields: &[(usize, Option<usize>)],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let (base_ref_local, mut elem_fields) =
            if let Some(rec) = self.ref_resolution.collection_elem_field_refs.get(&local) {
                (rec.base_ref_local, rec.elem_fields.clone())
            } else if self.ref_resolution.collection_index_refs.contains_key(&local) {
                (local, Vec::new())
            } else {
                return None;
            };

        let Some(cmr) = self.ref_resolution.collection_index_refs.get(&base_ref_local).cloned()
        else {
            return None;
        };

        elem_fields.extend_from_slice(extra_fields);
        match self.collection_elem_value(&cmr, &elem_fields, modified_locals) {
            Some(expr) => {
                debug!(
                    fn_name = %self.fn_name,
                    local,
                    base_ref_local,
                    coll_local = cmr.collection_local,
                    "CHC: collection-element ref resolved through the collection value lane"
                );
                Some(expr)
            }
            None => {
                // The reference IS into a collection element, but the location
                // could not be rebuilt. Do NOT let the caller fall through to a
                // type-indexed memory array the collection was never stored
                // into — that is the fabricated-counterexample shape. Fail closed.
                debug!(
                    fn_name = %self.fn_name,
                    local,
                    coll_local = cmr.collection_local,
                    "CHC: collection-element ref location unresolved — failing closed"
                );
                self.record_sound_fallback_reason("collection_elem_ref_location_unresolved");
                None
            }
        }
    }

    /// Parse `place.projection[1..]` (everything after the leading `Deref`) as
    /// a pure field path. Returns `None` when any other projection appears —
    /// an `Index`, a subslice — which this lane does not model.
    pub(in crate::codegen_ay::chc) fn collection_elem_trailing_fields(
        place: &Place,
    ) -> Option<Vec<(usize, Option<usize>)>> {
        let mut fields = Vec::new();
        let mut pending_cons: Option<usize> = None;
        for proj in place.projection.get(1..)? {
            match proj {
                ProjectionElem::Field(idx, _) => fields.push((*idx, pending_cons.take())),
                ProjectionElem::Downcast(variant) => {
                    pending_cons = Some(IndexedVal::to_index(variant));
                }
                _ => return None, // external enum: ProjectionElem
            }
        }
        Some(fields)
    }

    /// `field_fn(… field_f1(select(fld_data(c), i)) …)` for the element the
    /// `CollectionMutRef` addresses.
    ///
    /// Struct-embedded collections (`cmr.field_projections` non-empty) are
    /// declined: the flattened field indices used below address a bare
    /// collection local, so a struct-embedded receiver would read the wrong
    /// slots. The caller turns that into a fail-closed drop.
    fn collection_elem_value(
        &mut self,
        cmr: &CollectionMutRef,
        elem_fields: &[(usize, Option<usize>)],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if !cmr.field_projections.is_empty() {
            return None;
        }
        let coll_local = cmr.collection_local;

        // Path A: projected collection (ptr/len/cap/data as flat state vars).
        let data = if self.collections.projection_locals.get(&coll_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            self.flattened_local_field_expr(coll_local, VEC_FLD_DATA, modified_locals)
                .filter(|d| d.sort().is_array())
        } else {
            None
        }
        // Path B: the collection is a single datatype-sorted value.
        .or_else(|| {
            let coll_place = Place { local: coll_local, projection: Vec::new() };
            let vec_expr = self.translate_place_with_modified(&coll_place, modified_locals)?;
            vec_expr.sort().datatype_name()?;
            let (_, _, _, data) =
                super::super::codegen_call_vec::ChcVecFields::extract_without_name(vec_expr)?;
            data.sort().is_array().then_some(data)
        })?;

        let elem = data.select(cmr.index_expr.clone());
        let mut val = Val::of_value(elem);
        for &(field_idx, cons_idx) in elem_fields {
            val = Self::datatype_field_select(&val, field_idx, cons_idx)?;
        }
        Some(val.into_expr())
    }
}
