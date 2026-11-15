// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Per-translation memo of the type queries the CHC translator repeats.
//!
//! Every answer here is a pure function of the module and the type, so a memo
//! changes no result, only how often it is computed: once per distinct type in
//! one function's translation, however many instructions, lane steps or bulk
//! objects ask. Without it, a value walk asked the same question at every node
//! it visited (`composite_shape_of` re-walks the subtree it is asked about), so
//! a bulk write or a constant `GEP` chain at nesting depth `d` paid for the
//! whole subtree at each of its `d` levels.
//!
//! # Byte layouts
//!
//! [`ChcFuncTranslator::layout_fact`] asks trust-ir's `Module::ty_layout_shape`
//! once for a type nobody has asked about yet. That call VALIDATES the type's
//! whole layout: a struct's or an array's layout is `Ok` only when every field
//! and element layout under it is (`shape.rs`, the `Ty::Struct` and `Ty::Array`
//! arms, which return the first error they meet). An `Ok` in that call is the
//! same `Ok` a call on the nested type alone returns, because the only thing the
//! enclosing call adds is its cycle guard, and a cycle guard can only turn an
//! answer into an error. So once the outer call succeeds, every struct and array
//! nested in it is seeded from what trust-ir just validated, by the formulas of
//! those two arms: a struct is its declared `size` (in bytes, times 8), an array
//! is its element's size times its length with that size as its stride. Every
//! other nested type is asked directly when someone needs it. A chain of nested
//! types therefore costs ONE trust-ir walk, not one per level.
//!
//! trust-ir does not memoize inside one call, so that one walk is linear in the
//! UNFOLDED type tree: a type that shares a sub-type between two fields at every
//! level (`P{k+1} = { a: Pk, b: Pk }`) costs `2^depth` there. That is trust-ir's
//! to fix, and is recorded as such
//! (`docs/findings/2026-10-01-trust-ir-layout-walk-unfolds-shared-subtypes.md`);
//! nothing here walks a type twice.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use trust_ir::TyLayoutKind;
use trust_ir::ty::Ty;
use trust_ir::value::StructId;

use super::{
    ChcFuncTranslator, CompositeShape, ValueBinding, composite_shape_of, is_scalar_field_ty,
    lifted_sort, sort_matches, ty_to_sort,
};

/// What the translator reads of a type's byte layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct LayoutFact {
    /// `TyLayoutShape::size_bits`.
    pub(super) size_bits: u64,
    /// An array's element stride (`TyLayoutKind::Array::stride_bits`).
    pub(super) stride_bits: Option<u64>,
}

/// The memo tables (see the module documentation). Interior mutability, because
/// every query is a read-only question about the module.
#[derive(Debug, Default)]
pub(super) struct TyFacts {
    composite: RefCell<HashMap<Ty, Option<CompositeShape>>>,
    layout: RefCell<HashMap<Ty, Option<LayoutFact>>>,
    struct_ranges: RefCell<HashMap<StructId, Option<Rc<[(u64, u64)]>>>>,
    gep_lanes: RefCell<HashMap<(Ty, usize, Ty), Option<Ty>>>,
    first_subobjects: RefCell<HashMap<Ty, Option<(usize, Ty)>>>,
    byte_fills: RefCell<HashMap<Ty, bool>>,
}

impl ChcFuncTranslator<'_> {
    /// `composite_shape_of`, once per type.
    pub(super) fn composite_shape(&self, ty: &Ty) -> Option<CompositeShape> {
        if let Some(shape) = self.ty_facts.composite.borrow().get(ty) {
            return shape.clone();
        }
        let shape = composite_shape_of(self.module, ty);
        self.ty_facts.composite.borrow_mut().insert(ty.clone(), shape.clone());
        shape
    }

    /// `binding_matches_ty_at` over the memoized shapes: does `binding` have
    /// exactly the shape and leaf sorts a value of `ty` gets, every scalar leaf
    /// lifted through `depth` enclosing arrays?
    pub(super) fn binding_fits(&self, binding: &ValueBinding, ty: &Ty, depth: u32) -> bool {
        match (binding, self.composite_shape(ty)) {
            (ValueBinding::Scalar(expr), None) => {
                is_scalar_field_ty(ty)
                    && sort_matches(expr.sort(), &lifted_sort(ty_to_sort(ty), depth))
            }
            (ValueBinding::Aggregate(aggregate), Some(CompositeShape::Fields(fields))) => {
                aggregate.fields.len() == fields.len()
                    && aggregate
                        .fields
                        .iter()
                        .zip(&fields)
                        .all(|(field, field_ty)| self.binding_fits(field, field_ty, depth))
            }
            (ValueBinding::Array(array), Some(CompositeShape::Array { elem, len })) => {
                array.len == len
                    && array
                        .lanes
                        .as_ref()
                        .is_none_or(|lanes| self.binding_fits(lanes, &elem, depth + 1))
            }
            _ => false,
        }
    }

    /// trust-ir's byte layout of `ty` (`Module::ty_layout_shape`), `None` where it
    /// has none. One trust-ir walk per type tree: see the module documentation.
    pub(super) fn layout_fact(&self, ty: &Ty) -> Option<LayoutFact> {
        if let Some(fact) = self.ty_facts.layout.borrow().get(ty) {
            return *fact;
        }
        let fact = self.module.ty_layout_shape(ty).ok().map(|shape| LayoutFact {
            size_bits: shape.size_bits,
            stride_bits: match shape.kind {
                TyLayoutKind::Array { stride_bits, .. } => Some(stride_bits),
                _ => None,
            },
        });
        self.ty_facts.layout.borrow_mut().insert(ty.clone(), fact);
        if fact.is_some() {
            self.seed_validated_layouts(ty);
        }
        fact
    }

    /// What the layout memo holds for `ty`: `None` if nobody asked and no
    /// validated walk seeded it.
    #[cfg(test)]
    pub(super) fn memoized_layout(&self, ty: &Ty) -> Option<Option<LayoutFact>> {
        self.ty_facts.layout.borrow().get(ty).copied()
    }

    /// `ty`'s size in whole bytes, `None` without a layout or for a bit size that
    /// is not a whole number of bytes.
    pub(super) fn byte_size(&self, ty: &Ty) -> Option<u64> {
        let bits = self.layout_fact(ty)?.size_bits;
        (bits % 8 == 0).then_some(bits / 8)
    }

    /// Seed every struct and array nested in `root`, whose layout trust-ir has
    /// just validated, from that validation (module documentation). Iterative,
    /// each nested type once.
    fn seed_validated_layouts(&self, root: &Ty) {
        // `(type, its element is seeded)`: an array is sized after its element.
        let mut pending: Vec<(Ty, bool)> = self.layout_children(root);
        while let Some((ty, element_done)) = pending.pop() {
            if self.ty_facts.layout.borrow().contains_key(&ty) {
                continue;
            }
            match &ty {
                Ty::Struct(id) => {
                    let Some(size_bits) = self
                        .module
                        .struct_def(*id)
                        .and_then(|definition| definition.size)
                        .and_then(|size| size.checked_mul(8))
                    else {
                        continue;
                    };
                    let children = self.layout_children(&ty);
                    self.ty_facts
                        .layout
                        .borrow_mut()
                        .insert(ty, Some(LayoutFact { size_bits, stride_bits: None }));
                    pending.extend(children);
                }
                Ty::Array(element, len) => {
                    let Some(element_ty) = self.module.types.get(element.as_usize()).cloned()
                    else {
                        continue;
                    };
                    if !element_done {
                        pending.push((ty.clone(), true));
                        pending.push((element_ty, false));
                        continue;
                    }
                    // The element is seeded now when it is a struct or an array;
                    // any other element is asked directly (a scalar's layout is
                    // one table entry).
                    let Some(stride) = self.layout_fact(&element_ty).map(|fact| fact.size_bits)
                    else {
                        continue;
                    };
                    let Some(size_bits) = stride.checked_mul(*len) else {
                        continue;
                    };
                    self.ty_facts
                        .layout
                        .borrow_mut()
                        .insert(ty, Some(LayoutFact { size_bits, stride_bits: Some(stride) }));
                }
                _ => {}
            }
        }
    }

    /// The struct and array types directly nested in `ty` (its fields' types, or
    /// its element type), each to be seeded.
    fn layout_children(&self, ty: &Ty) -> Vec<(Ty, bool)> {
        match ty {
            Ty::Struct(id) => self.module.struct_def(*id).map_or_else(Vec::new, |definition| {
                definition
                    .fields
                    .iter()
                    .filter(|field| matches!(field.ty, Ty::Struct(_) | Ty::Array(..)))
                    .map(|field| (field.ty.clone(), false))
                    .collect()
            }),
            Ty::Array(element, _) => self
                .module
                .types
                .get(element.as_usize())
                .filter(|element| matches!(element, Ty::Struct(_) | Ty::Array(..)))
                .map(|element| vec![(element.clone(), false)])
                .unwrap_or_default(),
            _ => Vec::new(),
        }
    }

    /// The declared bit range `[start, end)` of every field of the struct `ty`, in
    /// field order, when its declared layout is exact lane evidence: one range per
    /// field of the trackable field list `field_tys` (the same types, in order),
    /// each with a declared offset and a layout, inside the struct, and no two
    /// starting at the same bit or overlapping. `None` otherwise.
    ///
    /// Once per struct, `O(F log F)` for `F` fields: sorted by start, a range
    /// conflicts with an earlier one exactly when it starts where the previous one
    /// does or before the furthest end so far — the same verdict as comparing
    /// every pair (`left_start == right_start || (left_start < right_end &&
    /// right_start < left_end)`), which cost `F^2` at every `GEP` step.
    pub(super) fn exact_struct_ranges(
        &self,
        id: StructId,
        field_tys: &[Ty],
    ) -> Option<Rc<[(u64, u64)]>> {
        if let Some(ranges) = self.ty_facts.struct_ranges.borrow().get(&id) {
            return ranges.clone();
        }
        let ranges = self.exact_struct_ranges_uncached(id, field_tys);
        self.ty_facts.struct_ranges.borrow_mut().insert(id, ranges.clone());
        ranges
    }

    fn exact_struct_ranges_uncached(
        &self,
        id: StructId,
        field_tys: &[Ty],
    ) -> Option<Rc<[(u64, u64)]>> {
        let total = self.layout_fact(&Ty::Struct(id))?.size_bits;
        // Indexed lookup (`Module::struct_def`), not a scan of the struct table.
        let definition = self.module.struct_def(id)?;
        if definition.fields.len() != field_tys.len() {
            return None;
        }
        let mut ranges = Vec::with_capacity(definition.fields.len());
        for (field, field_ty) in definition.fields.iter().zip(field_tys) {
            if field.ty != *field_ty {
                return None;
            }
            let start = field.offset?.checked_mul(8)?;
            let end = start.checked_add(self.layout_fact(&field.ty)?.size_bits)?;
            if end > total {
                return None;
            }
            ranges.push((start, end));
        }
        let mut by_start: Vec<(u64, u64)> = ranges.clone();
        by_start.sort_unstable();
        let mut furthest_end = 0u64;
        for (index, (start, end)) in by_start.iter().enumerate() {
            if index > 0 && (by_start[index - 1].0 == *start || *start < furthest_end) {
                return None;
            }
            furthest_end = furthest_end.max(*end);
        }
        Some(ranges.into())
    }

    /// `exact_gep_lane_ty`, once per `(aggregate, field, pointee)`.
    pub(super) fn exact_gep_lane_ty(
        &self,
        aggregate_ty: &Ty,
        field: usize,
        pointee_ty: &Ty,
    ) -> Option<Ty> {
        let key = (aggregate_ty.clone(), field, pointee_ty.clone());
        if let Some(lane) = self.ty_facts.gep_lanes.borrow().get(&key) {
            return lane.clone();
        }
        let lane = self.exact_gep_lane_ty_uncached(aggregate_ty, field, pointee_ty);
        self.ty_facts.gep_lanes.borrow_mut().insert(key, lane.clone());
        lane
    }

    /// The sub-object at byte 0 of `ty` that a lane path names: lane 0 of a
    /// non-empty array, or the one field of a struct whose DECLARED layout starts
    /// at byte 0 with a nonzero size and overlaps no other field (the evidence a
    /// constant `GEP` lane needs, `exact_gep_lane_ty`). `None` otherwise, which
    /// only ends the chain of objects a bulk range can name. Once per type,
    /// `O(F)` for `F` fields.
    pub(super) fn first_subobject(&self, ty: &Ty) -> Option<(usize, Ty)> {
        if let Some(first) = self.ty_facts.first_subobjects.borrow().get(ty) {
            return first.clone();
        }
        let first = self.first_subobject_uncached(ty);
        self.ty_facts.first_subobjects.borrow_mut().insert(ty.clone(), first.clone());
        first
    }

    fn first_subobject_uncached(&self, ty: &Ty) -> Option<(usize, Ty)> {
        match self.composite_shape(ty)? {
            CompositeShape::Array { elem, .. } => Some((0, elem)),
            CompositeShape::Fields(field_tys) => {
                let Ty::Struct(id) = ty else {
                    return None;
                };
                let definition = self.module.struct_def(*id)?;
                if definition.fields.len() != field_tys.len() {
                    return None;
                }
                let total = self.layout_fact(ty)?.size_bits;
                let mut ranges = Vec::with_capacity(definition.fields.len());
                for (field, field_ty) in definition.fields.iter().zip(&field_tys) {
                    if field.ty != *field_ty {
                        return None;
                    }
                    let start = field.offset?.checked_mul(8)?;
                    let end = start.checked_add(self.layout_fact(&field.ty)?.size_bits)?;
                    if end > total {
                        return None;
                    }
                    ranges.push((start, end));
                }
                let mut at_zero = ranges
                    .iter()
                    .enumerate()
                    .filter(|(_, (start, end))| *start == 0 && *end > 0)
                    .map(|(index, _)| index);
                let index = at_zero.next()?;
                if at_zero.next().is_some() {
                    return None;
                }
                let first_end = ranges[index].1;
                let overlapped = ranges.iter().enumerate().any(|(other, (start, end))| {
                    other != index && start < end && *start < first_end
                });
                (!overlapped).then(|| (index, field_tys[index].clone()))
            }
        }
    }

    /// Can every byte of a `ty` be set to one byte value, as a `memset` does? Yes
    /// exactly when every leaf is an integer of its full layout width (a `bool`,
    /// `char`, float, pointer or opaque value has invalid or unmodeled byte
    /// images). The same rule in every block, whether arrays there carry content
    /// or only a shape. Once per type.
    pub(super) fn byte_fill_fits(&self, ty: &Ty) -> bool {
        if let Some(fits) = self.ty_facts.byte_fills.borrow().get(ty) {
            return *fits;
        }
        let fits = match self.composite_shape(ty) {
            Some(CompositeShape::Fields(field_tys)) => {
                field_tys.iter().all(|field_ty| self.byte_fill_fits(field_ty))
            }
            Some(CompositeShape::Array { elem, .. }) => self.byte_fill_fits(&elem),
            None => {
                ty.is_integer()
                    && match (ty_to_sort(ty).bitvec_width(), self.layout_fact(ty)) {
                        (Some(width), Some(layout)) => {
                            width != 0 && width % 8 == 0 && u64::from(width) == layout.size_bits
                        }
                        _ => false,
                    }
            }
        };
        self.ty_facts.byte_fills.borrow_mut().insert(ty.clone(), fits);
        fits
    }
}
