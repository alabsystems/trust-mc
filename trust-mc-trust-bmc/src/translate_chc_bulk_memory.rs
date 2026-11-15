// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! trust-ir WS3.20 bulk memory (`MemCopy`, `MemSet`) over stack cells, in
//! encoding size independent of the byte count and linear in the cell.
//!
//! # What is exact
//!
//! A bulk operand is resolved to a [`BulkPlace`]: an exact byte offset inside a
//! single-cell stack `Alloca`, with the chain of objects that START at that
//! address (a cell, its field 0, that field's lane 0, ...), each with its type
//! and byte size. Everything below is arithmetic over those type sizes and ONE
//! comparison of the byte count `bytes` against each distinct size, so the
//! encoding has the same size whatever `bytes` is (a constant 1, a constant
//! 2^40, or a symbolic value):
//!
//! * `bytes == 0` is a no-op, even through a dangling pointer (trust-ir's own
//!   rule).
//! * In-bounds: `bytes <=u size_of(cell) - offset`, per range. Out of bounds is
//!   undefined behaviour: an error rule (with memory checks), after which the path
//!   continues only where the instruction is defined.
//! * `memcpy` overlap (`overlap: false`): two ranges in different allocations are
//!   disjoint; in the same one they overlap iff `bytes >u |dst_off - src_off|`.
//!   Undefined behaviour, the same rule. `memmove` (`overlap: true`) reads the
//!   whole source before it writes.
//! * The VALUE, where `bytes` is the size of an object starting at the
//!   destination: a copy writes the source object of the same type and size
//!   (exactly what a `Load` + `Store` of that type writes in this model — an
//!   array object moves as its SMT-array leaves, never lane by lane), and a fill
//!   writes, into every leaf of an object whose leaves are all integers of their
//!   full width, the byte repeated to the leaf's width (an array of them is one
//!   `const_array` per leaf). The fill rule is the same in every block, whether
//!   arrays there carry content or only a shape.
//!
//! # Size
//!
//! The objects are nested at one address, so a node of the cell is written
//! exactly when `bytes` names an object that contains it: one guard per object,
//! accumulated down the path, and one `ite` per leaf off the path
//! (`rebuild_bulk_target`). One write costs the cell's leaves plus the path's
//! length, as a `Store` through the same lanes does; a constant count builds
//! only the write it names. Every type query is memoized per translation
//! (`translate_chc_ty_facts.rs`).
//!
//! # What is not, and why it fails closed
//!
//! A defined, non-empty range that is NOT one whole object of a TRACKED cell — a
//! run of `k` lanes of an array with `1 < k < len`, a copy between objects of
//! different types, a fill of a non-integer leaf — has no exact encoding of
//! constant size on the CHC path. A lane run is `lambda i. ite(lo <= i < hi,
//! src[i - lo + s], dst[i])`, and neither the `ay_bindings::Expr` this lowering
//! builds nor `ay_chc::ChcExpr` (which the PDR engine consumes) has a lambda, a
//! quantifier or any other index-dependent array former; a store chain would be
//! one term per lane (a per-element unroll), which the size rule forbids
//! (`docs/ay-asks/2026-10-01-array-range-write-former`). Such a range havocs the
//! whole destination cell and raises the named fail-closed error
//! [`TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange`] where it happens.
//!
//! An operand with no exact place (a pointer parameter, a symbolic offset, a
//! heap block) keeps the previous model (`invalidate_store_targets`): when the
//! destination's provenance is known — a symbolic `GEP` index into a tracked
//! cell, say — that one cell is havocked; when it is not, every tracked cell
//! whose address escaped is. With memory checks the instruction then fails
//! closed as [`TrustIrChcUnsupportedReason::BulkMemoryTransfer`] wherever
//! `bytes != 0`.
//!
//! A destination cell the model does not track needs no value: its loads are
//! fresh already, so only the undefined behaviour above is decided for it.
//!
//! # Count/fill consumption and zero-byte pointer noninspection
//!
//! The shared source-consumption guard runs before this dispatcher. It checks
//! count and MemSet fill initializedness even for zero-byte operations, matching
//! canonical interpretation. A fresh SMT term or FreshSymbolicHavoc annotation
//! supplies no initializedness fact. A literal zero count still does not inspect
//! either pointer; null/dangling/scalar-poison pointers remain a no-op on it.
//! This module models byte values/ranges after that guard, not poison erasure.

use std::collections::{BTreeMap, HashSet};

use ay_bindings::Expr;
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, ValueId};
use trust_mc_core::chc::RelationApp;

use super::{
    AggregateValue, ArrayValue, ChcFuncTranslator, CompositeShape, PtrProvenance,
    TrustIrChcUnsupportedReason, ValueBinding, ty_to_sort,
};
use crate::bulk_count::{ByteCount, Truth};

/// One object that starts at a bulk operand's address: the object at
/// `path[..depth]` of its [`BulkPlace`].
#[derive(Debug, Clone)]
pub(super) struct BulkObject {
    pub(super) depth: usize,
    pub(super) ty: Ty,
    /// `size_of(ty)` in bytes.
    pub(super) size: u64,
}

/// Where a bulk operand points: an exact byte offset in a single-cell stack
/// `Alloca`, and every object that starts there.
#[derive(Debug, Clone)]
pub(super) struct BulkPlace {
    /// The `Alloca` result.
    pub(super) base: ValueId,
    /// Bytes from the start of the allocation to the pointer.
    pub(super) offset: u64,
    /// Bytes from the pointer to the end of the allocation.
    pub(super) room: u64,
    /// Field / lane indices from the cell root to the INNERMOST object that
    /// starts at the pointer (`update_binding_lane`'s path).
    pub(super) path: Vec<usize>,
    /// The objects starting at the pointer, outermost first; each encloses the
    /// next, which is one or more steps deeper on `path`.
    pub(super) objects: Vec<BulkObject>,
}

/// What a bulk instruction writes: a copy of `src`, or a fill with `byte`.
#[derive(Debug, Clone, Copy)]
enum BulkWrite {
    Copy { src: ValueId, overlap: bool },
    Fill { byte: ValueId },
}

/// What a bulk write may still need after its byte count is compared with the
/// destination's objects: the condition under which it lands on none of them.
struct PlacedWrite {
    /// The destination cell's new binding, when the cell is tracked and the
    /// binding could be built (`None`: the cell is invalidated instead).
    cell_value: Option<ValueBinding>,
    /// Defined, non-empty, and not one whole object of a tracked cell.
    unplaced: Truth,
}

impl ChcFuncTranslator<'_> {
    /// `MemCopy` / `MemSet`: see the module documentation.
    pub(super) fn translate_bulk_memory(
        &mut self,
        node: &InstrNode,
        block: BlockId,
        instruction_index: usize,
        from: &RelationApp,
        path_constraints: &mut Vec<Expr>,
    ) {
        let (dst, write, bytes) = match &node.inst {
            Inst::MemCopy { dst, src, bytes, overlap } => {
                (*dst, BulkWrite::Copy { src: *src, overlap: *overlap }, *bytes)
            }
            Inst::MemSet { dst, byte, bytes } => (*dst, BulkWrite::Fill { byte: *byte }, *bytes),
            _ => return,
        };
        let count = ByteCount::new(self.resolve(bytes, &Ty::Usize));
        let zero = count.as_ref().map_or(Truth::Known(false), |count| count.equals(0));
        if matches!(zero, Truth::Known(true)) {
            // A no-op by definition, even through a dangling pointer: nothing is
            // read, written or checked.
            return;
        }
        let (Some(count), Some(dst_place)) = (count, self.bulk_place(dst)) else {
            // No exact place for the destination (or a byte count that is not a
            // 64-bit vector): the previous model. The write is never dropped —
            // every tracked cell `dst` could reach is havocked, whatever
            // `check_memory_bounds` says — and the range's undefined behaviour has
            // no model here, so with memory checks the instruction fails closed
            // wherever it writes at all.
            self.invalidate_store_targets(dst);
            if self.options.check_memory_bounds {
                self.add_unsupported_error_when(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::BulkMemoryTransfer,
                    from,
                    path_constraints,
                    zero.negate().expr(),
                );
            }
            return;
        };

        // Undefined behaviour decided exactly, and the part that cannot be.
        let mut undefined = count.exceeds(dst_place.room);
        let mut unmodeled = Truth::Known(false);
        let src_place = match write {
            BulkWrite::Copy { src, overlap } => {
                let src_place = self.bulk_place(src);
                match &src_place {
                    Some(src_place) => {
                        undefined = undefined.or(count.exceeds(src_place.room));
                        if !overlap && src_place.base == dst_place.base {
                            let distance = dst_place.offset.abs_diff(src_place.offset);
                            undefined = undefined.or(count.exceeds(distance));
                        }
                    }
                    // The source's extent (and whether it overlaps the
                    // destination) is unknown: fail closed wherever it is read.
                    None => unmodeled = zero.clone().negate(),
                }
                src_place
            }
            BulkWrite::Fill { .. } => None,
        };

        let placed = self.place_bulk_write(&dst_place, src_place.as_ref(), write, &count, &zero);
        let unplaced = placed.unplaced.and(undefined.clone().negate());
        let checked = self.options.check_memory_bounds;
        if self.stack_cells.contains_key(&dst_place.base) {
            match placed.cell_value {
                Some(value) => {
                    // With memory checks off an undefined execution continues, and
                    // the program may then have written anything into the cell.
                    let value = if checked || undefined.is_false() {
                        Some(value)
                    } else {
                        self.havoc_where(dst_place.base, &undefined, value)
                    };
                    match value {
                        Some(value) => {
                            if let Some(cell) = self.stack_cells.get_mut(&dst_place.base) {
                                cell.value = value;
                            }
                        }
                        None => self.invalidate_stack_cell(dst_place.base),
                    }
                }
                None => self.invalidate_stack_cell(dst_place.base),
            }
        }

        if checked {
            if !undefined.is_false() {
                self.add_error_rule(from, path_constraints, undefined.expr());
                // Execution does not continue past undefined behaviour.
                path_constraints.push(undefined.clone().negate().expr());
            }
            if !unmodeled.is_false() {
                self.add_unsupported_error_when(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::BulkMemoryTransfer,
                    from,
                    path_constraints,
                    unmodeled.expr(),
                );
            }
            if !unplaced.is_false() {
                self.add_unsupported_error_when(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange,
                    from,
                    path_constraints,
                    unplaced.expr(),
                );
            }
        }
    }

    /// The destination cell's binding after the write.
    ///
    /// Every object that starts at `dst` (outermost first) is written exactly
    /// where `bytes` is its size and the write has a value for it (a same-typed
    /// source object, or an all-integer object to fill); one shared comparison
    /// per distinct size. Where `bytes` is zero the cell is kept, and where it
    /// names no such object (a defined but unplaced range) the cell is havocked.
    ///
    /// The objects are nested at one address, so a node of the cell is written
    /// exactly when `bytes` is the size of an object that CONTAINS it: the
    /// guards accumulate down the path, one `or` per object, and every node off
    /// the path takes one `ite` per leaf (`rebuild_bulk_target`). The encoding is
    /// linear in the cell's leaves plus the path's length — one whole-cell
    /// binding per object would be their product — and a constant count builds
    /// exactly the one write it names, at the cost of a `Store` through the same
    /// lanes (`update_binding_lane`).
    fn place_bulk_write(
        &mut self,
        dst: &BulkPlace,
        src: Option<&BulkPlace>,
        write: BulkWrite,
        count: &ByteCount,
        zero: &Truth,
    ) -> PlacedWrite {
        let Some(cell) = self.stack_cells.get(&dst.base).cloned() else {
            // Not tracked: loads of it are fresh already, so the value needs no
            // model and no range is "unplaced".
            return PlacedWrite { cell_value: None, unplaced: Truth::Known(false) };
        };
        // The whole write unmodeled: the cell is invalidated and every defined,
        // non-empty range fails closed.
        let unmodeled = PlacedWrite { cell_value: None, unplaced: zero.clone().negate() };
        let fill = match write {
            BulkWrite::Fill { byte } => {
                let byte = self.resolve(byte, &Ty::U8);
                if byte.sort().bitvec_width() != Some(8) {
                    return unmodeled;
                }
                Some(byte)
            }
            BulkWrite::Copy { .. } => None,
        };

        // `guards[depth]`: `bytes == size` of the object at that depth of the
        // path, where the write has an exact value for it; `false` elsewhere.
        let src_tys: HashSet<&Ty> = src
            .map(|src| src.objects.iter().map(|object| &object.ty).collect())
            .unwrap_or_default();
        let mut guards = vec![Truth::Known(false); dst.path.len() + 1];
        let mut by_size: BTreeMap<u64, Truth> = BTreeMap::new();
        let mut placed = Truth::Known(false);
        for object in &dst.objects {
            if object.size == 0 {
                continue;
            }
            let exact = match (write, src) {
                (BulkWrite::Fill { .. }, _) => self.byte_fill_fits(&object.ty),
                (BulkWrite::Copy { .. }, Some(_)) => src_tys.contains(&object.ty),
                // An unknown source holds any value of the type.
                (BulkWrite::Copy { .. }, None) => true,
            };
            if !exact {
                continue;
            }
            let guard = match by_size.get(&object.size) {
                Some(guard) => guard.clone(),
                None => {
                    let guard = count.equals(object.size);
                    placed = placed.or(guard.clone());
                    by_size.insert(object.size, guard.clone());
                    guard
                }
            };
            guards[object.depth] = guard;
        }
        let unplaced = zero.clone().negate().and(placed.negate());

        let written = if unplaced.is_true() {
            None
        } else {
            // `live[depth]`: some object at `depth` or below may be written.
            let mut live = vec![false; guards.len() + 1];
            for depth in (0..guards.len()).rev() {
                live[depth] = live[depth + 1] || !guards[depth].is_false();
            }
            let plan =
                BulkPlan { dst, src, write, fill: fill.as_ref(), guards: &guards, live: &live };
            match self.rebuild_bulk_target(&plan, &cell.value, 0, Truth::Known(false), None) {
                Some(written) => Some(written),
                None => return unmodeled,
            }
        };

        let value = match (&unplaced, written) {
            (Truth::Known(false), Some(written)) => written,
            (_, written) => {
                let Some(havoc) = self.fresh_stack_cell_value(&cell.ty) else {
                    return PlacedWrite { cell_value: None, unplaced };
                };
                match (&unplaced, written) {
                    (Truth::When(cond), Some(written)) => match havoc.select_by(cond, &written) {
                        Some(value) => value,
                        None => return unmodeled,
                    },
                    _ => havoc,
                }
            }
        };
        PlacedWrite { cell_value: Some(value), unplaced }
    }

    /// `old` (the binding at `dst.path[..depth]`) after the write, where `guard`
    /// says when an enclosing object is written exactly and `source` is then this
    /// node's new value (the same bytes of the written object).
    ///
    /// The object at `depth`, if the write can be exact on it, adds its own
    /// guard; its value is built here only when no enclosing object supplied one,
    /// so ONE value is built per write and every object inside it takes its part
    /// (the same bytes: an inner object of the copy starts at the source
    /// pointer too, and a fill writes the same byte everywhere). Below the path a
    /// sibling takes `ite(guard, source, old)` leaf by leaf; through an array the
    /// lane is `select`ed, rebuilt with the guard restarted (the enclosing guard
    /// replaces the whole array instead) and `store`d back. A shape-only array
    /// absorbs the write, as `ArrayValue::store` does.
    fn rebuild_bulk_target(
        &mut self,
        plan: &BulkPlan<'_>,
        old: &ValueBinding,
        depth: usize,
        guard: Truth,
        source: Option<&ValueBinding>,
    ) -> Option<ValueBinding> {
        let here = plan.guards.get(depth)?;
        let mut guard = guard;
        let mut built = None;
        if !here.is_false() {
            if source.is_none() {
                let object = plan.dst.objects.iter().find(|object| object.depth == depth)?;
                built = Some(self.bulk_source_value(plan, &object.ty)?);
            }
            guard = guard.or(here.clone());
        }
        let source = built.as_ref().or(source);
        if guard.is_true() {
            return source.cloned();
        }
        if depth == plan.dst.path.len() || !plan.live[depth + 1] {
            return guarded(&guard, source, old);
        }
        let index = plan.dst.path[depth];
        match old {
            ValueBinding::Aggregate(aggregate) => {
                let source_fields = match source {
                    Some(ValueBinding::Aggregate(source))
                        if source.fields.len() == aggregate.fields.len() =>
                    {
                        Some(&source.fields)
                    }
                    Some(_) => return None,
                    None => None,
                };
                if index >= aggregate.fields.len() {
                    return None;
                }
                let mut fields = Vec::with_capacity(aggregate.fields.len());
                for (field_index, field) in aggregate.fields.iter().enumerate() {
                    let field_source = source_fields.map(|fields| &fields[field_index]);
                    fields.push(if field_index == index {
                        self.rebuild_bulk_target(
                            plan,
                            field,
                            depth + 1,
                            guard.clone(),
                            field_source,
                        )?
                    } else {
                        guarded(&guard, field_source, field)?
                    });
                }
                Some(ValueBinding::Aggregate(AggregateValue { fields }))
            }
            ValueBinding::Array(array) if array.lanes.is_none() => Some(old.clone()),
            ValueBinding::Array(array) => {
                let lane = Expr::bitvec_const(u64::try_from(index).ok()?, 64);
                let lane_source = match source {
                    Some(ValueBinding::Array(source)) => Some(source.select(&lane)?),
                    Some(_) => return None,
                    None => None,
                };
                let lane_new = self.rebuild_bulk_target(
                    plan,
                    &array.select(&lane)?,
                    depth + 1,
                    Truth::Known(false),
                    lane_source.as_ref(),
                )?;
                let stored = ValueBinding::Array(array.store(&lane, &lane_new)?);
                guarded(&guard, source, &stored)
            }
            ValueBinding::Scalar(_) => None,
        }
    }

    /// The value the write puts into an object of type `ty` starting at the
    /// destination, checked against `ty`'s shape and sorts.
    fn bulk_source_value(&mut self, plan: &BulkPlan<'_>, ty: &Ty) -> Option<ValueBinding> {
        let value = match (plan.write, plan.fill) {
            (BulkWrite::Fill { .. }, Some(byte)) => self.bulk_fill_binding(ty, byte)?,
            (BulkWrite::Fill { .. }, None) => return None,
            (BulkWrite::Copy { .. }, _) => self.bulk_copy_source(plan.src, ty)?,
        };
        self.binding_fits(&value, ty, 0).then_some(value)
    }

    /// The value a copy writes into an object of type `ty`: the source object of
    /// the same type (read before anything is written, which is `memmove`'s "as
    /// if through a temporary"), or a fresh value of that type when the source is
    /// untracked or unknown. `None` when no source object has that type.
    fn bulk_copy_source(&mut self, src: Option<&BulkPlace>, ty: &Ty) -> Option<ValueBinding> {
        let Some(src) = src else {
            // An unknown source holds any value of the type.
            return Some(self.fresh_value_binding("bulk_copy_src", ty));
        };
        let source = src.objects.iter().find(|candidate| candidate.ty == *ty)?;
        let read = self
            .stack_cells
            .get(&src.base)
            .and_then(|cell| binding_at_path(&cell.value, src.path.get(..source.depth)?));
        Some(match read {
            Some(value) => value,
            // An untracked source (or a lane of a shape-only array) holds any
            // value of the type, exactly as a `Load` of it would read.
            None => self.fresh_value_binding("bulk_copy_src", ty),
        })
    }

    /// `ty` with every byte equal to `byte`: each leaf an integer whose bytes are
    /// all `byte` (an array of them is one `const_array` per leaf, or shape-only
    /// where arrays carry no content). `None` unless `byte_fill_fits(ty)`: the
    /// same rule in every block.
    fn bulk_fill_binding(&self, ty: &Ty, byte: &Expr) -> Option<ValueBinding> {
        if !self.byte_fill_fits(ty) {
            return None;
        }
        let mut repeated = BTreeMap::new();
        self.fill_binding_of(ty, byte, &mut repeated)
    }

    /// `bulk_fill_binding` below its check; `repeated` shares the repeated byte
    /// per width, so every leaf of one width is one term.
    fn fill_binding_of(
        &self,
        ty: &Ty,
        byte: &Expr,
        repeated: &mut BTreeMap<u32, Expr>,
    ) -> Option<ValueBinding> {
        match self.composite_shape(ty) {
            Some(CompositeShape::Fields(field_tys)) => {
                Some(ValueBinding::Aggregate(AggregateValue {
                    fields: field_tys
                        .iter()
                        .map(|field_ty| self.fill_binding_of(field_ty, byte, repeated))
                        .collect::<Option<Vec<_>>>()?,
                }))
            }
            Some(CompositeShape::Array { len, .. }) if !self.smt_arrays => {
                Some(ValueBinding::Array(ArrayValue::shape_only(len)))
            }
            Some(CompositeShape::Array { elem, len }) => {
                ArrayValue::splat(len, &self.fill_binding_of(&elem, byte, repeated)?)
                    .map(ValueBinding::Array)
            }
            None => {
                let width = ty_to_sort(ty).bitvec_width()?;
                if let Some(leaf) = repeated.get(&width) {
                    return Some(ValueBinding::Scalar(leaf.clone()));
                }
                let mut leaf = byte.clone();
                for _ in 1..width / 8 {
                    leaf = leaf.try_concat(byte.clone()).ok()?;
                }
                repeated.insert(width, leaf.clone());
                Some(ValueBinding::Scalar(leaf))
            }
        }
    }

    /// `value` where `undefined` is false, a fresh cell value where it holds.
    fn havoc_where(
        &mut self,
        base: ValueId,
        undefined: &Truth,
        value: ValueBinding,
    ) -> Option<ValueBinding> {
        let cell_ty = self.stack_cells.get(&base).map(|cell| cell.ty.clone())?;
        let havoc = self.fresh_stack_cell_value(&cell_ty)?;
        match undefined {
            Truth::Known(false) => Some(value),
            Truth::Known(true) => Some(havoc),
            Truth::When(cond) => havoc.select_by(cond, &value),
        }
    }

    /// The exact place `ptr` points to, when it is one: a single-cell stack
    /// `Alloca` reached through constant lanes with layout evidence
    /// (`PtrProvenance::lanes`). `None` for a pointer with no provenance, a
    /// symbolic or unevidenced offset, a dynamically sized `Alloca`, or a type
    /// without a byte layout. Linear in the path: every type query is memoized
    /// (`translate_chc_ty_facts.rs`).
    pub(super) fn bulk_place(&self, ptr: ValueId) -> Option<BulkPlace> {
        // An `Alloca` from an earlier block roots its own provenance, as at a
        // `GEP` or a borrow (R3): a static identity fact, never a value.
        let provenance = self.ptr_provenance.get(&ptr).cloned().or_else(|| {
            self.func_alloca_ptrs
                .contains(&ptr)
                .then(|| PtrProvenance { base: ptr, lanes: Some(Vec::new()) })
        })?;
        let lanes = provenance.lanes?;
        let cell_ty = self.func_alloca_tys.get(&provenance.base)?.clone();
        let cell_size = self.byte_size(&cell_ty)?;

        // The type and byte offset of every step from the cell to the pointee.
        let mut tys = Vec::with_capacity(lanes.len() + 1);
        tys.push(cell_ty);
        let mut steps = Vec::with_capacity(lanes.len());
        for (field, pointee_ty) in &lanes {
            let next = self.exact_gep_lane_ty(tys.last()?, *field, pointee_ty)?;
            steps.push(u64::try_from(*field).ok()?.checked_mul(self.byte_size(pointee_ty)?)?);
            tys.push(next);
        }
        let offset = steps.iter().try_fold(0u64, |acc, step| acc.checked_add(*step))?;
        let room = cell_size.checked_sub(offset)?;

        // The objects starting at the pointer, outermost first: each object
        // enclosing the pointee for as long as the step into it is at offset
        // zero, the pointee, then the pointee's first sub-objects (lane 0, the
        // field at byte 0).
        let mut path: Vec<usize> = lanes.iter().map(|(field, _)| *field).collect();
        let mut outermost = path.len();
        while outermost > 0 && steps[outermost - 1] == 0 {
            outermost -= 1;
        }
        let mut objects = Vec::new();
        for (depth, ty) in tys.iter().enumerate().skip(outermost) {
            objects.push(BulkObject { depth, ty: ty.clone(), size: self.byte_size(ty)? });
        }
        let mut inner_ty = tys.last()?.clone();
        while let Some((index, sub_ty)) = self.first_subobject(&inner_ty) {
            let Some(size) = self.byte_size(&sub_ty) else {
                break;
            };
            path.push(index);
            objects.push(BulkObject { depth: path.len(), ty: sub_ty.clone(), size });
            inner_ty = sub_ty;
        }
        Some(BulkPlace { base: provenance.base, offset, room, path, objects })
    }
}

/// What `rebuild_bulk_target` reads: the destination, the source of a copy (or
/// the byte of a fill), and per depth of the destination's path the guard of an
/// exact write of the object there and whether any object at or below it may be
/// written at all.
struct BulkPlan<'p> {
    dst: &'p BulkPlace,
    src: Option<&'p BulkPlace>,
    write: BulkWrite,
    fill: Option<&'p Expr>,
    guards: &'p [Truth],
    live: &'p [bool],
}

/// `ite(guard, source, old)` leaf by leaf, folded when `guard` is known.
fn guarded(
    guard: &Truth,
    source: Option<&ValueBinding>,
    old: &ValueBinding,
) -> Option<ValueBinding> {
    match guard {
        Truth::Known(false) => Some(old.clone()),
        Truth::Known(true) => source.cloned(),
        Truth::When(cond) => source?.select_by(cond, old),
    }
}

/// The sub-binding at `path` (fields by index, array lanes by `select`); `None`
/// through a shape-only array or a scalar.
pub(super) fn binding_at_path(binding: &ValueBinding, path: &[usize]) -> Option<ValueBinding> {
    let Some((&first, rest)) = path.split_first() else {
        return Some(binding.clone());
    };
    match binding {
        ValueBinding::Aggregate(aggregate) => binding_at_path(aggregate.fields.get(first)?, rest),
        ValueBinding::Array(array) => {
            let lane = Expr::bitvec_const(u64::try_from(first).ok()?, 64);
            binding_at_path(&array.select(&lane)?, rest)
        }
        ValueBinding::Scalar(_) => None,
    }
}
