// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Resolve a Field-only path on a flattened struct local to the flattened
//! slots it names.
//!
//! A flattened local keeps one state variable per leaf of its sort
//! (`collect_leaf_sorts`). The read side (`translate_flattened_place`, cases B
//! and C) and the direct write (`codegen_stmt_assign_projection.rs`) find a
//! path's slot by walking the SORT tree, which is only right while the sort
//! tree has the shape of the MIR type tree. `translate_ty` breaks that in
//! places: it collapses `(T,)` to T, models some ADTs by name (Cell,
//! ManuallyDrop, MaybeUninit, String, Vec, ...), gives a `&dyn` field a
//! two-leaf datatype, and flattening stops at depth 4. The resolver walks the
//! MIR types and the sorts together and refuses every level where they
//! disagree, so a caller either gets the exact slot span or a reason to fail
//! closed.
//!
//! Its first user is the Mem-level deref mirror
//! (`stmt/codegen_stmt_store/deref_mem_mirror_struct.rs`), where a store
//! through `r: &mut P` into `r.inner.a` must reach the owner's register slot.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Sort;
use rustc_public::ty::{AdtKind, RigidTy, Ty, TyKind};

use super::ChcCtx;
use super::FieldProjection;
use super::codegen_decl_flatten::{
    collect_leaf_sorts, compute_nested_flat_slot, compute_nested_flat_span, is_scalar_leaf_sort,
    nested_flat_walk_is_depth_faithful,
};
use super::codegen_types::CodegenTypes;
use crate::rustc_public_bridge::IndexedVal;

/// The flattened slots a Field-only path on a flattened struct local names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct FlatStructSpan {
    /// First flattened slot of the path's terminal place.
    pub(in crate::codegen_ay::chc) offset: usize,
    /// Number of leaf slots the terminal place occupies.
    pub(in crate::codegen_ay::chc) count: usize,
    /// Sort of the terminal place (`translate_ty` of its MIR type).
    pub(in crate::codegen_ay::chc) terminal_sort: Sort,
    /// Declared sort of every flattened slot of the local, in slot order.
    pub(in crate::codegen_ay::chc) declared: Vec<Sort>,
}

impl FlatStructSpan {
    /// Declared sorts of the terminal's slots, `[offset, offset + count)`.
    pub(in crate::codegen_ay::chc) fn terminal_slot_sorts(&self) -> &[Sort] {
        &self.declared[self.offset..self.offset + self.count]
    }
}

/// Whether the MIR step `parent.field_idx` (of type `field_ty`) projects the
/// one non-zero-sized field of a tuple or a single-variant struct: a step a
/// wrapper's sort can omit.
fn is_sole_payload_step(parent: Ty, field_idx: usize, field_ty: Ty) -> bool {
    use crate::codegen_ay::chc::call::codegen_call_kani_model_dst::is_zst_ty;
    let field_types: Vec<Ty> = match parent.kind() {
        TyKind::RigidTy(RigidTy::Tuple(elems)) => elems,
        TyKind::RigidTy(RigidTy::Adt(def, args)) if def.kind() == AdtKind::Struct => {
            let variants = def.variants();
            let [variant] = variants.as_slice() else { return false };
            let Some(types) = variant
                .fields()
                .iter()
                .map(|field| crate::codegen_ay::shared::mono_ty::field_ty(field, &args))
                .collect::<Option<Vec<_>>>()
            else {
                return false;
            };
            types
        }
        _ => return false,
    };
    let mut payload = field_types.iter().enumerate().filter(|(_, ty)| !is_zst_ty(**ty));
    let sole_payload =
        matches!((payload.next(), payload.next()), (Some((i, _)), None) if i == field_idx);
    sole_payload && field_types.get(field_idx) == Some(&field_ty)
}

/// How many leading steps of `projs`, from a value of MIR type `ty` and sort
/// `sort`, are the identity in the SORT tree: the longest run of sole-payload
/// steps that ends at a type whose sort is `sort` (0: none). A run, not a
/// step: `translate_ty` models `ManuallyDrop<P>` as P's sort and skips the
/// `MaybeDangling<P>` level between them, which on its own is a datatype of
/// its own, so `m.value.0` is the identity as a whole and neither of its steps
/// is alone. The run's end has `ty`'s sort, and a datatype sort names one type
/// (T3), so the run cannot end on an unrelated type of equal sort.
pub(in crate::codegen_ay::chc) fn sort_identity_run(
    ty: Ty,
    sort: &Sort,
    projs: &[FieldProjection],
) -> usize {
    let mut parent = ty;
    let mut run = 0;
    for (j, fp) in projs.iter().enumerate() {
        let Some(field_ty) = fp.field_ty else { break };
        if fp.cons_idx.is_some() || !is_sole_payload_step(parent, fp.field_idx, field_ty) {
            break;
        }
        if ChcCtx::translate_ty(field_ty).as_ref() == Some(sort) {
            run = j + 1;
        }
        parent = field_ty;
    }
    run
}

/// The Field path `indices` from a value of MIR type `root_ty`, typed (each
/// step's field type, from the tuple or the single-variant struct it
/// projects), for a caller that recorded the indices alone and must place
/// them through [`ChcCtx::flat_field_path_from`].
pub(in crate::codegen_ay::chc) fn typed_field_path(
    root_ty: Ty,
    indices: &[usize],
) -> Option<Vec<FieldProjection>> {
    let mut ty = root_ty;
    let mut out = Vec::with_capacity(indices.len());
    for &field_idx in indices {
        let field_ty = match ty.kind() {
            TyKind::RigidTy(RigidTy::Tuple(elems)) => *elems.get(field_idx)?,
            TyKind::RigidTy(RigidTy::Adt(def, args)) if def.kind() == AdtKind::Struct => {
                let variants = def.variants();
                let [variant] = variants.as_slice() else { return None };
                crate::codegen_ay::shared::mono_ty::field_ty(
                    variant.fields().get(field_idx)?,
                    &args,
                )?
            }
            _ => return None,
        };
        out.push(FieldProjection { field_idx, cons_idx: None, field_ty: Some(field_ty) });
        ty = field_ty;
    }
    Some(out)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// C5b (design trust-mc-reds-final §4.2): the Field path `projs` on a
    /// value of MIR type `root_ty` as the SORT tree walks it, every step
    /// checked against the type.
    ///
    /// A flattened local keeps one slot per leaf of its sort, and the walks
    /// that place a path (`compute_nested_flat_slot` / `_span`) follow the
    /// sort tree with the path's indices. The sort tree is the type tree with
    /// the identity steps removed (`sort_identity_run`): those steps are
    /// dropped here, wherever they are on the path. Every other step must land
    /// on a constructor field whose sort is `translate_ty` of the MIR field
    /// type (a terminal `&dyn` field keeps its two-leaf fat-pointer sort), or
    /// the path has no faithful slot and is refused. Before this, the walks
    /// took the indices raw: `RefCell::into_inner`'s `self.value` step is
    /// `UnsafeCell<(u8, u8)>.0`, whose sort is the tuple's, and the raw walk
    /// read the tuple's field 0 for the whole tuple, leaving `t.1` free
    /// (refcell_tuple_path_dual.rs, `safe_into_inner_second`: a false
    /// certificate on main 756f6eabf).
    ///
    /// From the first enum Downcast on, the path is the enum payload walk's
    /// (`translate_flattened_downcast_nested`) and is returned unchanged; so
    /// is the rest of a path at a level the sort walk cannot take at all (no
    /// sort, not a single-constructor datatype, an index out of range), where
    /// `compute_nested_flat_slot` / `_span` return `None` themselves and the
    /// caller takes its own fallback.
    pub(in crate::codegen_ay::chc) fn flat_field_path_from(
        root_ty: Ty,
        projs: &[FieldProjection],
    ) -> Result<Vec<FieldProjection>, &'static str> {
        let mut mir_ty = root_ty;
        let Some(mut sort) = Self::translate_ty(root_ty) else { return Ok(projs.to_vec()) };
        let mut kept = Vec::with_capacity(projs.len());
        let mut i = 0;
        while let Some(fp) = projs.get(i) {
            if fp.cons_idx.is_some() {
                kept.extend_from_slice(&projs[i..]);
                return Ok(kept);
            }
            let field_ty = fp.field_ty.ok_or("field_type_missing")?;
            let run = sort_identity_run(mir_ty, &sort, &projs[i..]);
            if run > 0 {
                mir_ty = projs[i + run - 1].field_ty.ok_or("field_type_missing")?;
                i += run;
                continue;
            }
            let next = {
                let walkable =
                    sort.datatype_sort().and_then(|dt| match dt.constructors.as_slice() {
                        [ctor] => ctor.fields.get(fp.field_idx).cloned(),
                        _ => None,
                    });
                let Some(field) = walkable else {
                    kept.extend_from_slice(&projs[i..]);
                    return Ok(kept);
                };
                if Self::translate_ty(field_ty).as_ref() != Some(&field.sort) {
                    let terminal_fat_pointer = i + 1 == projs.len()
                        && field.sort.datatype_sort().is_some_and(|fdt| {
                            crate::codegen_ay::names::is_dyn_sort_name(&fdt.name)
                        });
                    if !terminal_fat_pointer {
                        return Err("field_sort_differs_from_type");
                    }
                }
                field.sort.clone()
            };
            kept.push(fp.clone());
            sort = next;
            mir_ty = field_ty;
            i += 1;
        }
        Ok(kept)
    }

    /// [`Self::flat_field_path_from`] on `local`'s MIR type.
    pub(in crate::codegen_ay::chc) fn flat_field_path(
        &self,
        local: usize,
        projs: &[FieldProjection],
    ) -> Result<Vec<FieldProjection>, &'static str> {
        let root_ty = self.body.locals().get(local).ok_or("local_missing")?.ty;
        Self::flat_field_path_from(root_ty, projs)
    }

    /// Resolve `projs` (Field projections relative to `local`'s MIR type) to
    /// the flattened slot span they name, or say why not.
    ///
    /// Refuses unless every one of these holds:
    /// - `local` is flattened, is not a collection projection local, and the
    ///   path is non-empty with no enum Downcast;
    /// - its declared slots are all scalar and equal, element by element,
    ///   `collect_leaf_sorts(translate_ty(type))` -- the layout the read side
    ///   and the offset arithmetic assume (this also refuses a local whose
    ///   flattening stopped at depth 4 and left a datatype slot);
    /// - at every level the MIR type is a struct (built by the general
    ///   `translate_adt_sort` path, checked by its sort name), a tuple, or a
    ///   closure, whose field count equals the sort constructor's, and
    ///   `translate_ty` of the projected field's MIR type equals that
    ///   constructor field's sort;
    /// - a sort-identity run (`sort_identity_run`: `(T,)`, #1979, or a
    ///   wrapper `translate_ty` collapses onto its one field) consumes no sort
    ///   level, wherever it is on the path, exactly as the read side drops it
    ///   (`flat_field_path`). It used to be peeled only at the root and refused
    ///   inside: the readers then walked the remaining MIR indices over the
    ///   sort tree raw, so for `o.a.0.y` with `a: (QT,)` they landed on
    ///   another leaf's slot, and `r.a.0.x.r1 = v; assert!(o.a.0.y == v)` was
    ///   proved clean (nested_field_ref_write_dual.rs, the interior_tuple1
    ///   rows).
    pub(in crate::codegen_ay::chc) fn resolve_flat_struct_path(
        &self,
        local: usize,
        projs: &[FieldProjection],
    ) -> Result<FlatStructSpan, &'static str> {
        if projs.is_empty() {
            return Err("empty_path");
        }
        if !self.flatten.flattened_tuple_locals.contains(&local) {
            return Err("target_not_flattened");
        }
        if self.collections.projection_locals.contains_key(&local) {
            return Err("collection_projection_local");
        }
        if projs.iter().any(|fp| fp.cons_idx.is_some()) {
            return Err("enum_downcast_in_path");
        }
        let local_ty = self.body.locals().get(local).ok_or("local_missing")?.ty;
        let root_sort = Self::translate_ty(local_ty).ok_or("root_sort_unavailable")?;
        let declared = self.declared_flat_slot_sorts(local)?;
        if collect_leaf_sorts(&root_sort, 0) != declared {
            return Err("declared_layout_differs_from_type");
        }

        let mut mir_ty = local_ty;
        let mut sort = root_sort;
        let mut offset = 0usize;
        let mut i = 0;
        while let Some(fp) = projs.get(i) {
            let field_ty = fp.field_ty.ok_or("field_type_missing")?;
            // A run of sort-identity steps (`(T,)`, a wrapper `translate_ty`
            // collapses onto its content) has no sort level to consume,
            // wherever it is on the path: the read side drops it the same way
            // (`flat_field_path`).
            let run = sort_identity_run(mir_ty, &sort, &projs[i..]);
            if run > 0 {
                mir_ty = projs[i + run - 1].field_ty.ok_or("field_type_missing")?;
                i += run;
                continue;
            }
            i += 1;
            let (step_offset, field_sort) = {
                let dt = sort.datatype_sort().ok_or("level_sort_not_datatype")?;
                let [ctor] = dt.constructors.as_slice() else {
                    return Err("level_sort_not_single_constructor");
                };
                Self::check_flat_struct_level(mir_ty, &dt.name, ctor.fields.len())?;
                let field = ctor.fields.get(fp.field_idx).ok_or("field_index_out_of_range")?;
                if Self::translate_ty(field_ty).as_ref() != Some(&field.sort) {
                    return Err("field_sort_differs_from_type");
                }
                let step_offset: usize = ctor.fields[..fp.field_idx]
                    .iter()
                    .map(|sibling| collect_leaf_sorts(&sibling.sort, 0).len())
                    .sum();
                (step_offset, field.sort.clone())
            };
            offset += step_offset;
            sort = field_sort;
            mir_ty = field_ty;
        }

        let terminal_leaves = collect_leaf_sorts(&sort, 0);
        let count = terminal_leaves.len();
        let end = offset.checked_add(count).ok_or("span_overflow")?;
        if count == 0 || end > declared.len() {
            return Err("span_out_of_bounds");
        }
        if terminal_leaves[..] != declared[offset..end] {
            return Err("terminal_layout_mismatch");
        }
        Ok(FlatStructSpan { offset, count, terminal_sort: sort, declared })
    }

    /// The Field path `projs` on `local` as read case C
    /// (`translate_flattened_place`), the direct nested write
    /// (`encode_projection_assignment`, `faithful_nested_flat_slot`) and the
    /// stack Deref+Field read place it with `compute_nested_flat_slot` /
    /// `_span`: [`Self::flat_field_path`] (the sort-identity steps dropped,
    /// every other step checked against its type), refused also when the walk
    /// would pass `MAX_FLATTEN_DEPTH` (`nested_flat_walk_is_depth_faithful`):
    /// `o.k1.k2.k3.k4.y = v` on a five-level owner wrote `o.z`'s slot.
    ///
    /// The step check is what keeps a walk off another leaf's slot.
    /// `translate_ty` collapses `(T,)` and the wrappers it models by name
    /// (ManuallyDrop, MaybeUninit, Cell, UnsafeCell, NonZero, the sync guards,
    /// a single-field array wrapper) to their content's sort; taking the next
    /// MIR index one level too high named `x.r1`'s slot for `o.a.0.y` with
    /// `a: (QT,)`, and `assert!(o.a.0.y == a)` was proved clean. Those steps
    /// are now dropped, wherever they are, and a step that still disagrees
    /// with its sort is refused. Field counts are not compared: a model whose
    /// projected field has the MIR field's sort (a Vec's `len`, field 1 of
    /// both) is walked as before.
    pub(in crate::codegen_ay::chc) fn faithful_flat_field_path(
        &self,
        local: usize,
        projs: &[FieldProjection],
    ) -> Result<Vec<FieldProjection>, &'static str> {
        let path = self.flat_field_path(local, projs)?;
        let local_ty = self.body.locals().get(local).ok_or("local_missing")?.ty;
        if let Some(root_sort) = Self::translate_ty(local_ty) {
            let struct_prefix: Vec<usize> =
                path.iter().take_while(|fp| fp.cons_idx.is_none()).map(|fp| fp.field_idx).collect();
            if !nested_flat_walk_is_depth_faithful(&root_sort, &struct_prefix) {
                return Err("flat_layout_depth_capped");
            }
        }
        Ok(path)
    }

    /// The flattened slots `[offset, offset + count)` the Field path `projs`
    /// names on the flattened `local`, placed through
    /// [`Self::faithful_flat_field_path`]: a path of sort-identity steps only
    /// is the whole local. For the sites that used to walk the MIR indices
    /// raw (`compute_nested_flat_span(&sort, &[fp.field_idx])`).
    pub(in crate::codegen_ay::chc) fn flat_span_for(
        &self,
        local: usize,
        projs: &[FieldProjection],
    ) -> Result<(usize, usize), &'static str> {
        let path = self.faithful_flat_field_path(local, projs)?;
        if path.iter().any(|fp| fp.cons_idx.is_some()) {
            return Err("enum_downcast_in_path");
        }
        if path.is_empty() {
            return Ok((0, self.flattened_field_count(local)));
        }
        let local_ty = self.body.locals().get(local).ok_or("local_missing")?.ty;
        let sort = Self::translate_ty(local_ty).ok_or("root_sort_unavailable")?;
        let indices: Vec<usize> = path.iter().map(|fp| fp.field_idx).collect();
        compute_nested_flat_span(&sort, &indices).ok_or("span_unresolved")
    }

    /// The one flattened leaf slot the Field path `projs` names on `local`
    /// (its terminal is a scalar leaf), placed through
    /// [`Self::faithful_flat_field_path`]; for the sites that used to call
    /// `compute_nested_flat_slot` with the MIR indices raw.
    pub(in crate::codegen_ay::chc) fn flat_slot_for(
        &self,
        local: usize,
        projs: &[FieldProjection],
    ) -> Result<usize, &'static str> {
        let path = self.faithful_flat_field_path(local, projs)?;
        if path.iter().any(|fp| fp.cons_idx.is_some()) {
            return Err("enum_downcast_in_path");
        }
        if path.is_empty() {
            return Err("path_is_whole_local");
        }
        let local_ty = self.body.locals().get(local).ok_or("local_missing")?.ty;
        let sort = Self::translate_ty(local_ty).ok_or("root_sort_unavailable")?;
        let indices: Vec<usize> = path.iter().map(|fp| fp.field_idx).collect();
        compute_nested_flat_slot(&sort, &indices).ok_or("slot_unresolved")
    }

    /// Declared slot sorts of a flattened local: every slot must exist on the
    /// input and the output side with one sort, and be a scalar leaf.
    fn declared_flat_slot_sorts(&self, local: usize) -> Result<Vec<Sort>, &'static str> {
        let vec_idx = self.try_state_idx_for_local(local).ok_or("state_idx_missing")?;
        let slots = self
            .flatten
            .flattened_local_field_count
            .get(&local)
            .copied()
            .ok_or("flattened_field_count_missing")?;
        let mut declared = Vec::with_capacity(slots);
        for slot in 0..slots {
            let (_, in_sort) =
                self.state_var_mgr.state_vars.get(vec_idx + slot).ok_or("input_slot_missing")?;
            let (_, out_sort) = self
                .state_var_mgr
                .output_state_vars
                .get(vec_idx + slot)
                .ok_or("output_slot_missing")?;
            if in_sort != out_sort {
                return Err("slot_sort_differs_between_input_and_output");
            }
            if !is_scalar_leaf_sort(out_sort) {
                return Err("declared_slot_not_scalar");
            }
            declared.push(out_sort.clone());
        }
        Ok(declared)
    }

    /// One level of the walk: the MIR type must be one whose sort is built
    /// field by field from its MIR fields, in order.
    fn check_flat_struct_level(
        mir_ty: Ty,
        sort_name: &str,
        ctor_fields: usize,
    ) -> Result<(), &'static str> {
        match mir_ty.kind() {
            TyKind::RigidTy(RigidTy::Tuple(elems)) => {
                // `translate_ty` builds a tuple's sort from its elements and
                // models no tuple by name.
                if elems.len() != ctor_fields {
                    return Err("tuple_field_count_mismatch");
                }
                Ok(())
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                if def.kind() != AdtKind::Struct {
                    return Err("level_not_struct");
                }
                // Only `translate_adt_sort`'s struct path names the sort
                // `adt_sort_name(def, args)`, and it builds one constructor
                // field per MIR field, in order. Every ADT `translate_adt_ty`
                // models by name (Cell, ManuallyDrop, MaybeUninit, String,
                // Vec, NonZero, ...) either has another sort or another name.
                if crate::codegen_ay::names::adt_sort_name(def, &args) != sort_name {
                    return Err("level_modeled_by_name");
                }
                let variants = def.variants();
                let [variant] = variants.as_slice() else {
                    return Err("level_not_single_variant");
                };
                if variant.fields().len() != ctor_fields {
                    return Err("struct_field_count_mismatch");
                }
                Ok(())
            }
            TyKind::RigidTy(RigidTy::Closure(def, _)) => {
                // `translate_ty` builds a closure's sort with one field per
                // upvar, in order, under this name.
                let expected = crate::codegen_ay::names::closure_sort_name(def.0.to_index());
                if expected != sort_name {
                    return Err("closure_sort_name_mismatch");
                }
                Ok(())
            }
            _ => Err("level_not_struct_tuple_or_closure"),
        }
    }
}
