// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Deref+Field offset-based load optimization.
//!
//! When a Deref is followed exclusively by Field projections (no Downcast),
//! the load side can compute a cumulative byte offset and perform a single
//! field-level memory load — symmetric with the store side's
//! `try_decompose_struct_store`.
//!
//! Extracted from `codegen_expr_deref.rs` per #4125 (500 LOC threshold).

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::ProjectionElem;
use rustc_public::ty::{AdtKind, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::provenance::Loc;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_ctx::record_translation_drop_site_reason_for_fn;
use super::codegen_stmt_projection::FieldProjection;

/// Not blessed: a read through a pointer to a flattened stack local whose
/// field path has no faithful flattened slot, answered from memory instead.
/// Rule B (C5a): a pointer into a flattened stack local whose pointee is no
/// unique part of the local (an enum, a union, padding, or a window across two
/// fields): the read goes to memory, where the register's writes are not, so
/// it is fail-closed.
pub(in crate::codegen_ay::chc) const STACK_INTERIOR_PATH_UNRESOLVED: &str =
    "stack_interior_path_unresolved";

/// The field selections from a value of type `root_ty` to its part at byte
/// `offset` of type `pointee_ty` (`decl::static_path`, the one object-path
/// rule), each with its field type. `None` when no unique path of fields
/// exists (an array element is not a field selection of a flattened local).
pub(in crate::codegen_ay::chc) fn object_path_projections(
    root_ty: rustc_public::ty::Ty,
    offset: u64,
    pointee_ty: rustc_public::ty::Ty,
) -> Option<Vec<FieldProjection>> {
    use crate::codegen_ay::chc::decl::static_path::{StaticPathElem, static_type_path};
    let path = static_type_path(root_ty, offset, pointee_ty)?;
    let mut ty = root_ty;
    let mut out = Vec::with_capacity(path.len());
    for elem in path {
        let StaticPathElem::Field(i) = elem else { return None };
        let field_ty = match ty.kind() {
            TyKind::RigidTy(RigidTy::Tuple(tys)) => *tys.get(i)?,
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let variants = def.variants();
                let [variant] = variants.as_slice() else { return None };
                crate::codegen_ay::shared::mono_ty::field_ty(variant.fields().get(i)?, &args)?
            }
            _ => return None,
        };
        out.push(FieldProjection { field_idx: i, cons_idx: None, field_ty: Some(field_ty) });
        ty = field_ty;
    }
    Some(out)
}

pub(in crate::codegen_ay::chc) const STACK_DEREF_FIELD_PATH_UNFAITHFUL: &str =
    "stack_deref_field_path_unfaithful";

/// Result of attempting the Deref+Field offset-based load optimization.
pub(in crate::codegen_ay::chc) enum DerefFieldOffsetResult {
    /// Successfully loaded via field-offset path. Contains the loaded expression.
    Loaded(Expr),
    /// Optimization not applicable (Downcast present, offset computation failed, etc.).
    /// Caller should fall through to whole-struct load.
    NotApplicable,
    /// Hard bail: non-bitvec pointer or load failure. Caller should return None.
    Bail,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Try to load via Deref+Field offset optimization.
    ///
    /// If all remaining projections after Deref are Field projections, compute
    /// the cumulative byte offset and load from the field-level type array.
    /// This is symmetric with the store side (`try_decompose_struct_store`).
    ///
    /// Part of #1161: Make load side symmetric with store side.
    /// Part of #2323 Gap 1: Downcast projections fall through (need variant-aware selection).
    /// The base is the address the enclosing `Deref` consumes — see the tag site
    /// in `walk_deref_projection_loop`. Taking a [`Loc`] is what lets the byte
    /// arithmetic below stay an address all the way to the load: an offset added
    /// to an address is still an address, and the load is the one operation that
    /// turns it into a datum.
    pub(in crate::codegen_ay::chc) fn try_deref_field_offset_load(
        &mut self,
        current_expr: Loc,
        pointee_ty: rustc_public::ty::Ty,
        remaining_projs: &[ProjectionElem],
        modified_locals: &HashSet<usize>,
    ) -> DerefFieldOffsetResult {
        // Only applies when all remaining projections are Field (no Downcast).
        let all_fields = !remaining_projs.is_empty()
            && remaining_projs.iter().all(|p| matches!(p, ProjectionElem::Field(_, _)));

        if !all_fields {
            return DerefFieldOffsetResult::NotApplicable;
        }

        // Compute cumulative field offset
        let mut total_offset: u64 = 0;
        let mut load_ty = pointee_ty;
        let mut all_offsets_computed = true;

        for remaining_proj in remaining_projs {
            if let ProjectionElem::Field(field_idx, field_ty) = remaining_proj {
                // A UNION container is not laid out like a struct, so the
                // field-offset load is structurally wrong for it. `translate_ty`
                // lowers a union ADT to a FLAT `Sort::bitvec(size*8)` and the
                // static/heap mirrors register exactly ONE typed memory array —
                // keyed by the UNION's own type. Reading field `i` at its byte
                // offset would select from `mem_<field_ty>` instead, an array no
                // rule ever writes; after array scalarization that cell is a free
                // variable, so any assertion over it is trivially refutable
                // (spurious "Genuine" CTREX). Fall through to the whole-struct
                // load, whose Field arm is union-aware
                // (`union_bv_field_coerce`, codegen_expr.rs:472) and reads the
                // array the entry rule actually constrains. Checked per
                // container, not just on `pointee_ty`, so nested chains like
                // `(*p).0.1` with a union in the middle are covered too.
                if Self::is_union_adt(load_ty) {
                    debug!(
                        ?load_ty,
                        field_idx = *field_idx,
                        "CHC: Deref+Field offset load not applicable — union container \
                         (flat-BV model); falling through to union-aware whole-struct load"
                    );
                    return DerefFieldOffsetResult::NotApplicable;
                }
                if let Some(offset) = self.get_field_offset(load_ty, *field_idx) {
                    total_offset += offset;
                    load_ty = *field_ty;
                } else {
                    debug!("CHC: cannot compute field offset for field {}", *field_idx);
                    all_offsets_computed = false;
                    break;
                }
            } else {
                all_offsets_computed = false;
                break;
            }
        }

        if !all_offsets_computed {
            return DerefFieldOffsetResult::NotApplicable;
        }

        // Part of #2007: Guard against non-bitvec sorts.
        if !current_expr.as_expr().sort().is_bitvec() {
            self.diagnostics.place_translation_drop.inc();
            record_translation_drop_site_reason_for_fn(
                &self.fn_name,
                "deref_non_bitvec_field_load",
            );
            debug!(
                "CHC: translate_place_with_deref - non-bitvec sort in Deref+Field load, returning None"
            );
            return DerefFieldOffsetResult::Bail;
        }

        // The stack lane below reads the flattened register of the local the
        // BASE address names, so it needs the base before the field offset.
        let base_addr = current_expr.as_expr().clone();

        // Compute address with field offset. A byte offset added to an address
        // is an address, so the tag survives the arithmetic unchanged.
        let addr = if total_offset > 0 {
            Loc::of_address(
                current_expr
                    .into_expr()
                    .bvadd(Expr::bitvec_const(total_offset as i64, POINTER_WIDTH)),
            )
        } else {
            current_expr
        };

        if let Some(expr) = self.try_stack_deref_field_expr(
            &base_addr,
            pointee_ty,
            remaining_projs,
            modified_locals,
        ) {
            debug!(
                offset = total_offset,
                "CHC: translate_place_with_deref - resolved stack Deref+Field from flattened local"
            );
            return DerefFieldOffsetResult::Loaded(expr);
        }

        // A struct or tuple field is read from its leaves, the cells every
        // store of one of them writes (`load_aggregate_field_from_leaves`).
        if let Some(value) = self.load_aggregate_field_from_leaves(addr.as_expr(), load_ty) {
            debug!(offset = total_offset, "CHC: Deref+Field aggregate load rebuilt from its leaves");
            return DerefFieldOffsetResult::Loaded(value);
        }

        // Load from field-level type array (symmetric with store).
        // Dyn-tail normalization is handled inside load_from_memory (#3974).
        match self.load_from_memory(addr, load_ty) {
            Some(val) => {
                debug!(
                    offset = total_offset,
                    "CHC: translate_place_with_deref - Deref+Field load at offset"
                );
                DerefFieldOffsetResult::Loaded(val.into_expr())
            }
            None => {
                self.record_aggregate_gap("deref_field_load_failed");
                debug!("CHC: Deref+Field load_from_memory returned None");
                DerefFieldOffsetResult::Bail
            }
        }
    }

    /// `true` when `ty` is a union ADT — the one ADT kind whose fields all live
    /// at offset 0 inside a flat bitvec, so byte-offset field addressing does
    /// not describe it.
    fn is_union_adt(ty: rustc_public::ty::Ty) -> bool {
        matches!(
            ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == AdtKind::Union
        )
    }

    /// Read `(*p).f.g…` from the flattened register of the stack local `p`
    /// addresses, instead of from memory.
    ///
    /// Three conditions keep the read on the value the program last wrote:
    /// - `p` is the local's own address (offset 0) and its pointee type is the
    ///   local's type, so the path is relative to the local's root. The lane
    ///   used to take only the object id of the address with the field offset
    ///   already added, and walked the path from the root of whatever local
    ///   that object was.
    /// - The slot is read as `translate_flattened_place` reads it: the value
    ///   the block last wrote (`flattened_field_env`), else the output state
    ///   variable once the block has modified the local. The lane read the
    ///   INPUT variables whatever the block had done: in a walked `FnMut`
    ///   closure, `o.t.0.y = w; o.t.0.y` stored `w` and read the slot's
    ///   pre-block value, and `assert!(got == 0)` was proved
    ///   (nested_field_ref_write_dual.rs::bug_closure_fnmut_interior_tuple).
    /// - The path has a faithful slot (`faithful_flat_field_path`, C5b). The
    ///   field selection walks the sort tree, which has no level for an
    ///   interior `(T,)` or a wrapper `translate_ty` collapses: walked with the
    ///   MIR indices raw, `o.t.0.y` with `t: (QT,)` selected `x.r1`. Those
    ///   steps are dropped, and a step that still disagrees with its sort is
    ///   refused. A refused path
    ///   reads memory, where the stores through `p` went, and records
    ///   `stack_deref_field_path_unfaithful` (FailClose): a register write the
    ///   memory image never saw would be missed there.
    fn try_stack_deref_field_expr(
        &self,
        base_addr: &Expr,
        pointee_ty: rustc_public::ty::Ty,
        remaining_projs: &[ProjectionElem],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let (obj_id, base_offset) = match Self::try_extract_constant_addr(base_addr) {
            Some(addr) => addr,
            None => {
                debug!(?base_addr, "CHC: stack Deref+Field has no constant base address");
                return None;
            }
        };
        let target_local = match self.heap_state.local_idx_for_obj_id(obj_id) {
            Some(local_idx) => local_idx,
            None => {
                debug!(obj_id, "CHC: stack Deref+Field obj_id has no stack local");
                return None;
            }
        };
        let source_local = if self.flatten.flattened_tuple_locals.contains(&target_local) {
            target_local
        } else if let Some(ref_target) = self.ref_resolution.ref_targets.get(&target_local)
            && ref_target.projections.is_empty()
            && self.flatten.flattened_tuple_locals.contains(&ref_target.local)
        {
            ref_target.local
        } else {
            debug!(obj_id, target_local, "CHC: stack Deref+Field target local is not flattened");
            return None;
        };
        // Rule B (design trust-mc-reds-final §4.2, C5a): a pointer is (object,
        // offset, pointee type). The pointee is the part of the local's value
        // at `base_offset` of type `pointee_ty`, found by the one object-path
        // rule (`decl::static_path`, rustc's layout); the remaining
        // projections apply to THAT part, not to the local's root. Before,
        // a pointee that was not the whole local was refused here and read
        // from memory at the stack address, a cell no rule writes for a
        // flattened local, so the value was free and a counterexample through
        // it was certified Genuine (`flat_nested_path_dual.rs::safe_md_read`:
        // `o.m.b` through `ManuallyDrop<Q2>`'s `Deref`).
        let source_ty = self.body.locals().get(source_local)?.ty;
        let Some(mut field_selections) =
            object_path_projections(source_ty, u64::from(base_offset), pointee_ty)
        else {
            debug!(
                obj_id,
                source_local,
                base_offset,
                "CHC: stack Deref+Field pointee has no unique path in the local — reading memory"
            );
            self.record_sound_fallback_reason(STACK_INTERIOR_PATH_UNRESOLVED);
            return None;
        };
        for proj in remaining_projs {
            let ProjectionElem::Field(field_idx, field_ty) = proj else {
                return None;
            };
            field_selections.push(FieldProjection {
                field_idx: *field_idx,
                cons_idx: None,
                field_ty: Some(*field_ty),
            });
        }
        // The flattened slots follow the SORT tree, where a wrapper
        // `translate_ty` collapses onto its content (`ManuallyDrop<Q2>` is
        // `Q2`'s sort, its `MaybeDangling<Q2>` level absent): those MIR steps
        // are dropped, and every other step is checked against its sort
        // (`faithful_flat_field_path`, C5b).
        let field_selections = match self.faithful_flat_field_path(source_local, &field_selections)
        {
            Ok(path) => path,
            Err(why) => {
                debug!(
                    obj_id,
                    source_local,
                    why,
                    "CHC: stack Deref+Field path has no faithful flattened slot — reading memory"
                );
                self.record_sound_fallback_reason(STACK_DEREF_FIELD_PATH_UNFAITHFUL);
                return None;
            }
        };
        let root = match self.reconstruct_flattened_bare_read(source_local, modified_locals) {
            Some(expr) => expr,
            None => {
                debug!(
                    obj_id,
                    source_local, "CHC: stack Deref+Field could not reconstruct flattened local"
                );
                return None;
            }
        };
        if field_selections.is_empty() {
            return Some(root);
        }
        let selected = Self::apply_field_selections(root, &field_selections);
        if selected.is_none() {
            debug!(obj_id, source_local, "CHC: stack Deref+Field field selection failed");
        }
        selected
    }
}
