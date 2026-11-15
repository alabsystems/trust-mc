// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Precise register mirror for a Mem-level store through a reference into a
//! flattened struct owner: `let r = &mut o; r.inner.a = 7;`.
//!
//! The memory store is emitted by `handle_deref_store_mem_level`; this writes
//! the same value into the owner's flattened slots, which is what later reads
//! of `o.inner.a` (read cases B and C of `translate_flattened_place`) consult.
//! The slot span comes from `resolve_flat_struct_path`, and every check the
//! 2026-09-24 critique required (R2-R8 in
//! `docs/chc-hole-fix-designs-2026-09-24.md`) either holds or the mirror
//! fails closed through `fail_close_ref_mirror`.

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::mir::ProjectionElem;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use ay_bindings::{Expr, Sort};

use super::super::codegen_expr_flat_struct_path::FlatStructSpan;
use super::super::codegen_stmt_flatten_copy::collect_leaf_exprs;
use super::super::codegen_types::CodegenTypes;
use super::super::stmt_accumulator::StmtAccumulator;
use super::super::{ChcCtx, FieldProjection, RefTarget};

/// How a reference's ref_target relates to the owner's register image.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum RefTargetJoin {
    /// The ref_target is the referent itself, a place inside the owner: the
    /// store's projections continue it, and the mirror writes along the join.
    Place,
    /// The ref_target is a POINTER-typed place (`Box`, `NonNull`, `Unique`, a
    /// reference, a raw pointer) whose pointee is the reference's pointee: the
    /// reference points THROUGH it (`Box::as_mut` registers `_r ->
    /// b.[Field(Unique), Field(NonNull)]`). The referent lives behind the
    /// pointer, the Mem-level store has written it there, and the owner's
    /// register holds only the unchanged pointer, so there is nothing to mirror.
    ThroughPointer,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// R4: the path the mirror composes is `ref_target.projections` (relative
    /// to the target local) followed by the store's projections after the
    /// Deref (relative to the reference's pointee). That join is only a path
    /// into the target when the ref_target is a Field/Downcast path whose
    /// place type is the pointee type (or translates to the same sort). A
    /// ref_target reached through a cast pointer, a Deref (dropped by the Skip
    /// collector), or an allocation id (which forgets the byte offset) fails
    /// this and must not be mirrored as if it were.
    ///
    /// A place of pointer type whose pointee type IS the reference's pointee
    /// is the other exact answer, `ThroughPointer`: failing it closed havocked
    /// the Box's own pointer slot, and the next `*b` read an arbitrary address
    /// and tripped the alignment check, so `*b.as_mut() = 5; assert!(*b == 5)`
    /// (verified by Kani, and SUCCESSFUL on main, where the arm only warned)
    /// became FAILED OverApproximation.
    pub(super) fn ref_mirror_join_check(
        &self,
        ref_target: &RefTarget,
        ref_local: usize,
    ) -> Result<RefTargetJoin, &'static str> {
        let mut place_ty =
            self.body.locals().get(ref_target.local).ok_or("ref_target_local_missing")?.ty;
        for proj in &ref_target.projections {
            match proj {
                ProjectionElem::Field(_, field_ty) => place_ty = *field_ty,
                ProjectionElem::Downcast(_) => {}
                _ => return Err("ref_target_projection_not_field_or_downcast"),
            }
        }
        let ref_ty = self.body.locals().get(ref_local).ok_or("ref_local_missing")?.ty;
        let pointee = ChcCtx::deref_pointee_ty(ref_ty).ok_or("ref_local_not_a_pointer")?;
        if place_ty == pointee {
            return Ok(RefTargetJoin::Place);
        }
        // Before the sort comparison: `NonNull<*mut u8>` and `*mut u8` share a
        // sort, and writing the pointee's value into the pointer slot is wrong.
        if ChcCtx::deref_pointee_ty(place_ty) == Some(pointee) {
            return Ok(RefTargetJoin::ThroughPointer);
        }
        match (Self::translate_ty(place_ty), Self::translate_ty(pointee)) {
            (Some(place_sort), Some(pointee_sort)) if place_sort == pointee_sort => {
                Ok(RefTargetJoin::Place)
            }
            _ => Err("ref_target_type_differs_from_pointee"),
        }
    }

    /// Mirror a store of `rhs_expr` to the Field-only path `combined` of the
    /// flattened struct `target_local`, exactly or not at all.
    pub(super) fn mirror_flat_struct_path_store(
        &mut self,
        target_local: usize,
        combined: &[FieldProjection],
        rhs_expr: &Expr,
        ref_local: usize,
        acc: &mut StmtAccumulator<'_>,
    ) {
        let span = match self.resolve_flat_struct_path(target_local, combined) {
            Ok(span) => span,
            Err(why) => {
                warn!(
                    target_local,
                    ref_local,
                    field_count = combined.len(),
                    why,
                    "CHC: flat struct path for Mem-level Deref mirror not resolved"
                );
                self.fail_close_ref_mirror(target_local, "deref_mirror_flat_path_unresolved", acc);
                return;
            }
        };
        let values = match self.flat_struct_store_values(target_local, &span, rhs_expr, acc) {
            Ok(values) => values,
            Err(why) => {
                warn!(
                    target_local,
                    ref_local,
                    offset = span.offset,
                    count = span.count,
                    why,
                    "CHC: flat struct mirror values not exact"
                );
                self.fail_close_ref_mirror(target_local, "deref_mirror_flat_value_unresolved", acc);
                return;
            }
        };
        // Every value is Some and has its slot's declared sort, so each slot
        // gets `out == value` and a fresh `flattened_field_env` entry; none
        // reaches the sort-mismatch or missing-slot branches.
        if !self.constrain_flattened_fields(target_local, &values, acc) {
            self.fail_close_ref_mirror(
                target_local,
                "deref_mirror_constraint_emission_failed",
                acc,
            );
            return;
        }
        self.encode.local_expr_env.remove(&target_local);
        self.encode.invalidate_local_cache(target_local);
        debug!(
            target_local,
            ref_local,
            offset = span.offset,
            count = span.count,
            "CHC: flat struct path mirror for Mem-level Deref store"
        );
    }

    /// The value of every flattened slot of `target_local` after the store:
    /// the stored leaves in the span, the current value everywhere else.
    fn flat_struct_store_values(
        &self,
        target_local: usize,
        span: &FlatStructSpan,
        rhs_expr: &Expr,
        acc: &StmtAccumulator<'_>,
    ) -> Result<Vec<Option<Expr>>, &'static str> {
        // R3: the stored value must already have the terminal's sort. Never
        // coerce here: a datatype rhs coerced into a bitvector slot is
        // truncated, and a failed slot coercion is a SoundHavoc that leaves a
        // stale `flattened_field_env` entry.
        let replacement: Vec<Expr> = if span.count == 1 {
            if *rhs_expr.sort() != span.terminal_slot_sorts()[0] {
                return Err("rhs_sort_differs_from_slot");
            }
            vec![rhs_expr.clone()]
        } else {
            if *rhs_expr.sort() != span.terminal_sort {
                return Err("rhs_sort_differs_from_terminal");
            }
            let mut leaves = Vec::with_capacity(span.count);
            collect_leaf_exprs(rhs_expr, &mut leaves);
            if leaves.len() != span.count {
                return Err("rhs_leaf_count_mismatch");
            }
            let mut replacement = Vec::with_capacity(span.count);
            for (leaf, sort) in leaves.into_iter().zip(span.terminal_slot_sorts()) {
                // R7: a None leaf is a selector ay refused; writing None would
                // keep the slot's old value.
                let leaf = leaf.ok_or("rhs_leaf_unavailable")?;
                if leaf.sort() != sort {
                    return Err("rhs_leaf_sort_mismatch");
                }
                replacement.push(leaf);
            }
            replacement
        };

        let target_modified = acc.modified.contains(&target_local);
        let mut values = Vec::with_capacity(span.declared.len());
        for (slot, sort) in span.declared.iter().enumerate() {
            if let Some(stored) = slot.checked_sub(span.offset).and_then(|i| replacement.get(i)) {
                values.push(Some(stored.clone()));
                continue;
            }
            // R7: once the owner is modified in this block, a sibling with no
            // cached value would read back as its own `__out` variable, and
            // `fldK__out == fldK__out` would replace (free) its earlier
            // in-block constraint.
            if target_modified
                && !self.encode.flattened_field_env.contains_key(&(target_local, slot))
            {
                return Err("sibling_value_not_cached");
            }
            let sibling = self
                .flattened_local_field_expr(target_local, slot, acc.modified)
                .ok_or("sibling_value_unavailable")?;
            if sibling.sort() != sort {
                return Err("sibling_sort_mismatch");
            }
            values.push(Some(sibling));
        }
        Ok(values)
    }

    /// Follow-up (c): a store through a reference into a field of a target
    /// that has ONE state variable. Writing `target_vec_idx + field_idx` named
    /// another local's slot whenever `field_idx > 0`. The whole-variable write
    /// is exact only when the field is the whole value: field 0 of a struct
    /// or tuple whose every other field is zero-sized, with the field's sort
    /// equal to the variable's sort and to the stored value's sort.
    pub(in crate::codegen_ay::chc) fn non_flattened_field_is_whole_value(
        &self,
        target_local: usize,
        field_proj: &FieldProjection,
        slot_sort: &Sort,
        rhs_expr: &Expr,
    ) -> bool {
        if field_proj.field_idx != 0 || field_proj.cons_idx.is_some() {
            return false;
        }
        let Some(field_ty) = field_proj.field_ty else { return false };
        if Self::translate_ty(field_ty).as_ref() != Some(slot_sort) || rhs_expr.sort() != slot_sort
        {
            return false;
        }
        let Some(local_decl) = self.body.locals().get(target_local) else { return false };
        let is_zst = |ty: rustc_public::ty::Ty| {
            ty.layout().ok().is_some_and(|l| l.shape().is_sized() && l.shape().size.bytes() == 0)
        };
        match local_decl.ty.kind() {
            TyKind::RigidTy(RigidTy::Tuple(elems)) => {
                elems.first() == Some(&field_ty) && elems[1..].iter().all(|ty| is_zst(*ty))
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let variants = def.variants();
                let [variant] = variants.as_slice() else { return false };
                let fields = variant.fields();
                !fields.is_empty()
                    && fields[1..].iter().all(|f| mono_ty::field_ty(f, &args).is_some_and(is_zst))
            }
            _ => false,
        }
    }
}
