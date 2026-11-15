// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Static-local metadata propagation helpers for CHC encoding.
//!
//! Split from `codegen_decl_static.rs` to keep the static collection pass under
//! the file-size limit while preserving the local-to-static propagation logic.

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{Operand, Place, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use crate::codegen_ay::ptr_repr::PtrRepr;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn map_static_local_to_state_idx(
        &mut self,
        dest_local: usize,
        vec_idx: usize,
    ) {
        self.ref_resolution.static_ref_to_state_idx.insert(dest_local, vec_idx);
        self.seed_static_local_metadata(dest_local, vec_idx);
    }

    fn seed_static_local_metadata(&mut self, dest_local: usize, vec_idx: usize) {
        if let Some(seed_value) = self.ref_resolution.static_ref_value_seeds.get(&vec_idx).cloned()
        {
            self.ref_resolution.const_ref_values.insert(dest_local, seed_value);
        }
        if let Some(seed_len) = self.ref_resolution.static_ref_len_seeds.get(&vec_idx).cloned() {
            self.ref_resolution.subslice_len.insert(dest_local, seed_len);
        }
    }

    fn propagate_static_local(
        &mut self,
        src_local: usize,
        dest_local: usize,
        propagation: &'static str,
    ) -> bool {
        if self.ref_resolution.static_ref_to_state_idx.contains_key(&dest_local) {
            return false;
        }

        let Some(&vec_idx) = self.ref_resolution.static_ref_to_state_idx.get(&src_local) else {
            return false;
        };

        // A cast to another pointee TYPE reads another window of the static.
        // A FIXED static is then read from its memory, which is seeded whole at
        // every type the harness dereferences (D2); carrying its state
        // variable and value seed to `&raw const SW as *const u8` indexed the
        // `[u16; 2]` value by byte offset and certified a counterexample to a
        // true byte. A LIVE static keeps the mapping: its state variable is
        // the only place its writes reach, and a read at a mismatched type
        // through it fails closed (measured: `probe_live_cast`).
        if propagation == "Cast (#428)"
            && !self.ref_resolution.mutable_static_state_idxs.contains(&vec_idx)
        {
            let locals = self.body.locals();
            let pointee =
                |local: usize| locals.get(local).and_then(|l| Self::deref_pointee_ty(l.ty));
            if let (Some(src), Some(dest)) = (pointee(src_local), pointee(dest_local))
                && !crate::codegen_ay::chc::decl::global_objects::fact_types_compatible(src, dest)
            {
                debug!(
                    src = src_local,
                    dest = dest_local,
                    vec_idx,
                    "CHC: fixed static cast to another pointee type: memory answers"
                );
                return false;
            }
        }

        self.map_static_local_to_state_idx(dest_local, vec_idx);
        // The same pointer: the same part of the static (D6).
        if let Some(path) = self.ref_resolution.static_ref_paths.get(&src_local).cloned() {
            self.ref_resolution.static_ref_paths.insert(dest_local, path);
        }
        debug!(
            src = src_local,
            dest = dest_local,
            vec_idx,
            propagation,
            "CHC: propagated static ref"
        );
        true
    }

    fn propagate_projected_static_value(&mut self, place: &Place, dest_local: usize) -> bool {
        if self.ref_resolution.const_ref_values.contains_key(&dest_local) {
            return false;
        }
        if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            return false;
        }

        let Some((value, value_ty, slot_offset)) = self.projected_immutable_static_value(place)
        else {
            return false;
        };
        // `const_ref_values[X]` answers "what is `*X`?" — see
        // `try_resolve_const_ref_deref`. When `_dest = copy (*STATIC)` loads a
        // POINTER-typed static, `value` is the pointer itself, so recording it
        // here answers `*_dest` with `_dest`'s own address bits: `*Z == 14`
        // becomes a comparison of `Z`'s obj-id/offset word against 14 and the
        // assertion is refutable. A pointer-typed static's referent value is
        // one level further in, and that is what this entry must carry.
        if matches!(
            self.body.locals()[dest_local].ty.kind(),
            TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
        ) {
            let Some(&vec_idx) = self.ref_resolution.static_ref_to_state_idx.get(&place.local)
            else {
                return false;
            };
            if !self.static_metadata_value_is_stable(place.local)
                || !self.static_metadata_value_is_stable(dest_local)
                || !super::static_path::same_ty_modulo_regions(
                    value_ty,
                    self.body.locals()[dest_local].ty,
                )
            {
                return false;
            }
            let Some(pointee_ty) = Self::deref_pointee_ty(value_ty) else { return false };
            let Some((pointee_value, metadata)) =
                self.projected_pointer_static_seed(place.local, vec_idx, slot_offset, pointee_ty)
            else {
                return false;
            };
            self.ref_resolution.const_ref_values.insert(dest_local, pointee_value);
            if let Some(metadata) = metadata {
                self.ref_resolution.subslice_len.insert(dest_local, metadata);
            }
            debug!(
                src = place.local,
                dest = dest_local,
                "CHC: propagated projected pointer slot's fixed referent value"
            );
            return true;
        }
        // Address-vs-value: the metadata half is recorded only when the place's
        // Rust TYPE says a metadata half exists, and only when the term is a
        // GENUINE fat pointer.
        //
        // The retired test was `width == 2 * POINTER_WIDTH` alone, which is the
        // fabricated-fat-pointer-metadata shape verbatim: a `u128` static and a
        // thin pointer zero-extended into a wide slot are both `bv128`, and both
        // yielded a `subslice_len` — usually `0` for the widening, which makes
        // every downstream bounds obligation trivially satisfiable, i.e. it can
        // manufacture a PROOF rather than a spurious counterexample.
        //
        // Two independent facts now have to agree, neither of them a width test:
        // the projected place is a WIDE-pointer type (only those have metadata at
        // all), and `PtrRepr` decodes the term structurally as `Fat` — it returns
        // `None` for `WidenedThin`, so the padding is unrepresentable here rather
        // than merely discouraged.
        let place_ty = place.ty(self.body.locals()).ok();
        if place_ty.is_some_and(Self::is_wide_pointer_ty)
            && let Some(len) = PtrRepr::classify(&value).and_then(PtrRepr::into_metadata)
        {
            self.ref_resolution.subslice_len.insert(dest_local, len.into_expr());
        }
        self.ref_resolution.const_ref_values.insert(dest_local, value);
        debug!(
            src = place.local,
            dest = dest_local,
            "CHC: propagated projected immutable static value"
        );
        true
    }

    /// Does `ty` denote a **wide** pointer — a reference or raw pointer whose
    /// pointee is unsized, so the encoder gives it a `[metadata | data]` slot?
    ///
    /// This is the fact `propagate_projected_static_value` needs and the width
    /// test could not supply: only these types HAVE a metadata half, so only
    /// these can have one read back out. A `u128` static, a `[u8; 16]` flattened
    /// into a `bv128`, and a thin pointer widened into a wide slot are all
    /// `bv128` and all answer `false` here.
    fn is_wide_pointer_ty(ty: Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => matches!(
                pointee.kind(),
                TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str | RigidTy::Dynamic(..))
            ),
            _ => false, // external enum: TyKind
        }
    }

    fn projected_immutable_static_value(&self, place: &Place) -> Option<(Expr, Ty, usize)> {
        let &vec_idx = self.ref_resolution.static_ref_to_state_idx.get(&place.local)?;
        if self.ref_resolution.mutable_static_state_idxs.contains(&vec_idx) {
            return None;
        }
        let mut current = self.ref_resolution.static_initial_values.get(&vec_idx)?.clone();
        let mut current_ty =
            self.normalize_static_ty(*self.ref_resolution.static_state_ty.get(&vec_idx)?);
        let mut slot_offset = 0usize;

        for proj in &place.projection[1..] {
            let TyKind::RigidTy(RigidTy::Array(element_ty, length)) = current_ty.kind() else {
                return None;
            };
            let length = usize::try_from(length.eval_target_usize().ok()?).ok()?;
            let index = match proj {
                ProjectionElem::Index(index_local) => {
                    if !self.static_metadata_value_is_stable(*index_local) {
                        return None;
                    }
                    let value = self.unique_constant_usize_assignment(*index_local)?;
                    Expr::bitvec_const(value as u128, crate::codegen_ay::types::POINTER_WIDTH)
                }
                ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                    let offset = usize::try_from(*offset).ok()?;
                    if length < usize::try_from(*min_length).ok()? {
                        return None;
                    }
                    let actual = if *from_end { length.checked_sub(offset)? } else { offset };
                    Expr::bitvec_const(actual as u128, crate::codegen_ay::types::POINTER_WIDTH)
                }
                _ => return None,
            };
            let element_index = Self::bitvec_const_key(&index)?.0;
            let element_index = usize::try_from(element_index).ok()?;
            if element_index >= length {
                return None;
            }
            slot_offset = slot_offset
                .checked_add(element_index.checked_mul(self.get_type_size(element_ty)?)?)?;
            current = Self::simplify_select_from_static_array(&current, &index)?;
            current_ty = self.normalize_static_ty(element_ty);
        }

        Some((current, current_ty, slot_offset))
    }

    /// Declaration-time value facts cannot describe an entry parameter or
    /// storage that can be reassigned through an alias.
    fn static_metadata_value_is_stable(&self, local: usize) -> bool {
        !(local > 0 && local <= self.body.arg_locals().len())
            && !self.pointer_value_is_path_dependent(local)
            && !self.local_bytes_may_be_rewritten(local)
    }

    /// Decode the pointer at its actual slot in the immutable parent static,
    /// then read only the fixed pointee window that relocation and metadata name.
    fn projected_pointer_static_seed(
        &mut self,
        source_local: usize,
        vec_idx: usize,
        slot_offset: usize,
        pointee_ty: Ty,
    ) -> Option<(Expr, Option<Expr>)> {
        use crate::codegen_ay::shared::const_pointer::{self, Fixedness};
        // The one mapped state slot is not sufficient authority: a copied
        // argument or a join can have inherited one producer's mapping.
        let source = Operand::Copy(Place { local: source_local, projection: vec![] });
        let mut keys = self.static_pointer_sources(&source, 16)?.into_iter();
        let key = keys.next()?;
        if keys.next().is_some()
            || self.ref_resolution.static_state_idx_by_obj.get(&self.global_object(&key)?.obj_id)
                != Some(&vec_idx)
        {
            return None;
        }
        let (bytes, fixed) = const_pointer::target_bytes(self.tcx, &key)?;
        if fixed != Fixedness::Fixed {
            return None;
        }
        let (pointer, value) = self.fixed_window_value(&bytes, slot_offset, pointee_ty)?;
        let metadata = if const_pointer::pointee_has_len_metadata(pointee_ty) {
            Some(Expr::bitvec_const(
                u128::from(pointer.metadata?),
                crate::codegen_ay::types::POINTER_WIDTH,
            ))
        } else {
            None
        };
        Some((value, metadata))
    }

    fn unique_constant_usize_assignment(&self, local: usize) -> Option<usize> {
        let mut values = Vec::new();
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && lhs.projection.is_empty()
                    && lhs.local == local
                    && let Rvalue::Use(Operand::Constant(const_op), ..) = rhs
                    && let Some(value) = Self::extract_static_const_usize(&const_op.const_)
                {
                    values.push(value);
                }
            }
        }
        values.sort_unstable();
        values.dedup();
        match values.as_slice() {
            [value] => Some(*value),
            _ => None,
        }
    }

    fn extract_static_const_usize(mir_const: &rustc_public::ty::MirConst) -> Option<usize> {
        if !matches!(
            mir_const.ty().kind(),
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Uint(_))
        ) {
            return None;
        }
        crate::codegen_ay::shared::const_pointer::const_uint(mir_const)
            .and_then(|value| usize::try_from(value).ok())
    }

    fn simplify_select_from_static_array(array: &Expr, select_index: &Expr) -> Option<Expr> {
        match array.value() {
            ExprValue::ConstArray { value, .. } => Some(value.clone()),
            ExprValue::Store { array: inner, index: store_index, value } => {
                if select_index == store_index
                    || Self::bitvec_const_key(select_index) == Self::bitvec_const_key(store_index)
                {
                    return Some(value.clone());
                }

                if Self::bitvec_const_key(select_index).is_some()
                    && Self::bitvec_const_key(store_index).is_some()
                {
                    return Self::simplify_select_from_static_array(inner, select_index);
                }

                None
            }
            _ => None,
        }
    }

    fn bitvec_const_key(expr: &Expr) -> Option<(num_bigint::BigInt, u32)> {
        if let ExprValue::BitVecConst { value, width } = expr.value() {
            Some((value.clone(), *width))
        } else {
            None
        }
    }

    pub(in crate::codegen_ay::chc) fn propagate_static_ref_state_idxs(&mut self) {
        if self.ref_resolution.static_ref_to_state_idx.is_empty() {
            return;
        }

        let mut changed = true;
        while changed {
            changed = false;
            for bb_data in &self.body.blocks {
                for stmt in &bb_data.statements {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                        continue;
                    };

                    if let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) = rhs
                        && place.projection.is_empty()
                    {
                        changed |=
                            self.propagate_static_local(place.local, lhs.local, "Copy/Move (#428)");
                    }
                    if let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) = rhs
                        && !place.projection.is_empty()
                    {
                        changed |= self.propagate_projected_static_value(place, lhs.local);
                    }

                    if let Rvalue::CopyForDeref(place) = rhs
                        && place.projection.is_empty()
                    {
                        changed |= self.propagate_static_local(
                            place.local,
                            lhs.local,
                            "CopyForDeref (#1836)",
                        );
                    }

                    if let Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) = rhs
                        && place.projection.is_empty()
                    {
                        changed |=
                            self.propagate_static_local(place.local, lhs.local, "Cast (#428)");
                    }

                    let reborrow_place = match rhs {
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => Some(place),
                        _ => None,
                    };
                    if let Some(place) = reborrow_place
                        && place.projection.len() == 1
                        && matches!(place.projection.first(), Some(ProjectionElem::Deref))
                    {
                        changed |= self.propagate_static_local(
                            place.local,
                            lhs.local,
                            "Ref/AddressOf reborrow (#1836)",
                        );
                    }
                }
            }
        }
    }
}
