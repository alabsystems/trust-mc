// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Section 1.25: Auxiliary pointee state variables for reference-bearing arguments.
//!
//! Extracted from `codegen_decl_state_vars_collections.rs` for 500-LOC compliance
//! and to keep wrapped-ref propagation logic isolated from collection aux state.

use std::collections::HashMap;

use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::codegen_types::CodegenTypes;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn wrapped_ref_arg_pointee_ty(ty: Ty) -> Option<(usize, Ty)> {
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            return None;
        };
        let variants = def.variants();
        if variants.len() != 1 {
            return None;
        }
        let fields = variants[0].fields();
        if fields.len() != 1 {
            return None;
        }
        let field_ty = fields[0].ty_with_args(&args);
        match field_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => Some((0, inner)),
            _ => None,
        }
    }

    /// Create auxiliary pointee state variables for `&T`/`&mut T`-shaped function arguments.
    ///
    /// Function arguments that arrive as references have no `_N = &_M` statement in MIR,
    /// so CHC must synthesize a pointee slot for the incoming argument. The same mechanism
    /// now covers single-field wrappers like `Pin<&mut T>`, where the field copy becomes
    /// the actual ref local that downstream deref paths operate on.
    pub(in crate::codegen_ay::chc) fn collect_state_vars_ref_pointees(&mut self) {
        let arg_count = self.body.arg_locals().len();
        for (local_idx, local_decl) in self.body.local_decls() {
            if local_idx == 0 || local_idx > arg_count {
                continue;
            }
            let wrapped_ref = Self::wrapped_ref_arg_pointee_ty(local_decl.ty);
            let direct_ref = match local_decl.ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => Some(inner),
                _ => None,
            };
            let Some((field_idx, pointee_ty)) = direct_ref
                .map(|inner| (None, inner))
                .or_else(|| wrapped_ref.map(|(field_idx, inner)| (Some(field_idx), inner)))
            else {
                continue;
            };

            if Self::type_name_contains_bigint(&pointee_ty)
                || Self::type_name_contains_bigrational(&pointee_ty)
            {
                continue;
            }
            let Some(pointee_sort) = Self::translate_ty(pointee_ty) else {
                continue;
            };

            let pointee_vec_idx = self.state_var_mgr.state_vars.len();
            let pointee_name = crate::codegen_ay::names::pointee_var_name(&self.fn_name, local_idx);
            let pointee_out_name = crate::codegen_ay::names::out_name(&pointee_name);

            self.push_state_var_pair(&pointee_name, &pointee_out_name, pointee_sort);

            if let Some(field_idx) = field_idx {
                self.ref_resolution
                    .arg_wrapper_field_pointee_idx
                    .insert((local_idx, field_idx), pointee_vec_idx);
                debug!(
                    local_idx,
                    field_idx,
                    pointee_vec_idx,
                    "CHC: created auxiliary pointee state var for wrapper arg field"
                );
            } else {
                self.ref_resolution.ref_arg_pointee_idx.insert(local_idx, pointee_vec_idx);
                debug!(
                    local_idx,
                    pointee_vec_idx,
                    "CHC: created auxiliary pointee state var for &T argument (#2496)"
                );
            }
        }

        self.propagate_arg_ref_pointee_use_chains();
        self.propagate_coroutine_root_map();
    }

    fn arg_ref_pointee_idx_for_use_place(&self, place: &rustc_public::mir::Place) -> Option<usize> {
        if place.projection.is_empty() {
            return self.ref_resolution.ref_arg_pointee_idx.get(&place.local).copied();
        }

        if place.projection.len() == 1
            && let rustc_public::mir::ProjectionElem::Field(field_idx, field_ty) =
                place.projection[0]
            && matches!(field_ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, _, _)))
        {
            return self
                .ref_resolution
                .arg_wrapper_field_pointee_idx
                .get(&(place.local, field_idx))
                .copied();
        }

        None
    }

    fn arg_ref_pointee_idx_for_derived_ref_rvalue(&self, rhs: &Rvalue) -> Option<usize> {
        match rhs {
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
            | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
                self.arg_ref_pointee_idx_for_use_place(place)
            }
            Rvalue::CopyForDeref(place) => self.arg_ref_pointee_idx_for_use_place(place),
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                if place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref) =>
            {
                self.ref_resolution.ref_arg_pointee_idx.get(&place.local).copied()
            }
            _ => None,
        }
    }

    /// Propagate synthesized pointee slots through copy/cast/reborrow chains.
    ///
    /// Coroutine resume lowers `Pin<&mut Coroutine>` by copying the wrapped ref field
    /// into a temporary before dereferencing it for discriminant reads/writes, and
    /// later reborrows that temporary with `&*ref`. This pass preserves the incoming
    /// pointee slot across both stages so downstream `Discriminant(*_ref)` and
    /// `SetDiscriminant(*_ref, ..)` can resolve the referent precisely.
    fn propagate_arg_ref_pointee_use_chains(&mut self) {
        for _pass in 0..self.body.locals().len().max(1) {
            let mut new_entries: Vec<(usize, usize)> = Vec::new();
            for bb in &self.body.blocks {
                for stmt in &bb.statements {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                        continue;
                    };
                    if !lhs.projection.is_empty() {
                        continue;
                    }
                    let src_pointee_idx = self.arg_ref_pointee_idx_for_derived_ref_rvalue(rhs);
                    if let Some(pointee_vec_idx) = src_pointee_idx
                        && self.ref_resolution.ref_arg_pointee_idx.get(&lhs.local)
                            != Some(&pointee_vec_idx)
                    {
                        new_entries.push((lhs.local, pointee_vec_idx));
                    }
                }
            }
            if new_entries.is_empty() {
                break;
            }
            for (dest_local, pointee_vec_idx) in new_entries {
                self.ref_resolution
                    .ref_arg_pointee_idx
                    .entry(dest_local)
                    .or_insert(pointee_vec_idx);
            }
        }
    }

    fn local_points_directly_to_coroutine(&self, local_idx: usize) -> bool {
        matches!(
            self.body.locals()[local_idx].ty.kind(),
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Coroutine(..)))
        )
    }

    fn seed_coroutine_root_map(&self) -> HashMap<usize, usize> {
        let mut root_map: HashMap<usize, usize> = HashMap::new();

        for (&local_idx, &pointee_vec_idx) in &self.ref_resolution.ref_arg_pointee_idx {
            if self.local_points_directly_to_coroutine(local_idx) {
                root_map.insert(local_idx, pointee_vec_idx);
            }
        }

        let arg_count = self.body.arg_locals().len();
        for local_idx in 1..=arg_count {
            let local_ty = self.body.locals()[local_idx].ty;
            let Some((field_idx, pointee_ty)) = Self::wrapped_ref_arg_pointee_ty(local_ty) else {
                continue;
            };
            if !matches!(pointee_ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
                continue;
            }
            if let Some(&pointee_vec_idx) =
                self.ref_resolution.arg_wrapper_field_pointee_idx.get(&(local_idx, field_idx))
            {
                root_map.insert(local_idx, pointee_vec_idx);
            }
        }

        // Part of #3807: type-based seeding for inlined coroutine bodies.
        // When coroutine bodies are inlined into main, the coroutines are
        // local variables (not args). Find ALL Coroutine-typed locals and their
        // state vars, then seed all locals whose type is `&[mut] Coroutine` or
        // `Pin<&mut Coroutine>` into root_map. Multiple coroutines (e.g.,
        // gen_copy + gen_move in resume-arg.rs) each need separate root entries.
        let mut coroutine_locals: Vec<(Ty, usize)> = Vec::new();
        for (local_idx, local_decl) in self.body.local_decls() {
            if matches!(local_decl.ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
                if let Some(vec_idx) = self.state_var_mgr.try_state_idx_for_local(local_idx) {
                    debug!(local_idx, vec_idx, "coroutine_root_map: found Coroutine-typed local");
                    coroutine_locals.push((local_decl.ty, vec_idx));
                }
            }
        }
        for (coroutine_ty, vec_idx) in &coroutine_locals {
            for (local_idx, local_decl) in self.body.local_decls() {
                if root_map.contains_key(&local_idx) {
                    continue;
                }
                let is_ref_to_coroutine = match local_decl.ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                    | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner == *coroutine_ty,
                    _ => false,
                };
                let is_pin_ref_to_coroutine = if !is_ref_to_coroutine {
                    Self::wrapped_ref_arg_pointee_ty(local_decl.ty)
                        .is_some_and(|(_, inner)| inner == *coroutine_ty)
                } else {
                    false
                };
                if is_ref_to_coroutine || is_pin_ref_to_coroutine {
                    root_map.insert(local_idx, *vec_idx);
                }
            }
        }

        root_map
    }

    fn coroutine_root_for_rvalue(rhs: &Rvalue, root_map: &HashMap<usize, usize>) -> Option<usize> {
        match rhs {
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
            | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                if place.projection.is_empty() =>
            {
                root_map.get(&place.local).copied()
            }
            // Part of #3807: wrapper-field copies like `copy (_pin.0)` where _pin
            // is already in root_map. Coroutine resume MIR re-wraps Pin<&mut Self>
            // across basic blocks, producing new locals that copy the inner &mut
            // from these re-wrapped Pins. Propagate the root through single-field
            // projections so later deref sites resolve the coroutine root.
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                if place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Field(..)) =>
            {
                root_map.get(&place.local).copied()
            }
            Rvalue::CopyForDeref(place) if place.projection.is_empty() => {
                root_map.get(&place.local).copied()
            }
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                if place.projection.is_empty() =>
            {
                root_map.get(&place.local).copied()
            }
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                if place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref) =>
            {
                root_map.get(&place.local).copied()
            }
            _ => None,
        }
    }

    /// Pre-register coroutine root state vars for Pin/ref locals and propagate
    /// them through identity-like MIR chains.
    ///
    /// Part of #3807: coroutine resume MIR repeatedly copies and reborrows
    /// `Pin<&mut Coroutine>`-derived locals before reaching `SetDiscriminant`
    /// and discriminant reads. Record the concrete coroutine root once, then
    /// carry that root through the local chain instead of retracing Pin unwraps
    /// at each use site.
    fn propagate_coroutine_root_map(&mut self) {
        let mut root_map = self.seed_coroutine_root_map();
        if root_map.is_empty() {
            self.ref_resolution.coroutine_root_map.clear();
            return;
        }
        debug!(
            body_locals = self.body.locals().len(),
            seed_count = root_map.len(),
            ?root_map,
            "coroutine_root_map: seeded"
        );

        for _pass in 0..self.body.locals().len().max(1) {
            let mut new_entries: Vec<(usize, usize)> = Vec::new();
            for bb in &self.body.blocks {
                for stmt in &bb.statements {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                        continue;
                    };
                    if !lhs.projection.is_empty() || root_map.contains_key(&lhs.local) {
                        continue;
                    }

                    if let Some(pointee_vec_idx) = Self::coroutine_root_for_rvalue(rhs, &root_map) {
                        new_entries.push((lhs.local, pointee_vec_idx));
                    }
                }
            }

            if new_entries.is_empty() {
                break;
            }

            for (local_idx, pointee_vec_idx) in new_entries {
                root_map.insert(local_idx, pointee_vec_idx);
            }
        }

        self.ref_resolution.coroutine_root_map = root_map;
    }
}
