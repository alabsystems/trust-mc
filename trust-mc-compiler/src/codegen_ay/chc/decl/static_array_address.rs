// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Storage-address facts for bounded LIVE arrays. These are deliberately not
//! referent VALUE facts: interior-mutable values must never seed an alias.
use super::ChcCtx;
use super::static_path::{same_ty_modulo_regions, static_path};
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::BTreeSet;

impl ChcCtx<'_, '_> {
    /// Origin keys are established at producers, before declaration or flow
    /// encoding. Resolve them to this body's one state variable per object.
    pub(in crate::codegen_ay::chc) fn static_array_address_origins(
        &self,
        op: &Operand,
    ) -> Option<BTreeSet<usize>> {
        self.static_pointer_sources(op, 16)?
            .into_iter()
            .map(|key| {
                let object = self.ref_resolution.global_objects.get(&key)?;
                self.ref_resolution.static_state_idx_by_obj.get(&object.obj_id).copied()
            })
            .collect()
    }

    /// Rebuild only the addressed element. Every address comparison uses the
    /// entire pointer, including allocation identity. No coverage assumption is
    /// added to the VC. Bounds/liveness checks remain on the ordinary store.
    pub(in crate::codegen_ay::chc) fn static_array_after_address_store(
        &self,
        idx: usize,
        addr: &Expr,
        value_ty: rustc_public::ty::Ty,
        current: &Expr,
        value: Expr,
    ) -> Option<Expr> {
        let ty = *self.ref_resolution.static_state_ty.get(&idx)?;
        let TyKind::RigidTy(RigidTy::Array(elem, len)) = ty.kind() else { return None };
        if !same_ty_modulo_regions(elem, value_ty) {
            return None;
        }
        let len = len.eval_target_usize().ok()?;
        // Match the existing static image expansion bound, never enlarge it.
        if len == 0 || len > 256 {
            return None;
        }
        let stride = self.get_type_size(elem)?;
        if stride == 0 {
            return None;
        }
        let mut objects =
            self.ref_resolution.static_state_idx_by_obj.iter().filter(|(_, i)| **i == idx);
        let (&object, _) = objects.next()?;
        if objects.next().is_some() {
            return None;
        }
        let base = Expr::bitvec_const(object as u128, 32).concat(Expr::bitvec_const(0u128, 32));
        if (stride as u64).checked_mul(len)? > u32::MAX as u64 {
            return None;
        }
        let mut updated = current.clone();
        for i in 0..len {
            let offset = i.checked_mul(stride as u64)?;
            let path = static_path(ty, offset, elem)?;
            let old = Self::select_static_path(current.clone(), &path)?;
            let written = Self::update_static_path_scalar(&old, &[], value.clone())?;
            let address = base.clone().bvadd(Expr::bitvec_const(offset as u128, POINTER_WIDTH));
            let cell = Expr::ite(addr.clone().eq(address), written, old);
            updated = Self::update_static_path(&updated, &path, cell)?;
        }
        Some(updated)
    }
    /// A complete case split has a symbolic catch-all; these addresses are
    /// optimization cases, never an assumed coverage disjunction.
    pub(in crate::codegen_ay::chc) fn static_array_store_address_cases(
        &self,
        routes: &[super::static_path::StaticStoreRoute],
        value_ty: rustc_public::ty::Ty,
    ) -> Option<Vec<Expr>> {
        let mut addresses = Vec::new();
        for route in routes {
            route.address.as_ref()?;
            let ty = *self.ref_resolution.static_state_ty.get(&route.vec_idx)?;
            let TyKind::RigidTy(RigidTy::Array(elem, n)) = ty.kind() else { return None };
            if !same_ty_modulo_regions(elem, value_ty) {
                return None;
            }
            let n = n.eval_target_usize().ok()?;
            if n == 0 || n > 256 || addresses.len().checked_add(n as usize)? > 256 {
                return None;
            }
            let stride = self.get_type_size(elem)? as u64;
            if stride == 0 || n.checked_mul(stride)? > u32::MAX as u64 {
                return None;
            }
            let mut objects = self
                .ref_resolution
                .static_state_idx_by_obj
                .iter()
                .filter(|(_, i)| **i == route.vec_idx);
            let (&object, _) = objects.next()?;
            if objects.next().is_some() {
                return None;
            }
            for j in 0..n {
                addresses.push(
                    Expr::bitvec_const(object as u128, 32)
                        .concat(Expr::bitvec_const((j * stride) as u128, 32)),
                );
            }
        }
        (!addresses.is_empty()).then_some(addresses)
    }
}
