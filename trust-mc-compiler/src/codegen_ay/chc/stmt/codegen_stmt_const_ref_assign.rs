// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Promoted const-ref assignment helpers for CHC statement lowering.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Rvalue};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Try to resolve a promoted const-ref array assignment to a concrete
    /// promoted address. Handles three patterns:
    ///
    /// 1. Copy/Move of a local with known const_ref_values (propagation)
    /// 2. Inline constant operand
    /// 3. Fallback: any array RHS where destination is a pointer type —
    ///    register the array as the const-ref value so downstream loads
    ///    can find it.
    pub(in crate::codegen_ay::chc) fn try_promoted_const_ref_array_address_fallback(
        &mut self,
        rhs: &Rvalue,
        rhs_expr: &Expr,
        local_idx: usize,
    ) -> Option<Expr> {
        if !rhs_expr.sort().is_array() {
            return None;
        }
        // Some promoted ref locals are pre-seeded during decl passes with the
        // backing array in const_ref_values even when the MIR local type later
        // reaches assignment lowering in a non-ref shape.
        if self
            .ref_resolution
            .const_ref_values
            .get(&local_idx)
            .is_some_and(|expr| expr.sort().is_array())
        {
            let promoted_obj_id = self
                .ref_resolution
                .const_ref_promoted_obj_ids
                .get(&local_idx)
                .copied()
                .unwrap_or(self.heap_state.promoted_const_obj_id);
            return Some(self.heap_state.promoted_const_address_for(promoted_obj_id));
        }
        let local_ty = self.body.locals()[local_idx].ty;
        if !matches!(local_ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))) {
            return None;
        }

        match rhs {
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                if place.projection.is_empty() =>
            {
                let src_local = place.local;
                if let Some(const_value) =
                    self.ref_resolution.const_ref_values.get(&src_local).cloned()
                {
                    // Part of #3860: Always propagate promoted_obj_id from source
                    // to destination on Copy/Move, even for non-array const refs.
                    // Without this, a copied promoted ref (e.g., assert_eq! macro
                    // temporaries for &Some(4u8)) loses its per-constant obj_id
                    // and falls back to the shared obj_id=1, producing an address
                    // mismatch with the entry rule / bb0 memory seeds.
                    let promoted_obj_id = self
                        .ref_resolution
                        .const_ref_promoted_obj_ids
                        .get(&src_local)
                        .copied()
                        .unwrap_or(self.heap_state.promoted_const_obj_id);
                    self.ref_resolution
                        .const_ref_promoted_obj_ids
                        .insert(local_idx, promoted_obj_id);
                    if !const_value.sort().is_array() {
                        // Part of #4070: propagate DT const ref values on copy/move
                        // so downstream PartialEq tuple comparisons can resolve the
                        // promoted constant referent. Without this, copy chains like
                        // `_38 = move _40` where _40 has a DT const_ref_values entry
                        // leave _38 unresolvable, causing fallback on tuple PartialEq.
                        self.ref_resolution.const_ref_values.insert(local_idx, const_value);
                        return None;
                    }
                    self.ref_resolution.const_ref_values.insert(local_idx, const_value);
                    if let Some(len) = self.ref_resolution.subslice_len.get(&src_local).cloned() {
                        self.ref_resolution.subslice_len.insert(local_idx, len);
                    }
                    if let Some(offset) =
                        self.ref_resolution.subslice_offset.get(&src_local).cloned()
                    {
                        self.ref_resolution.subslice_offset.insert(local_idx, offset);
                    }
                    return Some(self.heap_state.promoted_const_address_for(promoted_obj_id));
                }
                // Source local has no const_ref_values entry — fall through
                // to the array catch-all below.
            }
            Rvalue::Use(Operand::Constant(_)) => {
                self.ref_resolution.const_ref_values.insert(local_idx, rhs_expr.clone());
                let promoted_obj_id = self
                    .ref_resolution
                    .const_ref_promoted_obj_ids
                    .get(&local_idx)
                    .copied()
                    .unwrap_or(self.heap_state.promoted_const_obj_id);
                return Some(self.heap_state.promoted_const_address_for(promoted_obj_id));
            }
            _ => {}
        }

        // Part of #3794: Catch-all for array-to-pointer sort mismatch.
        // When the RHS translates to an array expression but the destination
        // is a pointer (Ref/RawPtr), the array IS the promoted const data.
        // Register it so downstream deref loads can find the concrete bytes
        // instead of seeing an unconstrained symbolic pointer.
        debug!(
            local_idx,
            ?rhs,
            "promoted_const_ref_array: catch-all for unmatched array→pointer pattern"
        );
        self.ref_resolution.const_ref_values.insert(local_idx, rhs_expr.clone());
        let promoted_obj_id = self
            .ref_resolution
            .const_ref_promoted_obj_ids
            .get(&local_idx)
            .copied()
            .unwrap_or(self.heap_state.promoted_const_obj_id);
        Some(self.heap_state.promoted_const_address_for(promoted_obj_id))
    }
}
