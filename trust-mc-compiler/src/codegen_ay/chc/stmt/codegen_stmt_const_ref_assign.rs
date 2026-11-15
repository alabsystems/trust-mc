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
            // D4: the recorded object base PLUS its offset; a local with no
            // record has no address here (never the shared object 1).
            return self.ref_resolution.const_ref_objects.get(&local_idx).map(|o| o.address());
        }
        let local_ty = self.body.locals()[local_idx].ty;
        if !matches!(local_ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))) {
            return None;
        }

        match rhs {
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                if place.projection.is_empty() =>
            {
                let src_local = place.local;
                if let Some(const_value) =
                    self.ref_resolution.const_ref_values.get(&src_local).cloned()
                {
                    // Part of #3860 / D4: always propagate the object RECORD
                    // (object and offset) from source to destination on
                    // Copy/Move, even for non-array const refs. Without it a
                    // copied constant ref (e.g., assert_eq! macro temporaries
                    // for &Some(4u8)) loses its object and offset.
                    let object = self.ref_resolution.const_ref_objects.get(&src_local).copied();
                    match object {
                        Some(object) => {
                            self.ref_resolution.const_ref_objects.insert(local_idx, object);
                        }
                        None => {
                            self.ref_resolution.const_ref_objects.remove(&local_idx);
                        }
                    }
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
                    return object.map(|o| o.address());
                }
                // Source local has no const_ref_values entry — fall through
                // to the array catch-all below.
            }
            Rvalue::Use(Operand::Constant(_), ..) => {
                self.ref_resolution.const_ref_values.insert(local_idx, rhs_expr.clone());
                return self.ref_resolution.const_ref_objects.get(&local_idx).map(|o| o.address());
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
        // D4: without a recorded object this catch-all DECLINES (residual 5):
        // borrowing the shared object 1 aliased every unregistered constant.
        let object = self.ref_resolution.const_ref_objects.get(&local_idx).copied()?;
        self.ref_resolution.const_ref_values.insert(local_idx, rhs_expr.clone());
        Some(object.address())
    }
}
