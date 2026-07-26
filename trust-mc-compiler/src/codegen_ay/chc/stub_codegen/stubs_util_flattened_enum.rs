// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Flattened enum fld0/fld1 resolution helpers for CHC stub translation.
//!
//! Extracted from stubs_util.rs per #2408 decomposition.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};

use super::ChcCtx;
use crate::codegen_ay::chc::codegen_types::CodegenTypes;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Returns whether a local should be treated as a flattened enum value.
    ///
    /// The primary source of truth is `flattened_enum_discr`. Some MIR paths can
    /// still produce flattened Option/Result locals where that map entry is absent.
    /// In those cases, fall back to local-type and flattened-shape checks.
    pub(in crate::codegen_ay::chc) fn is_flattened_enum_like_local(
        &self,
        local_idx: usize,
    ) -> bool {
        if self.flatten.flattened_enum_discr.contains_key(&local_idx) {
            return true;
        }
        // Part of #3240: Strategy 3 (BV-flattened multi-ctor) enums are also
        // flattened enum-like — they have a tag at fld0 and payload at fld1+.
        if self.flatten.enum_bv_layouts.contains_key(&local_idx) {
            return true;
        }
        if !self.flatten.flattened_tuple_locals.contains(&local_idx) {
            return false;
        }
        if self.flattened_field_count(local_idx) < 2 {
            return false;
        }
        // Option/Result local type information can be missing after MIR-level
        // lowering/copy propagation. In that case, use shape: flattened locals
        // with a Bool discriminant in fld0 are Option/Result-like.
        if let Some(vec_idx) = self.try_state_idx_for_local(local_idx) {
            if self.state_var_mgr.state_vars.get(vec_idx).is_some_and(|(_, sort)| sort.is_bool()) {
                return true;
            }
        }
        let Some(local_decl) = self.body.locals().get(local_idx) else {
            return false;
        };
        matches!(
            local_decl.ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _))
                if {
                    let name = def.trimmed_name();
                    name == "Option" || name == "Result"
                }
        )
    }

    fn resolve_flattened_field_expr(
        &self,
        local_idx: usize,
        field_idx: usize,
        vec_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Reuse the exact field expression emitted by the current assignment or
        // call-result constraints before falling back to state variables.
        if let Some(expr) = self.encode.flattened_field_env.get(&(local_idx, field_idx)) {
            return Some(expr.clone());
        }

        let vars = if modified_locals.contains(&local_idx) {
            &self.state_var_mgr.output_state_vars
        } else {
            &self.state_var_mgr.state_vars
        };
        vars.get(vec_idx + field_idx).map(|(name, sort)| Expr::var(&**name, sort.clone()))
    }

    /// Resolve the fld0 discriminant of a flattened enum local referenced by
    /// the first operand (typically `&self` for predicate calls).
    ///
    /// Part of #2244: After flattening (#2214), Option/Result locals are decomposed
    /// into scalar state vars. Predicate stubs like `is_some`/`is_ok` pass `&self`
    /// as the first arg, which is a reference to the flattened local. This helper
    /// follows `ref_targets` to find the target local, checks if it's in
    /// `flattened_enum_discr`, and returns the fld0 expression (the discriminant).
    pub(in crate::codegen_ay::chc) fn resolve_flattened_enum_discr(
        &self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let arg = args.first()?;
        let place = match arg {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }
        let ref_local: usize = place.local;

        // Resolve through ref_targets to get the actual Option/Result local.
        let ref_target = self.ref_resolution.ref_targets.get(&ref_local)?;
        let target_local = ref_target.local;

        // Check if the target is a flattened enum (has discriminant info).
        if !self.is_flattened_enum_like_local(target_local) {
            return None;
        }

        // Read fld0 (discriminant) from the flattened local.
        let vec_idx = self.try_state_idx_for_local(target_local)?;
        self.resolve_flattened_field_expr(target_local, 0, vec_idx, modified_locals)
    }

    /// Resolve fld0 (discriminant) from a by-value flattened enum operand.
    ///
    /// Part of #2244: unwrap_or and other by-value stubs pass `self` as Move/Copy
    /// of the local directly. This helper reads fld0 without going through ref_targets.
    pub(in crate::codegen_ay::chc) fn resolve_flattened_enum_discr_by_value(
        &self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let place = match operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }
        let local_idx: usize = place.local;

        if !self.is_flattened_enum_like_local(local_idx) {
            return None;
        }

        let vec_idx = self.try_state_idx_for_local(local_idx)?;
        self.resolve_flattened_field_expr(local_idx, 0, vec_idx, modified_locals)
    }

    /// Resolve the payload from a by-value or by-ref flattened enum operand.
    ///
    /// For Strategy 2 (Bool+payload) enums, the payload is at fld1 (vec_idx + 1).
    /// For Strategy 3 (BV-flattened multi-ctor) enums, the payload slot is
    /// determined by `ctor_field_slot`: we find the first constructor with at
    /// least one field and return its first field's state var.
    ///
    /// Part of #2244, #3240.
    pub(in crate::codegen_ay::chc) fn resolve_flattened_enum_payload(
        &self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        fn is_leaf_sort(sort: &Sort) -> bool {
            sort.is_bitvec() || sort.is_bool() || sort.is_int() || sort.is_real() || sort.is_array()
        }

        let place = match operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }
        let operand_local: usize = place.local;

        // Try direct local first (by-value), then ref_targets (by-ref).
        let target_local = if self.is_flattened_enum_like_local(operand_local) {
            operand_local
        } else if let Some(ref_target) = self.ref_resolution.ref_targets.get(&operand_local) {
            let tgt = ref_target.local;
            if self.is_flattened_enum_like_local(tgt) {
                tgt
            } else {
                return None;
            }
        } else {
            return None;
        };

        let vec_idx = self.try_state_idx_for_local(target_local)?;

        // Part of #3240: For Strategy 3 enums, use ctor_field_slot to find the
        // correct payload slot instead of hardcoded fld1.
        let local_decl = self.body.locals().get(target_local)?;
        let enum_sort = Self::translate_ty(local_decl.ty)?;
        let enum_dt = enum_sort.datatype_sort()?;
        let (payload_offset, payload_sort) =
            if let Some(layout) = self.flatten.enum_bv_layouts.get(&target_local) {
                let first_payload =
                    layout.ctor_field_slot.iter().enumerate().find_map(|(ctor_idx, slots)| {
                        slots.iter().enumerate().find_map(|(field_idx, &slot)| {
                            (slot != usize::MAX).then_some((ctor_idx, field_idx, slot))
                        })
                    })?;
                let payload_sort = enum_dt
                    .constructors
                    .get(first_payload.0)?
                    .fields
                    .get(first_payload.1)?
                    .sort
                    .clone();
                (1 + first_payload.2, payload_sort)
            } else {
                let mut payload_field = None;
                for ctor in &enum_dt.constructors {
                    if let Some(field) = ctor.fields.first() {
                        payload_field = Some(field.sort.clone());
                        break;
                    }
                }
                let payload_sort = payload_field?;
                let n_fields = self.flattened_field_count(target_local);
                (if n_fields == 1 { 0 } else { 1 }, payload_sort)
            };

        if !is_leaf_sort(&payload_sort) {
            return self
                .reconstruct_nested_datatype_from_slots(
                    target_local,
                    payload_offset,
                    &payload_sort,
                    modified_locals,
                )
                .map(|(expr, _)| expr);
        }

        self.resolve_flattened_field_expr(target_local, payload_offset, vec_idx, modified_locals)
    }
}
