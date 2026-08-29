// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared helpers for Option/Result handling.
//!
//! Extracted from `option.rs`. These helpers are used by both `option.rs` and
//! `result.rs` as well as collection stubs for discriminant handling and
//! symbolic result generation.

use ay_bindings::SortInner;
use rustc_public::mir::{Operand, Place};
use std::sync::Arc;
use tracing::{debug, warn};

use super::{IntoOption, StatementCodegen};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Generate a symbolic (unconstrained) result for a destination.
    ///
    /// Used when we need to produce a result but don't have enough information
    /// to compute the exact value. The symbolic value allows verification to
    /// continue and may still prove properties that don't depend on the exact value.
    pub(super) fn codegen_symbolic_result(&mut self, destination: &Place) {
        let dest_ty = if let Some(ty) = destination.ty(self.body.locals()).into_option() {
            ty
        } else {
            warn!("codegen_symbolic_result: cannot determine destination type");
            return;
        };

        let sort = if let Some(s) = Self::infer_sort_from_ty(dest_ty) {
            s
        } else {
            warn!("codegen_symbolic_result: cannot infer sort for {:?}", dest_ty);
            return;
        };

        let base_name = self.ssa_base_name(destination);
        let dest_name = self.ssa_name_from_base(&base_name, true);
        let symbolic_val = self.ctx.declare_var(&dest_name, sort);
        self.env_update(base_name, symbolic_val);
    }

    /// Get the base name of an Option from a direct (owned) operand.
    ///
    /// For unwrap(self) which takes ownership, the operand IS the Option value.
    /// We directly look up the place name in the environment. (#274)
    /// Updated for #431: Use projection-aware base_name for Options in projected locations.
    pub(super) fn get_option_base_direct(&mut self, operand: &Operand) -> Option<Arc<str>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                // Build the direct base name using projection-aware ssa_base_name (#431).
                // This enables lookup of Options stored in projected locations (e.g., tuple fields).
                let base_name = self.ssa_base_name(place);

                // Check if this name (or a field of it) exists in the environment
                // For flattened Option, we'd have base_name.0 and base_name.1
                let discrim_name = crate::codegen_ay::names::discrim_name(&base_name);
                if self.env_lookup(&discrim_name).is_some() {
                    debug!("Option::unwrap: found flattened Option at {}", base_name);
                    return Some(base_name.into());
                }

                // For native SMT datatype, the Option itself is stored
                if self.env_lookup(&base_name).is_some() {
                    debug!("Option::unwrap: found native SMT Option at {}", base_name);
                    return Some(base_name.into());
                }

                debug!(
                    "Option::unwrap: direct lookup failed for '{}' - \
                     not found in environment",
                    base_name
                );
                None
            }
            _ => {
                // external enum: Operand
                debug!("Option::unwrap: expected Copy/Move operand, got {:?}", operand);
                None
            }
        }
    }

    /// Get the base name of an Option from a reference operand.
    ///
    /// Uses `ref_pointees` to find the actual pointee base name. (#266)
    /// Updated for #431: Use projection-aware ref_base for references in projected locations.
    pub(super) fn get_option_base_from_ref(&mut self, operand: &Operand) -> Option<Arc<str>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                // Build the reference base name using projection-aware ssa_base_name (#431).
                // This enables lookup of refs stored in projected locations (e.g., tuple fields).
                let ref_base = self.ssa_base_name(place);

                // Look up in ref_pointees - this was recorded when `_ref = &_pointee` was translated
                if let Some(pointee) = self.ref_pointees.get(ref_base.as_str()) {
                    Some(Arc::clone(pointee))
                } else {
                    warn!(
                        "Option method: ref_pointees lookup failed for '{}' - \
                         reference was not tracked during assignment translation (#266)",
                        ref_base
                    );
                    None
                }
            }
            _ => {
                // external enum: Operand
                warn!("Option method: expected Copy/Move operand, got {:?}", operand);
                None
            }
        }
    }

    /// Build the "this `Option` is `None`" predicate for an already-resolved
    /// Option base name.
    ///
    /// `codegen_option_is_none` works from a `&Option<T>` operand; this works
    /// from the base name that `get_option_base_direct` resolved for a
    /// by-value receiver (`unwrap(self)` / `expect(self, _)`), so the two
    /// representations stay in sync without duplicating the operand handling.
    ///
    /// Representation handling mirrors `codegen_option_is_none`:
    /// - flattened: `{base}.0` discriminant == 0
    /// - native datatype: `is-None` constructor test
    ///
    /// ENSURES: Returns `None` when the representation exposes no discriminant
    /// (a flattened Some payload stored bare under the base key). Callers must
    /// treat that as "cannot decide" and skip the check rather than assume Some.
    pub(super) fn option_none_predicate(&self, option_base: &str) -> Option<ay_bindings::Expr> {
        let discrim_name = crate::codegen_ay::names::discrim_name(option_base);
        if let Some(discrim_expr) = self.env_lookup(&discrim_name) {
            let zero = self.make_zero_for_discrim(discrim_expr)?;
            return Some(discrim_expr.clone().eq(zero));
        }

        let option_expr = self.env_lookup(option_base)?;
        let sort = option_expr.sort();
        let dt_name = sort.datatype_name()?;
        let none_ctor = crate::codegen_ay::names::option_none_constructor_name(dt_name);
        if !sort.datatype_has_constructor(&none_ctor) {
            debug!(
                "option_none_predicate: datatype '{}' missing constructor '{}' for {}",
                dt_name, none_ctor, option_base
            );
            return None;
        }
        Some(option_expr.clone().is_constructor(dt_name, none_ctor))
    }

    /// Helper to create zero constant matching discriminant expression sort.
    ///
    /// Returns None if the discriminant sort is unsupported.
    pub(super) fn make_zero_for_discrim(
        &self,
        discrim_expr: &ay_bindings::Expr,
    ) -> Option<ay_bindings::Expr> {
        let sort = discrim_expr.sort();
        match sort.inner() {
            SortInner::Bool => Some(ay_bindings::Expr::bool_const(false)),
            SortInner::BitVec(bv) => Some(ay_bindings::Expr::bitvec_const(0, bv.width)),
            SortInner::Int => Some(ay_bindings::Expr::int_const(0)),
            SortInner::Real
            | SortInner::Array(_)
            | SortInner::Datatype(_)
            | SortInner::String
            | SortInner::FloatingPoint(_, _)
            | SortInner::Uninterpreted(_)
            | SortInner::RegLan => {
                warn!(
                    sort = ?sort,
                    "Option discriminant has unsupported sort for zero comparison"
                );
                None
            }
            _ => {
                warn!(
                    sort = ?sort,
                    "Option discriminant has unsupported sort for zero comparison"
                );
                None
            }
        }
    }
}
