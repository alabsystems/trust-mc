// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC encoding of `StatementKind::SetDiscriminant`.
//!
//! Ported from the BMC backend (`statement/codegen_statement.rs:39-211`)
//! to close the silent-drop gap in the CHC statement loop.
//!
//! Part of #3743: CHC statement dispatch + SetDiscriminant parity.

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind, VariantIdx};
use rustc_public_bridge::IndexedVal;
use tracing::{debug, warn};
use trust_mc_codegen_shared::IntoOption;

// `super` = codegen_stmt module; `super::super` = chc module.
use super::super::ChcCtx;
use super::super::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use super::super::stmt_accumulator::StmtAccumulator;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Encode `StatementKind::SetDiscriminant { place, variant_index }` as a
    /// CHC constraint on the destination local's output variable.
    ///
    /// Returns `true` if the discriminant was successfully encoded.
    /// On failure, marks the local as modified with a tautological placeholder
    /// and calls `record_sound_fallback_reason()`.
    pub(super) fn encode_set_discriminant(
        &mut self,
        place: &Place,
        variant_index: &VariantIdx,
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        if let Some(encoded) =
            self.encode_flattened_enum_tag_discriminant(place, variant_index, bb_idx, acc)
        {
            return encoded;
        }

        let ty = match place.ty(self.body.locals()).into_option() {
            Some(ty) => ty,
            None => {
                warn!(bb_idx, "SetDiscriminant: failed to resolve place type");
                self.set_discriminant_fallback(place, bb_idx, acc);
                return false;
            }
        };

        if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..))) {
            return self.encode_coroutine_discriminant(place, ty, variant_index, bb_idx, acc);
        }

        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            warn!(bb_idx, "SetDiscriminant: non-ADT type {:?}", ty.kind());
            self.set_discriminant_fallback(place, bb_idx, acc);
            return false;
        };

        let variants = def.variants();
        let is_unit_enum = variants.iter().all(|v| v.fields().is_empty());

        if is_unit_enum {
            return self.encode_unit_enum_discriminant(
                place,
                variant_index,
                &def,
                &variants,
                bb_idx,
                acc,
            );
        }

        // Non-unit ADT: try to reconstruct variant from previously-written fields.
        self.encode_non_unit_adt_discriminant(
            place,
            variant_index,
            &def,
            &args,
            &variants,
            bb_idx,
            acc,
        )
    }

    /// Unit enum: assign the actual discriminant value to the destination local.
    fn encode_unit_enum_discriminant(
        &mut self,
        place: &Place,
        variant_index: &VariantIdx,
        def: &rustc_public::ty::AdtDef,
        variants: &[rustc_public::ty::VariantDef],
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let local_idx: usize = place.local;
        let internal_def = rustc_internal::internal(self.tcx, *def);
        let variant_idx_internal = rustc_abi::VariantIdx::from_usize(variant_index.to_index());
        let discr = internal_def.discriminant_for_variant(self.tcx, variant_idx_internal);

        let num_variants = variants.len();
        let bits = if num_variants <= 65536 { 32 } else { 64 };
        let discriminant_val = sign_extend_discr_val(discr.val, discr.ty, self.tcx, bits);
        let rhs_expr = Expr::bitvec_const(discriminant_val, bits);

        // Part of #3768: graceful fallback instead of panic
        let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
            self.set_discriminant_fallback(place, bb_idx, acc);
            return false;
        };
        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
        {
            let coerced = if let Some(w) = out_sort.bitvec_width() {
                coerce_bitvec_width_safe(rhs_expr, w, SignExtension::ZeroExtend)
            } else {
                rhs_expr
            };
            let out_var = Expr::var(&*out_name, out_sort);
            acc.replace_constraint(local_idx, out_var.eq(coerced.clone()));
            acc.modified.insert(local_idx);
            self.encode.local_expr_env.insert(local_idx, coerced);
            debug!(bb_idx, local_idx, "CHC: SetDiscriminant unit enum encoded");
            true
        } else {
            warn!(bb_idx, local_idx, "SetDiscriminant: no output state var for local");
            self.set_discriminant_fallback(place, bb_idx, acc);
            false
        }
    }

    fn resolve_coroutine_root_aux_state_expr(
        &self,
        local_idx: usize,
    ) -> Option<(usize, usize, Expr)> {
        let root_state_idx = *self.ref_resolution.coroutine_root_map.get(&local_idx)?;
        let track_key = usize::MAX - root_state_idx;
        let root_expr = if let Some(env_expr) = self.encode.local_expr_env.get(&track_key) {
            env_expr.clone()
        } else if self.encode.modified_state_indices.contains(&root_state_idx) {
            let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(root_state_idx)?;
            Expr::var(&**out_name, out_sort.clone())
        } else {
            let (in_name, in_sort) = self.state_var_mgr.state_vars.get(root_state_idx)?;
            Expr::var(&**in_name, in_sort.clone())
        };
        crate::codegen_ay::types::coroutine_discriminant_select(root_expr.clone())?;
        Some((root_state_idx, track_key, root_expr))
    }

    pub(in crate::codegen_ay::chc) fn encode_coroutine_discriminant(
        &mut self,
        place: &Place,
        ty: rustc_public::ty::Ty,
        variant_index: &VariantIdx,
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let source_local: usize = place.local;
        let mut aux_state = None;
        let local_idx = if place.projection.is_empty() {
            Some(source_local)
        } else if place.projection.len() == 1
            && matches!(place.projection[0], ProjectionElem::Deref)
        {
            if let Some(ref_target) = self.ref_resolution.ref_targets.get(&source_local) {
                if !ref_target.projections.is_empty() {
                    warn!(
                        bb_idx,
                        source_local,
                        ?ref_target.projections,
                        "SetDiscriminant: projected coroutine deref target unsupported"
                    );
                    self.set_discriminant_fallback(place, bb_idx, acc);
                    return false;
                }
                if let Some((pointee_vec_idx, track_key, pointee_expr)) =
                    self.resolve_arg_ref_pointee_expr(ref_target.local)
                {
                    aux_state = Some((pointee_vec_idx, track_key, pointee_expr));
                    None
                } else if let Some((root_state_idx, track_key, root_expr)) =
                    self.resolve_coroutine_root_aux_state_expr(ref_target.local)
                {
                    // Part of #3807: wrapper arg locals bridged via ref_target
                    // resolve through coroutine_root_map to the aux state path.
                    aux_state = Some((root_state_idx, track_key, root_expr));
                    None
                } else {
                    Some(ref_target.local)
                }
            } else if let Some((pointee_vec_idx, track_key, pointee_expr)) =
                self.resolve_arg_ref_pointee_expr(source_local)
            {
                aux_state = Some((pointee_vec_idx, track_key, pointee_expr));
                None
            } else if let Some((root_state_idx, track_key, root_expr)) =
                self.resolve_coroutine_root_aux_state_expr(source_local)
            {
                aux_state = Some((root_state_idx, track_key, root_expr));
                None
            } else {
                warn!(bb_idx, source_local, "SetDiscriminant: missing coroutine deref ref_target");
                self.set_discriminant_fallback(place, bb_idx, acc);
                return false;
            }
        } else {
            warn!(
                bb_idx,
                source_local,
                ?place.projection,
                "SetDiscriminant: unsupported coroutine place shape"
            );
            self.set_discriminant_fallback(place, bb_idx, acc);
            return false;
        };
        let (root_expr, local_idx) = if let Some(local_idx) = local_idx {
            let root_expr = self.resolve_coroutine_root_expr(local_idx, acc.modified);
            (root_expr, Some(local_idx))
        } else if let Some((_, _, root_expr)) = aux_state.as_ref() {
            (Some(root_expr.clone()), None)
        } else {
            (None, None)
        };
        let Some(root_expr) = root_expr else {
            warn!(bb_idx, source_local, "SetDiscriminant: missing coroutine root expr");
            self.set_discriminant_fallback(place, bb_idx, acc);
            return false;
        };

        let discr_width =
            crate::codegen_ay::types::coroutine_discriminant_select(root_expr.clone())
                .and_then(|expr| expr.sort().bitvec_width())
                .unwrap_or(32);
        let internal_ty = rustc_internal::internal(self.tcx, ty);
        let variant_idx_internal = rustc_internal::internal(self.tcx, *variant_index);
        let Some(discr) = internal_ty.discriminant_for_variant(self.tcx, variant_idx_internal)
        else {
            warn!(bb_idx, source_local, "SetDiscriminant: coroutine discriminant lookup failed");
            self.set_discriminant_fallback(place, bb_idx, acc);
            return false;
        };
        let discr_expr = Expr::bitvec_const(
            sign_extend_discr_val(discr.val, discr.ty, self.tcx, discr_width),
            discr_width,
        );
        let Some(updated) =
            crate::codegen_ay::types::coroutine_discriminant_update(&root_expr, discr_expr)
        else {
            warn!(bb_idx, source_local, "SetDiscriminant: coroutine root update failed");
            self.set_discriminant_fallback(place, bb_idx, acc);
            return false;
        };

        if let Some(local_idx) = local_idx {
            // Part of #3768: graceful fallback instead of panic
            let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
                self.set_discriminant_fallback(place, bb_idx, acc);
                return false;
            };
            let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
            else {
                warn!(
                    bb_idx,
                    local_idx, "SetDiscriminant: no output state var for coroutine local"
                );
                self.set_discriminant_fallback(place, bb_idx, acc);
                return false;
            };
            let out_var = Expr::var(&*out_name, out_sort);
            acc.replace_constraint(local_idx, out_var.eq(updated.clone()));
            acc.modified.insert(local_idx);
            self.encode.local_expr_env.insert(local_idx, updated);
            debug!(bb_idx, source_local, local_idx, "CHC: SetDiscriminant coroutine encoded");
        } else if let Some((state_var_idx, track_key, _)) = aux_state {
            let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(state_var_idx).cloned()
            else {
                warn!(
                    bb_idx,
                    source_local,
                    state_var_idx,
                    "SetDiscriminant: no output state var for coroutine aux state"
                );
                self.set_discriminant_fallback(place, bb_idx, acc);
                return false;
            };
            let out_var = Expr::var(&*out_name, out_sort);
            acc.replace_constraint(track_key, out_var.eq(updated.clone()));
            self.encode.local_expr_env.insert(track_key, updated);
            self.mark_state_var_modified(state_var_idx);
            debug!(
                bb_idx,
                source_local, state_var_idx, "CHC: SetDiscriminant coroutine encoded via aux state"
            );
        }
        true
    }

    /// Non-unit ADT: piecewise enum construction.
    ///
    /// For BV-flattened enums (in `enum_bv_layouts`), set the tag state variable
    /// to the correct constructor index while leaving payload slots unchanged.
    /// For other non-unit ADTs, use sound fallback (universally quantified output).
    fn encode_non_unit_adt_discriminant(
        &mut self,
        place: &Place,
        variant_index: &VariantIdx,
        _def: &rustc_public::ty::AdtDef,
        _args: &rustc_public::ty::GenericArgs,
        _variants: &[rustc_public::ty::VariantDef],
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        if let Some(encoded) =
            self.encode_flattened_enum_tag_discriminant(place, variant_index, bb_idx, acc)
        {
            return encoded;
        }
        // Non-BV-flattened non-unit ADT: sound fallback.
        // The Aggregate rvalue path handles most real-world cases.
        debug!(
            bb_idx,
            local_idx = place.local,
            "CHC: SetDiscriminant non-unit ADT — sound fallback"
        );
        self.set_discriminant_fallback(place, bb_idx, acc);
        false
    }

    fn encode_flattened_enum_tag_discriminant(
        &mut self,
        place: &Place,
        variant_index: &VariantIdx,
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> Option<bool> {
        if !place.projection.is_empty() {
            return None;
        }
        let local_idx: usize = place.local;

        let tag_expr = if let Some(layout) = self.flatten.enum_bv_layouts.get(&local_idx) {
            let ctor_idx = variant_index.to_index();
            Some(if layout.num_constructors == 2 {
                Expr::bool_const(ctor_idx == 1)
            } else {
                Expr::bitvec_const(ctor_idx as u64, layout.tag_bits)
            })
        } else if let Some((true_variant, false_variant)) =
            self.flatten.flattened_enum_discr.get(&local_idx).copied()
        {
            let discr_val = self
                .variant_discriminant_value_for_local(local_idx, variant_index)
                .unwrap_or_else(|| variant_index.to_index() as u64);
            if discr_val == true_variant {
                Some(Expr::bool_const(true))
            } else if discr_val == false_variant {
                Some(Expr::bool_const(false))
            } else {
                self.set_discriminant_fallback(place, bb_idx, acc);
                return Some(false);
            }
        } else if self.flatten.flattened_tuple_locals.contains(&local_idx) {
            let vec_idx = self.try_state_idx_for_local(local_idx)?;
            let (_, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx)?;
            if !out_sort.is_bool() {
                None
            } else {
                let (true_variant, false_variant) = self.infer_flattened_discr(local_idx);
                let discr_val = self
                    .variant_discriminant_value_for_local(local_idx, variant_index)
                    .unwrap_or_else(|| variant_index.to_index() as u64);
                if discr_val == true_variant {
                    Some(Expr::bool_const(true))
                } else if discr_val == false_variant {
                    Some(Expr::bool_const(false))
                } else {
                    self.set_discriminant_fallback(place, bb_idx, acc);
                    return Some(false);
                }
            }
        } else {
            None
        }?;

        let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
            self.set_discriminant_fallback(place, bb_idx, acc);
            return Some(false);
        };
        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
        else {
            self.set_discriminant_fallback(place, bb_idx, acc);
            return Some(false);
        };
        let Some(tag_expr) = Self::coerce_flatten_slot_value(&out_sort, tag_expr) else {
            self.set_discriminant_fallback(place, bb_idx, acc);
            return Some(false);
        };
        let out_var = Expr::var(&*out_name, out_sort);
        acc.replace_constraint(local_idx, out_var.eq(tag_expr.clone()));
        acc.modified.insert(local_idx);
        self.encode.flattened_field_env.insert((local_idx, 0), tag_expr);
        debug!(
            bb_idx,
            local_idx,
            ctor_idx = variant_index.to_index(),
            "CHC: SetDiscriminant flattened enum tag constrained"
        );
        Some(true)
    }

    fn variant_discriminant_value_for_local(
        &self,
        local_idx: usize,
        variant_index: &VariantIdx,
    ) -> Option<u64> {
        let local_ty = self.body.locals().get(local_idx)?.ty;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = local_ty.kind() else {
            return None;
        };
        let internal_def = rustc_internal::internal(self.tcx, def);
        let variant_idx_internal = rustc_abi::VariantIdx::from_usize(variant_index.to_index());
        let discr = internal_def.discriminant_for_variant(self.tcx, variant_idx_internal);
        Some(sign_extend_discr_val(discr.val, discr.ty, self.tcx, POINTER_WIDTH) as u64)
    }

    /// Sound fallback for failed SetDiscriminant: mark destination as modified
    /// with a tautological constraint (universally quantified output) and record
    /// a sound over-approximation fallback.
    ///
    /// Per the design: do NOT emit a self-loop (preserving old value would be
    /// under-approximate for a write). Instead, leave output unconstrained.
    fn set_discriminant_fallback(
        &mut self,
        place: &Place,
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) {
        let local_idx: usize = place.local;
        acc.modified.insert(local_idx);
        self.encode.local_expr_env.remove(&local_idx);
        self.encode.local_signedness.remove(&local_idx);
        acc.replace_constraint(local_idx, Expr::bool_const(true));
        self.record_sound_fallback_reason("set_discriminant_fallback");
        warn!(
            bb_idx,
            local_idx,
            "CHC: SetDiscriminant fallback — output universally quantified (sound over-approx)"
        );
    }
}
