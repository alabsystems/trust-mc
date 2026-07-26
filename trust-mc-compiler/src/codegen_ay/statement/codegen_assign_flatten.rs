// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Flattened tuple/option aggregate assignment (converted from include!() per #2595).
// Extracted from codegen_assign_helpers.rs for #2246 large-file decomposition.

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::{POINTER_WIDTH, ty_to_bv_width};
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::{Operand, Place, ProjectionElem};
use rustc_public::ty::{AdtDef, GenericArgKind, GenericArgs, RigidTy, TyKind, VariantIdx};
use rustc_public_bridge::IndexedVal;
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen flattened tuple aggregate assignment: emit field-wise assignments.
    ///
    /// Instead of building a datatype constructor like `(mk fld_0 fld_1 ...)`,
    /// emit separate constraints for each field: `lhs_field_0 = op_0`, `lhs_field_1 = op_1`, etc.
    ///
    /// This avoids SMT datatypes entirely, which is critical for soundness since
    /// AY's datatype theory is currently a stub (ay#517).
    ///
    /// Returns `true` if handled, `false` if fallback to datatype encoding is needed.
    pub(super) fn try_codegen_flattened_tuple_aggregate(
        &mut self,
        lhs: &Place,
        operands: &[Operand],
    ) -> bool {
        if !self.tuple_flattening_allowed(lhs) {
            debug!(
                "tuple flattening NOT allowed for local={}, operands={}",
                lhs.local,
                operands.len()
            );
            return false;
        }
        // Allow field projections (e.g., _struct.tuple_field = (a, b)) but not Deref.
        // Field projections are handled by ssa_base_name which flattens them into
        // names like fn::local_X_field_Y. Deref projections require ref_pointees
        // resolution which is more complex (#431).
        let has_deref = lhs.projection.iter().any(|p| matches!(p, ProjectionElem::Deref));
        if has_deref {
            return false;
        }

        // Empty tuple (unit type) - still handled by datatype encoding for now
        if operands.is_empty() {
            return false;
        }

        // Phase 1: Collect all field expressions BEFORE emitting any constraints.
        // This ensures we fail-fast without leaving partial state if any operand fails.
        let mut field_exprs = Vec::with_capacity(operands.len());
        for operand in operands {
            let Some(field_expr) = self.codegen_operand(operand) else {
                // Fallback to datatype encoding if operand codegen fails
                return false;
            };
            field_exprs.push(field_expr);
        }

        // Phase 2: Now emit all constraints (we know all operands succeeded)
        let lhs_base = self.ssa_base_name(lhs);
        debug!(
            "AY codegen: flattened tuple aggregate {} with {} fields",
            lhs_base,
            field_exprs.len()
        );

        for (field_idx, field_expr) in field_exprs.into_iter().enumerate() {
            let field_sort = field_expr.sort().clone();
            let lhs_field_base = crate::codegen_ay::names::indexed_field_name(&lhs_base, field_idx);
            let lhs_field_name = self.ssa_name_from_base(&lhs_field_base, true);
            let lhs_field = self.ctx.declare_var(&lhs_field_name, field_sort);

            // Assert SSA definition with ite semantics (#2081)
            self.assert_ssa_def(lhs_field.clone(), field_expr, &lhs_field_base);

            self.env_update(lhs_field_base.clone(), lhs_field);

            // Track ref_pointees for tuple fields that contain references (#407).
            // When we create a tuple containing a reference, propagate the pointee so that
            // copies from tuple fields (e.g., _X = Copy(_tuple.0)) can resolve Deref.
            if let Some(operand) = operands.get(field_idx)
                && let Operand::Copy(src) | Operand::Move(src) = operand
            {
                let src_base = self.ssa_base_name(src);
                // Direct reference propagation
                if let Some(pointee) = self.ref_pointees.get(&*src_base).cloned() {
                    debug!(
                        "tuple aggregate: propagating ref {} (field {}) -> {} (pointee={})",
                        src_base, field_idx, lhs_field_base, pointee
                    );
                    self.ref_pointees.insert(std::sync::Arc::from(lhs_field_base.clone()), pointee);
                }
                // Nested tuple/struct/enum propagation (#441, #3133):
                // Propagate ref_pointees and env values for all piecewise key patterns:
                //   _field_  — flattened tuple/struct fields
                //   _variant_ — flattened enum variant fields (e.g., Option<&T>)
                //   .0       — discriminant entries
                // Use BTreeMap range query for O(log n + k) prefix scanning (#1337)
                let prefixes = ["_field_", "_variant_"];
                for pfx in &prefixes {
                    let prefix = {
                        let mut s = String::with_capacity(src_base.len() + pfx.len());
                        s.push_str(&src_base);
                        s.push_str(pfx);
                        s
                    };
                    // Part of #2267: create Arc once, clone for second range query.
                    let arc_prefix: std::sync::Arc<str> = std::sync::Arc::from(prefix.as_str());
                    let arc_prefix_env = std::sync::Arc::clone(&arc_prefix);
                    let nested_refs: Vec<_> = self
                        .ref_pointees
                        .range(arc_prefix..)
                        .take_while(|(k, _)| k.starts_with(prefix.as_str()))
                        .map(|(k, v)| (std::sync::Arc::clone(k), std::sync::Arc::clone(v)))
                        .collect();
                    for (nested_key, nested_pointee) in nested_refs {
                        let suffix = &nested_key[src_base.len()..];
                        let lhs_nested_base = [lhs_field_base.as_str(), suffix].concat();
                        debug!(
                            "tuple aggregate: propagating nested ref {} -> {} (pointee={})",
                            nested_key, lhs_nested_base, nested_pointee
                        );
                        self.ref_pointees
                            .insert(std::sync::Arc::from(lhs_nested_base), nested_pointee);
                    }
                    // Also propagate nested env values (#441, #3133).
                    let nested_env_entries: Vec<_> = self
                        .current_env
                        .range(arc_prefix_env..)
                        .take_while(|(k, _)| k.starts_with(&prefix))
                        .map(|(k, v)| (std::sync::Arc::clone(k), v.clone()))
                        .collect();
                    for (nested_key, nested_expr) in nested_env_entries {
                        let suffix = &nested_key[src_base.len()..];
                        let lhs_nested_base = [lhs_field_base.as_str(), suffix].concat();
                        let lhs_nested_name = self.ssa_name_from_base(&lhs_nested_base, true);
                        let lhs_nested_var =
                            self.ctx.declare_var(&lhs_nested_name, nested_expr.sort().clone());
                        self.assert_ssa_def(lhs_nested_var.clone(), nested_expr, &lhs_nested_base);
                        debug!(
                            "tuple aggregate: propagating nested env {} -> {}",
                            nested_key, lhs_nested_base
                        );
                        self.env_update(lhs_nested_base, lhs_nested_var);
                    }
                }
                // Propagate discriminant entry ({src}.0 -> {lhs_field}.0) (#3133).
                let src_discrim_key = crate::codegen_ay::names::discrim_name(&src_base);
                let src_discrim_arc: std::sync::Arc<str> =
                    std::sync::Arc::from(src_discrim_key.as_str());
                if let Some(pointee) = self.ref_pointees.get(&src_discrim_arc).cloned() {
                    let lhs_discrim = crate::codegen_ay::names::discrim_name(&lhs_field_base);
                    debug!(
                        "tuple aggregate: propagating discrim ref {} -> {} (pointee={})",
                        src_discrim_key, lhs_discrim, pointee
                    );
                    self.ref_pointees.insert(std::sync::Arc::from(lhs_discrim), pointee);
                }
                if let Some(discrim_expr) = self.current_env.get(&src_discrim_arc).cloned() {
                    let lhs_discrim = crate::codegen_ay::names::discrim_name(&lhs_field_base);
                    let lhs_discrim_name = self.ssa_name_from_base(&lhs_discrim, true);
                    let lhs_discrim_var =
                        self.ctx.declare_var(&lhs_discrim_name, discrim_expr.sort().clone());
                    self.assert_ssa_def(lhs_discrim_var.clone(), discrim_expr, &lhs_discrim);
                    debug!(
                        "tuple aggregate: propagating discrim env {} -> {}",
                        src_discrim_key, lhs_discrim
                    );
                    self.env_update(lhs_discrim, lhs_discrim_var);
                }
            }
        }

        true
    }

    /// Flatten Option-like enum aggregates to avoid DT+BV theory mixing (ay#1766).
    ///
    /// When `checked_align_of_raw` / `checked_size_of_raw` are inlined, they produce
    /// `Aggregate(Adt(Option, Some), [const usize])`. The default codegen creates an SMT
    /// datatype `(Some const)`, but extracting the payload via `field_select` and then
    /// using it in bitvector arithmetic causes DT+BV mixing — the ay solver returns
    /// UNKNOWN or incomplete results.
    ///
    /// This method flattens Option-like enums with bitvector payloads into separate
    /// SSA fields, matching the piecewise construction pattern that `SetDiscriminant`
    /// and `codegen_place` already support:
    ///   - `{base}_variant_{V}_field_0` = payload value (bitvec)
    ///   - `{base}` = payload value as bitvec (so Discriminant handler returns correct variant)
    ///
    /// Part of #2076: BMC codegen gaps for inlined kani::mem predicates.
    pub(super) fn try_codegen_flattened_option_aggregate(
        &mut self,
        lhs: &Place,
        def: &AdtDef,
        variant_idx: &VariantIdx,
        args: &GenericArgs,
        operands: &[Operand],
    ) -> bool {
        // Only apply to Option-like enums: exactly 2 variants, one with 0 fields, one with 1 field.
        let variants = def.variants();
        if variants.len() != 2 {
            return false;
        }
        let v0_fields = variants[0].fields().len();
        let v1_fields = variants[1].fields().len();
        if !((v0_fields == 0 && v1_fields == 1) || (v0_fields == 1 && v1_fields == 0)) {
            return false;
        }

        let variant_idx_val = variant_idx.to_index();
        let variant = &variants[variant_idx_val];
        let variant_has_field = !variant.fields().is_empty();

        if variant_has_field {
            // Some-like variant: flatten to bitvec fields
            if operands.len() != 1 {
                return false;
            }
            // #3133: For Option<&T>, dereference through ref_pointees to get
            // the value (e.g., BV32(5)) instead of the address (BV64). This
            // aligns with CHC value semantics where references are transparent.
            let Some(payload) = self.get_value_through_ref(&operands[0]) else {
                return false;
            };
            // A `bool` payload has Bool sort, not BitVec. Coerce it to BitVec(1)
            // so the Some arm FLATTENS (bitvec) instead of falling through to the
            // native Option datatype below. This mirrors the None arm, whose base
            // is `bitvec_const(0, value_payload_width)` = BitVec(1) for a bool
            // payload (`ty_to_bv_width(bool) == 1`). Keeping BOTH arms flattened in
            // bitvec land is required because ay has no datatype theory (#517): if
            // the Some arm builds an `Option<bool>` datatype while the None arm
            // flattens, they collide at the match/`.copied()` phi merge, #3260
            // harmonizes "preferring BitVec" and the Some payload is dropped,
            // which havocs a downstream `Option::unwrap_or` (the ay-pb `eval_lit`
            // completeness gap G1). Coercing here keeps the payload live end-to-end.
            let payload = if payload.sort().is_bool() {
                Expr::ite(payload, Expr::bitvec_const(1u64, 1), Expr::bitvec_const(0u64, 1))
            } else {
                payload
            };
            // Only flatten if payload is bitvec (avoid DT+BV mixing)
            if !payload.sort().is_bitvec() {
                // Part of #4112 follow-up: ZST payloads (e.g. `Some(())` in
                // `Option<()>` from `Result::ok` desugaring) carry no data, but
                // the Some arm must still flatten so both arms agree on the
                // base sort and both record the `.0` discriminant. Otherwise
                // the Some arm builds a datatype while the None arm flattens,
                // and the phi-merged discriminant is only constrained on the
                // None edge — `discriminant(x)` degrades to symbolic.
                let payload_is_zst = args.0.first().is_some_and(
                    |arg| matches!(arg, GenericArgKind::Type(ty) if Self::is_zst_type(*ty)),
                );
                if payload_is_zst {
                    self.codegen_flattened_option_zst_some(lhs, args);
                    return true;
                }
                return false;
            }

            let lhs_base = self.ssa_base_name(lhs);
            // Hoist sort once — avoids redundant payload.sort().clone() per binding.
            let payload_sort = payload.sort().clone();

            // Store payload under the piecewise key: {base}_variant_{V}_field_0
            let field_key =
                crate::codegen_ay::names::base_variant_field_name(&lhs_base, variant_idx_val, 0);
            // Save Arc before env_update consumes field_key (#3133).
            let field_key_arc: std::sync::Arc<str> = std::sync::Arc::from(field_key.as_str());
            let field_name = self.ssa_name_from_base(&field_key, true);
            let field_var = self.ctx.declare_var(&field_name, payload_sort.clone());
            self.assert_ssa_def(field_var.clone(), payload.clone(), &field_key);
            self.env_update(field_key, field_var);

            // Store payload under the base key as bitvec.
            let base_name = self.ssa_name_from_base(&lhs_base, true);
            let base_var = self.ctx.declare_var(&base_name, payload_sort);
            // Last use of payload — move instead of clone.
            self.assert_ssa_def(base_var.clone(), payload, &lhs_base);
            self.env_update(lhs_base.clone(), base_var);

            // Part of #3094: Store discriminant 1 (Some) under {base}.0 so that
            // SSA merging with the None branch (which sets .0=0) produces correct
            // ITE guards. Without this, .0 is uninitialized on the Some branch,
            // allowing the solver to set it to 0 (None) — a false failure.
            let discrim_key = crate::codegen_ay::names::discrim_name(&lhs_base);
            let one = Expr::bitvec_const(1u64, 32);
            let discrim_name = self.ssa_name_from_base(&discrim_key, true);
            let discrim_var = self.ctx.declare_var(&discrim_name, Sort::bitvec(32));
            self.assert_ssa_def(discrim_var.clone(), one, &discrim_key);
            self.env_update(discrim_key, discrim_var);

            // #3133: Propagate ref_pointees from the operand to the field key
            // and base key. The early return from this flattened path skips
            // track_rvalue_aggregate_refs in codegen_assign, so references
            // inside flattened Option aggregates (e.g., Some(&42)) would lose
            // their pointee tracking without this.
            if let Operand::Copy(src) | Operand::Move(src) = &operands[0] {
                let src_base: std::sync::Arc<str> = self.ssa_base_name(src).into();
                if let Some(pointee) = self.ref_pointees.get(&*src_base).cloned() {
                    let base_arc: std::sync::Arc<str> = std::sync::Arc::from(lhs_base.as_str());
                    debug!(
                        "flattened Option: propagating ref {} -> field {}, base {} (pointee={})",
                        src_base, field_key_arc, lhs_base, pointee
                    );
                    self.ref_pointees.insert(field_key_arc, pointee.clone());
                    self.ref_pointees.insert(base_arc, pointee);
                }
            }

            debug!("AY codegen: flattened Option Some aggregate (Part of #2076)");
            true
        } else {
            // None-like variant: store discriminant as 0
            if !operands.is_empty() {
                return false;
            }
            self.codegen_flattened_option_none(lhs, args);
            true
        }
    }

    /// Flatten a None-like (empty) variant: `.0` discriminant = 0, base = zero
    /// bitvec of the value-payload width. Extracted from
    /// `try_codegen_flattened_option_aggregate` so call stubs (e.g.
    /// `FromResidual::from_residual` for `Option<T>` destinations) can produce
    /// the same encoding. Part of #2076 / #4112 follow-up.
    pub(in crate::codegen_ay::statement) fn codegen_flattened_option_none(
        &mut self,
        lhs: &Place,
        args: &GenericArgs,
    ) {
        let lhs_base = self.ssa_base_name(lhs);

        // Store a zero bitvec under the base key.
        // The Discriminant handler for Option bitvec returns 1 (Some), but
        // for None we need 0. We handle this by storing discriminant directly
        // under the {base}.0 key that the discriminant handler checks first.
        let discrim_key = crate::codegen_ay::names::discrim_name(&lhs_base);
        let zero = Expr::bitvec_const(0u64, 32);
        let discrim_name = self.ssa_name_from_base(&discrim_key, true);
        let discrim_var = self.ctx.declare_var(&discrim_name, Sort::bitvec(32));
        self.assert_ssa_def(discrim_var.clone(), zero, &discrim_key);
        self.env_update(discrim_key, discrim_var);

        // #3133: Store zero under base key with sort matching the Some path's
        // payload sort. When the Some path uses get_value_through_ref to
        // dereference Option<&T> → T (e.g., BV32 for &i32), the None path
        // must use the same width so SSA phi merging produces valid ITEs.
        let payload_width = Self::value_payload_width(args);
        let base_name = self.ssa_name_from_base(&lhs_base, true);
        let base_var = self.ctx.declare_var(&base_name, Sort::bitvec(payload_width));
        let zero_val = Expr::bitvec_const(0u64, payload_width);
        self.assert_ssa_def(base_var.clone(), zero_val, &lhs_base);
        self.env_update(lhs_base, base_var);

        debug!("AY codegen: flattened Option None aggregate (Part of #2076)");
    }

    /// Flatten a Some-like variant carrying a ZST payload (Part of #4112
    /// follow-up). The payload has no runtime data, so the base is the same
    /// canonical zero bitvec the None arm uses — only the `.0` discriminant
    /// (= 1) distinguishes the variants. Keeping both arms flattened ensures
    /// the phi-merged discriminant is constrained on every edge.
    fn codegen_flattened_option_zst_some(&mut self, lhs: &Place, args: &GenericArgs) {
        let lhs_base = self.ssa_base_name(lhs);

        let discrim_key = crate::codegen_ay::names::discrim_name(&lhs_base);
        let one = Expr::bitvec_const(1u64, 32);
        let discrim_name = self.ssa_name_from_base(&discrim_key, true);
        let discrim_var = self.ctx.declare_var(&discrim_name, Sort::bitvec(32));
        self.assert_ssa_def(discrim_var.clone(), one, &discrim_key);
        self.env_update(discrim_key, discrim_var);

        let payload_width = Self::value_payload_width(args);
        let base_name = self.ssa_name_from_base(&lhs_base, true);
        let base_var = self.ctx.declare_var(&base_name, Sort::bitvec(payload_width));
        let zero_val = Expr::bitvec_const(0u64, payload_width);
        self.assert_ssa_def(base_var.clone(), zero_val, &lhs_base);
        self.env_update(lhs_base, base_var);

        debug!("AY codegen: flattened Option Some(ZST) aggregate (Part of #4112 follow-up)");
    }

    /// `FromResidual::from_residual` for an `Option<T>` destination returns
    /// exactly `None` (the only Option residual is `Option::<Infallible>::None`).
    /// Encode it as the flattened None so the destination's discriminant and
    /// payload stay constrained. Returns false for non-Option destinations
    /// (e.g. allocation `Result`s), which keep their legacy handling.
    /// Part of #4112 follow-up.
    pub(in crate::codegen_ay::statement) fn try_codegen_from_residual_option_none(
        &mut self,
        destination: &Place,
    ) -> bool {
        let Some(dest_ty) = destination.ty(self.body.locals()).into_option() else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = dest_ty.kind() else {
            return false;
        };
        if def.trimmed_name() != "Option" {
            return false;
        }
        let variants = def.variants();
        // std Option shape: None (variant 0, fieldless), Some (variant 1, one field).
        if variants.len() != 2
            || !variants[0].fields().is_empty()
            || variants[1].fields().len() != 1
        {
            return false;
        }
        self.codegen_flattened_option_none(destination, &args);
        true
    }

    /// Compute the bitvec width for the value-semantic payload of an Option<T>.
    ///
    /// For value-semantic encoding (#3133), references are transparent:
    /// `Option<&i32>` encodes as `Option<i32>` with width 32, not 64.
    /// This ensures the None path uses the same sort as the Some path
    /// (which dereferences via `get_value_through_ref`).
    ///
    /// Falls back to `POINTER_WIDTH` if the generic arg cannot be resolved.
    fn value_payload_width(args: &GenericArgs) -> u32 {
        let Some(first_arg) = args.0.first() else {
            return POINTER_WIDTH;
        };
        let GenericArgKind::Type(ty) = first_arg else {
            return POINTER_WIDTH;
        };
        // For references/raw pointers, use the pointee type's width (value semantics).
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => {
                ty_to_bv_width(pointee).unwrap_or(POINTER_WIDTH)
            }
            _ => ty_to_bv_width(*ty).unwrap_or(POINTER_WIDTH),
        }
    }
}
