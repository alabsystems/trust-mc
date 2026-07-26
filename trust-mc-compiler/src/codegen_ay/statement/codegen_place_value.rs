// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Place value and reference assignment (converted from include!() per #2595).

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::ptr_sort;
use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{Operand, Place, ProjectionElem};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use std::sync::Arc;
use tracing::{debug, warn};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    // Call dispatch functions moved to dispatch.rs - Part of #1354.
    // Moved: try_codegen_std_intrinsic, resolve_callee_path, try_codegen_stdlib_stub_call, codegen_closure_call

    // Slice codegen stubs moved to slice.rs - Part of #1354.

    /// Assign a value to a place, creating a new SSA variable.
    /// Made pub(super) for heap allocation handlers (#1100).
    pub(super) fn assign_value_to_place(&mut self, destination: &Place, value: Expr) {
        let value_for_tracking = value.clone();
        self.bind_ssa_result(destination, value);

        let dest_base: Arc<str> = self.ssa_base_name(destination).into();
        self.propagate_nested_ref_pointees_from_value(&value_for_tracking, &dest_base);
    }

    pub(super) fn assign_reference_to_place(&mut self, destination: &Place, pointee_expr: Expr) {
        let dest_ty = destination.ty(self.body.locals()).into_option();
        let is_ref = dest_ty.is_some_and(|ty| {
            matches!(
                ty.kind(),
                TyKind::RigidTy(RigidTy::Ref(..)) | TyKind::RigidTy(RigidTy::RawPtr(..))
            )
        });

        if !is_ref {
            self.assign_value_to_place(destination, pointee_expr);
            return;
        }

        let dest_base: Arc<str> = self.ssa_base_name(destination).into();
        let dest_name = self.ssa_name_from_base(dest_base.as_ref(), true);
        let dest_sort = self.infer_sort_from_place(destination).unwrap_or_else(ptr_sort);
        let dest_expr = self.ctx.declare_var(&dest_name, dest_sort);
        self.env_update(Arc::clone(&dest_base), dest_expr);

        let pointee_base: Arc<str> = {
            use std::fmt::Write;
            let fn_name = self.ctx.current_fn_name();
            let mut s = String::with_capacity(fn_name.len() + 25);
            s.push_str(fn_name);
            s.push_str("::slice_index_pointee_");
            let _ = write!(s, "{}", self.synthetic_pointee_counter);
            Arc::from(s)
        };
        self.synthetic_pointee_counter += 1;

        let pointee_expr_for_tracking = pointee_expr.clone();
        let pointee_name = self.ssa_name_from_base(pointee_base.as_ref(), true);
        let pointee_var = self.ctx.declare_var(&pointee_name, pointee_expr.sort().clone());
        self.assert_ssa_def(pointee_var.clone(), pointee_expr, pointee_base.as_ref());
        self.env_update(Arc::clone(&pointee_base), pointee_var);

        self.propagate_nested_ref_pointees_from_value(&pointee_expr_for_tracking, &pointee_base);
        self.ref_pointees.insert(dest_base, pointee_base);
    }

    fn propagate_nested_ref_pointees_from_value(
        &mut self,
        pointee_expr: &Expr,
        target_pointee_base: &Arc<str>,
    ) {
        let Some(source_base) = self
            .current_env
            .iter()
            .find_map(|(base, expr)| (expr == pointee_expr).then(|| Arc::clone(base)))
        else {
            return;
        };

        let mut prefix = String::with_capacity(source_base.len() + 1);
        prefix.push_str(source_base.as_ref());
        prefix.push('_');
        let range_start: Arc<str> = Arc::from(prefix.as_str());
        let nested_refs: Vec<_> = self
            .ref_pointees
            .range(range_start..)
            .take_while(|(key, _)| key.starts_with(prefix.as_str()))
            .map(|(key, pointee)| (Arc::clone(key), Arc::clone(pointee)))
            .collect();

        for (nested_key, nested_pointee) in nested_refs {
            let suffix = &nested_key[source_base.len()..];
            let mut propagated_key =
                String::with_capacity(target_pointee_base.len() + suffix.len());
            propagated_key.push_str(target_pointee_base);
            propagated_key.push_str(suffix);
            self.ref_pointees.insert(Arc::from(propagated_key), nested_pointee);
        }
    }

    // Bit manipulation intrinsics (rotate, ctlz, cttz, ctpop, bswap, bitreverse)
    // are implemented in intrinsics.rs

    // Arithmetic operations (wrapping, unchecked, checked, saturating, overflowing)
    // are implemented in arithmetic.rs

    // Option handling (is_none, is_some, unwrap, map) is implemented in option.rs

    /// Get the value expression from a reference operand by dereferencing through ref_pointees.
    ///
    /// For Ord::cmp and similar methods that take &self and &other, the MIR operands are references.
    /// This method looks up the pointee via ref_pointees and returns its value from the environment.
    /// Falls back to constructing a deref place if the reference can't be resolved.
    ///
    /// Part of #409: Fix raw_eq to compare array content, not pointer addresses.
    /// Updated for #431: Use projection-aware ref_base for references in projected locations.
    pub(super) fn get_value_through_ref(&mut self, operand: &Operand) -> Option<Expr> {
        debug!("get_value_through_ref: called with operand={:?}", operand);
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                // Build the reference base name using projection-aware ssa_base_name (#431).
                // This enables lookup of refs stored in projected locations (e.g., tuple fields).
                let ref_base = self.ssa_base_name(place);
                debug!("get_value_through_ref: ref_base={}", ref_base);

                // Look up in ref_pointees to find the actual pointee
                if let Some(pointee_base) = self.ref_pointees.get(ref_base.as_str()).cloned() {
                    debug!("get_value_through_ref: found pointee_base={}", pointee_base);
                    // Get the pointee's value from the environment
                    if let Some(pointee_expr) = self.env_lookup(&pointee_base).cloned() {
                        debug!("get_value_through_ref: found expr sort={:?}", pointee_expr.sort());
                        // #2076 follow-up: When the pointee is a flattened Option-like
                        // enum (stored as a bare payload bitvec with a separate `{base}.0`
                        // discriminant), reading just the bitvec loses the variant. A
                        // None aggregate then reads back as a payload bitvec which, in
                        // comparison contexts, gets wrapped unconditionally in `Some(..)`
                        // — encoding `None == None` as always-false. Reconstruct the true
                        // Option datatype value from the discriminant before returning.
                        if let Some(reconstructed) = self.reconstruct_flattened_option_through_ref(
                            place,
                            &pointee_base,
                            &pointee_expr,
                        ) {
                            return Some(reconstructed);
                        }
                        return Some(pointee_expr);
                    }
                    debug!("get_value_through_ref: pointee not in env");
                } else {
                    debug!("get_value_through_ref: ref_base not in ref_pointees");
                    if self.ensure_ref_pointee_for_place(place).is_some()
                        && let Some(pointee_base) =
                            self.ref_pointees.get(ref_base.as_str()).cloned()
                        && let Some(pointee_expr) = self.env_lookup(&pointee_base).cloned()
                    {
                        debug!(
                            "get_value_through_ref: derived pointee sort={:?}",
                            pointee_expr.sort()
                        );
                        if let Some(reconstructed) = self.reconstruct_flattened_option_through_ref(
                            place,
                            &pointee_base,
                            &pointee_expr,
                        ) {
                            return Some(reconstructed);
                        }
                        return Some(pointee_expr);
                    }
                }

                // Fallback: if this is a reference type, construct a deref place and codegen it (#409)
                // This handles cases where ref_pointees doesn't have the mapping (e.g., raw_eq on enum fields)
                if let Some(ty) = place.ty(self.body.locals()).into_option() {
                    debug!(
                        "get_value_through_ref: checking type for {:?}, ty={:?}",
                        place,
                        ty.kind()
                    );
                    if matches!(
                        ty.kind(),
                        TyKind::RigidTy(RigidTy::Ref(..)) | TyKind::RigidTy(RigidTy::RawPtr(..))
                    ) {
                        // Construct a place with Deref projection: *place
                        let mut deref_projections = vec![ProjectionElem::Deref];
                        deref_projections.extend(place.projection.iter().cloned());
                        let deref_place =
                            Place { local: place.local, projection: deref_projections };
                        debug!("get_value_through_ref: fallback to deref place for {:?}", place);
                        if let Some(expr) = self.codegen_place(&deref_place) {
                            debug!(
                                "get_value_through_ref: deref succeeded, sort={:?}",
                                expr.sort()
                            );
                            return Some(expr);
                        }
                        debug!("get_value_through_ref: deref failed for {:?}", deref_place);
                    }
                }

                // Final fallback: codegen_operand (returns pointer value for references)
                self.codegen_operand(operand)
            }
            Operand::Constant(_) => {
                // For constant operands, codegen directly
                self.codegen_operand(operand)
            }
        }
    }

    /// Reconstruct the true Option datatype value for a flattened Option-like
    /// enum read through a reference.
    ///
    /// `try_codegen_flattened_option_aggregate` (#2076) stores Option-like enums
    /// piecewise — a bare payload bitvec under `{base}` and the discriminant under
    /// `{base}.0` — to avoid mixing the datatype and bitvector theories in
    /// arithmetic contexts. Reading the value back through `get_value_through_ref`
    /// only recovers the payload bitvec, discarding the variant. In comparison
    /// contexts that bitvec is then wrapped unconditionally in `Some(..)`, so a
    /// `None` value is mis-encoded as `Some(payload)` and `None == None` becomes
    /// always-false.
    ///
    /// When (a) the dereferenced place type is an Option-like enum, (b) the
    /// resolved pointee value is a bare bitvec, and (c) a `{base}.0` discriminant
    /// entry exists, rebuild the proper Option datatype value:
    /// `ite(discrim != 0, Some(payload), None)`. This restores variant fidelity so
    /// the discriminant is respected by downstream equality/ordering codegen.
    ///
    /// Returns `None` (leaving the caller to use the raw value) when the pattern
    /// does not apply, so the intentional flattening for non-Option payloads is
    /// left untouched.
    fn reconstruct_flattened_option_through_ref(
        &mut self,
        ref_place: &Place,
        pointee_base: &str,
        pointee_expr: &Expr,
    ) -> Option<Expr> {
        // Only the flattened encoding produces a bare bitvec payload; a value that
        // is already a datatype carries its own variant and needs no fixup.
        if !pointee_expr.sort().is_bitvec() {
            return None;
        }

        // Determine the dereferenced pointee type: the reference operand has type
        // `&Option<T>` / `*Option<T>`, so peel one Ref/RawPtr layer.
        let ref_ty = ref_place.ty(self.body.locals()).into_option()?;
        let pointee_ty = match ref_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => inner,
            _ => return None,
        };

        // Require an Option-like enum: exactly 2 variants, one empty + one with a
        // single field (matching try_codegen_flattened_option_aggregate's guard).
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = pointee_ty.kind() else {
            return None;
        };
        let variants = def.variants();
        if variants.len() != 2 {
            return None;
        }
        let v0_fields = variants[0].fields().len();
        let v1_fields = variants[1].fields().len();
        if !((v0_fields == 0 && v1_fields == 1) || (v0_fields == 1 && v1_fields == 0)) {
            return None;
        }
        // Restrict to genuine Option to avoid disturbing other 2-variant enums.
        if !def.trimmed_name().contains("Option") {
            return None;
        }

        // The flattened encoding records the variant under `{base}.0`. Without it
        // we cannot tell None from Some, so leave the value untouched.
        let discrim_key = crate::codegen_ay::names::discrim_name(pointee_base);
        let discrim = self.env_lookup(&discrim_key)?.clone();
        if !discrim.sort().is_bitvec() {
            return None;
        }

        // Build the concrete Option datatype from the MIR type (e.g. `Option_i32`)
        // so the reconstructed value's sort matches the one used elsewhere for the
        // same type — `make_option_sort` would derive a width-based `Option_bv32`
        // name and reintroduce a sort mismatch against the const-encoded operand.
        let option_sort = Self::infer_adt_sort(def, args)?;
        let dt_name = option_sort.datatype_name()?;

        // The Some payload sort must match the flattened bitvec; otherwise the
        // datatype constructor would be ill-typed.
        let some_payload_sort = option_sort
            .datatype_sort()
            .and_then(|dt| dt.constructors.iter().find(|c| c.fields.len() == 1))
            .and_then(|c| c.fields.first())
            .map(|f| f.sort.clone())?;
        if some_payload_sort != *pointee_expr.sort() {
            return None;
        }

        let some_ctor = crate::codegen_ay::names::option_some_constructor_name(dt_name);
        let none_ctor = crate::codegen_ay::names::option_none_constructor_name(dt_name);
        let some_val = Expr::datatype_constructor(
            dt_name,
            &some_ctor,
            vec![pointee_expr.clone()],
            option_sort.clone(),
        );
        let none_val = Expr::datatype_constructor(dt_name, &none_ctor, vec![], option_sort.clone());

        // Reconstruct ite(discrim != 0, Some(payload), None) so the discriminant
        // drives the variant rather than defaulting to the payload-bearing Some.
        let zero = Expr::bitvec_const(0u128, discrim.sort().bitvec_width().unwrap_or(32));
        let is_some = discrim.ne(zero);
        debug!(
            "get_value_through_ref: reconstructed flattened Option {} from discriminant {} (Part of #2076)",
            pointee_base, discrim_key
        );
        Some(Expr::ite(is_some, some_val, none_val))
    }

    // Kani intrinsic functions (any_raw, assume, assert, create_constrained_symbolic)
    // are implemented in kani.rs

    /// Get value for Option payload, dereferencing if the operand is a reference type.
    ///
    /// Part of #824: Apply value semantics for Option<&T> construction.
    ///
    /// When constructing `Some(&value)`, the MIR gives us a reference operand. Without
    /// this function, we'd get `Option<bv64>` (pointer sort). But HashMap::get returns
    /// `Option<T>` with value sort (e.g., `Option<bv32>` for u32 values).
    ///
    /// This function:
    /// 1. Checks if the operand is a reference type
    /// 2. If so, dereferences to get the pointee value via `get_value_through_ref`
    /// 3. Falls back to `codegen_operand` if dereference fails (logs warning)
    ///
    /// # Fallback Behavior
    ///
    /// If dereference fails (e.g., the reference isn't tracked in ref_pointees),
    /// this function falls back to `codegen_operand` which returns a pointer bitvec.
    /// This may cause sort mismatch downstream - a warning is logged when this occurs.
    ///
    /// This aligns with CHC's functional model where references have value semantics.
    pub(super) fn get_option_payload_value(&mut self, operand: &Operand) -> Option<Expr> {
        use rustc_public::ty::{RigidTy, TyKind};

        // Check if this operand has a reference type
        let is_ref_type = match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if let Some(ty) = place.ty(self.body.locals()).into_option() {
                    matches!(
                        ty.kind(),
                        TyKind::RigidTy(RigidTy::Ref(..)) | TyKind::RigidTy(RigidTy::RawPtr(..))
                    )
                } else {
                    false
                }
            }
            Operand::Constant(_) => false,
        };

        if is_ref_type {
            // Try to dereference and get the actual value
            debug!("get_option_payload_value: operand is reference, applying value semantics");
            if let Some(value) = self.get_value_through_ref(operand) {
                debug!("get_option_payload_value: dereferenced to sort {:?}", value.sort());
                return Some(value);
            }
            // Fallback: if dereference failed, use codegen_operand (will get pointer bitvec)
            // This may cause sort mismatch if caller expects value sort, not pointer sort.
            warn!(
                "get_option_payload_value: dereference failed for reference operand, using pointer value - may cause sort mismatch"
            );
        }

        self.codegen_operand(operand)
    }

    /// Extract the pointee type from a Box<T> type.
    ///
    /// Returns Some(T) if the type is Box<T>, None otherwise.
    /// Used for Box unwrap pattern detection (#1039).
    pub(super) fn box_pointee_ty(ty: rustc_public::ty::Ty) -> Option<rustc_public::ty::Ty> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args))
                if def.name().ends_with("::Box") || def.name() == "Box" =>
            {
                args.0.iter().find_map(|arg| {
                    if let GenericArgKind::Type(inner_ty) = arg { Some(*inner_ty) } else { None }
                })
            }
            _ => None, // external enum: TyKind
        }
    }
}
