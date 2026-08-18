// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Datatype field select/update and projection application.
//!
//! Extracted from codegen_stmt_projection.rs per #3254 (packet 3).

use ay_bindings::{Expr, ExprValue, SortInner};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, trace};

use crate::codegen_ay::chc::stubs_util::extract_payload_from_option_reconstruction_ite;
use crate::codegen_ay::chc::{ChcCtx, chc_fresh_name, declare_pending_var};
use crate::codegen_ay::provenance::{Val, is_transparent_pointer_wrapper_repr};
use crate::codegen_ay::shared::IntoOption;

use super::field_select_coercion::coerce_selected_field_value;
use super::projection_path::FieldProjection;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // ===== Projection Handling (#600) =====

    /// Selects a field from a datatype **value**.
    ///
    /// For a struct expression `s` of type `Point { x: i32, y: i32 }`, selecting field 0
    /// returns the expression `(get-Point-x s)`.
    ///
    /// # Provenance
    ///
    /// Field projection is a pure operation on the CHC term algebra: it never
    /// consults the memory model and never takes the address of anything, so a
    /// field of a [`Val`] is itself a [`Val`]. That is the whole crossing rule
    /// here, and it is what makes the transparent-wrapper passthrough below
    /// safe to state: what comes back out of a flattened `NonNull`/`Unique`/`Box`
    /// is the pointer **datum** the wrapper holds, *not* an address of storage.
    /// A consumer that wants to load or store through it must obtain a
    /// [`crate::codegen_ay::provenance::Loc`] from an address producer
    /// (`translate_ref_to_address`, `extract_pointer_expr`); it may not
    /// reinterpret this `Val` as one.
    ///
    /// # Arguments
    /// * `container` - The datatype value to select from
    /// * `field_idx` - The field index (0-based)
    /// * `cons_idx` - Optional constructor index for multi-constructor datatypes (enums)
    pub(in crate::codegen_ay::chc) fn datatype_field_select(
        container: &Val,
        field_idx: usize,
        cons_idx: Option<usize>,
    ) -> Option<Val> {
        Self::datatype_field_select_term(container.as_expr(), field_idx, cons_idx)
            .map(Val::of_value)
    }

    /// Term-level core of [`Self::datatype_field_select`].
    ///
    /// Carries no provenance because it does not need any: every path here maps
    /// a sub-term of the container to another sub-term of the same container, so
    /// the tag the public entry applies is preserved by construction. Keeping the
    /// recursion (and the `apply_*` helpers below, which are still `Expr`-shaped
    /// and have ~100 callers) on this core avoids minting a tag per recursive
    /// step for a fact the caller already established.
    fn datatype_field_select_term(
        container: &Expr,
        field_idx: usize,
        cons_idx: Option<usize>,
    ) -> Option<Expr> {
        if crate::codegen_ay::types::is_coroutine_root_sort(container.sort()) {
            return crate::codegen_ay::types::coroutine_root_select(
                container.clone(),
                cons_idx,
                field_idx,
            );
        }

        // Flattened Option reconstruction pattern: ite(is_some, Some(payload), None).
        // For Downcast(Some)+Field(0), return payload directly instead of building a
        // selector over constructor terms that may not be declared in flattened CHC.
        if cons_idx == Some(1)
            && field_idx == 0
            && let Some(payload) = extract_payload_from_option_reconstruction_ite(container)
        {
            return Some(payload);
        }

        // Handle bitvec types that represent special wrappers.
        if container.sort().is_bitvec() {
            let width = container.sort().bitvec_width();
            // Transparent wrapper flattened to a single bv64 (e.g., NonNull/Unique/Box).
            // Field(0) returns the underlying bv64 unchanged. The predicate is shared
            // with `datatype_field_update` (and the BMC post-deref projection) so the
            // read side and the write side cannot disagree about which slot field 0 is.
            if is_transparent_pointer_wrapper_repr(container.sort())
                && field_idx == 0
                && cons_idx.is_none()
            {
                return Some(container.clone());
            }
            // Part of #2161: Flattened alloc-infra enums (e.g. Result<Layout, LayoutError>)
            // are bv128 in CHC encoding. Downcast+Field(0) extracts the payload variant
            // which IS the bv128 value itself (the enum wrapper was erased by translate_ty).
            if width == Some(128) && field_idx == 0 && cons_idx.is_some() {
                debug!("datatype_field_select: bv128 flattened enum variant select -> passthrough");
                return Some(container.clone());
            }
            // Layout struct field access: bv128 = concat(size:bv64, align:bv64).
            // MIR inlines Layout::size()/align() into plain Field(0)/Field(1) projections.
            if width == Some(128) && cons_idx.is_none() {
                return match field_idx {
                    0 => {
                        debug!(
                            "datatype_field_select: bv128 Layout field 0 (size) -> extract(127,64)"
                        );
                        Some(container.clone().extract(127, 64))
                    }
                    1 => {
                        debug!(
                            "datatype_field_select: bv128 Layout field 1 (align) -> extract(63,0)"
                        );
                        Some(container.clone().extract(63, 0))
                    }
                    _ => None, // non-enum: usize (field index)
                };
            }
            // Other bitvec widths/field indices not supported for field access.
            debug!(
                "datatype_field_select: bitvec width {:?} with field_idx {} cons_idx {:?} not supported",
                width, field_idx, cons_idx
            );
            return None;
        }

        // Part of #3792: repr-SIMD types are translated as bare Arrays (not
        // Datatype wrappers). Field(0) on a SIMD value accesses the inner [T; N]
        // array, which is identity when the sort is already Array.
        if container.sort().is_array() && field_idx == 0 && cons_idx.is_none() {
            debug!(
                "datatype_field_select: Array sort with field_idx=0 -> identity (repr-SIMD passthrough)"
            );
            return Some(container.clone());
        }

        let SortInner::Datatype(dt) = container.sort().inner() else {
            debug!("datatype_field_select: container is not a datatype");
            return None;
        };

        // (#686 follow-up) Detect Option-like struct encoding
        // These have fields [is_some: Bool, value: payload] but MIR uses Downcast(variant) + Field(0)
        // For cons_idx=1 (Some variant), remap field 0 to struct field 1 (value)
        let is_option_like_struct = dt.constructors.len() == 1
            && dt.constructors[0].fields.len() == 2
            && dt.constructors[0].fields[0].name == "is_some";

        // For multi-constructor datatypes (enums), require a constructor index
        // For single-constructor datatypes, always use constructor 0 (ignore MIR cons_idx)
        let constructor_idx = if dt.constructors.len() > 1 {
            if let Some(idx) = cons_idx {
                idx
            } else {
                debug!("datatype_field_select: multi-constructor '{}' requires Downcast", dt.name);
                return None;
            }
        } else {
            0 // Single constructor - always use 0
        };

        // Remap field index for Option-like structs
        let actual_field_idx = if is_option_like_struct && cons_idx == Some(1) && field_idx == 0 {
            // MIR Downcast(Some=1) + Field(0) → struct field 1 (value)
            1
        } else {
            field_idx
        };

        let Some(cons) = dt.constructors.get(constructor_idx) else {
            debug!(
                "datatype_field_select: constructor {} out of bounds ({})",
                constructor_idx, dt.name
            );
            return None;
        };

        let Some(field) = cons.fields.get(actual_field_idx) else {
            debug!(
                "datatype_field_select: field {} out of bounds ({}::{})",
                actual_field_idx, dt.name, cons.name
            );
            return None;
        };
        let fresh_field_value =
            || declare_pending_var(chc_fresh_name("field_select"), field.sort.clone());

        if let ExprValue::Ite { cond, then_expr, else_expr } = container.value() {
            let then_selected = Self::datatype_field_select_term(then_expr, field_idx, cons_idx)
                .and_then(|selected| coerce_selected_field_value(selected, &field.sort))
                .unwrap_or_else(&fresh_field_value);
            let else_selected = Self::datatype_field_select_term(else_expr, field_idx, cons_idx)
                .and_then(|selected| coerce_selected_field_value(selected, &field.sort))
                .unwrap_or_else(&fresh_field_value);
            return Some(Expr::ite(cond.clone(), then_selected, else_selected));
        }

        // Beta-reduction: sel_i(C(a_0, ..., a_n)) → a_i (Part of #3348)
        // When the container is a known DatatypeConstructor (e.g., reconstructed
        // from flattened state vars), extract the field arg directly instead of
        // wrapping in DatatypeSelector. Eliminates nested unsimplified selectors
        // like fld_data(S_mk(Vec_bool_mk(...))) that PDR cannot handle across
        // CHC rule boundaries.
        if let ExprValue::DatatypeConstructor { constructor_name: ctor_name, args, .. } =
            container.value()
        {
            if *ctor_name == cons.name {
                if let Some(arg) = args.get(actual_field_idx) {
                    return coerce_selected_field_value(arg.clone(), &field.sort)
                        .or_else(|| Some(fresh_field_value()));
                }
            }
            return Some(fresh_field_value());
        }

        Some(container.clone().field_select(&*dt.name, &*field.name, field.sort.clone()))
    }

    /// Updates a field in a datatype **value** using functional update.
    ///
    /// Reconstructs the datatype with the specified field replaced by `new_val`.
    /// For example, updating field 0 of `Point { x: 1, y: 2 }` with `10` produces
    /// `(mk 10 (get-Point-y original))`.
    ///
    /// # Provenance
    ///
    /// The write-side mirror of [`Self::datatype_field_select`]: a functional
    /// update rebuilds one value out of another, so container, replacement and
    /// result are all [`Val`]. Nothing is stored to memory here — the caller
    /// still owns that step — so no address ever enters or leaves this function.
    ///
    /// The two halves **must** agree about which slot `field_idx` names; a
    /// disagreement writes a different slot than the read side reads, which is
    /// the slot-misalignment shape that has fabricated proofs before. Every
    /// slot decision below is therefore taken from the same shared predicate
    /// the select side uses.
    ///
    /// # Arguments
    /// * `container` - The datatype value to update
    /// * `field_idx` - The field index to update
    /// * `cons_idx` - Optional constructor index for multi-constructor datatypes
    /// * `new_val` - The new value for the field
    pub(in crate::codegen_ay::chc) fn datatype_field_update(
        container: &Val,
        field_idx: usize,
        cons_idx: Option<usize>,
        new_val: Val,
    ) -> Option<Val> {
        Self::datatype_field_update_term(
            container.as_expr(),
            field_idx,
            cons_idx,
            new_val.into_expr(),
        )
        .map(Val::of_value)
    }

    /// Term-level core of [`Self::datatype_field_update`]; see
    /// [`Self::datatype_field_select_term`] for why the core is untagged.
    fn datatype_field_update_term(
        container: &Expr,
        field_idx: usize,
        cons_idx: Option<usize>,
        new_val: Expr,
    ) -> Option<Expr> {
        if crate::codegen_ay::types::is_coroutine_root_sort(container.sort()) {
            return crate::codegen_ay::types::coroutine_root_update(
                container, cons_idx, field_idx, new_val,
            );
        }

        if container.sort().is_bitvec() {
            let width = container.sort().bitvec_width();
            // Transparent wrapper (bv64): field 0 update replaces the value. Same
            // shared predicate as the select side — see the note on drift above.
            if is_transparent_pointer_wrapper_repr(container.sort())
                && field_idx == 0
                && cons_idx.is_none()
            {
                if new_val.sort() != container.sort() {
                    debug!(
                        "datatype_field_update: sort mismatch - expected {:?}, got {:?}",
                        container.sort(),
                        new_val.sort()
                    );
                    return None;
                }
                return Some(new_val);
            }
            // Flattened enum payload update: Downcast+Field(0) writes the full
            // bv128 payload value. Match the select-side passthrough semantics.
            if width == Some(128) && field_idx == 0 && cons_idx.is_some() {
                if new_val.sort() != container.sort() {
                    debug!(
                        "datatype_field_update: bv128 enum payload sort mismatch - expected {:?}, got {:?}",
                        container.sort(),
                        new_val.sort()
                    );
                    return None;
                }
                debug!("datatype_field_update: bv128 flattened enum variant update -> passthrough");
                return Some(new_val);
            }
            // Layout struct field update: bv128 = concat(size:bv64, align:bv64).
            // Reconstruct bv128 with one half replaced.
            if width == Some(128) && cons_idx.is_none() {
                if !new_val.sort().is_bitvec() || new_val.sort().bitvec_width() != Some(64) {
                    debug!(
                        "datatype_field_update: bv128 Layout field expects bv64, got {:?}",
                        new_val.sort()
                    );
                    return None;
                }
                return match field_idx {
                    0 => {
                        // Update size (upper 64 bits), keep align (lower 64 bits).
                        debug!("datatype_field_update: bv128 Layout field 0 (size) update");
                        Some(new_val.concat(container.clone().extract(63, 0)))
                    }
                    1 => {
                        // Keep size (upper 64 bits), update align (lower 64 bits).
                        debug!("datatype_field_update: bv128 Layout field 1 (align) update");
                        Some(container.clone().extract(127, 64).concat(new_val))
                    }
                    _ => None, // non-enum: usize (field index)
                };
            }
            debug!(
                "datatype_field_update: bitvec width {:?} with field_idx {} not supported",
                width, field_idx
            );
            return None;
        }

        // Part of #3792: repr-SIMD passthrough for field update.
        // When the container is an Array (SIMD unwrapped), field 0 update is identity.
        if container.sort().is_array() && field_idx == 0 && cons_idx.is_none() {
            debug!(
                "datatype_field_update: Array sort with field_idx=0 -> identity (repr-SIMD passthrough)"
            );
            return Some(new_val);
        }

        let SortInner::Datatype(dt) = container.sort().inner() else {
            debug!("datatype_field_update: container is not a datatype");
            return None;
        };

        // (#686 follow-up) Detect Option-like struct encoding
        let is_option_like_struct = dt.constructors.len() == 1
            && dt.constructors[0].fields.len() == 2
            && dt.constructors[0].fields[0].name == "is_some";

        // For multi-constructor datatypes (enums), require a constructor index
        // For single-constructor datatypes, always use constructor 0 (ignore MIR cons_idx)
        let constructor_idx = if dt.constructors.len() > 1 {
            if let Some(idx) = cons_idx {
                idx
            } else {
                debug!("datatype_field_update: multi-constructor '{}' requires Downcast", dt.name);
                return None;
            }
        } else {
            0 // Single constructor - always use 0
        };

        // Remap field index for Option-like structs
        let actual_field_idx = if is_option_like_struct && cons_idx == Some(1) && field_idx == 0 {
            1
        } else {
            field_idx
        };

        let Some(cons) = dt.constructors.get(constructor_idx) else {
            debug!(
                "datatype_field_update: constructor {} out of bounds ({})",
                constructor_idx, dt.name
            );
            return None;
        };

        let Some(field) = cons.fields.get(actual_field_idx) else {
            debug!(
                "datatype_field_update: field {} out of bounds ({}::{})",
                actual_field_idx, dt.name, cons.name
            );
            return None;
        };

        let new_val =
            crate::codegen_ay::types::unwrap_single_field_datatype_to_sort(&new_val, &field.sort)
                .unwrap_or(new_val);

        // Verify sort compatibility
        if new_val.sort() != &field.sort {
            debug!(
                "datatype_field_update: sort mismatch - expected {:?}, got {:?}",
                field.sort,
                new_val.sort()
            );
            return None;
        }

        // Beta-reduction: extract constructor args if container is a known
        // constructor, avoiding unnecessary DatatypeSelector wrappers (Part of #3348).
        let ctor_args =
            if let ExprValue::DatatypeConstructor {
                constructor_name: ctor_name, args: cargs, ..
            } = container.value()
            {
                if *ctor_name == cons.name { Some(cargs) } else { None }
            } else {
                None
            };

        // Reconstruct the datatype with the updated field
        let mut args = Vec::with_capacity(cons.fields.len());
        for (idx, f) in cons.fields.iter().enumerate() {
            if idx == actual_field_idx {
                args.push(new_val.clone());
            } else {
                // Use constructor arg directly when available (beta-reduction),
                // otherwise fall back to field_select.
                let val = ctor_args.and_then(|ca| ca.get(idx).cloned()).unwrap_or_else(|| {
                    container.clone().field_select(&*dt.name, &*f.name, f.sort.clone())
                });
                args.push(val);
            }
        }

        Some(Expr::datatype_constructor(&*dt.name, &*cons.name, args, container.sort().clone()))
    }

    /// Checks if a field access targets a ZST marker field represented without runtime data.
    ///
    /// BTree internal types have `_marker: PhantomData<T>` fields that are modeled as a
    /// compact scalar (e.g., Bool/bv32) in the CHC encoding. Field access on these should
    /// be a no-op since ZST fields have no runtime representation.
    ///
    /// Returns true if:
    /// - Container is encoded as bv32
    /// - Field type is zero-sized (like PhantomData)
    fn is_marker_bv32_field(container: &Expr, field_ty: Option<rustc_public::ty::Ty>) -> bool {
        if !container.sort().is_bitvec() || container.sort().bitvec_width() != Some(32) {
            return false;
        }
        let Some(field_ty) = field_ty else {
            return false;
        };
        // Check if field type is ZST - defensive: handle missing layout or TLS panics.
        let layout_zst = std::panic::catch_unwind(|| {
            field_ty.layout().map(|l| l.shape().is_sized() && l.shape().size.bytes() == 0)
        })
        .ok()
        .and_then(std::result::Result::ok)
        .unwrap_or(false);

        if layout_zst {
            return true;
        }

        // Fallback for contexts where layout is unavailable (unit tests, missing TLS).
        Self::is_zst_type_fallback(field_ty)
    }

    fn is_zst_type_fallback(ty: rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            // Unit type ()
            TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => true,
            // Never type ! (also ZST but uninhabited)
            TyKind::RigidTy(RigidTy::Never) => true,
            // Zero-length array [T; 0] or array of ZST elements [(); N]
            TyKind::RigidTy(RigidTy::Array(elem_ty, len)) => {
                if len.eval_target_usize().into_option() == Some(0) {
                    return true;
                }
                Self::is_zst_type_fallback(elem_ty)
            }
            _ => false, // external enum: TyKind
        }
    }

    /// Applies a chain of field selections to an expression.
    ///
    /// For projections `[Field(0), Field(1)]` on `s`, returns `(get-field1 (get-field0 s))`.
    pub(in crate::codegen_ay::chc) fn apply_field_selections(
        root: Expr,
        projections: &[FieldProjection],
    ) -> Option<Expr> {
        let mut current = root;
        for (idx, projection) in projections.iter().enumerate() {
            if Self::is_marker_bv32_field(&current, projection.field_ty) {
                if idx + 1 < projections.len() {
                    trace!(
                        "apply_field_selections: marker field with trailing projections; aborting"
                    );
                    return None;
                }
                trace!("apply_field_selections: bv32 marker field - no-op");
                return Some(current);
            }
            current = Self::datatype_field_select_term(
                &current,
                projection.field_idx,
                projection.cons_idx,
            )?;
        }
        Some(current)
    }

    /// Applies a functional update through a chain of field projections.
    ///
    /// For nested assignment `x.a.b = val`, this:
    /// 1. Builds the path: `[(x, field_a, None), (x.a, field_b, None)]`
    /// 2. Applies updates bottom-up: `new_a = update(x.a, field_b, val), new_x = update(x, field_a, new_a)`
    pub(in crate::codegen_ay::chc) fn apply_projection_update(
        root: &Expr,
        projections: &[FieldProjection],
        new_val: Expr,
    ) -> Option<Expr> {
        if projections.is_empty() {
            // No projections - this shouldn't happen, but handle it
            return Some(new_val);
        }

        // Build the path of (container, field_idx, cons_idx) tuples
        let mut path: Vec<(Expr, usize, Option<usize>)> = Vec::with_capacity(projections.len());
        let mut current = root.clone();

        for (i, projection) in projections.iter().enumerate() {
            if Self::is_marker_bv32_field(&current, projection.field_ty) {
                if i + 1 < projections.len() {
                    trace!(
                        "apply_projection_update: marker field with trailing projections; aborting"
                    );
                    return None;
                }
                trace!("apply_projection_update: bv32 marker field update is no-op");
                return Some(root.clone());
            }
            path.push((current.clone(), projection.field_idx, projection.cons_idx));
            if i + 1 < projections.len() {
                // Navigate to next level
                current = Self::datatype_field_select_term(
                    &current,
                    projection.field_idx,
                    projection.cons_idx,
                )?;
            }
        }

        // Apply updates bottom-up: start with the new value and work back to root.
        // This is the write side of the whole projection machinery, so it goes
        // through the TYPED entry: `new_val` is the datum being written and every
        // `container` on the path was reached by selecting fields of `root`, so
        // both are values, and the type now stops an address from being handed to
        // either one.
        let mut updated = Val::of_value(new_val);
        for (container, field_idx, cons_idx) in path.into_iter().rev() {
            updated = Self::datatype_field_update(
                &Val::of_value(container),
                field_idx,
                cons_idx,
                updated,
            )?;
        }

        Some(updated.into_expr())
    }
}
