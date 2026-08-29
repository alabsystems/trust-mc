// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Mirror-store helpers for Mem-level deref stores.
//!
//! These methods mirror `*ref = value` updates into register state so that
//! subsequent deref reads via `ref_targets` observe the updated value.
//!
//! Part of #2278: Extracted from `deref_mem.rs` for #2884 file decomposition.

use rustc_public::CrateDef;
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use ay_bindings::Expr;

use super::super::codegen_call_coerce::coerce_eq_constraint;
use super::super::codegen_ctx::CollectionProjectionKind;
use super::super::codegen_types::CodegenTypes;
use super::super::stmt_accumulator::StmtAccumulator;
use super::super::{
    ChcCtx, FieldProjection, POINTER_WIDTH, RefTarget, UnknownProjectionPolicy, chc_fresh_name,
    collect_field_projections, constant_index_offset, declare_pending_var,
};
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

struct DatatypeMirrorTarget {
    ref_local: usize,
    target_local: usize,
    target_vec_idx: usize,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Opaque iterator adapters are intentionally encoded as pointer-width
    /// scalar symbols rather than datatypes. A write through `&mut self.field`
    /// must therefore update the whole opaque abstraction, not attempt a field
    /// slot mirror against the scalar state var.
    fn try_build_opaque_iterator_adapter_store_expr(
        &self,
        target_local: usize,
        out_sort: &ay_bindings::Sort,
        combined_field_projs: &[FieldProjection],
    ) -> Option<Expr> {
        if combined_field_projs.is_empty() || out_sort.is_datatype() {
            return None;
        }

        let local_ty = self.body.locals().get(target_local)?.ty;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = local_ty.kind() else {
            return None;
        };
        if !matches!(def.trimmed_name().as_str(), "FlatMap" | "FlattenCompat" | "Chain" | "Fuse") {
            return None;
        }

        self.record_aggregate_gap("opaque_iterator_adapter_field_store_symbolic");
        Some(declare_pending_var(chc_fresh_name("__opaque_iter_adapter_store"), out_sort.clone()))
    }

    /// Check whether this is an unmodeled VecIntoIter projection (field index
    /// beyond the Datatype constructor arity). Uses the typed
    /// `CollectionProjectionKind` enum instead of string-based name matching.
    fn is_unmodeled_vec_into_iter_projection(
        &self,
        target_local: usize,
        out_sort: &ay_bindings::Sort,
        combined_field_projs: &[FieldProjection],
    ) -> bool {
        if self.collections.projection_locals.get(&target_local).copied()
            != Some(CollectionProjectionKind::VecIntoIter)
        {
            return false;
        }
        let Some(dt) = out_sort.datatype_sort() else {
            return false;
        };
        let Some(ctor) = dt.constructors.first() else {
            return false;
        };
        let modeled_fields = ctor.fields.len();
        combined_field_projs.iter().any(|proj| proj.field_idx >= modeled_fields)
    }

    /// Mirror a scalar/field ref store into register state.
    ///
    /// Part of #2278: Mem-level *ref stores must mirror into register state for
    /// scalar/field ref targets so subsequent deref reads via ref_targets don't
    /// observe stale __in values.
    pub(in crate::codegen_ay::chc) fn mirror_scalar_ref_store(
        &mut self,
        ref_target: &RefTarget,
        lhs: &Place,
        rhs_expr: &Expr,
        local_idx: usize,
        store_ty: rustc_public::ty::Ty,
        acc: &mut StmtAccumulator<'_>,
    ) {
        let target_local = ref_target.local;
        // Part of #3768: graceful fallback instead of panic
        let Some(target_vec_idx) = self.try_state_idx_for_local(target_local) else {
            debug!(target_local, "CHC: scalar ref store target not in state map — skipping");
            self.record_sound_fallback_reason("state_idx_missing_scalar_ref_store");
            return;
        };
        // Part of #3041/#3223: Track Downcast projections as cons_idx on subsequent Field.
        let mut combined_field_projs =
            collect_field_projections(&ref_target.projections, UnknownProjectionPolicy::Skip);
        combined_field_projs.extend(collect_field_projections(
            &lhs.projection[1..],
            UnknownProjectionPolicy::Break,
        ));

        // Part of #3814: Detect Field+Index pattern — when the LHS after Deref
        // contains an Index/ConstantIndex following the Field projections,
        // the store targets an array element, not the whole array field.
        // collect_field_projections with Break stops at the Index, so we
        // scan for it separately and build array.store(idx, val).
        let index_proj = lhs.projection[1..]
            .iter()
            .find(|p| matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }));
        if let Some(index_proj) = index_proj {
            if let Some(field_proj) = combined_field_projs.first() {
                let index_expr = match index_proj {
                    ProjectionElem::Index(index_local) => {
                        let idx_local: usize = *index_local;
                        self.resolve_local_expr(idx_local, &acc.modified)
                    }
                    ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                        // #from_end: needs the slice's runtime length -> fail closed (projection_path.rs)
                        constant_index_offset(*offset, *min_length, *from_end)
                            .map(|i| Expr::bitvec_const(i as u128, POINTER_WIDTH))
                    }
                    _ => None,
                };
                if let Some(index_expr) = index_expr {
                    let index_expr = coerce_bitvec_width_safe(
                        index_expr,
                        POINTER_WIDTH,
                        SignExtension::ZeroExtend,
                    );
                    let field_idx = field_proj.field_idx;
                    let arr_in = if self.flatten.flattened_tuple_locals.contains(&target_local) {
                        self.flattened_local_field_expr(target_local, field_idx, &acc.modified)
                    } else {
                        None
                    };
                    if let Some(arr_in) = arr_in {
                        if arr_in.sort().is_array() {
                            let coerced_rhs = ChcCtx::coerce_store_value(
                                arr_in.sort(),
                                rhs_expr.clone(),
                                false,
                                &self.diagnostics,
                            );
                            let updated_array = arr_in.store(index_expr, coerced_rhs);
                            debug!(
                                target_local,
                                ref_local = local_idx,
                                field_idx,
                                "CHC: Field+Index mirror store on flattened local (#3814)"
                            );
                            self.mirror_flattened_field_store(
                                field_proj,
                                &updated_array,
                                local_idx,
                                target_local,
                                target_vec_idx,
                                acc,
                            );
                            return;
                        }
                    }
                }
            }
            // Fall through to existing paths if index resolution fails
        }

        // Part of #2323: when ref_targets resolves to a pointer-valued
        // field (for example Closure.cap0: &mut T), `*ref = value` should
        // update pointee memory, not overwrite the pointer field itself.
        // Skip register mirroring in this shape to avoid corrupting the
        // captured pointer local (which can fabricate pointer CTREX paths).
        let mirrors_pointer_field = combined_field_projs
            .last()
            .and_then(|proj| proj.field_ty)
            .and_then(|field_ty| match field_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)) => {
                    ChcCtx::deref_pointee_ty(field_ty)
                }
                TyKind::RigidTy(RigidTy::Adt(def, _))
                    if def.name() == "std::boxed::Box" || def.name() == "alloc::boxed::Box" =>
                {
                    ChcCtx::deref_pointee_ty(field_ty)
                }
                _ => None, // external enum: TyKind
            })
            .is_some_and(|field_pointee| field_pointee == store_ty);
        if mirrors_pointer_field {
            debug!(
                target_local,
                ref_local = local_idx,
                "CHC: skipped Mem-level Deref register mirror for pointer-valued ref_target field"
            );
            return;
        }

        let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(target_vec_idx).cloned()
        else {
            warn!(
                target_local,
                ref_local = local_idx,
                "CHC: skipped Mem-level Deref register mirror — missing output state var"
            );
            return;
        };

        if let Some(opaque_post_store_expr) = self.try_build_opaque_iterator_adapter_store_expr(
            target_local,
            &out_sort,
            &combined_field_projs,
        ) {
            let out_var = Expr::var(&*out_name, out_sort.clone());
            if let Some(constraint) =
                coerce_eq_constraint(&out_var, opaque_post_store_expr.clone(), &out_sort, false)
            {
                acc.replace_constraint(target_local, constraint);
                self.encode.local_expr_env.insert(target_local, opaque_post_store_expr);
                acc.modified.insert(target_local);
            } else {
                warn!(
                    target_local,
                    ref_local = local_idx,
                    "CHC: opaque iterator adapter post-store sort mismatch"
                );
            }
        } else if combined_field_projs.is_empty() {
            // Part of #2876: When target is flattened and RHS is a Datatype
            // (whole struct store through deref), decompose into per-field
            // constraints instead of trying to equate scalar with Datatype.
            if self.flatten.flattened_tuple_locals.contains(&target_local)
                && rhs_expr.sort().is_datatype()
            {
                if let Some(dt) = rhs_expr.sort().datatype_sort()
                    && dt.constructors.len() == 1
                {
                    let ctor = &dt.constructors[0];
                    let n_fields = ctor.fields.len();
                    let mut values: Vec<Option<Expr>> = Vec::with_capacity(n_fields);
                    for field in &ctor.fields {
                        values.push(Some(rhs_expr.clone().field_select(
                            &dt.name,
                            &field.name,
                            field.sort.clone(),
                        )));
                    }
                    self.constrain_flattened_fields(target_local, &values, acc);
                } else {
                    warn!(
                        target_local,
                        ref_local = local_idx,
                        "CHC: Mem-level Deref mirror — multi-constructor Datatype to flattened local"
                    );
                }
            } else {
                let out_var = Expr::var(&*out_name, out_sort.clone());
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, rhs_expr.clone(), &out_sort, false)
                {
                    acc.replace_constraint(target_local, constraint);
                    self.encode.local_expr_env.insert(target_local, rhs_expr.clone());
                    acc.modified.insert(target_local);
                } else {
                    warn!(
                        target_local,
                        ref_local = local_idx,
                        "CHC: Mem-level Deref scalar mirror sort mismatch"
                    );
                }
            }
        } else if out_sort.is_datatype() {
            let target =
                DatatypeMirrorTarget { ref_local: local_idx, target_local, target_vec_idx };
            self.mirror_datatype_field_store(&target, &combined_field_projs, rhs_expr, acc);
        } else if combined_field_projs.len() == 1 {
            self.mirror_flattened_field_store(
                &combined_field_projs[0],
                rhs_expr,
                local_idx,
                target_local,
                target_vec_idx,
                acc,
            );
        } else if self.flatten.flattened_tuple_locals.contains(&target_local)
            && combined_field_projs.len() >= 2
            && combined_field_projs[0].cons_idx.is_some()
        {
            // Part of #435: Flattened enum with struct payload (e.g., Option<Point>).
            // combined_field_projs = [Downcast+Field(payload), Field(inner_field)].
            // Map the nested projection to the correct scalar slot:
            //   payload_start (1 for Option) + inner field offset.
            let n_fields = self.flattened_field_count(target_local);
            let cons_idx_val =
                combined_field_projs[0].cons_idx.expect("invariant: guard checked is_some()");
            let payload_field_idx = combined_field_projs[0].field_idx;
            let payload_start = if let Some(layout) =
                self.flatten.enum_bv_layouts.get(&target_local)
                && cons_idx_val < layout.ctor_field_slot.len()
                && payload_field_idx < layout.ctor_field_slot[cons_idx_val].len()
            {
                let Some(payload_slot) = layout.payload_slot(cons_idx_val, payload_field_idx)
                else {
                    warn!(
                        target_local,
                        cons_idx_val,
                        payload_field_idx,
                        "CHC: nested flattened enum mirror targeted omitted payload slot"
                    );
                    return;
                };
                1 + payload_slot
            } else if n_fields == 1 {
                // Part of #3041: Single-variant enum, no discriminant — payload IS fld0
                0
            } else if n_fields == 3 {
                let true_discr = self
                    .flatten
                    .flattened_enum_discr
                    .get(&target_local)
                    .map(|(t, _)| *t)
                    .unwrap_or(0);
                if (cons_idx_val as u64) == true_discr { 1 } else { 2 }
            } else {
                1 // 2-field enum: payload at fld1
            };

            // Compute inner field offset within payload type.
            let inner_indices: Vec<usize> =
                combined_field_projs[1..].iter().map(|fp| fp.field_idx).collect();
            let inner_offset = if let Some(local_decl) = self.body.locals().get(target_local)
                && let Some(sort) = <Self as CodegenTypes>::translate_ty(local_decl.ty)
                && let Some(dt) = sort.datatype_sort()
                && cons_idx_val < dt.constructors.len()
            {
                let variant = &dt.constructors[cons_idx_val];
                if payload_field_idx < variant.fields.len() {
                    let payload_sort = &variant.fields[payload_field_idx].sort;
                    crate::codegen_ay::chc::codegen_decl_flatten::compute_nested_flat_slot(
                        payload_sort,
                        &inner_indices,
                    )
                    .unwrap_or(inner_indices[0])
                } else {
                    inner_indices[0]
                }
            } else {
                inner_indices[0]
            };

            let target_slot = payload_start + inner_offset;
            let corrected_proj = FieldProjection {
                field_idx: target_slot,
                cons_idx: None,
                field_ty: combined_field_projs.last().and_then(|fp| fp.field_ty),
            };
            debug!(
                target_local,
                ref_local = local_idx,
                payload_start,
                inner_offset,
                target_slot,
                "CHC: Downcast+nested field mirror on flattened enum (#435)"
            );
            self.mirror_flattened_field_store(
                &corrected_proj,
                rhs_expr,
                local_idx,
                target_local,
                target_vec_idx,
                acc,
            );
        } else {
            warn!(
                target_local,
                ref_local = local_idx,
                field_count = combined_field_projs.len(),
                "CHC: unsupported nested flattened field mirror for Mem-level Deref store"
            );
        }
    }

    /// Mirror a deref store into a datatype-sorted register field.
    fn mirror_datatype_field_store(
        &mut self,
        target: &DatatypeMirrorTarget,
        combined_field_projs: &[FieldProjection],
        rhs_expr: &Expr,
        acc: &mut StmtAccumulator<'_>,
    ) {
        let target_local = target.target_local;
        let target_vec_idx = target.target_vec_idx;
        let ref_local = target.ref_local;
        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(target_vec_idx)
        else {
            warn!(
                target_local,
                ref_local,
                "CHC: skipped Mem-level Deref aggregate mirror — missing output state var"
            );
            return;
        };
        let out_var = Expr::var(&**out_name, out_sort.clone());
        let root_in = if acc.modified.contains(&target_local) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&target_local) {
                env_expr.clone()
            } else {
                Expr::var(&**out_name, out_sort.clone())
            }
        } else {
            self.state_var_mgr.state_vars.get(target_vec_idx).map_or_else(
                || Expr::var(&**out_name, out_sort.clone()),
                |(n, s)| Expr::var(&**n, s.clone()),
            )
        };

        match ChcCtx::apply_projection_update(&root_in, combined_field_projs, rhs_expr.clone()) {
            Some(mirrored_expr) => {
                if let Some(constraint) =
                    coerce_eq_constraint(&out_var, mirrored_expr.clone(), &out_sort, false)
                {
                    acc.replace_constraint(target_local, constraint);
                    self.encode.local_expr_env.insert(target_local, mirrored_expr);
                    acc.modified.insert(target_local);
                } else {
                    warn!(
                        target_local,
                        ref_local, "CHC: Mem-level Deref aggregate mirror sort mismatch"
                    );
                }
            }
            None => {
                if self.is_unmodeled_vec_into_iter_projection(
                    target_local,
                    &out_sort,
                    combined_field_projs,
                ) {
                    debug!(
                        target_local,
                        ref_local,
                        "CHC: VecIntoIter unmodeled projection in datatype mirror — emitting identity transition"
                    );
                    if let Some(constraint) =
                        coerce_eq_constraint(&out_var, root_in.clone(), &out_sort, false)
                    {
                        acc.replace_constraint(target_local, constraint);
                        self.encode.local_expr_env.insert(target_local, root_in);
                        acc.modified.insert(target_local);
                    } else {
                        warn!(
                            target_local,
                            ref_local, "CHC: VecIntoIter identity mirror sort mismatch"
                        );
                    }
                } else {
                    warn!(
                        target_local,
                        ref_local,
                        "CHC: apply_projection_update failed for Mem-level Deref field mirror"
                    );
                }
            }
        }
    }

    /// Mirror a deref store into a flattened (non-datatype) single-field slot.
    fn mirror_flattened_field_store(
        &mut self,
        field_proj: &FieldProjection,
        rhs_expr: &Expr,
        local_idx: usize,
        target_local: usize,
        target_vec_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) {
        let field_idx = field_proj.field_idx;
        if self.flatten.flattened_tuple_locals.contains(&target_local) {
            let field_count = self.flattened_field_count(target_local);
            if field_idx >= field_count {
                // Part of #2912: VecIntoIter deep-flattening maps 5 fields
                // (Vec.ptr, Vec.len, Vec.cap, Vec.data, pos) but MIR's IntoIter
                // has additional fields (e.g. field 5 = `end: *const T`) with no
                // counterpart in the CHC model. The iteration bound is derived
                // from fld_len, so dropping `end` writes is sound.
                if self.collections.projection_locals.get(&target_local).copied()
                    == Some(CollectionProjectionKind::VecIntoIter)
                {
                    debug!(
                        target_local,
                        ref_local = local_idx,
                        field_idx,
                        field_count,
                        "CHC: VecIntoIter unmodeled MIR field — emitting identity transition"
                    );
                    // OI1 (#2876): Emit deterministic out==in constraints for all
                    // projected slots instead of silently dropping. This prevents
                    // the CHC relation from becoming underconstrained on the
                    // IntoIter internal-field write path.
                    let mut values = Vec::with_capacity(field_count);
                    for idx in 0..field_count {
                        values.push(self.flattened_local_field_expr(
                            target_local,
                            idx,
                            acc.modified,
                        ));
                    }
                    self.constrain_flattened_fields(target_local, &values, acc);
                } else {
                    warn!(
                        target_local,
                        ref_local = local_idx,
                        field_idx,
                        field_count,
                        "CHC: flattened field mirror index out of bounds"
                    );
                }
                return;
            }

            // Preserve untouched flattened fields so updates through deref mirrors
            // do not unconstrain sibling fields (e.g., Range.end when writing Range.start).
            let mut values = Vec::with_capacity(field_count);
            for idx in 0..field_count {
                if idx == field_idx {
                    values.push(Some(rhs_expr.clone()));
                } else {
                    values.push(self.flattened_local_field_expr(target_local, idx, acc.modified));
                }
            }

            if !self.constrain_flattened_fields(target_local, &values, acc) {
                warn!(
                    target_local,
                    ref_local = local_idx,
                    field_idx,
                    "CHC: failed flattened field mirror constraint emission"
                );
            }
            return;
        }

        // Fallback for non-flattened scalar slots.
        let field_slot = target_vec_idx + field_idx;
        if let Some((field_out_name, field_out_sort)) =
            self.state_var_mgr.output_state_vars.get(field_slot)
        {
            let out_var = Expr::var(&**field_out_name, field_out_sort.clone());
            if let Some(constraint) =
                coerce_eq_constraint(&out_var, rhs_expr.clone(), field_out_sort, false)
            {
                // Encode (target_local, field_idx) into a single usize key.
                // Collision-free iff target_local < body.locals().len(),
                // which holds because MIR local indices are bounded by
                // the local declaration count.  Part of #2931.
                let n_locals = self.body.locals().len();
                assert!(
                    target_local < n_locals,
                    "track_key collision: target_local ({target_local}) >= locals count ({n_locals})"
                );
                let track_key =
                    if field_idx == 0 { target_local } else { target_local + field_idx * n_locals };
                acc.replace_constraint(track_key, constraint);
                acc.modified.insert(target_local);
            } else {
                warn!(
                    target_local,
                    ref_local = local_idx,
                    field_idx,
                    "CHC: Mem-level Deref flattened field mirror sort mismatch"
                );
            }
        } else {
            warn!(
                target_local,
                ref_local = local_idx,
                field_idx,
                "CHC: missing flattened output slot for Mem-level Deref field mirror"
            );
        }
    }
}
