// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Simple (non-projection) assignment encoding for CHC block statements.
//! Handles `_N = rhs` where `lhs.projection.is_empty()`: signedness propagation,
//! vtable tracking (#3159), sort coercion, SSA emission (#2055), collection
//! shadow state (#3057), Mem-level mirroring (#3096). Part of #3269.
//!
//! VTable tracking logic: `codegen_stmt_assign_simple_vtable.rs`
//! Collection propagation: `codegen_stmt_assign_simple_collection.rs`

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{CastKind, Operand, Place, ProjectionElem, Rvalue};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::args::ChcTrackLevel;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

use super::codegen_expr_signedness::ExprSignedness;
use super::stmt_accumulator::StmtAccumulator;
use super::{ChcCtx, chc_fresh_name, declare_pending_var};

// Re-export for codegen_stmt/mod.rs which imports extract_vtable_source_local.
pub(in crate::codegen_ay::chc) use super::codegen_stmt_assign_simple_vtable::extract_vtable_source_local;

fn ty_is_nonzero(ty: &rustc_public::ty::Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, _)) => {
            let name = def.trimmed_name();
            name == "NonZero" || name.starts_with("NonZero")
        }
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty_is_nonzero(&inner),
        _ => false,
    }
}

fn rvalue_copies_nonzero_local(rhs: &Rvalue, locals: &[rustc_public::mir::LocalDecl]) -> bool {
    let place = match rhs {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
        | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => place,
        _ => return false,
    };
    place.projection.is_empty() && ty_is_nonzero(&locals[place.local].ty)
}

fn nonzero_expr_guard(expr: &Expr) -> Option<Expr> {
    if let Some(width) = expr.sort().bitvec_width() {
        Some(expr.clone().ne(Expr::bitvec_const(0u64, width)))
    } else if expr.sort().is_int() {
        Some(expr.clone().ne(Expr::int_const(0)))
    } else {
        None
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Encode a simple (non-projection) assignment: `_N = rhs`.
    ///
    /// Handles signedness propagation, sort coercion, constraint emission,
    /// collection shadow state propagation, vtable discriminant tracking,
    /// and Mem-level memory store mirroring.
    pub(in crate::codegen_ay::chc) fn encode_simple_assignment(
        &mut self,
        lhs: &Place,
        rhs: &Rvalue,
        rhs_expr: Expr,
        local_idx: usize,
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) {
        // Part of #3768: bail out before any destination-local side effects.
        let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
            debug!(
                bb_idx,
                local_idx,
                fn_name = %self.fn_name,
                "assign: untracked destination, sound over-approx"
            );
            self.record_sound_fallback_reason("state_idx_missing_simple_assign");
            self.clear_untracked_assignment_metadata(local_idx);
            return;
        };

        self.update_local_signedness_from_rvalue(local_idx, rhs);

        // --- VTable tracking (pre-assignment) ---
        self.apply_vtable_tracking(rhs, &rhs_expr, local_idx, acc);

        // --- Core assignment: sort coercion + SSA emission ---
        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
        {
            let signed = self.encode.local_signedness.get(&local_idx).copied().or_else(|| {
                let local_ty = self.body.locals()[local_idx].ty;
                Some(super::codegen_expr_signedness::ty_signedness(local_ty).unwrap_or(false))
            });
            // Part of #3687: BV address → Int-sort BigInt local must select from
            // the typed memory array, not bv2int(addr).
            let bigint_load = if rhs_expr.sort().is_bitvec()
                && out_sort.is_int()
                && Self::type_name_contains_bigint(&self.body.locals()[local_idx].ty)
            {
                self.load_bigint_from_typed_array(
                    rhs_expr.clone(),
                    self.body.locals()[local_idx].ty,
                )
            } else {
                None
            };
            let coerced_rhs = if let Some(loaded) = bigint_load {
                loaded
            } else if let Some(coerced) =
                Self::coerce_assignment_rhs_to_sort(rhs_expr.clone(), &out_sort, signed)
            {
                coerced
            } else if let Some(projected) =
                Self::try_coroutine_projection_reroute(rhs, &rhs_expr, &out_sort, signed)
            {
                projected
            } else if let Some(field_expr) =
                self.try_coroutine_ref_target_field_extract(rhs, &rhs_expr, &out_sort, signed)
            {
                // Part of #4181: when the rhs is a Coroutine root Datatype from
                // an unresolved deref chain (e.g., Copy(*_ref) where _ref→coroutine.Field(N)),
                // extract the captured field through ref_targets + coroutine_root_select.
                field_expr
            } else if let Some(out_width) = out_sort.bitvec_width() {
                let addr_fallback = match rhs {
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                        self.translate_ref_to_address(place, acc.modified)
                    }
                    _ => None,
                };
                if let Some(addr_expr) = addr_fallback {
                    coerce_bitvec_width_safe(addr_expr, out_width, SignExtension::ZeroExtend)
                } else if let Some(promoted_addr) =
                    self.try_promoted_const_ref_array_address_fallback(rhs, &rhs_expr, local_idx)
                {
                    coerce_bitvec_width_safe(promoted_addr, out_width, SignExtension::ZeroExtend)
                } else if let Some(selected) =
                    self.try_array_element_select_for_deref(rhs, &rhs_expr, &out_sort, acc.modified)
                {
                    // Part of #4022: when rhs is Array(K→V) and out_sort is V,
                    // the deref translation returned the memory array instead of
                    // selecting an element. Resolve the pointer address and select.
                    selected
                } else {
                    let sym_name = chc_fresh_name("__ssa_init_assign");
                    warn!(
                        "bb{} Assign _{} SORT_MISMATCH rhs_discr={:?} (rhs_sort={:?}, out_sort={:?}) \
                         using symbolic fallback {}",
                        bb_idx,
                        local_idx,
                        std::mem::discriminant(rhs),
                        rhs_expr.sort(),
                        out_sort,
                        sym_name
                    );
                    self.record_sound_fallback_reason("assign_sort_mismatch_bv");
                    self.encode.local_signedness.remove(&local_idx);
                    declare_pending_var(sym_name, out_sort.clone())
                }
            } else {
                let sym_name = chc_fresh_name("__ssa_init_assign");
                warn!(
                    "bb{} Assign _{} SORT_MISMATCH rhs_discr={:?} (rhs_sort={:?}, out_sort={:?}) \
                     using symbolic fallback {}",
                    bb_idx,
                    local_idx,
                    std::mem::discriminant(rhs),
                    rhs_expr.sort(),
                    out_sort,
                    sym_name
                );
                self.record_sound_fallback_reason("assign_sort_mismatch_nonbv");
                self.encode.local_signedness.remove(&local_idx);
                declare_pending_var(sym_name, out_sort.clone())
            };
            let out_var = Expr::var(&*out_name, out_sort);

            // Fix #2055: SSA replace + block-local env update.
            self.encode.local_expr_env.insert(local_idx, coerced_rhs.clone());
            // Part of #3905/#1739: Safe cross-block scalar propagation for
            // single-assignment locals. Constants remain cacheable; symbolic
            // RHS expressions are cacheable only when their source operands are
            // themselves single-assignment locals, so later reads cannot observe
            // a stale value after a reassignment.
            let stable_sources = self.rvalue_has_single_assign_sources(rhs);
            self.cache_single_assign_scalar_expr(local_idx, &coerced_rhs, stable_sources);
            acc.replace_constraint(local_idx, out_var.eq(coerced_rhs.clone()));
            acc.modified.insert(local_idx);
            // Preserve the scalar invariant for transparent NonZero wrappers after MIR has
            // lowered construction/get paths to plain assignments.
            if (ty_is_nonzero(&self.body.locals()[local_idx].ty)
                || rvalue_copies_nonzero_local(rhs, self.body.locals()))
                && let Some(guard) = nonzero_expr_guard(&coerced_rhs)
            {
                acc.constraints.push(guard);
            }

            // Part of #3930: Encode Rust char validity invariant on u32→char transmutes.
            if let Rvalue::Cast(CastKind::Transmute, _, target_ty) = rhs
                && matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::Char))
            {
                use crate::codegen_ay::chc::rules::codegen_rules_entry_char::char_validity_expr;
                if let Some(guard) = char_validity_expr(coerced_rhs.clone()) {
                    debug!("bb{bb_idx} Assign _{local_idx} transmute→char validity guard");
                    acc.constraints.push(guard);
                }
            }

            // Part of #3495: Propagate subslice metadata through Ref/AddressOf.
            if let Rvalue::Ref(_, _, ref_place) | Rvalue::AddressOf(_, ref_place) = rhs {
                self.propagate_subslice_metadata(ref_place, local_idx);
                self.record_known_stack_addr_expr(local_idx, coerced_rhs.clone(), "ref-address");
            }

            // --- Collection shadow state propagation ---
            self.apply_collection_propagation(rhs, &rhs_expr, local_idx, acc);

            // --- Late VTable propagation ---
            self.apply_late_vtable_propagation(rhs, local_idx, acc);

            // --- Mem-level mirroring ---
            if self.track_level >= ChcTrackLevel::Mem {
                let local_ty = self.body.locals()[local_idx].ty;
                self.mirror_local_assignment_to_memory(
                    lhs.local,
                    rhs,
                    local_ty,
                    &coerced_rhs,
                    acc.modified,
                    acc.constraints,
                );
            }

            // --- Ref/AddressOf value mirroring ---
            // Mirror the referenced value into typed memory at ALL track levels
            // so that subsequent raw-pointer dereferences (in both the main encoder
            // and the inline walker) can load the value via load_from_memory.
            // Previously gated on Mem level only, which caused CTREX when inlined
            // code dereferenced raw pointers at functions encoded at lower levels
            // or when the auto-promote path was not triggered.
            if let Rvalue::Ref(_, _, ref_place) | Rvalue::AddressOf(_, ref_place) = rhs {
                if ref_place.projection.is_empty() {
                    let ref_local_idx: usize = ref_place.local;
                    let ref_local_ty = self.body.locals()[ref_local_idx].ty;
                    let ref_value = if self.flatten.flattened_tuple_locals.contains(&ref_local_idx)
                    {
                        self.translate_place_with_modified(ref_place, acc.modified)
                    } else if let Some(ref_vec_idx) = self.try_state_idx_for_local(ref_local_idx) {
                        if acc.modified.contains(&ref_local_idx) {
                            self.state_var_mgr
                                .output_state_vars
                                .get(ref_vec_idx)
                                .map(|(name, sort)| Expr::var(&**name, sort.clone()))
                        } else {
                            self.state_var_mgr
                                .state_vars
                                .get(ref_vec_idx)
                                .map(|(name, sort)| Expr::var(&**name, sort.clone()))
                        }
                    } else {
                        debug!(
                            bb_idx,
                            ref_local_idx,
                            fn_name = %self.fn_name,
                            "assign ref/value mirror: untracked referent, sound over-approx"
                        );
                        self.record_sound_fallback_reason("state_idx_missing_ref_mirror");
                        None
                    };
                    if let Some(value_expr) = ref_value {
                        self.mirror_ref_value_to_memory(
                            &coerced_rhs,
                            &value_expr,
                            ref_local_ty,
                            ref_local_idx,
                            acc.modified,
                            acc.constraints,
                        );
                    }
                }
            }
        }
    }

    /// Part of #4022: when the deref translation returned the memory array
    /// instead of selecting an element, resolve the pointer address and select.
    ///
    /// Pattern: `_N = Copy(*_ptr)` where `_ptr` was offset from an array base.
    /// The deref path returned Array(BV64→BV_V) instead of BV_V because no
    /// subslice_offset was registered. We recover by resolving `_ptr`'s address
    /// expression and doing `select(array, address)`.
    fn try_array_element_select_for_deref(
        &mut self,
        rhs: &Rvalue,
        rhs_expr: &Expr,
        out_sort: &ay_bindings::Sort,
        modified: &HashSet<usize>,
    ) -> Option<Expr> {
        // Only handle Array → element sort mismatch.
        let array_sort = rhs_expr.sort().array_sort()?;
        if array_sort.element_sort != *out_sort {
            return None;
        }

        // Extract the base pointer local from Use(Copy/Move(Deref place)).
        let ptr_local = match rhs {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                if matches!(p.projection.first(), Some(ProjectionElem::Deref)) =>
            {
                p.local
            }
            // CopyForDeref implies a Deref — projection may be empty or explicit.
            Rvalue::CopyForDeref(p) => p.local,
            _ => return None,
        };

        // Resolve the pointer address.
        let addr_expr = self.resolve_local_expr(ptr_local, modified)?;
        if !addr_expr.sort().is_bitvec() {
            return None;
        }

        let idx = coerce_bitvec_width_safe(
            addr_expr,
            array_sort.index_sort.bitvec_width()?,
            SignExtension::ZeroExtend,
        );
        debug!(ptr_local, "assign: Array→element select via deref pointer address (#4022)");
        Some(rhs_expr.clone().select(idx))
    }

    /// Part of #4079 D2: recover precise field projection from coroutine root.
    ///
    /// When `coerce_assignment_rhs_to_sort` returns `None` and the RHS
    /// expression is a coroutine root Datatype, recover the post-deref
    /// projection chain from the MIR Place and apply it to select the
    /// specific captured field. Then retry generic coercion on the leaf.
    ///
    /// Only handles `Rvalue::Use(Copy(place) | Move(place))` — the only
    /// patterns that carry a Place with the original projection chain.
    fn try_coroutine_projection_reroute(
        rhs: &Rvalue,
        rhs_expr: &Expr,
        out_sort: &ay_bindings::Sort,
        signed: Option<bool>,
    ) -> Option<Expr> {
        if !crate::codegen_ay::types::is_coroutine_root_sort(rhs_expr.sort()) {
            return None;
        }

        // Extract the Place from Use(Copy/Move).
        let place = match rhs {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => p,
            _ => return None,
        };

        // Find the first Deref in the projection chain and collect
        // Field/Downcast projections after it.
        let deref_pos = place.projection.iter().position(|p| matches!(p, ProjectionElem::Deref))?;
        let after_deref = &place.projection[deref_pos + 1..];
        if after_deref.is_empty() {
            return None;
        }

        let field_projs = super::codegen_stmt_projection::collect_field_projections(
            after_deref,
            super::codegen_stmt_projection::UnknownProjectionPolicy::Break,
        );
        if field_projs.is_empty() {
            return None;
        }

        // Apply the projection chain to the coroutine root expression.
        let leaf = Self::apply_field_selections(rhs_expr.clone(), &field_projs)?;

        // If the projected leaf already matches the destination sort, done.
        if leaf.sort() == out_sort {
            return Some(leaf);
        }

        // Retry generic coercion on the projected leaf.
        Self::coerce_assignment_rhs_to_sort(leaf, out_sort, signed)
    }

    /// Part of #4181: Extract a captured coroutine field when the rhs expression
    /// is a Coroutine root Datatype but the destination sort is a scalar (Bool/BV).
    ///
    /// This handles the case where `_dest = Copy(*_ref)` and `_ref` has a
    /// ref_target `{local: coroutine_local, projections: [Field(N, _)]}`.
    /// The deref resolution failed to apply the Field(N) projection, producing
    /// the full Coroutine Datatype instead of the captured field.
    fn try_coroutine_ref_target_field_extract(
        &self,
        rhs: &Rvalue,
        rhs_expr: &Expr,
        out_sort: &ay_bindings::Sort,
        signed: Option<bool>,
    ) -> Option<Expr> {
        use crate::codegen_ay::types::{coroutine_root_select, is_coroutine_root_sort};

        if !is_coroutine_root_sort(rhs_expr.sort()) {
            return None;
        }

        // Extract the ref local from Use(Copy/Move(*_ref)) pattern.
        let ref_local = match rhs {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                if matches!(p.projection.first(), Some(ProjectionElem::Deref)) =>
            {
                p.local
            }
            _ => return None,
        };

        // Look up the ref_target for the ref local.
        let ref_target = self.ref_resolution.ref_targets.get(&ref_local)?;

        // Extract the first Field projection from the ref_target.
        let mut field_idx = None;
        for proj in &ref_target.projections {
            if let ProjectionElem::Field(idx, _) = proj {
                field_idx = Some(*idx);
                break;
            }
        }
        let field_idx: usize = field_idx?;

        let leaf = coroutine_root_select(rhs_expr.clone(), None, field_idx)?;

        // If the ref_target had a trailing Deref (e.g., Field(0, &bool), Deref),
        // the leaf is the captured field value (&bool → BV64 pointer), not the
        // final bool. But the rhs_expr was already the full Coroutine (not the
        // pointer), so this case means the deref was never resolved. The leaf IS
        // the captured field (e.g., coroutine_field_0: BV64 for a bool stored
        // as BV64 in the coroutine layout).

        if leaf.sort() == out_sort {
            return Some(leaf);
        }

        Self::coerce_assignment_rhs_to_sort(leaf, out_sort, signed)
    }
}
