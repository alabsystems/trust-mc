// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ref/AddressOf encoding for CHC rvalue translation.
//!
//! Contains `translate_ref_or_addressof` — the shared logic for
//! `Rvalue::Ref` and `Rvalue::AddressOf` encoding at Reg/Ptr/Mem levels.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use super::super::ChcCtx;
use crate::args::ChcTrackLevel;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Shared logic for `Rvalue::Ref` and `Rvalue::AddressOf` encoding.
    ///
    /// Extracted per R748 Option B (#2084): the borrow-kind-aware fallback needs
    /// `is_shared` to distinguish `&arr[i]` (value semantics) from `&mut arr[i]`
    /// (auto-promote to Mem).
    pub(in crate::codegen_ay::chc) fn translate_ref_or_addressof(
        &mut self,
        place: &Place,
        is_shared: bool,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let local_idx: usize = place.local;
        let local_ty = self.body.locals()[local_idx].ty;

        // At Mem level, use abstract heap model for ALL references (#869)
        // Part of #1460: ALWAYS use translate_ref_to_address for Ref/AddressOf.
        // The value semantics shortcut was returning x's value instead of its address,
        // breaking store/load round-trip verification.
        if self.track_level >= ChcTrackLevel::Mem {
            // Part of #4030: `&*ptr` / `&raw const (*ptr)` must preserve the
            // existing pointer value, including wide-pointer metadata. Routing
            // the whole-deref case through translate_ref_to_address() collapses
            // `*const [T]` / `&[T]` operands to an address-only lane and strands
            // the metadata needed by raw-pointer comparison helpers.
            if place.projection.len() == 1
                && matches!(place.projection[0], ProjectionElem::Deref)
                && matches!(
                    local_ty.kind(),
                    TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
                )
            {
                let base_place = Place { local: local_idx, projection: Vec::new() };
                if let Some(existing_ptr) =
                    self.translate_place_with_modified(&base_place, modified_locals)
                {
                    debug!(
                        ?place,
                        "CHC: Mem-level &*ptr / &raw const (*ptr) - preserving base pointer value"
                    );
                    // Soundness (raw-ptr deref pointee-size): creating a reference
                    // `&*ptr` from a RAW pointer asserts the pointee is valid for
                    // `size_of::<pointee>()` bytes. When `ptr` was cast to a LARGER
                    // pointee than its source allocation holds (e.g. `*const i64`
                    // cast to `*const i128`, or a ZST-allocation cast to a sized
                    // type), the reference is invalid even though no load happens.
                    // trust-mc's null/align checks miss this widening. Raw pointers
                    // only — `&T`/`&mut T` are already valid by language guarantee.
                    // (ptr_to_ref_cast.rs missed_bug.)
                    if matches!(local_ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
                        && let Some(pointee_ty) = Self::deref_pointee_ty(local_ty)
                    {
                        self.emit_deref_ref_pointee_size_check(&existing_ptr, pointee_ty);
                    }
                    return Some(existing_ptr);
                }
            }
            debug!(?place, "CHC: Mem-level reference using symbolic address");
            return self.translate_ref_to_address(place, modified_locals);
        }

        // Ref/AddressOf at Reg vs Ptr level:
        // - Reg: No heap model, so addresses are meaningless. Use value
        //   semantics (local_expr_env) for ALL simple locals so downstream
        //   deref reads resolve to concrete values. (#2074 RC-1b fix)
        // - Ptr: Has address identity semantics. Use stable symbolic
        //   addresses for non-Ordering locals; value semantics only for
        //   Ordering locals (so Discriminant extraction works). (#2064)
        if place.projection.is_empty() {
            if self.track_level < ChcTrackLevel::Ptr {
                // Reg level: always use value semantics (#2074 RC-1b)
                debug!(?place, "CHC: Reg-level reference - using value semantics for all locals");
                self.translate_place_with_modified(place, modified_locals)
            } else {
                // Ptr level: stable addresses, except Ordering for Discriminant
                let is_ordering_local = match local_ty.kind() {
                    TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                        let name = def.name();
                        name == "Ordering" || name.ends_with("::Ordering")
                    }
                    _ => false, // external enum: TyKind
                };
                if is_ordering_local {
                    debug!(?place, "CHC: Ptr-level Ordering local - using value semantics");
                    self.translate_place_with_modified(place, modified_locals)
                } else {
                    debug!(?place, "CHC: Ptr-level reference - using stable symbolic address");
                    self.get_or_create_local_address(place.local)
                }
            }
        } else if Self::type_name_contains_bigint(&local_ty)
            || Self::type_name_contains_bigrational(&local_ty)
        {
            // BigInt/BigRational reference with projections: translate directly
            debug!(?place, "CHC: BigInt/BigRational reference - using value semantics");
            self.translate_place_with_modified(place, modified_locals)
        } else {
            // Part of #1712: Try to resolve deref chains via ref_targets
            // Pattern: &(*ref_local).field -> use value of target_local.field
            let has_deref = place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref));
            if has_deref {
                // Canonical `&*ptr`/`&*ref` case: address-of immediately after
                // deref should preserve the base pointer identity.
                if place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)
                {
                    let base_place = Place { local: local_idx, projection: Vec::new() };
                    return self.translate_place_with_modified(&base_place, modified_locals);
                }

                let deref_pos =
                    place.projection.iter().position(|p| matches!(p, ProjectionElem::Deref));
                // Part of #1712: Use RefTarget with projections
                if let Some(deref_idx) = deref_pos
                    && let Some(ref_target) =
                        self.ref_resolution.ref_targets.get(&local_idx).cloned()
                {
                    let remaining_projs = &place.projection[deref_idx + 1..];
                    let all_value_projs = remaining_projs.iter().all(|p| {
                        matches!(
                            p,
                            ProjectionElem::Field(_, _)
                                | ProjectionElem::Downcast(_)
                                | ProjectionElem::Index(_)
                                | ProjectionElem::ConstantIndex { .. }
                                | ProjectionElem::Subslice { .. }
                        )
                    });
                    if all_value_projs {
                        // Combine pre-existing projections with remaining
                        let mut combined_projs: Vec<ProjectionElem> =
                            ref_target.projections.clone();
                        combined_projs.extend(remaining_projs.iter().cloned());

                        let resolved_place =
                            Place { local: ref_target.local, projection: combined_projs };
                        debug!(
                            orig_local = local_idx,
                            target_local = ref_target.local,
                            pre_projs = ref_target.projections.len(),
                            "CHC: resolved Ref deref chain via ref_targets"
                        );
                        // Ref/AddressOf must produce an address expression.
                        // After deref-chain resolution, compute the address of
                        // the resolved place (e.g., &(*ptr).field -> &target.field),
                        // not the field value.
                        return self.translate_ref_to_address(&resolved_place, modified_locals);
                    }
                }
            }

            // R748 Option B: Shared non-deref projections (e.g., &s.field)
            // use value semantics at Reg level — the consumer reads through this ref,
            // so the address isn't needed. Mutable borrows (&mut arr[i]) still
            // auto-promote to Mem so subsequent stores work correctly.
            //
            // Part of #2876: Exclude places with Index/ConstantIndex projections
            // (e.g., &arr[0].x). `translate_place_with_modified` calls
            // `extract_field_projections` which cannot handle Index projections,
            // causing the ref local to become unconstrained (nondet). Route these
            // through the Mem-level path instead, which computes proper addresses.
            let has_index_proj = place.projection.iter().any(|p| {
                matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
            });
            if !has_deref && is_shared && !has_index_proj {
                debug!(?place, "CHC: Reg-level shared non-deref projection — value semantics");
                return self.translate_place_with_modified(place, modified_locals);
            }

            // Failed deref resolution or mutable non-deref projection at Reg level.
            // Auto-promote to Mem so mir_to_chc retries at Mem level (Part of #2084).
            self.needs_mem_promote = true;
            warn!(
                ?place,
                track_level = ?self.track_level,
                is_shared,
                "CHC: Ref/AddressOf — auto-promoting to mem-track"
            );
            None
        }
    }

    /// Stage a `offset + size_of::<pointee>() <= alloc_size` obligation for a
    /// reference created from a raw-pointer dereference (`&*raw_ptr`).
    ///
    /// This closes the widening-cast soundness gap: a raw pointer cast to a
    /// pointee LARGER than its backing allocation (`*const i64` → `*const i128`,
    /// or a ZST allocation reinterpreted as a sized type) produces an invalid
    /// reference. The obligation is pushed onto `heap_state.pending_checks`,
    /// drained by the block encoder into per-block error rules (fail-closed).
    ///
    /// Deliberately mirrors the const-obj_id convention of `heap_access_checks`:
    /// - No obligation for ZST pointees (they read no bytes).
    /// - No obligation when the pointer's obj_id does not const-fold — the
    ///   allocation size is a caller contract we cannot invent for genuinely
    ///   unknown provenance (avoids false positives on symbolic-pointer code).
    /// - NO zero-size exemption: a genuine ZST source allocation (`obj_size == 0`)
    ///   MUST fail a nonzero-pointee deref (`check_zst_deref`), unlike the
    ///   dyn-trait `obj_size == 0` placeholder handled elsewhere.
    fn emit_deref_ref_pointee_size_check(
        &mut self,
        ptr: &ay_bindings::Expr,
        pointee_ty: rustc_public::ty::Ty,
    ) {
        use ay_bindings::Expr;

        if !self.memory_safety_checks {
            return;
        }
        let Some(pointee_size) = self.get_type_size(pointee_ty) else {
            return;
        };
        if pointee_size == 0 {
            return;
        }
        let Ok(size32) = u32::try_from(pointee_size) else {
            return;
        };
        let Some((obj_id, offset)) = self.split_pointer(ptr) else {
            return;
        };
        let Some(const_obj_id) = Self::const_obj_id_u32(&obj_id) else {
            return;
        };
        let Some(alloc_size) = self.alloc_size_expr_for_const_obj_id(const_obj_id, &obj_id) else {
            return;
        };
        let size_expr = Expr::bitvec_const(size32 as i128, 32);
        let end_offset = offset.clone().bvadd(size_expr);
        // Positive conditions that must HOLD (the error-rule generator negates
        // them): the pointee window neither wraps the 32-bit offset lane nor
        // exceeds the backing allocation.
        let no_wrap = end_offset.clone().bvuge(offset);
        let fits = end_offset.bvule(alloc_size);
        for check in [no_wrap, fits] {
            if !self.heap_state.pending_checks.contains(&check) {
                self.heap_state.pending_checks.push(check);
            }
        }
        debug!(
            pointee_size,
            const_obj_id, "CHC: staged raw-ptr deref pointee-size obligation (ptr_to_ref_cast)"
        );
    }
}
