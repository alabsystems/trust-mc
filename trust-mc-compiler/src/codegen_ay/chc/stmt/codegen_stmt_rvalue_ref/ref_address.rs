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
use crate::codegen_ay::provenance::Loc;
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

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
            // The Rvalue::Ref/AddressOf result becomes the destination local's
            // DATUM (a pointer value), and this function's other lanes are
            // value-semantics lanes for Reg/Ptr track levels, so the slot is
            // not an address slot; the wave-11 tag ends here.
            return self.translate_ref_to_address(place, modified_locals).map(Loc::into_expr);
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
                        return self
                            .translate_ref_to_address(&resolved_place, modified_locals)
                            .map(Loc::into_expr);
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

    /// Stage the validity obligation for a reference to a raw SLICE (or
    /// `str`) pointer's whole extent: `&*ptr` with `ptr: *const [T]` asserts
    /// that `data .. data + len * size_of::<T>()` lies inside one live
    /// allocation.
    ///
    /// Why this exists: [`Self::emit_deref_ref_pointee_size_check`] sizes the
    /// pointee with `get_type_size`, and `[T]` / `str` have no static size, so
    /// a raw slice pointer moved with `byte_add` (which keeps its metadata, see
    /// `with_metadata_of`) and turned back into a reference carried NO
    /// obligation at all. tests/expected/ptr_to_ref_cast/slice/test.rs
    /// `check_with_byte_add_fail` proved clean (`[AY:PROOF_QUALIFIERS:clean]`)
    /// where Kani reports "dereference failure: pointer invalid".
    ///
    /// The length is the pointer's OWN metadata from the known-metadata
    /// resolver (never a havoc). The allocation is the const-folded obj_id's
    /// extent, else the fail-closed single-assignment provenance walk's
    /// (obj_id, size) — in which case the pointer must also still name that
    /// object. When either cannot be resolved and the extent is not provably
    /// empty, the harness fails CLOSED with a recorded reason: a proof must
    /// not rest on an obligation that was never stated.
    ///
    /// `Rvalue::Ref` only (the caller): `&raw const (*p)` is not UB.
    pub(in crate::codegen_ay::chc) fn emit_raw_slice_ref_extent_check(
        &mut self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) {
        use rustc_public::mir::Operand;

        if !self.memory_safety_checks {
            return;
        }
        if place.projection.len() != 1 || !matches!(place.projection[0], ProjectionElem::Deref) {
            return;
        }
        let base_ty = self.body.locals()[place.local].ty;
        let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) = base_ty.kind() else {
            return;
        };
        let elem_size = match pointee.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem)) => self.get_type_size(elem),
            TyKind::RigidTy(RigidTy::Str) => Some(1),
            _ => return,
        };
        let Some(elem_size) = elem_size.and_then(|s| u32::try_from(s).ok()) else {
            self.record_sound_fallback_reason("raw_slice_ref_elem_size_unknown");
            return;
        };
        if elem_size == 0 {
            return; // a ZST slice reads no bytes
        }
        if self.track_level < ChcTrackLevel::Mem {
            // The obligation needs the address model: re-encode at Mem.
            self.needs_mem_promote = true;
            return;
        }
        let base_place = Place { local: place.local, projection: Vec::new() };
        let Some(ptr) = self.translate_place_with_modified(&base_place, modified_locals) else {
            self.record_sound_fallback_reason("raw_slice_ref_pointer_untranslatable");
            return;
        };
        let Some(repr) = PtrRepr::classify(&ptr) else {
            self.record_sound_fallback_reason("raw_slice_ref_pointer_shape_unknown");
            return;
        };
        let data = repr.into_data().into_expr();
        let Some((obj_lane, offset)) = self.split_pointer(&data) else {
            self.record_sound_fallback_reason("raw_slice_ref_pointer_unsplittable");
            return;
        };
        let Some(len) =
            self.resolve_ptr_metadata_known(&Operand::Copy(base_place.clone()), modified_locals)
        else {
            self.record_sound_fallback_reason("raw_slice_ref_len_unresolved");
            return;
        };
        let len = coerce_bitvec_width_safe(len, 64, SignExtension::ZeroExtend);

        let (alloc_size, same_object) = if let Some(const_obj_id) =
            Self::const_obj_id_u32(&obj_lane)
        {
            match self.alloc_size_expr_for_const_obj_id(const_obj_id, &obj_lane) {
                Some(size) => (size, None),
                None => {
                    self.record_sound_fallback_reason("raw_slice_ref_alloc_unresolved");
                    return;
                }
            }
        } else if let Some((obj_id, size)) = self
            .stack_provenance_for_local(place.local)
            .or_else(|| self.heap_alloc_provenance_for_local(place.local))
        {
            (
                Expr::bitvec_const(size as u128, 32),
                Some(obj_lane.eq(Expr::bitvec_const(obj_id as u128, 32))),
            )
        } else {
            let provably_empty = crate::codegen_ay::chc::expr::codegen_expr_heap_bv_eval::const_bv_value(&len)
                .is_some_and(|(v, _)| v == num_bigint::BigInt::from(0u8));
            if !provably_empty {
                warn!(
                    ptr_local = place.local,
                    "CHC: reference to a raw slice pointer whose allocation is unresolved (fail closed)"
                );
                self.record_sound_fallback_reason("raw_slice_ref_alloc_unresolved");
            }
            return;
        };
        let checks = Self::slice_ref_extent_checks(offset, len, elem_size, alloc_size, same_object);
        for check in checks {
            if !self.heap_state.pending_checks.contains(&check) {
                self.heap_state.pending_checks.push(check);
            }
        }
        debug!(ptr_local = place.local, elem_size, "CHC: staged raw slice reference extent obligation");
    }

    /// The positive conditions (the error-rule generator negates them) for a
    /// reference to `len` elements of `elem_size` bytes at offset lane
    /// `offset` (bv32) of an allocation of `alloc_size` bytes (bv32):
    ///
    /// - `len * elem_size` does not overflow 64 bits;
    /// - the byte extent fits the 32-bit offset lane (obj_size is bv32, so a
    ///   larger extent fits no allocation);
    /// - `offset + extent` does not wrap the lane and is `<= alloc_size`;
    /// - `same_object` (the pointer still names the walk-resolved object).
    ///
    /// An EMPTY extent is valid for any pointer (a zero-length slice at a
    /// dangling address is the canonical empty slice), so every condition
    /// after the overflow check is guarded by `extent == 0`.
    pub(in crate::codegen_ay::chc) fn slice_ref_extent_checks(
        offset: Expr,
        len: Expr,
        elem_size: u32,
        alloc_size: Expr,
        same_object: Option<Expr>,
    ) -> Vec<Expr> {
        let len64 = coerce_bitvec_width_safe(len, 64, SignExtension::ZeroExtend);
        let extent64 = if elem_size == 1 {
            len64.clone()
        } else {
            len64.clone().bvmul(Expr::bitvec_const(elem_size as u128, 64))
        };
        let mut checks = Vec::new();
        if elem_size > 1 {
            let max_len = u64::MAX / u64::from(elem_size);
            checks.push(len64.bvule(Expr::bitvec_const(max_len as u128, 64)));
        }
        let extent_is_zero = extent64.clone().eq(Expr::bitvec_const(0u128, 64));
        let fits_lane = extent64.clone().extract(63, 32).eq(Expr::bitvec_const(0u128, 32));
        let end = offset.clone().bvadd(extent64.extract(31, 0));
        let no_wrap = end.clone().bvuge(offset);
        let in_bounds = end.bvule(alloc_size);
        for condition in [fits_lane, no_wrap, in_bounds].into_iter().chain(same_object) {
            checks.push(Expr::or(extent_is_zero.clone(), condition));
        }
        checks
    }

    /// Stage a VIOLATED obligation when a reference is created from a raw
    /// pointer into DEAD storage: `&*raw_ptr` / `&(*raw_ptr).field` where the
    /// pointer resolves through `ref_targets` to a local whose `StorageDead`
    /// has already run (use-after-scope, e.g. a pointer to a callee local that
    /// escaped an inlined frame).
    ///
    /// Why at the REFERENCE and not only at a load: a reference to dangling
    /// storage is UB on creation (Kani's ptr_to_ref_cast check reports
    /// "dereference failure: pointer invalid" / "dead object"), and the load
    /// that would otherwise catch it may never appear in the encoded body.
    /// `println!("{}", *p)` lowers to `_r = &(*p)` handed to
    /// `Argument::new_display`; the READ happens inside `<T as Display>::fmt`,
    /// reached through a formatter fn pointer from `_print`, which CHC models
    /// as a side-effect-free no-op. With no load site, the Mem-level `&*ptr`
    /// lane returned the pointer unchecked and the harness proved CLEAN
    /// (dangling_stack_escape_dual.rs::escape_println_unsafe, --ay-chc).
    ///
    /// ADDITIVE, exactly like the deref-side check in
    /// `try_resolve_deref_via_ref_targets`: resolution is left untouched (an
    /// earlier refuse-to-resolve attempt diverted caught cases off the lane
    /// that catches them), and this only ADDS an obligation, so it can turn a
    /// proof into a failure but never a failure into a proof.
    ///
    /// Scope (each exclusion leaves the pre-existing encoding unchanged):
    /// - `Rvalue::Ref` only; the caller does not route `&raw const (*p)`
    ///   here, because taking a raw address of a dangling place is not UB.
    /// - Raw-pointer bases only: `&T`/`&mut T` bases are valid by language
    ///   guarantee, and a raw-to-ref conversion already sits upstream of any
    ///   such reference into dead storage.
    /// - Deref must be the FIRST projection: `ref_targets[local]` describes
    ///   `*local`, not `*(local.field)` (same rule as #4181).
    /// - Value-alias targets are skipped: when the resolved target is itself
    ///   pointer-typed and the base is not a pointer-to-pointer, `ref_targets`
    ///   records a VALUE alias (the #2323 closure-capture shape), so the
    ///   target's storage is not the pointee's storage.
    /// - Zero-sized (or unsized / unknown-size) borrowed places are skipped: a
    ///   dangling reference to a ZST reads no bytes and is valid
    ///   (thin_ptr_validity::check_invalid_zst), and an unsized place may
    ///   have zero length.
    /// The dead-storage obligation above needs a `ref_targets` edge, and a
    /// pointer with several producers (`let p = if b { &raw const x } else {
    /// &raw const y };`), or a copy of one, has none: its edge would name one
    /// producer's referent on every path
    /// (tools/soundness-duals/negative/joined_pointer_last_producer.rs). Without
    /// this, a reference made from such a pointer into dead storage, read only by
    /// unmodeled code (format-args), proved clean — the escape
    /// `dangling_stack_escape_dual.rs::escape_println_unsafe` closes, reached
    /// through a joined pointer. When any producer on the walk borrows a local
    /// that is dead here, the path is not decided: record a fail-closed fallback.
    fn fail_close_joined_ref_into_dead_storage(&mut self, place: &Place) {
        use rustc_public::mir::{Operand, Rvalue, StatementKind};
        const MAX_VISITED: usize = 64;
        let Ok(place_ty) = place.ty(self.body.locals()) else {
            return;
        };
        if !matches!(self.get_type_size(place_ty), Some(size) if size > 0) {
            return;
        }
        let operand_local = |op: &Operand| match op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
            _ => None,
        };
        let mut stack = vec![place.local];
        let mut seen = HashSet::new();
        let mut joined = false;
        let mut dead_candidate = false;
        let mut complete = true;
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            if seen.len() > MAX_VISITED {
                complete = false;
                break;
            }
            joined |= self.local_has_multiple_whole_definitions(current);
            for stmt in self.body.blocks.iter().flat_map(|block| &block.statements) {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if lhs.local != current || !lhs.projection.is_empty() {
                    continue;
                }
                match rhs {
                    Rvalue::Ref(_, _, borrowed) | Rvalue::AddressOf(_, borrowed) => {
                        if matches!(borrowed.projection.first(), Some(ProjectionElem::Deref)) {
                            stack.push(borrowed.local);
                        } else if self.liveness.dead_locals.contains(&borrowed.local) {
                            dead_candidate = true;
                        }
                    }
                    Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => stack.extend(operand_local(op)),
                    Rvalue::CopyForDeref(src) => stack.push(src.local),
                    _ => {}
                }
            }
        }
        if joined && (dead_candidate || !complete) {
            warn!(
                ptr_local = place.local,
                dead_candidate,
                complete,
                "CHC: reference from a joined raw pointer that may address dead storage (fail closed)"
            );
            self.record_sound_fallback_reason("ref_into_dead_storage_joined_pointer");
        }
    }

    /// Whether a ref target names its referent THROUGH a constant pointer:
    /// its first projection dereferences `target_local`, whose one definition
    /// is a constant (`(*_2)` with `_2 = const &A`, which is
    /// `let p: *const _ = &A`, or a promoted `&5`). The referent is then a
    /// static or constant memory, not `target_local`'s own storage, and no
    /// `StorageDead` ends it. The use-after-scope checks (here and in
    /// `codegen_expr_deref_field.rs`) fired on every such pointer once `_2`
    /// was dead: a constant-false obligation, so a safe `(*p).store(7)` into
    /// a static and a read through `&A as *const AtomicU32 as *const u32`
    /// failed, and with no other approximation in the harness the failure
    /// was certified Genuine (const_pointer_live_atomic_reach_dual.rs,
    /// `safe_ptr_param_store_load`).
    ///
    /// That false obligation was also the ONLY thing failing an access past
    /// the referent through such a pointer (`*(&V as *const u32).add(1)`),
    /// so skipping it alone turned those into clean proofs. The bound is now
    /// stated where the access is made: the global-object lane of the
    /// provenance walk (`codegen_stmt_rvalue_offset_const_object.rs`,
    /// `codegen_stmt_rvalue_offset_const_access.rs`) bounds every read, store
    /// and reborrow through a pointer that walks back to a constant pointer by
    /// the static's or the allocation's bytes (const_pointer_live_oob_dual.rs).
    /// Every caller that skips on this answer must also call
    /// `bound_access_through_constant_or_fail_close`: where that lane cannot
    /// bound the access (a pointer it cannot walk, as a field held in a
    /// struct once was), the access fails closed instead of proving
    /// (const_pointer_live_held_dual.rs).
    pub(in crate::codegen_ay::chc) fn ref_target_through_constant(
        &self,
        target_local: usize,
        projections: &[ProjectionElem],
    ) -> bool {
        matches!(projections.first(), Some(ProjectionElem::Deref))
            && matches!(
                crate::codegen_ay::chc::modifies_frame_net::unique_def(self.body, target_local),
                Some(rustc_public::mir::Rvalue::Use(rustc_public::mir::Operand::Constant(_), ..))
            )
    }

    /// `&*p` from a RAW pointer `p` chosen on a path (`p = if c { &A } else
    /// { &x }`, or a copy of such a pointer). The reference names ONE
    /// referent in every lane that resolves it (the producer encoded last),
    /// so a call model reading or writing through it may miss the object
    /// another path chose: with `x` a scoped `AtomicU32`, `(*p).load()` after
    /// `x` died proved clean on the CHC lane, because the load's model reads
    /// through the reference and the read-side net in
    /// `try_resolve_deref_cascade` never sees `*p`. Fail closed, exactly as a
    /// read or store through such a pointer does.
    pub(in crate::codegen_ay::chc) fn fail_close_reborrow_of_path_merged_pointer(
        &mut self,
        place: &Place,
    ) {
        if matches!(place.projection.first(), Some(ProjectionElem::Deref))
            && matches!(
                self.body.locals()[place.local].ty.kind(),
                TyKind::RigidTy(RigidTy::RawPtr(..))
            )
            && self.pointer_value_is_path_dependent(place.local)
        {
            self.record_sound_fallback_reason("deref_through_path_merged_pointer");
        }
    }

    pub(in crate::codegen_ay::chc) fn emit_ref_into_dead_storage_check(
        &mut self,
        place: &Place,
        modified_locals: &std::collections::HashSet<usize>,
    ) {
        if !self.memory_safety_checks {
            return;
        }
        if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            return;
        }
        let base_ty = self.body.locals()[place.local].ty;
        let TyKind::RigidTy(RigidTy::RawPtr(base_pointee_ty, _)) = base_ty.kind() else {
            return;
        };
        let Some((target_local, target_projections)) = self
            .ref_resolution
            .ref_targets
            .get(&place.local)
            .map(|rt| (rt.local, rt.projections.clone()))
        else {
            self.fail_close_joined_ref_into_dead_storage(place);
            return;
        };
        if !self.liveness.dead_locals.contains(&target_local) {
            return;
        }
        if self.ref_target_through_constant(target_local, &target_projections) {
            // The constant's pointee never dies; the skip stands only where
            // the global-object lane bounds the reference's bytes (`&*p`), or
            // can bound its uses (`&(*p).f`).
            if matches!(place.projection.as_slice(), [ProjectionElem::Deref]) {
                self.bound_access_through_constant_or_fail_close(place, modified_locals);
            } else {
                self.require_const_provenance_or_fail_close(place);
            }
            return;
        }
        let is_ptr_ty = |ty: rustc_public::ty::Ty| {
            matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)))
        };
        let target_place = Place { local: target_local, projection: target_projections };
        let target_is_ptr = target_place.ty(self.body.locals()).ok().is_some_and(is_ptr_ty);
        if target_is_ptr && !is_ptr_ty(base_pointee_ty) {
            return;
        }
        let Ok(place_ty) = place.ty(self.body.locals()) else {
            return;
        };
        if !matches!(self.get_type_size(place_ty), Some(size) if size > 0) {
            return;
        }
        let dead = Expr::bool_const(false);
        if !self.heap_state.pending_checks.contains(&dead) {
            self.heap_state.pending_checks.push(dead);
        }
        warn!(
            ptr_local = place.local,
            target = target_local,
            "CHC: reference created from a raw pointer into DEAD storage (use-after-scope)"
        );
    }
}

#[cfg(test)]
mod tests {
    use ay_bindings::{Expr, ExprValue, Sort};

    use super::super::super::ChcCtx;

    fn bv(v: u128, w: u32) -> Expr {
        Expr::bitvec_const(v, w)
    }

    /// Folds every obligation; `true` when all hold for these constants.
    fn all_hold(checks: &[Expr]) -> bool {
        checks.iter().all(|c| {
            let folded = trust_mc_core::chc_const_prop::eval::try_eval_to_const(c)
                .unwrap_or_else(|| panic!("obligation must fold for constant inputs: {c}"));
            match folded.value() {
                ExprValue::BoolConst(b) => *b,
                other => panic!("expected a bool constant, got {other:?}"),
            }
        })
    }

    #[test]
    fn slice_extent_exactly_fitting_holds() {
        // [u8; 5] at offset 0, len 5.
        let checks = ChcCtx::slice_ref_extent_checks(bv(0, 32), bv(5, 64), 1, bv(5, 32), None);
        assert!(all_hold(&checks));
    }

    #[test]
    fn slice_extent_one_byte_past_end_fails() {
        // byte_add(1) on [u8; 5] keeping len 5 (ptr_to_ref_cast/slice check_with_byte_add_fail).
        let checks = ChcCtx::slice_ref_extent_checks(bv(1, 32), bv(5, 64), 1, bv(5, 32), None);
        assert!(!all_hold(&checks));
    }

    #[test]
    fn slice_extent_scales_by_element_size() {
        // [u32; 3] (12 bytes): byte_add(4) with len 3 ends at 16.
        let past = ChcCtx::slice_ref_extent_checks(bv(4, 32), bv(3, 64), 4, bv(12, 32), None);
        assert!(!all_hold(&past));
        // len 2 from offset 4 ends at 12: fits.
        let fits = ChcCtx::slice_ref_extent_checks(bv(4, 32), bv(2, 64), 4, bv(12, 32), None);
        assert!(all_hold(&fits));
    }

    #[test]
    fn slice_extent_empty_is_valid_anywhere() {
        // A zero-length slice at a dangling address in the null object.
        let checks = ChcCtx::slice_ref_extent_checks(
            bv(8, 32),
            bv(0, 64),
            4,
            bv(0, 32),
            Some(Expr::bool_const(false)),
        );
        assert!(all_hold(&checks));
    }

    #[test]
    fn slice_extent_len_times_size_overflow_fails() {
        // 2^62 * 8 wraps to 0 in 64 bits; the overflow guard must still fail.
        let checks =
            ChcCtx::slice_ref_extent_checks(bv(0, 32), bv(1u128 << 62, 64), 8, bv(16, 32), None);
        assert!(!all_hold(&checks));
    }

    #[test]
    fn slice_extent_wrong_object_fails() {
        let checks = ChcCtx::slice_ref_extent_checks(
            bv(0, 32),
            bv(1, 64),
            1,
            bv(5, 32),
            Some(bv(3, 32).eq(bv(2, 32))),
        );
        assert!(!all_hold(&checks));
    }

    #[test]
    fn slice_extent_symbolic_len_stays_symbolic() {
        let len = Expr::var("len", Sort::bitvec(64));
        let checks = ChcCtx::slice_ref_extent_checks(bv(1, 32), len, 1, bv(5, 32), None);
        assert!(!checks.is_empty());
        assert!(
            checks.iter().any(|c| trust_mc_core::chc_const_prop::eval::try_eval_to_const(c).is_none()),
            "a symbolic length must leave a live obligation"
        );
    }
}
