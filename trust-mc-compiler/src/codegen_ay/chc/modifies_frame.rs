// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FC-06: modifies frame-condition enforcement for contract CHECK mode.
//!
//! The contract transform instruments the modifies-wrapper closure with
//! `modifies_frame_enter(_wrapper_arg)` / `modifies_frame_exit()` marker
//! calls (see `kani_middle::transform::contracts_frame`). After the wrapper
//! is inlined into the harness those markers delimit the dynamic extent of
//! the checked function: every block reachable from the enter call without
//! crossing an exit call executes inside the checked function (its body plus
//! inlined callees).
//!
//! This module:
//! 1. Pre-scans the harness body for marker calls and computes each frame's
//!    extent block set (`prescan_modifies_frames`).
//! 2. Resolves the declared footprint — the `_wrapper_arg` tuple of
//!    `*const T` pointers — into `(base, size)` byte ranges at the enter
//!    block, where the tuple local is still live
//!    (`resolve_modifies_footprint`).
//! 3. Checks every memory store encoded in an extent block against the
//!    footprint (`modifies_frame_store_check`), pushing a fail-if-false
//!    pending check that makes the CHC error state reachable on violation
//!    (CBMC DFCC "Check that *x is assignable" equivalent).
//!
//! Precision notes (documented FC-06 limits):
//! - Object-granular fallback when a footprint element's pointee size is
//!   unknown (matches any offset within the same object).
//! - Stores whose address cannot be split into (obj, offset) are not checked
//!   (fail-open, never a false positive).
//! - `suppress_heap_store_checks` stores (fresh-allocation writes such as
//!   `Box::new` initialization) are exempt — allocations created during the
//!   call may be freely written, matching DFCC freshness semantics.

use std::collections::{HashMap, HashSet};

use ay_bindings::Expr;
use rustc_public::mir::{Body, Operand, ProjectionElem, Terminator, TerminatorKind};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::call::chc_call_context::DispatchCallContext;
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::kani_functions::{KaniFunction, KaniHook, try_kani_function_from_fn_def};

/// One byte-range of the declared assignable footprint.
pub(in crate::codegen_ay::chc) struct FootprintRange {
    /// BV64 pointer value (obj_id ++ offset) of the range base.
    pub base: Expr,
    /// BV32 byte size of the range; `None` = object-granular (whole object
    /// with the base's obj_id is assignable).
    pub size: Option<Expr>,
}

/// A modifies frame: the dynamic extent of one checked-function invocation.
pub(in crate::codegen_ay::chc) struct ModifiesFrame {
    /// Block whose terminator is the `modifies_frame_enter` call.
    pub enter_bb: usize,
    /// Blocks that execute inside the checked function's extent.
    pub blocks: HashSet<usize>,
    /// Footprint ranges, resolved when the enter block is encoded.
    pub footprint: Vec<FootprintRange>,
    /// Whether footprint resolution ran (extent checks are fail-open until
    /// then, and permanently fail-open if resolution was not possible).
    pub resolved: bool,
}

/// Classify a terminator as one of the modifies-frame marker calls.
fn frame_hook_kind(body: &Body, term: &Terminator) -> Option<KaniHook> {
    let TerminatorKind::Call { func, .. } = &term.kind else {
        return None;
    };
    let (def, _) = func.ty(body.locals()).ok()?.kind().fn_def()?;
    match try_kani_function_from_fn_def(def)? {
        KaniFunction::Hook(hook @ (KaniHook::ModifiesFrameEnter | KaniHook::ModifiesFrameExit)) => {
            Some(hook)
        }
        _ => None,
    }
}

/// Pre-scan the body for modifies-frame markers and compute extent blocks.
///
/// Runs before block encoding (from `generate_transition_rules`), so the
/// enter block — encoded in topological order before its extent — can resolve
/// the footprint before any extent store is checked.
pub(in crate::codegen_ay::chc) fn prescan_modifies_frames(ctx: &mut ChcCtx<'_, '_>) {
    let mut frames: Vec<ModifiesFrame> = Vec::new();
    for (bb_idx, block) in ctx.body.blocks.iter().enumerate() {
        if frame_hook_kind(ctx.body, &block.terminator) != Some(KaniHook::ModifiesFrameEnter) {
            continue;
        }
        let TerminatorKind::Call { target, .. } = &block.terminator.kind else {
            continue;
        };
        // Forward DFS from the enter call's continuation; an exit call block
        // belongs to the extent (its statements run inside the wrapper) but
        // its successors do not.
        let mut extent: HashSet<usize> = HashSet::new();
        if let Some(entry) = target {
            let mut stack = vec![*entry];
            while let Some(bb) = stack.pop() {
                if !extent.insert(bb) {
                    continue;
                }
                let term = &ctx.body.blocks[bb].terminator;
                if frame_hook_kind(ctx.body, term) == Some(KaniHook::ModifiesFrameExit) {
                    continue;
                }
                stack.extend(term.successors());
            }
        }
        debug!(enter_bb = bb_idx, extent_blocks = extent.len(), "FC-06: prescanned modifies frame");
        frames.push(ModifiesFrame {
            enter_bb: bb_idx,
            blocks: extent,
            footprint: Vec::new(),
            resolved: false,
        });
    }
    if frames.is_empty() {
        return;
    }
    let mut by_bb: HashMap<usize, usize> = HashMap::new();
    for (idx, frame) in frames.iter().enumerate() {
        for bb in &frame.blocks {
            by_bb.insert(*bb, idx);
        }
    }
    ctx.modifies_frames = frames;
    ctx.modifies_frame_by_bb = by_bb;
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle the `ModifiesFrameEnter` hook: resolve the footprint from the
    /// `_wrapper_arg` tuple argument, then pass through control flow.
    pub(in crate::codegen_ay::chc) fn hook_modifies_frame_enter(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) {
        self.resolve_modifies_footprint(dcx);
        self.hook_noop_transition(dcx, "kani_hook::modifies_frame_enter");
    }

    /// Resolve the declared footprint of the frame entered at `dcx.bb_idx`.
    ///
    /// Each `_wrapper_arg` tuple field is a `*const T` pointer:
    /// - thin pointer: range = (ptr, size_of::<T>())
    /// - slice/str fat pointer (BV128 = len ++ data): range = (data, len * elem_size)
    /// - unknown size: object-granular range.
    fn resolve_modifies_footprint(&mut self, dcx: &DispatchCallContext<'_>) {
        let Some(frame_idx) = self.modifies_frames.iter().position(|f| f.enter_bb == dcx.bb_idx)
        else {
            return;
        };
        let Some(arg) = dcx.args.first() else {
            self.modifies_frames[frame_idx].resolved = true;
            return;
        };
        let Ok(arg_ty) = arg.ty(self.body.locals()) else {
            debug!("FC-06: cannot type _wrapper_arg; footprint unresolved (fail-open)");
            return;
        };
        let TyKind::RigidTy(RigidTy::Tuple(fields)) = arg_ty.kind() else {
            debug!(?arg_ty, "FC-06: _wrapper_arg is not a tuple; footprint unresolved (fail-open)");
            return;
        };
        if fields.is_empty() {
            // No modifies clause: empty footprint, every extent store violates.
            self.modifies_frames[frame_idx].resolved = true;
            return;
        }
        let place = match arg {
            Operand::Copy(p) | Operand::Move(p) => p.clone(),
            Operand::Constant(_) => {
                debug!("FC-06: constant _wrapper_arg tuple; footprint unresolved (fail-open)");
                return;
            }
        };
        let mut ranges: Vec<FootprintRange> = Vec::new();
        let mut all_resolved = true;
        for (i, field_ty) in fields.iter().enumerate() {
            let mut field_place = place.clone();
            field_place.projection.push(ProjectionElem::Field(i, *field_ty));
            let Some(expr) = self.translate_place_with_modified(&field_place, dcx.modified_locals)
            else {
                debug!(field = i, "FC-06: footprint pointer untranslatable");
                all_resolved = false;
                continue;
            };
            match self.footprint_range_for(expr, *field_ty) {
                Some(range) => ranges.push(range),
                None => {
                    debug!(field = i, "FC-06: unsupported footprint pointer shape");
                    all_resolved = false;
                }
            }
        }
        let frame = &mut self.modifies_frames[frame_idx];
        frame.footprint = ranges;
        // If any element failed to resolve, enforcing the partial footprint
        // could reject writes to the missing element: stay fail-open.
        frame.resolved = all_resolved;
        debug!(
            enter_bb = dcx.bb_idx,
            ranges = self.modifies_frames[frame_idx].footprint.len(),
            resolved = all_resolved,
            "FC-06: resolved modifies footprint"
        );
    }

    /// Build a footprint range from a resolved pointer expression + its type.
    fn footprint_range_for(&self, expr: Expr, field_ty: Ty) -> Option<FootprintRange> {
        let pointee = match field_ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(t, _)) => t,
            TyKind::RigidTy(RigidTy::Ref(_, t, _)) => t,
            _ => return None,
        };
        let width = expr.sort().bitvec_width();
        let is_slice_like =
            matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str));
        match width {
            Some(128) if is_slice_like => {
                // BV128 fat pointer = concat(len: BV64, data: BV64).
                let base = expr.clone().extract(63, 0);
                let len32 = expr.extract(95, 64);
                let elem_size = self.get_type_size(pointee).unwrap_or(1).max(1);
                let size = len32.bvmul(Expr::bitvec_const(elem_size as u128, 32));
                Some(FootprintRange { base, size: Some(size) })
            }
            Some(128) => {
                // Other fat pointers (dyn Trait): object-granular.
                Some(FootprintRange { base: expr.extract(63, 0), size: None })
            }
            Some(64) => {
                let size = self.get_type_size(pointee).map(|sz| Expr::bitvec_const(sz as u128, 32));
                Some(FootprintRange { base: expr, size })
            }
            _ => None,
        }
    }

    /// Check a register-promoted deref store (`*p = v` lowered to a direct
    /// state-var write via ref_targets / arg-ref / static-ref resolution)
    /// against the active modifies frame.
    ///
    /// These stores bypass `build_memory_store` entirely, so the frame check
    /// resolves the pointer local's value as the store address instead.
    pub(in crate::codegen_ay::chc) fn modifies_frame_ref_store_check(
        &mut self,
        lhs: &rustc_public::mir::Place,
        modified_locals: &HashSet<usize>,
    ) {
        if self.modifies_frames.is_empty()
            || !self.modifies_frame_by_bb.contains_key(&self.current_encode_bb)
        {
            return;
        }
        // Soundness (missed-bug E): compute the FULL store address, INCLUDING
        // the place's Deref+Field/Index projection offsets, via
        // `translate_ref_to_address` (which Deref-loads the pointer then adds
        // each field/index byte offset). The previous code translated only the
        // pointer local's VALUE (`Place{local, projection: []}`), dropping the
        // sub-field offset — so a store to `(*p).b` was checked at `(*p)`'s base
        // and spuriously matched a `modifies((*p).a)` footprint (whose offset IS
        // retained by resolve_modifies_footprint), letting an undeclared-field
        // write escape the frame check (a false Safe, regression from FC-06).
        let Some(addr) = self.translate_ref_to_address(lhs, modified_locals) else {
            debug!(
                bb = self.current_encode_bb,
                ptr_local = lhs.local,
                "FC-06: reg-level deref store address untranslatable — not checked (fail-open)"
            );
            return;
        };
        // GUARD DELETED (wave 11): this site used to re-test the width of
        // `translate_ref_to_address`'s result and take `extract(63, 0)` on a
        // 128-bit "fat pointer". That branch is unreachable — the producer's
        // ENSURES states every `Some` result is exactly `POINTER_WIDTH` wide
        // (allocation base `concat(bv32, bv32)`, deref lanes normalized by
        // `normalize_deref_address_expr`, projections width-preserving
        // `bvadd`s), and it now says so in its return type. Re-deriving
        // address shape from a width test is exactly the heuristic this
        // refactor removes.
        //
        // The assertion below restates the ENSURES but is NOT what makes the
        // deletion safe: this workspace sets `profile.dev.debug-assertions =
        // false`, so it is compiled out of the driver. The argument is the
        // structural one above (and a non-`POINTER_WIDTH` `current_addr` could
        // not survive a projection's `bvadd` in the first place).
        debug_assert_eq!(
            addr.as_expr().sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "translate_ref_to_address must mint POINTER_WIDTH addresses"
        );
        let pointee_ty =
            lhs.ty(self.body.locals()).ok().unwrap_or_else(|| self.body.locals()[lhs.local].ty);
        self.modifies_frame_store_check(addr.as_expr(), pointee_ty);
    }

    /// Check a memory store against the active modifies frame, if any.
    ///
    /// Pushes a fail-if-false pending check: the store address (byte range
    /// `[addr, addr + size_of(pointee_ty))`) must lie within one of the
    /// declared footprint ranges. Violation makes the CHC error state
    /// reachable, failing the harness.
    pub(in crate::codegen_ay::chc) fn modifies_frame_store_check(
        &mut self,
        addr: &Expr,
        pointee_ty: Ty,
    ) {
        if self.modifies_frames.is_empty() {
            return;
        }
        // ZST writes are trivially assignable (no bytes touched).
        if super::call::codegen_call_kani_model_dst::is_zst_ty(pointee_ty) {
            return;
        }
        let Some(&frame_idx) = self.modifies_frame_by_bb.get(&self.current_encode_bb) else {
            return;
        };
        let frame = &self.modifies_frames[frame_idx];
        if !frame.resolved {
            debug!(
                bb = self.current_encode_bb,
                "FC-06: store in modifies frame with unresolved footprint — not checked (fail-open)"
            );
            return;
        }
        let Some((obj_a, off_a)) = self.split_pointer(addr) else {
            debug!(
                bb = self.current_encode_bb,
                "FC-06: store address not splittable — not checked (fail-open)"
            );
            return;
        };
        let store_size = self.get_type_size(pointee_ty).unwrap_or(1).max(1);
        let store_end = off_a.clone().bvadd(Expr::bitvec_const(store_size as u128, 32));
        let mut allowed = Expr::bool_const(false);
        for range in &frame.footprint {
            let Some((obj_b, off_b)) = self.split_pointer(&range.base) else {
                continue;
            };
            let same_obj = obj_a.clone().eq(obj_b);
            let cond = match &range.size {
                Some(size) => {
                    let starts_after = off_b.clone().bvule(off_a.clone());
                    let ends_before = store_end.clone().bvule(off_b.clone().bvadd(size.clone()));
                    same_obj.and(starts_after).and(ends_before)
                }
                None => same_obj,
            };
            allowed = allowed.or(cond);
        }
        debug!(
            bb = self.current_encode_bb,
            ranges = frame.footprint.len(),
            "FC-06: emitted modifies frame store check"
        );
        self.heap_state.pending_checks.push(allowed);
    }
}
