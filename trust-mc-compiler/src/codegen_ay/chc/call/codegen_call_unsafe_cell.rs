// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! UnsafeCell::get call handler for CHC encoding.
//!
//! UnsafeCell<T> is #[repr(transparent)], so get(&self) -> *mut T returns
//! a pointer to the same memory. When stable atomic operations are inlined
//! by the compiler, UnsafeCell::get is the only remaining call — the atomic
//! intrinsic itself is lowered to a non-call MIR construct (direct dereference).
//! Without this handler, get() becomes an uninterpreted function with
//! unconstrained output, making all Stable atomic tests UNKNOWN.
//!
//! Split from the `codegen_call_dispatch_misc` module per file size limit.
//! Part of #3452, #3516.

use std::collections::HashSet;

use rustc_public::mir::{Operand, Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::args::ChcTrackLevel;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::super::heap::is_value_widened_into_address;
use super::ChcCtx;
use super::chc_call_context::CallEmitContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_misc::CallMisc;
use super::codegen_rules::CodegenRules;

/// Extension trait for UnsafeCell::get call handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallUnsafeCell {
    fn codegen_call_unsafe_cell_get(&mut self, bb_idx: usize, ecx: &CallEmitContext<'_>);
}

impl<'tcx, 'body> CallUnsafeCell for ChcCtx<'tcx, 'body> {
    /// Handle UnsafeCell::get as transparent pointer identity with value forwarding.
    ///
    /// Three-part fix:
    /// 1. Forward ref_targets from &self to dest and mark dest as
    ///    call-forwarded so the Mem-level raw-pointer guard in
    ///    try_resolve_deref_via_ref_targets allows ref_target resolution.
    /// 2. Also insert into const_ref_values as a fallback (in case
    ///    ref_target resolution fails for structural reasons).
    /// 3. Constrain dest = self_ptr (pointer value identity) for the CHC rule.
    fn codegen_call_unsafe_cell_get(&mut self, bb_idx: usize, ecx: &CallEmitContext<'_>) {
        let dest_local: usize = ecx.destination.local;

        // Forward ref_targets: dest_ptr points to the same referent as &self.
        // Mark as call-forwarded so the raw-pointer guard is bypassed.
        if let Some(arg) = ecx.args.first() {
            if let Operand::Copy(place) | Operand::Move(place) = arg {
                let arg_local: usize = place.local;
                if place.projection.is_empty() {
                    if let Some(ref_target) =
                        self.ref_resolution.ref_targets.get(&arg_local).cloned()
                    {
                        debug!(
                            arg_local,
                            dest_local,
                            referent = ref_target.local,
                            "UnsafeCell::get: forwarded ref_target"
                        );
                        self.ref_resolution.ref_targets.insert(dest_local, ref_target);
                        // Mark as call-forwarded to bypass Mem-level raw-ptr guard.
                        self.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
                    }
                }
            } else {
                debug!("UnsafeCell::get: arg is Constant, not Copy/Move");
            }
            // Also insert into const_ref_values as fallback.
            let inner = self.resolve_ref_operand(arg, ecx.modified_locals);
            let referent = self.resolve_ref_or_const_referent(arg, ecx.modified_locals);
            if let Some(inner_value) = inner.or(referent) {
                self.ref_resolution.const_ref_values.insert(dest_local, inner_value);
            }
        }

        // Constrain dest pointer = input pointer (identity).
        //
        // fc-interior-mut FP cluster: through contract-instrumentation chains
        // (modifies tuple, old()/ensures closure captures) operand resolution
        // dematerializes the &self reference into the referent's flattened
        // VALUE (e.g. the bv32 payload of a Cell<u32>). Widening that value
        // into the bv64 dest fabricates an address with obj_id=0 whose deref
        // checks (alignment/overflow/bounds/frame containment) are then
        // decided by the cell's arbitrary payload — spurious Genuine CTREX —
        // or, worse, checked against the wrong object (fail-open surface).
        //
        // Reject exactly the confirmed-poison shape — a bitvec NARROWER than
        // pointer width (a value, never an address) — and keep every other
        // resolved shape (bv64/bv128 pointers, Int in int-lift mode, datatype
        // wrappers) on the legacy coercion path. For rejected shapes, recover
        // the referent's REAL memory-mirror address (obj_id, offset) from
        // ref-resolution. If no real address can be recovered,
        // `make_coerced_eq_constraint` (which independently refuses
        // narrow-to-pointer widening) routes to the sound fallback: dest
        // stays havoced and downstream checks remain fail-closed.
        let identity_shaped = |expr: &ay_bindings::Expr| {
            expr.sort().bitvec_width().is_none_or(|w| w >= POINTER_WIDTH)
                && !is_value_widened_into_address(expr)
        };
        let ptr_expr = ecx.args.first().and_then(|arg| {
            self.translate_operand_with_modified(arg, ecx.modified_locals)
                .or_else(|| self.resolve_ref_operand(arg, ecx.modified_locals))
                .filter(identity_shaped)
                .or_else(|| {
                    let addr =
                        self.recover_unsafe_cell_referent_address(arg, ecx.modified_locals)?;
                    // Record concrete stack provenance for the dest pointer so
                    // downstream deref load/store paths resolve the same
                    // (obj_id, offset) instead of re-deriving it symbolically.
                    // record_known_stack_addr_expr is a no-op unless the
                    // address is a constant naming a tracked stack object.
                    self.record_known_stack_addr_expr(
                        dest_local,
                        addr.clone(),
                        "unsafe_cell_get_referent_recovery",
                    );
                    Some(addr)
                })
        });
        if let Some(ptr_expr) = ptr_expr
            && let Some((_, dest_var)) = self.resolve_destination(dest_local)
        {
            if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                ptr_expr,
                dest_var.sort(),
                dest_local,
                "codegen_call_unsafe_cell_get",
            ) {
                let new_output_args = self.build_output_args(ecx.modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    ecx.from_app,
                    ecx.target,
                    &new_output_args,
                    ecx.stmt_constraints,
                    [eq],
                );
            } else {
                #[rustfmt::skip]
                emit_sound_fallback_goto(self, ecx.from_app, ecx.target, ecx.modified_locals, &[dest_local], ecx.stmt_constraints);
            }
            debug!(
                "modeled UnsafeCell::get as pointer identity with value forwarding (bb{})",
                bb_idx
            );
        } else {
            #[rustfmt::skip]
            emit_sound_fallback_goto(self, ecx.from_app, ecx.target, ecx.modified_locals, &[ecx.destination.local], ecx.stmt_constraints);
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Recover the REAL (obj_id, offset) address of the referent behind an
    /// `UnsafeCell::get`-style `&self` argument whose direct operand
    /// resolution yielded a dematerialized VALUE instead of a pointer.
    ///
    /// Part of the fc-interior-mut fix. Two sound recovery routes:
    /// - Unprojected arg place with a tracked `ref_targets` entry: the
    ///   referent PLACE is known — its memory-mirror address (stack obj_id
    ///   concat field offset via `translate_ref_to_address`) IS the pointer
    ///   value. Precise: deref checks against it discharge statically.
    /// - Projected arg place (e.g. a contract modifies-tuple field holding
    ///   the pointer): load the pointer value from typed pointer memory at
    ///   the slot's address. Either the mirrored real pointer (precise) or
    ///   an unconstrained cell (fail-closed FAILED) — never a fabricated
    ///   value-as-address.
    ///
    /// Returns `None` when no pointer-width address can be recovered; the
    /// caller then falls through to the sound-fallback lane (dest havoced,
    /// checks fail-closed), matching the OffsetProvenanceUnresolved
    /// discipline of never failing open on unresolved provenance.
    pub(in crate::codegen_ay::chc) fn recover_unsafe_cell_referent_address(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<ay_bindings::Expr> {
        // Addresses only exist in the Mem-level split-pointer model.
        if self.track_level < ChcTrackLevel::Mem {
            return None;
        }
        let (Operand::Copy(place) | Operand::Move(place)) = arg else {
            return None;
        };
        let recovered = if place.projection.is_empty() {
            let ref_target = self.ref_resolution.ref_targets.get(&place.local).cloned()?;
            let referent = Place { local: ref_target.local, projection: ref_target.projections };
            let addr = self.translate_ref_to_address(&referent, modified_locals)?;
            debug!(
                arg_local = place.local,
                referent = referent.local,
                "UnsafeCell::get: recovered referent mirror address via ref_targets"
            );
            addr
        } else {
            // The arg place names a slot HOLDING the pointer (field of a
            // wrapper/tuple, possibly behind a Deref). Only pointer-typed
            // slots qualify; anything else is a value, not an address source.
            let slot_ty = place.ty(self.body.locals()).ok()?;
            if !matches!(slot_ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))) {
                return None;
            }
            // Reject slot shapes whose projections translate_ref_to_address
            // cannot resolve precisely enough for identity purposes.
            if place
                .projection
                .iter()
                .any(|p| matches!(p, ProjectionElem::Downcast(_) | ProjectionElem::OpaqueCast(_)))
            {
                return None;
            }
            let slot_addr = self.translate_ref_to_address(place, modified_locals)?;
            let loaded = self.load_ptr_from_memory(slot_addr, slot_ty)?;
            debug!(
                arg_local = place.local,
                "UnsafeCell::get: recovered pointer identity via typed-memory slot load"
            );
            loaded
        };
        // Identity must be a thin pointer-width address; anything else would
        // reintroduce the value-as-address fabrication this path removes.
        (recovered.sort().bitvec_width() == Some(POINTER_WIDTH)).then_some(recovered)
    }
}
