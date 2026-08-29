// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Sound EFFECT FRAME for a call to a foreign (`extern "C"`) function whose
//! definition the user supplied but the encoder cannot read.
//!
//! # What this replaces
//!
//! Every `extern "C" { fn f(..); }` call used to reach the undefined-foreign
//! `error()` emission in `codegen_call.rs`, i.e. `from_app ∧ stmt_constraints →
//! error` with a BARE `error` head carrying no `error_p{N}`. For a harness
//! whose FIRST statement is such a call that is not a check — it is the whole
//! verification collapsing at the call site. `ForeignItems/fixme_varadic.rs`
//! and `ForeignItems/fixme_option_ref.rs` exported a three-rule VC
//! (`true → main__bb0`, `main__bb0 → error`, `query error`): the harness fails
//! at entry and NO property is ever checked. `ForeignItems/extern_fn_ptr.rs`
//! went further and DECLARED `error_p4` in its `.vc.json` while the `.smt2`
//! neither declared nor produced it — the artifact advertised a property the
//! SMT did not contain.
//!
//! # The frame
//!
//! For an unknown `f(a1..an) -> R` the encoder asserts only theorems of
//! "`f` is SOME C function with this prototype":
//!
//! 1. RETURN — a fresh unconstrained value of `sort(R)`. Nothing is assumed
//!    about it (no validity narrowing, no range); the only constraints added
//!    are the int-lift REPRESENTATION bounds that every nondet site emits.
//! 2. EFFECTS, reachable memory — every `&mut T` / `*mut T` / `*const T`
//!    argument (and `&T` where `T` is non-`Freeze`) has its pointee havocked.
//! 3. EFFECTS, globals — every `static mut` and every non-`Freeze` static is
//!    havocked; linked C can reach an exported symbol without being handed a
//!    pointer. Foreign statics are already nondet (`codegen_decl_static.rs`).
//! 4. TRANSITIVE reach — the type-indexed `mem_*` arrays and the per-allocation
//!    `region_*` arrays are havocked. A C callee that ever received a pointer
//!    may have kept it, so the frame does not try to prove which cells stay
//!    intact; it drops the contents wholesale.
//! 5. DIVERGENCE — `f` may never return. The successor edge is KEPT (otherwise
//!    every path through the call disappears from verification, which is the
//!    real fail-open), and a fail-closed sound-fallback reason is recorded so a
//!    `Success` verdict is demoted rather than resting on the assumption that
//!    the callee returns. The frame therefore cannot turn into a proof.
//!
//! # Determinism is NOT assumed (the crux)
//!
//! `ay/docs/2026-07-24-trust-mc-parity-uf-request.md` argues that an undefined
//! extern whose signature is all-by-value scalars has no side-effect channel,
//! so a PURE uninterpreted function over its arguments cannot hide a bug. That
//! reasoning is WRONG, and the counterexample has the same prototype as this
//! corpus's own callee:
//!
//! ```c
//! static uint32_t c;
//! uint32_t takes_int(uint32_t i) { return i + c++; }
//! ```
//!
//! No pointer arguments, every parameter by value — and yet
//! `takes_int(x) != takes_int(x)`. A UF over the arguments alone PROVES the two
//! calls equal, which is a fabricated proof: the missed_bug class. It is the
//! same trap `codegen_call_cmp_string/fallback_dispatch.rs` already documents
//! and closed for alloc/RNG/IO, re-appearing in a shape whose signature merely
//! LOOKS pure. So each call site gets its OWN fresh return, and the encoder
//! never equates two returns on argument syntax.
//!
//! The determinism clause of the model is gated on purity being ESTABLISHED —
//! by ingesting the C body, or by a `#[kani::stub]` replacement. Neither source
//! exists at this layer, so the gate is never open here and no return-variable
//! reuse is performed. Signature shape is not, and must never become, the gate.
//!
//! # Honest consequence, and what supersedes it
//!
//! This frame does NOT buy parity for the value-dependent rows. `extern_fn_ptr`
//! asserts `call_on(input, Some(takes_int)).unwrap() == takes_int(input)`;
//! under the frame the two calls have independent returns, so the property is
//! reachable-but-unprovable. What the frame buys is the honesty fix —
//! properties are CHECKED instead of pre-empted by an entry-level error.
//!
//! Parity for those rows needs the C definition to actually be READ, which is
//! what `codegen_call_c_body.rs` now does: it runs FIRST, and this frame is
//! the per-FUNCTION fallback for everything outside its accepted fragment. That
//! also settles the determinism question above in the only admissible way —
//! purity is ESTABLISHED from the body rather than inferred from the signature,
//! so `takes_int(x) == takes_int(x)` is provable because the body provably
//! reads no state, not because the prototype looked pure.
//!
//! # Gate
//!
//! Only symbols with a definition available from SOME source take the frame
//! (see `codegen_ay::foreign_defs`). A symbol nobody supplied keeps Kani's
//! `assert(false)` semantics exactly — that is what `ForeignItems/
//! missing_fn_fail.rs` (`// kani-verify-fail`) pins.

use ay_bindings::Expr;
use std::collections::BTreeSet;
use std::sync::Arc;
use tracing::debug;

use super::codegen_call_c_body::CallDispatchCBody;

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_call_kani_model::CallKaniModel;
use super::super::codegen_rules::CodegenRules;
use super::super::{ChcCtx, chc_fresh_name, declare_pending_var};

/// Sound-fallback reason recorded by every foreign effect frame.
///
/// Deliberately NOT in the `SoundHavoc` bless-list of
/// `chc::codegen_ctx::fallback_soundness`: the frame keeps the successor edge
/// without having established that the callee returns, so it must fail closed
/// and demote any `Success` to `OverApproximation`.
pub(in crate::codegen_ay::chc) const FOREIGN_EFFECT_FRAME_REASON: &str =
    "foreign_call_effect_frame";

pub(in crate::codegen_ay::chc) trait CallDispatchForeign {
    /// Model a call to a foreign function whose definition the user supplied.
    ///
    /// Returns `false` — leaving the caller's fail-closed `error()` in place —
    /// for a diverging call (no successor), a callee whose symbol cannot be
    /// resolved, or a symbol no `--c-lib` file defines.
    fn try_dispatch_call_foreign_model(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchForeign for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_foreign_model(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        // A diverging foreign call (`target == None`) keeps the fail-closed
        // error: there is no successor to carry the frame onto, and pruning the
        // path would silently drop it from verification.
        let Some(target) = dcx.target else { return false };
        if !self.is_foreign_call(dcx.func) {
            return false;
        }
        let Ok(func_ty) = dcx.func.ty(self.body.locals()) else { return false };
        let Some(symbol) = crate::codegen_ay::foreign_defs::foreign_link_symbol(self.tcx, func_ty)
        else {
            return false;
        };
        if !crate::codegen_ay::foreign_defs::c_lib_defines(&symbol) {
            // Nobody supplied a definition. Kani's contract for that is
            // `assert(false)`; keep it.
            return false;
        }

        // PRECISE LANE FIRST. When the supplied definition is inside the C
        // front-end's accepted fragment AND its prototype checks out against
        // the Rust `extern` declaration, encode the body's real semantics
        // instead of abstracting it. This frame is what everything OUTSIDE
        // that fragment falls back to, per FUNCTION — a refused `my_add` does
        // not cost its neighbours their precision.
        if self.try_dispatch_call_c_body(dcx, &symbol) {
            return true;
        }

        // (1) RETURN — a fresh unconstrained value of the destination's sort.
        // Representation bounds only (an Int-lifted slot must still denote a
        // value of the machine width). No semantic narrowing of the return.
        let dest_local = dcx.destination.local;
        let mut extra: Vec<Expr> = self.int_lift_nondet_bounds(dest_local);
        let mut havoc_slots: BTreeSet<usize> = BTreeSet::new();
        self.collect_local_state_slots(dest_local, &mut havoc_slots);

        // (2) EFFECTS, reachable memory — havoc the pointee of every argument
        // the callee could legally write through.
        let mut writable_ptr_args = 0usize;
        let mut unresolved_pointees = 0usize;
        for arg in dcx.args {
            let Ok(arg_ty) = arg.ty(self.body.locals()) else { continue };
            if !crate::codegen_ay::foreign_defs::arg_is_writable_pointer(self.tcx, arg_ty) {
                continue;
            }
            writable_ptr_args += 1;
            // Havoc the WHOLE pointee local, not the projected sub-place: a
            // coarser over-approximation is the safe direction here.
            match self.resolve_write_any_slim_target_place(arg) {
                Some(place) => self.collect_local_state_slots(place.local, &mut havoc_slots),
                // An unresolved pointee is covered by the fail-closed reason
                // recorded below — no `Success` can rest on the stale contents.
                None => unresolved_pointees += 1,
            }
        }

        // (3) EFFECTS, globals — `static mut` and non-`Freeze` statics.
        havoc_slots.extend(self.ref_resolution.c_writable_static_state_idxs.iter().copied());

        // (4) TRANSITIVE reach — the typed-memory and region array families.
        // Unconditional, not keyed on this call having a pointer argument: a C
        // callee may have retained a pointer handed to it by an EARLIER call,
        // or taken the address of an exported static.
        let array_names: Vec<Arc<str>> = self
            .heap_state
            .type_arrays
            .values()
            .map(|(name, _)| Arc::clone(name))
            .chain(self.heap_state.region_arrays.values().map(|(name, _)| Arc::clone(name)))
            .collect();
        let mut havocked_arrays = 0usize;
        for name in array_names {
            if let Some(idx) = self.state_var_index_by_name(&name) {
                havoc_slots.insert(idx);
                havocked_arrays += 1;
            }
        }

        // Bind every havocked slot to a FRESH variable that appears nowhere
        // else, rather than leaving its `__out` unconstrained in the head.
        //
        // Both readings of a bare unconstrained `__out` are in use in this
        // encoder: "identity pass-through" and "havoc". The constant folder
        // resolves that ambiguity toward pass-through —
        // `chc_const_prop_eval::propagate_to_unconstrained_out_vars` copies a
        // known constant from `X` onto an unconstrained `X__out` — so a bare
        // `__out` havoc of a slot the folder has pinned is silently UNDONE and
        // the callee's write disappears. An explicit `X__out = <fresh>` states
        // the havoc in the encoding instead of leaving it to a convention:
        // `X__out` is then constrained (the folder skips it) and the fresh
        // right-hand side is never known, so nothing propagates through.
        // `kani::write_any_slim` binds its havoc the same way.
        for &idx in &havoc_slots {
            self.mark_state_var_modified(idx);
            let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(idx).cloned()
            else {
                continue;
            };
            let out_var = Expr::var(&*out_name, out_sort.clone());
            let fresh =
                declare_pending_var(chc_fresh_name("__foreign_effect_havoc"), out_sort.clone());
            extra.push(out_var.eq(fresh));
        }

        // (5) DIVERGENCE + honesty. Fail-closed: the frame keeps the successor
        // edge without having established that `f` returns, and an unresolved
        // pointee above would leave stale contents, so no `Success` verdict may
        // rest on this encoding.
        self.record_sound_fallback_reason(FOREIGN_EFFECT_FRAME_REASON);

        let new_output_args = self.build_output_args(dcx.modified_locals, &[]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            extra,
        );
        debug!(
            symbol = %symbol,
            bb_idx = dcx.bb_idx,
            writable_ptr_args,
            unresolved_pointees,
            havocked_slots = havoc_slots.len(),
            havocked_arrays,
            "foreign call modelled as a sound effect frame (C definition supplied)"
        );
        true
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Add every state-vector slot backing `local` to `slots`.
    ///
    /// A FLATTENED aggregate occupies N consecutive slots; havocking only the
    /// first would leave the remaining fields carrying pre-call values, so the
    /// whole group is taken. Mirrors the expansion `build_output_args` performs
    /// for its `extra_dests`.
    fn collect_local_state_slots(&self, local: usize, slots: &mut BTreeSet<usize>) {
        let Some(vec_idx) = self.try_state_idx_for_local(local) else { return };
        slots.insert(vec_idx);
        if self.flatten.flattened_tuple_locals.contains(&local) {
            let n = self.flattened_field_count(local);
            for i in 0..n {
                if vec_idx + i < self.state_var_mgr.state_vars.len() {
                    slots.insert(vec_idx + i);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::FOREIGN_EFFECT_FRAME_REASON;
    use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};

    /// The frame keeps the successor edge without having established that the
    /// callee returns, and an unresolved pointee leaves stale contents, so the
    /// reason must stay FAIL-CLOSED. Blessing it `SoundHavoc` would let a
    /// harness whose only fallback is a foreign call report a clean PROOF that
    /// silently assumes termination.
    #[test]
    fn foreign_effect_frame_reason_is_fail_closed() {
        assert_eq!(
            fallback_soundness(FOREIGN_EFFECT_FRAME_REASON),
            FallbackSoundness::FailClose,
            "the foreign effect frame must never be blessed as a clean havoc"
        );
    }
}
