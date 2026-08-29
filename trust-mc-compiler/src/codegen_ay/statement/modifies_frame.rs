// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FC-06 (BMC): modifies frame-condition enforcement for contract CHECK mode.
//!
//! The contracts transform instruments the modifies-wrapper closure with
//! `modifies_frame_enter(_wrapper_arg)` / `modifies_frame_exit()` marker
//! calls (`kani_middle::transform::contracts_frame`). After MIR inlining the
//! markers delimit the dynamic extent of the checked function inside the
//! harness body. The CHC backend enforces the full declared footprint
//! (`chc::modifies_frame`); until this module existed, BMC treated the
//! markers as pure control-flow no-ops, so a checked function that wrote
//! memory with NO `#[kani::modifies]` clause verified SUCCESSFUL — a false
//! proof (corpus: `function-contract/modifies/simple_fail`, `global_fail`).
//!
//! BMC enforcement scope (everything outside it is fail-open — no check,
//! never a false positive):
//! - Only frames whose declared footprint is EMPTY (`()` wrapper tuple, i.e.
//!   no modifies clause) are enforced. A CBMC DFCC empty write set permits
//!   only frame-local storage, so every attributable store to pre-existing
//!   storage is a violation. Non-empty footprints would need the pointer
//!   ranges compared against the register-level store model; not built yet.
//! - Checked store shapes: register-promoted ref-deref stores
//!   (`try_codegen_assign_ref_deref`) whose pointee base pre-exists the
//!   frame, and raw-pointer deref stores (`try_codegen_assign_raw_ptr_deref`)
//!   — the latter includes `static mut` writes, whose pointer operand is a
//!   constant allocation address.
//!
//! Known fail-open/fail-closed limits, documented on purpose:
//! - Raw-pointer stores into allocations created INSIDE the extent (e.g.
//!   `Box::new` initialization in a no-modifies checked function) would be
//!   flagged; no currently-passing corpus test has that shape, and DFCC
//!   freshness support belongs with full footprint enforcement.
//! - Stores the BMC model cannot attribute (datatype deref writes, memory
//!   intrinsics) are not checked.

use rustc_public::mir::{Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::{BmcModifiesFrame, Expr, IntoOption, StatementCodegen};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Handle the `modifies_frame_enter(_wrapper_arg)` marker: push a frame.
    ///
    /// The declared footprint is the tuple type of `_wrapper_arg`: an empty
    /// tuple means no `#[kani::modifies]` clause — enforced. A non-empty
    /// tuple is recorded as unenforced (fail-open) until BMC learns to
    /// compare declared pointer ranges against its store models.
    pub(super) fn bmc_modifies_frame_enter(&mut self, args: &[Operand]) {
        let field_count = args
            .first()
            .and_then(|arg| arg.ty(self.body.locals()).into_option())
            .and_then(|ty| match ty.kind() {
                TyKind::RigidTy(RigidTy::Tuple(fields)) => Some(fields.len()),
                _ => None,
            });
        let enforce_empty = field_count == Some(0);
        // NON-empty footprint: resolve each wrapper-tuple pointer field to
        // its tracked pointee BASE NAME. Any miss leaves the whole frame
        // fail-open (`allowed: None`), exactly the pre-existing behavior.
        let allowed = match field_count {
            Some(n) if n > 0 => self.resolve_footprint_pointees(args, n),
            _ => None,
        };
        let preexisting = self.current_env.keys().cloned().collect();
        debug!(enforce_empty, ?allowed, "FC-06(bmc): modifies frame entered");
        self.modifies_frames.push(BmcModifiesFrame { enforce_empty, preexisting, allowed });
    }

    /// Resolve the wrapper tuple's pointer fields to pointee base names.
    ///
    /// Returns `None` — the frame stays fail-open — unless EVERY field has
    /// a `ref_pointees` entry: a partial footprint could certify stores the
    /// unresolved remainder was meant to constrain.
    fn resolve_footprint_pointees(
        &mut self,
        args: &[Operand],
        field_count: usize,
    ) -> Option<std::collections::BTreeSet<std::sync::Arc<str>>> {
        let (Operand::Copy(place) | Operand::Move(place)) = args.first()? else {
            return None;
        };
        let base = self.ssa_base_name(place);
        let mut set = std::collections::BTreeSet::new();
        for i in 0..field_count {
            let key = crate::codegen_ay::names::indexed_field_name(&base, i);
            let pointee = self.ref_pointees.get(key.as_str())?;
            // The tracked pointee may itself be a deref-alias name whose own
            // ref_pointees entry names the real storage (e.g. the wrapper
            // field resolves to `local_75_deref` while the checked function's
            // stores resolve to `local_2`). Every hop denotes storage reached
            // from the SAME declared pointer, so insert the whole chain.
            let mut current = std::sync::Arc::clone(pointee);
            for _ in 0..8 {
                set.insert(std::sync::Arc::clone(&current));
                // `X_deref` names the pointee of pointer-typed name `X`; the
                // storage it denotes is wherever X's own tracked chain ends
                // (a re-borrow `&mut *x` mints the `_deref` alias while the
                // direct call chain keeps the original name).
                let next = match self.ref_pointees.get(current.as_ref()).cloned() {
                    Some(n) => Some(n),
                    None => current
                        .as_ref()
                        .strip_suffix("_deref")
                        .and_then(|stem| self.ref_pointees.get(stem).cloned()),
                };
                match next {
                    Some(n) => current = n,
                    None => break,
                }
            }
            set.insert(current);
        }
        Some(set)
    }

    /// Certify a store against a NON-empty resolved footprint: a pointee
    /// base in the allowed set (or a field path under one) discharges the
    /// per-store assigns obligation with a passing check — the same
    /// obligation Kani reports as 'Check that *x is assignable: SUCCESS'.
    /// A store that does NOT match stays fail-open (no check): base-name
    /// aliasing is not precise enough to ACCUSE, only to certify.
    /// Certify a swap's deref-store by its tracked pointee NAME against the
    /// frame's declared footprint.
    pub(super) fn bmc_modifies_certify_swap_store(&mut self, pointee_base: Option<&str>) {
        if let Some(base) = pointee_base {
            self.bmc_modifies_certify_allowed(base);
        }
    }

    fn bmc_modifies_certify_allowed(&mut self, pointee_base: &str) {
        let Some(frame) = self.modifies_frames.last() else {
            return;
        };
        let Some(allowed) = &frame.allowed else {
            return;
        };
        if !frame.preexisting.contains(pointee_base) {
            return; // Frame-local storage: always assignable, no obligation.
        }
        let in_footprint = allowed.iter().any(|a| {
            pointee_base == a.as_ref()
                || (pointee_base.starts_with(a.as_ref())
                    && pointee_base[a.len()..].starts_with("_field_"))
        });
        if in_footprint {
            debug!(pointee = pointee_base, "FC-06(bmc): store certified inside modifies footprint");
            self.record_violation_guarded_with_message(
                Expr::bool_const(false),
                "assigns_check",
                Some(format!("Check that *{pointee_base} is assignable")),
            );
        } else {
            debug!(
                pointee = pointee_base,
                "FC-06(bmc): store not certifiable against footprint (fail-open)"
            );
        }
    }

    /// Handle the `modifies_frame_exit()` marker: pop the innermost frame.
    pub(super) fn bmc_modifies_frame_exit(&mut self) {
        debug!("FC-06(bmc): modifies frame exited");
        self.modifies_frames.pop();
    }

    /// Check a register-promoted ref-deref store (`*r = v` resolved through
    /// `ref_pointees`) against the innermost modifies frame.
    ///
    /// A store whose pointee base name existed in the environment BEFORE the
    /// frame was entered writes storage that pre-exists the checked call;
    /// with an empty declared footprint that is an assigns violation.
    /// Frame-fresh pointees (locals of the checked function itself) are
    /// always assignable and never checked.
    pub(super) fn bmc_modifies_check_ref_store(&mut self, lhs: &Place, pointee_base: &str) {
        let Some(frame) = self.modifies_frames.last() else {
            return;
        };
        if !frame.enforce_empty {
            // Declared footprint not empty: certify what the resolved
            // footprint covers; everything else stays fail-open.
            self.bmc_modifies_certify_allowed(pointee_base);
            return;
        }
        if !frame.preexisting.contains(pointee_base) {
            return; // Frame-local storage: always assignable.
        }
        debug!(
            pointee = pointee_base,
            "FC-06(bmc): ref-deref store outside empty modifies footprint"
        );
        self.record_violation_guarded_with_message(
            Expr::bool_const(true),
            "assigns_check",
            Some(format!("Check that *var_{} is assignable", lhs.local)),
        );
    }

    /// Check a raw-pointer deref store (`*p = v`, including `static mut`
    /// writes) against the innermost modifies frame.
    ///
    /// With an empty declared footprint every raw-pointer store inside the
    /// extent writes memory the contract did not declare. (Fresh-allocation
    /// stores are not exempted yet — see module docs.)
    pub(super) fn bmc_modifies_check_raw_store(&mut self, lhs: &Place) {
        let Some(frame) = self.modifies_frames.last() else {
            return;
        };
        if !frame.enforce_empty {
            return; // Declared footprint not empty: not enforced (fail-open).
        }
        debug!(
            ptr_local = lhs.local,
            "FC-06(bmc): raw-pointer store outside empty modifies footprint"
        );
        self.record_violation_guarded_with_message(
            Expr::bool_const(true),
            "assigns_check",
            Some(format!("Check that *var_{} is assignable", lhs.local)),
        );
    }
}
