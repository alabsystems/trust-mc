// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BMC twin of the CHC foreign-call EFFECT FRAME.
//!
//! The CHC lane's rationale — including why a pure uninterpreted function over
//! the arguments is NOT sound even for an all-by-value-scalar prototype — lives
//! in `chc/call/codegen_call_foreign.rs`. This module implements the same frame
//! against the SSA/BMC state.
//!
//! What it replaces: `record_violation_guarded(bool_const(true), "unsupported
//! foreign function")` followed by `return vec![]`, which reported an
//! unconditional violation AND dropped every successor block, so no statement
//! after the call was ever encoded.
//!
//! What it emits instead: a fresh unconstrained return, a fresh unconstrained
//! value for every pointee the callee could legally write through, and the
//! successor edge — plus `unsupported_with_fallback`, a DEMOTING category, so
//! the frame can never stand as a proof (the callee is not assumed to return,
//! and an unresolved pointee would otherwise leave stale contents).

use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Model a call to a foreign function whose definition the user supplied
    /// with `--c-lib`, returning the successor block.
    ///
    /// `None` — leaving the caller's fail-closed "unsupported foreign function"
    /// violation in place — for a diverging call, an unresolvable symbol, a
    /// symbol no `--c-lib` file defines, or a return whose sort the encoder
    /// cannot name (havocking a value it cannot represent is not possible, so
    /// it must not pretend the call happened).
    pub(super) fn try_codegen_foreign_effect_frame_bmc(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let target = target?;
        let func_ty = func.ty(self.body.locals()).ok()?;
        let symbol = crate::codegen_ay::foreign_defs::foreign_link_symbol(self.ctx.tcx, func_ty)?;
        if !crate::codegen_ay::foreign_defs::c_lib_defines(&symbol) {
            return None;
        }

        // (1) RETURN — fresh and unconstrained. A ZST/unit destination has no
        // representable value to havoc and needs none.
        let dest_ty = self.body.locals().get(destination.local).map(|d| d.ty);
        let dest_is_zst = dest_ty.is_some_and(Self::is_zst_type);
        if !dest_is_zst {
            let sort = self.infer_sort_from_place(destination)?;
            let name = self.ctx.fresh_name("foreign_ret");
            let fresh = self.ctx.declare_var(&name, sort);
            self.assign_value_to_place(destination, fresh);
        }

        // (2) EFFECTS — havoc the pointee of every argument the callee could
        // legally write through. An unresolved pointee is covered by the
        // demoting fallback recorded below.
        let mut havocked_pointees = 0usize;
        for arg in args {
            let Ok(arg_ty) = arg.ty(self.body.locals()) else { continue };
            if !crate::codegen_ay::foreign_defs::arg_is_writable_pointer(self.ctx.tcx, arg_ty) {
                continue;
            }
            if self.havoc_pointee_of_arg_bmc(arg) {
                havocked_pointees += 1;
            }
        }

        // (5) DIVERGENCE + honesty: a DEMOTING category, so a Success verdict
        // over this frame is downgraded rather than published.
        self.ctx.unsupported_with_fallback(
            "Foreign function effect frame",
            format!("extern \"C\" {symbol} (definition supplied, semantics not read)"),
        );
        debug!(
            symbol = %symbol,
            havocked_pointees,
            "BMC: foreign call modelled as a sound effect frame"
        );
        Some(target)
    }

    /// Assign a fresh unconstrained value to the pointee `arg` points at.
    /// Returns `false` when the pointee does not resolve to a place.
    fn havoc_pointee_of_arg_bmc(&mut self, arg: &Operand) -> bool {
        let place = match arg {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return false,
        };
        let ref_base = self.ssa_base_name(place);
        let Some(pointee_base) = self
            .ref_pointees
            .get(ref_base.as_str())
            .cloned()
            .or_else(|| self.ensure_ref_pointee_for_place(place))
        else {
            return false;
        };
        let target_local = Self::resolve_ref_chain_target(&self.ref_pointees, &pointee_base);
        if target_local == usize::MAX {
            return false;
        }
        let target_place = Place { local: target_local, projection: vec![] };
        let Some(sort) = self.infer_sort_from_place(&target_place) else {
            return false;
        };
        let name = self.ctx.fresh_name("foreign_pointee_havoc");
        let fresh = self.ctx.declare_var(&name, sort);
        self.assign_value_to_place(&target_place, fresh);
        true
    }
}
