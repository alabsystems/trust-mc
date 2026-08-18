// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ptr-level validity checks for raw-pointer deref field resolution.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use crate::codegen_ay::ptr_repr::PtrRepr;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Emit Ptr-level object validity check for raw pointer dereferences (#2310).
    ///
    /// At Ptr level, emit obj_valid check for raw pointer dereferences even though
    /// the load value is unconstrained. This catches use-after-free: the pointer
    /// local holds a BV64 address that we can split into (obj_id, offset) and
    /// check obj_valid[obj_id].
    pub(in crate::codegen_ay::chc) fn emit_ptr_obj_valid_check(
        &mut self,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) {
        let base_ty = self.body.locals()[local_idx].ty;
        if !matches!(base_ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(_, _))) {
            return;
        }

        if let Some(addr) = self.known_stack_addr_expr(local_idx)
            && let Some((obj_id, _)) = Self::try_extract_constant_addr(&addr)
            && self.heap_state.local_idx_for_obj_id(obj_id).is_some()
        {
            debug!(
                local_idx,
                obj_id,
                "CHC: raw pointer deref points at stack local; obj_valid check is trivially true"
            );
            return;
        }
        if let Some(ref_target) = self.ref_resolution.ref_targets.get(&local_idx)
            && self.body.locals().get(ref_target.local).is_some()
        {
            debug!(
                local_idx,
                target_local = ref_target.local,
                "CHC: raw pointer deref targets MIR stack local; obj_valid check is trivially true"
            );
            return;
        }

        let traced_obj_id = self
            .known_alloc_ids
            .get(&local_idx)
            .copied()
            .or_else(|| self.trace_deref_store_alloc_id(local_idx))
            .map(|obj_id| Expr::bitvec_const(obj_id as i128, 32));
        let state_obj_id = || {
            // Part of #3768: graceful fallback instead of panic on unregistered locals.
            let Some(vec_idx) = self.try_state_idx_for_local(local_idx) else {
                debug!(local_idx, "CHC: ptr obj_valid check — local not in state map");
                return None;
            };
            let ptr_expr = if modified_locals.contains(&local_idx) {
                if let Some(env_expr) = self.encode.local_expr_env.get(&local_idx) {
                    Some(env_expr.clone())
                } else {
                    self.state_var_mgr
                        .output_state_vars
                        .get(vec_idx)
                        .map(|(name, sort)| Expr::var(&**name, sort.clone()))
                }
            } else {
                self.state_var_mgr
                    .state_vars
                    .get(vec_idx)
                    .map(|(name, sort)| Expr::var(&**name, sort.clone()))
            };
            // The local's MIR type is `RawPtr` (checked at the top of this
            // function), so its state variable holds an ADDRESS — that fact is
            // what licenses reading an object id out of it, and it is known
            // here, from the type. What the code used to test instead was
            // `bitvec_width() == Some(64)`: a hard-coded width (not even
            // `POINTER_WIDTH`) that silently dropped the obj_valid obligation
            // for every wide-pointer state var, i.e. a fail-open on exactly the
            // use-after-free class this check exists to catch. `PtrRepr` decides
            // the shape structurally and yields a pointer-width data address for
            // every shape it recognizes; a thin pointer decodes to itself, so
            // the emitted check is unchanged there.
            ptr_expr
                .as_ref()
                .and_then(PtrRepr::classify)
                .map(PtrRepr::into_data)
                // `[obj_id : 63..32 | offset : 31..0]` — the encoder-wide split
                // that `try_extract_constant_addr` and `pointer_step` also use.
                .map(|addr| addr.into_expr().extract(63, 32))
        };
        if let Some(obj_id) = traced_obj_id.or_else(state_obj_id) {
            let obj_valid = self.current_obj_valid_array();
            self.heap_state.pending_checks.push(obj_valid.select(obj_id));
            // Part of #3436: track that this block reads heap metadata.
            self.mark_heap_metadata_read();
            debug!(
                local_idx,
                "CHC: emitted obj_valid check for raw pointer deref at Ptr level (#2310)"
            );
        }
    }
}
