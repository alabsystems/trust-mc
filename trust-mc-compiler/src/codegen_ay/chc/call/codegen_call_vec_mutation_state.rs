// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Complete aggregate writes for legacy mutations that only set sidecars.
//!
//! A later append/index reads the aggregate. Leaving its old data or length
//! there can both invent bugs and erase the uncertainty a partial model booked.

use super::{ChcCtx, call_accumulator::CallAccumulator, chc_fresh_name};
use crate::codegen_ay::chc::codegen_ctx::{Havoc, sound_havoc};
use crate::codegen_ay::names::out_name;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::ptr_sort;
use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use std::collections::HashSet;

impl ChcCtx<'_, '_> {
    pub(super) fn finish_sidecar_vec_mutation(
        &mut self,
        stub: StubKind,
        local: Option<usize>,
        destination: Option<usize>,
        modified: &HashSet<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        if stub == StubKind::VecFromIter {
            // The fallback constructor only set query sidecars and left its
            // aggregate unconstrained. Preserve its incomplete provenance on
            // the actual result rather than accidentally rewriting the input
            // iterator's state or letting append bypass the length havoc.
            self.synchronize_sidecar_vec_fields(destination, modified, true, acc);
            return;
        }
        let unknown_data = match stub {
            StubKind::VecClear | StubKind::VecTruncate => false,
            StubKind::VecInsert
            | StubKind::VecRemove
            | StubKind::VecRetain
            | StubKind::VecDedup
            | StubKind::VecDrain
            | StubKind::VecSplice
            | StubKind::VecExtendWith
            | StubKind::VecExtendTrusted => true,
            // Other handlers already write the complete aggregate. Rewriting
            // them here would give their outputs contradictory definitions.
            _ => return,
        };
        self.synchronize_sidecar_vec_fields(local, modified, unknown_data, acc);
    }

    pub(super) fn synchronize_sidecar_vec_fields(
        &mut self,
        local: Option<usize>,
        modified: &HashSet<usize>,
        unknown_data: bool,
        acc: &mut CallAccumulator<'_>,
    ) {
        if unknown_data {
            // Fresh contents alone do not model the original bounds/overflow,
            // callbacks, returned values or drop obligations. This UNLISTED
            // reason must remain fail-closed until those are implemented.
            self.record_sound_fallback_reason("vec_mutation_effects_unmodelled");
        }
        let Some(local) = local else {
            self.record_sound_fallback_reason("vec_mutation_state_local_unresolved");
            return;
        };
        let Some((ptr, old_len, old_cap, data)) = self.read_vec_fields(local, modified) else {
            self.record_sound_fallback_reason("vec_mutation_state_fields_unresolved");
            acc.dests.push(local);
            return;
        };
        let state = &self.collections.len_state;
        let wrote_len = state
            .get_len_var(local)
            .is_some_and(|name| state.modified_len_vars.contains(name.as_ref()));
        if !wrote_len {
            self.record_sound_fallback_reason("vec_mutation_state_length_unwritten");
        }
        let len = state.get_len_var(local).map_or(old_len, |name| {
            if state.modified_len_vars.contains(name.as_ref()) {
                Expr::var(out_name(name), ptr_sort())
            } else {
                self.collection_current_len(name)
            }
        });
        let cap = state.get_cap_var(local).map_or_else(
            || old_cap.clone(),
            |name| {
                if state.modified_cap_vars.contains(name.as_ref()) {
                    Expr::var(out_name(name), ptr_sort())
                } else {
                    old_cap.clone()
                }
            },
        );
        let data = if unknown_data {
            Havoc::mint(
                self,
                sound_havoc::UNTRACKED_COLLECTION_STATE,
                chc_fresh_name("vec_mutated_data"),
                data.sort().clone(),
            )
        } else {
            if !self.vec_mutation_elements_have_no_drop(local) {
                self.record_sound_fallback_reason("vec_mutation_drop_effects_unmodelled");
            }
            data
        };
        if !self.write_vec_fields(local, modified, |_, _, _, _| (ptr, len, cap, data), acc) {
            self.record_sound_fallback_reason("vec_mutation_state_fields_unwritten");
            acc.dests.push(local);
        }
    }

    fn vec_mutation_elements_have_no_drop(&self, local: usize) -> bool {
        let mut ty = self.resolve_body_ty(self.body.locals()[local].ty);
        for _ in 0..16 {
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => {
                    ty = self.resolve_body_ty(inner);
                }
                TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Vec" => {
                    return matches!(args.0.first(), Some(GenericArgKind::Type(elem))
                        if !rustc_internal::internal(self.tcx, self.resolve_body_ty(*elem))
                            .needs_drop(self.tcx, rustc_middle::ty::TypingEnv::fully_monomorphized()));
                }
                _ => return false,
            }
        }
        false
    }
}
