// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A proved full scalar/primitive-array store initializes precisely its native
//! byte range. This does not initialize padding, grant liveness, or bless any
//! unsupported RHS. The caller already checked the exact native allocation.

use super::ChcCtx;
use crate::codegen_ay::chc::shadow_mem_state::{
    SHMEM_OBJ, SHMEM_OFF, SHMEM_VAL, shadow_in, shadow_out,
};
use ay_bindings::{Expr, ExprValue};
use rustc_public::ty::Ty;

pub(super) fn shadow_output_bound(constraints: &[Expr]) -> bool {
    constraints.iter().any(|constraint|matches!(constraint.value(),ExprValue::Eq(lhs,_) if matches!(lhs.value(),ExprValue::Var{name} if name=="shmem_val__out")))
}

impl ChcCtx<'_, '_> {
    pub(super) fn native_init_shadow_write(
        &mut self,
        allocation: u32,
        payload: Ty,
        constraints: &mut Vec<Expr>,
    ) -> bool {
        if !self.uninit_checks {
            return true;
        }
        if !self.initialized_payload_shape(payload) {
            self.record_sound_fallback_reason("native_init_shadow_payload_unmodeled");
            return false;
        }
        if !self.shadow_mem_enabled() {
            self.record_sound_fallback_reason("native_init_shadow_state_unavailable");
            return false;
        }
        // Another shadow event in this statement block needs event-time
        // rebinding of every observer. Keep that order explicitly refused.
        if shadow_output_bound(constraints) {
            self.record_sound_fallback_reason("native_init_shadow_order_unmodeled");
            return false;
        }
        let Some(bytes) =
            self.get_type_size(payload).and_then(|n| u32::try_from(n).ok()).filter(|n| *n > 0)
        else {
            self.record_sound_fallback_reason("native_init_shadow_extent_unmodeled");
            return false;
        };
        let inside = shadow_in(SHMEM_OBJ)
            .eq(Expr::bitvec_const(allocation, 32))
            .and(shadow_in(SHMEM_OFF).bvult(Expr::bitvec_const(bytes, 32)));
        constraints.push(shadow_out(SHMEM_VAL).eq(Expr::ite(
            inside,
            Expr::bool_const(true),
            shadow_in(SHMEM_VAL),
        )));
        self.mark_shadow_mem_modified(&[SHMEM_VAL]);
        true
    }
}
