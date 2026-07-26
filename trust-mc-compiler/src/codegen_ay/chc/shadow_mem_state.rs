// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC state-variable plumbing for the scalar shadow-memory model
//! (MEMUB-24/25/27, `-Z uninit-checks`).
//!
//! Declares and threads six always-live state vars through every Horn
//! relation (mirroring the `obj_valid`/`obj_size` heap-metadata pattern):
//!
//! - `shmem_obj: BV32`, `shmem_off: BV32` — the nondeterministically tracked
//!   byte, in split-pointer coordinates (`pointer_object`/`pointer_offset`).
//! - `shmem_val: Bool` — the tracked byte's initialization state.
//! - `shmem_ab_some: Bool`, `shmem_ab_sel: BV32`, `shmem_ab_addr: BV64` — the
//!   `ARGUMENT_BUFFER` used by `Load/StoreArgument` to carry union
//!   initialization state across function boundaries.
//!
//! The expression-level semantics live in `crate::codegen_ay::shadow_mem`;
//! the call handlers in `call/codegen_call_kani_model_mem_init.rs`.

use ay_bindings::{Expr, Sort};

use crate::codegen_ay::types::{bool_sort, ptr_sort};

use super::ChcCtx;

pub(in crate::codegen_ay::chc) const SHMEM_OBJ: &str = "shmem_obj";
pub(in crate::codegen_ay::chc) const SHMEM_OFF: &str = "shmem_off";
pub(in crate::codegen_ay::chc) const SHMEM_VAL: &str = "shmem_val";
pub(in crate::codegen_ay::chc) const SHMEM_AB_SOME: &str = "shmem_ab_some";
pub(in crate::codegen_ay::chc) const SHMEM_AB_SEL: &str = "shmem_ab_sel";
pub(in crate::codegen_ay::chc) const SHMEM_AB_ADDR: &str = "shmem_ab_addr";

fn bv32_sort() -> Sort {
    Sort::bitvec(32)
}

/// `(in_name, out_name, sort)` for every shadow-memory state var, in
/// declaration order. Used by `collect_state_vars` and the liveness pass.
pub(in crate::codegen_ay::chc) const SHADOW_MEM_STATE_VARS: &[(&str, &str, fn() -> Sort)] = &[
    (SHMEM_OBJ, "shmem_obj__out", bv32_sort),
    (SHMEM_OFF, "shmem_off__out", bv32_sort),
    (SHMEM_VAL, "shmem_val__out", bool_sort),
    (SHMEM_AB_SOME, "shmem_ab_some__out", bool_sort),
    (SHMEM_AB_SEL, "shmem_ab_sel__out", bv32_sort),
    (SHMEM_AB_ADDR, "shmem_ab_addr__out", ptr_sort),
];

/// Input-side variable for a shadow state var.
pub(in crate::codegen_ay::chc) fn shadow_in(name: &str) -> Expr {
    let sort = SHADOW_MEM_STATE_VARS
        .iter()
        .find(|(n, _, _)| *n == name)
        .map(|(_, _, s)| s())
        .expect("known shadow mem state var");
    Expr::var(name, sort)
}

/// Output-side (`__out`) variable for a shadow state var.
pub(in crate::codegen_ay::chc) fn shadow_out(name: &str) -> Expr {
    let (out_name, sort) = SHADOW_MEM_STATE_VARS
        .iter()
        .find(|(n, _, _)| *n == name)
        .map(|(_, out, s)| (*out, s()))
        .expect("known shadow mem state var");
    Expr::var(out_name, sort)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Whether the shadow-memory state vars are declared in this context.
    pub(in crate::codegen_ay::chc) fn shadow_mem_enabled(&self) -> bool {
        self.uninit_checks
            && !self.int_lift
            && self.state_var_mgr.state_var_index_by_name(SHMEM_OBJ).is_some()
    }

    /// Marks `names` as modified so `build_output_args` emits their `__out`
    /// variables in the successor relation head.
    pub(in crate::codegen_ay::chc) fn mark_shadow_mem_modified(&mut self, names: &[&str]) {
        for name in names {
            if let Some(idx) = self.state_var_mgr.state_var_index_by_name(name) {
                self.mark_state_var_modified(idx);
            }
        }
    }

    // NOTE: the shadow state is deliberately NOT seeded in the entry rule.
    // Entry-rule constant seeds get const-propagated into relation apps and
    // the downstream closed-position pruning then strips the state slot
    // inconsistently (consumers of the in-var dangle as free vars). The
    // injected `InitializeMemoryInitializationState` call — always the
    // harness's first statement — is the semantic initializer instead: it
    // sets `shmem_val = false` and clears the argument buffer.
}
