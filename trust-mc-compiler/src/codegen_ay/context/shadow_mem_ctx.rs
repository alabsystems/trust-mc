// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BMC-side scalar shadow-memory state (MEMUB-24/25/27, `-Z uninit-checks`).
//!
//! Mirrors the heap model's "current SSA expression" idiom: the mutable
//! shadow state lives on `AYCtx` (so it threads through mini-inlined callee
//! frames, which share the ctx), and every mutation declares a fresh SSA
//! variable bound to the updated expression.
//!
//! Semantics are Kani's scalar model (see `codegen_ay::shadow_mem`): one
//! nondeterministically tracked byte `(obj, off)` in the BMC stride model
//! (`obj = ptr / HEAP_STRIDE`, `off = ptr % HEAP_STRIDE`, both BV64) with an
//! init bit, plus the Load/StoreArgument buffer.

use ay_bindings::Expr;

use crate::codegen_ay::shadow_mem::ShadowMemExprs;
use crate::codegen_ay::types::{POINTER_WIDTH, bool_sort};

use super::AYCtx;

/// Current SSA expressions for the shadow-memory model. `None` until the
/// harness's injected `InitializeMemoryInitializationState` call runs.
#[derive(Debug, Clone, Default)]
pub(in crate::codegen_ay) struct BmcShadowMemState {
    /// Tracked byte's allocation id (BV64, stride model).
    pub(super) obj: Option<Expr>,
    /// Tracked byte's offset within the allocation (BV64).
    pub(super) off: Option<Expr>,
    /// Tracked byte's initialization bit (Bool).
    pub(super) val: Option<Expr>,
    /// Argument buffer occupancy (Bool).
    pub(super) ab_some: Option<Expr>,
    /// Argument buffer selected-argument index (BV64).
    pub(super) ab_sel: Option<Expr>,
    /// Argument buffer latched source address (BV64).
    pub(super) ab_addr: Option<Expr>,
}

impl<'tcx, 't> AYCtx<'tcx, 't> {
    /// (Re-)initialize the tracked byte: fresh nondet `(obj, off)`, value
    /// false. Encodes `InitializeMemoryInitializationState`. Also resets the
    /// argument buffer on first initialization only (Kani leaves it alone,
    /// but it starts `None` at program start).
    pub(in crate::codegen_ay) fn shadow_mem_initialize(&mut self) {
        let obj_name = self.fresh_name("shmem_obj");
        let obj = self.declare_var(&obj_name, crate::codegen_ay::types::ptr_sort());
        let off_name = self.fresh_name("shmem_off");
        let off = self.declare_var(&off_name, crate::codegen_ay::types::ptr_sort());
        self.shadow_mem.obj = Some(obj);
        self.shadow_mem.off = Some(off);
        self.shadow_mem.val = Some(Expr::bool_const(false));
        if self.shadow_mem.ab_some.is_none() {
            self.shadow_mem.ab_some = Some(Expr::bool_const(false));
            self.shadow_mem.ab_sel = Some(Expr::bitvec_const(0u64, POINTER_WIDTH));
            self.shadow_mem.ab_addr = Some(Expr::bitvec_const(0u64, POINTER_WIDTH));
        }
    }

    /// Current tracked-byte exprs, or `None` before initialization.
    pub(in crate::codegen_ay) fn shadow_mem_exprs(&self) -> Option<ShadowMemExprs> {
        Some(ShadowMemExprs {
            obj: self.shadow_mem.obj.clone()?,
            off: self.shadow_mem.off.clone()?,
            init: self.shadow_mem.val.clone()?,
        })
    }

    /// Current argument-buffer exprs `(some, sel, addr)`.
    pub(in crate::codegen_ay) fn shadow_mem_arg_buffer(&self) -> Option<(Expr, Expr, Expr)> {
        Some((
            self.shadow_mem.ab_some.clone()?,
            self.shadow_mem.ab_sel.clone()?,
            self.shadow_mem.ab_addr.clone()?,
        ))
    }

    /// Replace the tracked byte's init bit with `new_val` (SSA rebind).
    pub(in crate::codegen_ay) fn shadow_mem_update_val(&mut self, new_val: Expr) {
        let bound = self.declare_ssa_var_eq_expr("shmem_val", new_val);
        self.shadow_mem.val = Some(bound);
    }

    /// Replace the full tracked-byte state (used by copy/load retargeting).
    pub(in crate::codegen_ay) fn shadow_mem_update_state(&mut self, state: ShadowMemExprs) {
        let obj = self.declare_ssa_var_eq_expr("shmem_obj", state.obj);
        let off = self.declare_ssa_var_eq_expr("shmem_off", state.off);
        let val = self.declare_ssa_var_eq_expr("shmem_val", state.init);
        self.shadow_mem.obj = Some(obj);
        self.shadow_mem.off = Some(off);
        self.shadow_mem.val = Some(val);
    }

    /// Replace the argument buffer state (SSA rebind).
    pub(in crate::codegen_ay) fn shadow_mem_update_arg_buffer(
        &mut self,
        some: Expr,
        sel: Expr,
        addr: Expr,
    ) {
        let some = self.declare_ssa_var_eq_expr("shmem_ab_some", some);
        let sel = self.declare_ssa_var_eq_expr("shmem_ab_sel", sel);
        let addr = self.declare_ssa_var_eq_expr("shmem_ab_addr", addr);
        self.shadow_mem.ab_some = Some(some);
        self.shadow_mem.ab_sel = Some(sel);
        self.shadow_mem.ab_addr = Some(addr);
    }

    /// Fresh nondeterministic Bool (for `should_reset` / `should_store`).
    pub(in crate::codegen_ay) fn shadow_mem_nondet_bool(&mut self, prefix: &str) -> Expr {
        let name = self.fresh_name(prefix);
        self.declare_var(&name, bool_sort())
    }
}
