// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BMC handlers for the `kani_core::mem_init` shadow-memory model calls
//! (MEMUB-24/25/27, `-Z uninit-checks`).
//!
//! Same scalar semantics as the CHC handlers
//! (`chc/call/codegen_call_kani_model_mem_init.rs`), expressed against the
//! ctx-level SSA shadow state (`context/shadow_mem_ctx.rs`) and the BMC
//! stride pointer model (`heap_pointer_object` / `heap_pointer_offset`).
//!
//! Untranslatable shapes fail closed: they record both a demoting unsupported
//! fallback and an explicit always-violated property. The existing shadow
//! state is preserved so an encoding gap can never bless uninitialized data.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Place};
use rustc_public::ty::GenericArgKind;
use tracing::{debug, warn};

use crate::codegen_ay::shadow_mem::{ShadowMemExprs, layout_mask_from_operand};
use crate::codegen_ay::shared::IntoOption;
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::kani_functions::KaniModel;

use super::StatementCodegen;

/// Split coordinates of a mem-init pointer argument (BV64 obj/off).
struct BmcMemInitPtr {
    obj: Expr,
    off: Expr,
    /// `Some(len)` when the operand was a fat slice/str pointer.
    fat_len: Option<Expr>,
}

fn requires_fat_ptr(model: KaniModel) -> bool {
    matches!(
        model,
        KaniModel::IsSlicePtrInitialized
            | KaniModel::IsStrPtrInitialized
            | KaniModel::SetSlicePtrInitialized
            | KaniModel::SetStrPtrInitialized
    )
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// `InitializeMemoryInitializationState`: fresh nondet tracked byte.
    pub(super) fn codegen_shadow_mem_initialize(&mut self) {
        if !self.ctx.config.uninit_checks {
            return;
        }
        self.ctx.shadow_mem_initialize();
        debug!("shadow_mem(bmc): initialized tracked byte");
    }

    /// `Is*PtrInitialized(...) -> bool`: bind destination to the real
    /// shadow predicate. An untranslatable predicate records an explicit
    /// fail-closed violation before returning the conservative legacy value.
    pub(super) fn codegen_shadow_mem_is(
        &mut self,
        model: KaniModel,
        args: &[Operand],
        destination: &Place,
    ) {
        let result = if self.ctx.config.uninit_checks {
            match self.shadow_mem_get_expr(model, args) {
                Some(result) => result,
                None => {
                    warn!(?model, "shadow_mem(bmc): Is* untranslatable — fail-closed");
                    self.fail_closed_shadow_mem(
                        "shadow_mem_is_untranslatable",
                        format!("{model:?}"),
                    );
                    Expr::bool_const(true)
                }
            }
        } else {
            Expr::bool_const(true)
        };
        self.bind_ssa_result(destination, result);
        debug!(?model, "shadow_mem(bmc): Is* encoded");
    }

    /// `Set*PtrInitialized(...)`: guarded update of the tracked byte.
    pub(super) fn codegen_shadow_mem_set(&mut self, model: KaniModel, args: &[Operand]) {
        if !self.ctx.config.uninit_checks {
            return;
        }
        let Some(state) = self.ctx.shadow_mem_exprs() else {
            // Set before harness init: nothing tracked yet.
            return;
        };
        let Some(new_val) = self.shadow_mem_set_expr(model, args, &state) else {
            warn!(?model, "shadow_mem(bmc): Set* untranslatable — fail-closed");
            self.fail_closed_shadow_mem("shadow_mem_set_untranslatable", format!("{model:?}"));
            return;
        };
        let guarded = self.shadow_mem_guard(new_val, state.init);
        self.ctx.shadow_mem_update_val(guarded);
        debug!(?model, "shadow_mem(bmc): Set* encoded");
    }

    /// `CopyInitState{,Single}(from, to[, num_elts])`.
    pub(super) fn codegen_shadow_mem_copy(
        &mut self,
        model: KaniModel,
        fn_args: &rustc_public::ty::GenericArgs,
        args: &[Operand],
    ) {
        if !self.ctx.config.uninit_checks {
            return;
        }
        let Some(state) = self.ctx.shadow_mem_exprs() else { return };
        let post = self.shadow_mem_copy_post(model, fn_args, args, &state);
        let Some(post) = post else {
            warn!(?model, "shadow_mem(bmc): Copy* untranslatable — fail-closed");
            self.fail_closed_shadow_mem("shadow_mem_copy_untranslatable", format!("{model:?}"));
            return;
        };
        let guarded = self.shadow_mem_guard_state(post, &state);
        self.ctx.shadow_mem_update_state(guarded);
        debug!(?model, "shadow_mem(bmc): Copy* encoded");
    }

    /// `StoreArgument(from, selected_argument)`.
    pub(super) fn codegen_shadow_mem_store_argument(&mut self, args: &[Operand]) {
        if !self.ctx.config.uninit_checks {
            return;
        }
        let Some((ab_some, ab_sel, ab_addr)) = self.ctx.shadow_mem_arg_buffer() else { return };
        let encoded = (|| {
            let from = self.shadow_mem_thin_ptr(args.first()?)?;
            let sel = self.shadow_mem_usize_operand(args.get(1)?)?;
            let should_store = self.ctx.shadow_mem_nondet_bool("shmem_ab_store");
            Some((
                Expr::ite(should_store.clone(), Expr::bool_const(true), ab_some.clone()),
                Expr::ite(should_store.clone(), sel, ab_sel.clone()),
                Expr::ite(should_store, from, ab_addr.clone()),
            ))
        })();
        let Some((new_some, new_sel, new_addr)) = encoded else {
            warn!("shadow_mem(bmc): StoreArgument untranslatable — fail-closed");
            self.fail_closed_shadow_mem(
                "shadow_mem_store_argument_untranslatable",
                "StoreArgument",
            );
            return;
        };
        let new_some = self.shadow_mem_guard(new_some, ab_some.clone());
        let new_sel = self.shadow_mem_guard(new_sel, ab_sel.clone());
        let new_addr = self.shadow_mem_guard(new_addr, ab_addr.clone());
        self.ctx.shadow_mem_update_arg_buffer(new_some, new_sel, new_addr);
        debug!("shadow_mem(bmc): StoreArgument encoded");
    }

    /// `LoadArgument(to, selected_argument)`.
    pub(super) fn codegen_shadow_mem_load_argument(
        &mut self,
        fn_args: &rustc_public::ty::GenericArgs,
        args: &[Operand],
    ) {
        if !self.ctx.config.uninit_checks {
            return;
        }
        let Some(state) = self.ctx.shadow_mem_exprs() else { return };
        let Some((ab_some, ab_sel, ab_addr)) = self.ctx.shadow_mem_arg_buffer() else { return };
        let encoded = (|| {
            let layout_size = shadow_mem_layout_size(fn_args)?.max(1);
            let to = self.shadow_mem_ptr(args.first()?)?;
            let sel = self.shadow_mem_usize_operand(args.get(1)?)?;
            let hit = ab_some.clone().and(ab_sel.clone().eq(sel));
            let elem_bytes = Expr::bitvec_const(layout_size as u128, POINTER_WIDTH);
            let from_obj = self.ctx.heap_pointer_object(ab_addr.clone());
            let from_off = self.ctx.heap_pointer_offset(ab_addr.clone());
            let should_reset = self.ctx.shadow_mem_nondet_bool("shmem_load_reset");
            let copied = state.copy_exprs(
                &from_obj,
                &from_off,
                &to.obj,
                &to.off,
                &elem_bytes,
                &elem_bytes,
                &should_reset,
            );
            let blessed = state.bless_expr(&to.obj, &to.off, &elem_bytes);
            Some((
                ShadowMemExprs {
                    obj: Expr::ite(hit.clone(), copied.obj, state.obj.clone()),
                    off: Expr::ite(hit.clone(), copied.off, state.off.clone()),
                    init: Expr::ite(hit.clone(), copied.init, blessed),
                },
                Expr::ite(hit, Expr::bool_const(false), ab_some.clone()),
            ))
        })();
        let Some((post, new_some)) = encoded else {
            warn!("shadow_mem(bmc): LoadArgument untranslatable — fail-closed");
            self.fail_closed_shadow_mem("shadow_mem_load_argument_untranslatable", "LoadArgument");
            return;
        };
        let post = self.shadow_mem_guard_state(post, &state);
        let new_some = self.shadow_mem_guard(new_some, ab_some);
        self.ctx.shadow_mem_update_state(post);
        self.ctx.shadow_mem_update_arg_buffer(new_some, ab_sel, ab_addr);
        debug!("shadow_mem(bmc): LoadArgument encoded");
    }

    // ---- helpers ----

    /// Register an encoding gap as both a demoting fallback and a reachable
    /// property failure. Callers leave the current shadow state unchanged.
    fn fail_closed_shadow_mem(&mut self, construct: &'static str, detail: impl Into<String>) {
        self.ctx.unsupported_with_fallback(construct, detail);
        self.record_violation_guarded(Expr::bool_const(true), "unsupported_shadow_memory");
    }

    /// Wrap an update in the current path condition: on untaken paths the
    /// previous value is preserved.
    fn shadow_mem_guard(&self, new_val: Expr, old_val: Expr) -> Expr {
        match &self.current_path_condition {
            None => new_val,
            Some(pc) => Expr::ite(pc.clone(), new_val, old_val),
        }
    }

    fn shadow_mem_guard_state(&self, post: ShadowMemExprs, old: &ShadowMemExprs) -> ShadowMemExprs {
        ShadowMemExprs {
            obj: self.shadow_mem_guard(post.obj, old.obj.clone()),
            off: self.shadow_mem_guard(post.off, old.off.clone()),
            init: self.shadow_mem_guard(post.init, old.init.clone()),
        }
    }

    /// UNRESOLVED address-vs-value guard — deliberately left standing.
    ///
    /// The `2 * POINTER_WIDTH` arm below reads bits 127..64 as `fat_len`, i.e.
    /// as the slice length that then scales every byte range this model checks
    /// (`shadow_mem_total_bytes`). That is the `PtrRepr::WidenedThin`
    /// fabrication by name: a thin pointer that `coerce_bitvec_width_safe`
    /// widened into a wide slot carries extension padding there, so the length
    /// would be a fabricated `0` and the byte range would collapse to nothing.
    ///
    /// It is NOT converted to `PtrRepr` here because refusing is not the safe
    /// direction at this call site. This module fails CLOSED (see the module
    /// doc): a `None` from here makes `shadow_mem_{get,set}_expr` record a
    /// demoting fallback *and* an always-violated property, so every harness
    /// that reaches this arm with a widened operand would flip to FAILED. That
    /// is a coverage change and has to be measured against the burndown, not
    /// smuggled into a retyping pass — the same reason `MaybeLoc::Unknown` is
    /// still permissive (`docs/addr-vs-value-conversion-queue.md` §4 item 10).
    /// The CHC twin `codegen_call_kani_model_mem_init.rs::mem_init_ptr` has the
    /// identical guard and the mirror-image problem (it fails OPEN, so refusing
    /// there blesses the byte instead).
    fn shadow_mem_ptr(&mut self, op: &Operand) -> Option<BmcMemInitPtr> {
        let expr = self.codegen_operand(op)?;
        let (data, fat_len) = match expr.sort().bitvec_width()? {
            w if w == POINTER_WIDTH => (expr, None),
            w if w == 2 * POINTER_WIDTH => {
                let data = expr.clone().extract(POINTER_WIDTH - 1, 0);
                let len = expr.extract(2 * POINTER_WIDTH - 1, POINTER_WIDTH);
                (data, Some(len))
            }
            _ => return None,
        };
        Some(BmcMemInitPtr {
            obj: self.ctx.heap_pointer_object(data.clone()),
            off: self.ctx.heap_pointer_offset(data),
            fat_len,
        })
    }

    fn shadow_mem_thin_ptr(&mut self, op: &Operand) -> Option<Expr> {
        let expr = self.codegen_operand(op)?;
        match expr.sort().bitvec_width()? {
            w if w == POINTER_WIDTH => Some(expr),
            w if w == 2 * POINTER_WIDTH => Some(expr.extract(POINTER_WIDTH - 1, 0)),
            _ => None,
        }
    }

    fn shadow_mem_usize_operand(&mut self, op: &Operand) -> Option<Expr> {
        let expr = self.codegen_operand(op)?;
        let width = expr.sort().bitvec_width()?;
        Some(if width == POINTER_WIDTH {
            expr
        } else if width < POINTER_WIDTH {
            expr.zero_extend(POINTER_WIDTH - width)
        } else {
            expr.extract(POINTER_WIDTH - 1, 0)
        })
    }

    fn shadow_mem_bool_operand(&mut self, op: &Operand) -> Option<Expr> {
        let expr = self.codegen_operand(op)?;
        if expr.sort().is_bool() {
            Some(expr)
        } else {
            let width = expr.sort().bitvec_width()?;
            Some(expr.eq(Expr::bitvec_const(0u64, width)).not())
        }
    }

    fn shadow_mem_total_bytes(
        &mut self,
        ptr: &BmcMemInitPtr,
        mask_len: usize,
        num_elts_op: Option<&Operand>,
    ) -> Option<Expr> {
        let n = Expr::bitvec_const(mask_len as u128, POINTER_WIDTH);
        let elts = if let Some(len) = &ptr.fat_len {
            Some(len.clone())
        } else if let Some(op) = num_elts_op {
            Some(self.shadow_mem_usize_operand(op)?)
        } else {
            None
        };
        Some(match elts {
            Some(elts) => n.bvmul(elts),
            None => n,
        })
    }

    fn shadow_mem_get_expr(&mut self, model: KaniModel, args: &[Operand]) -> Option<Expr> {
        let state = self.ctx.shadow_mem_exprs()?;
        let ptr = self.shadow_mem_ptr(args.first()?)?;
        if requires_fat_ptr(model) && ptr.fat_len.is_none() {
            return None;
        }
        let mask = layout_mask_from_operand(self.body, args.get(1)?)?;
        if mask.is_empty() {
            return Some(Expr::bool_const(true));
        }
        let num_elts_op = if matches!(model, KaniModel::IsSliceChunkPtrInitialized) {
            Some(args.get(2)?)
        } else {
            None
        };
        let multi_elt = ptr.fat_len.is_some() || num_elts_op.is_some();
        let total = self.shadow_mem_total_bytes(&ptr, mask.len(), num_elts_op)?;
        Some(state.get_expr(&ptr.obj, &ptr.off, &mask, &total, multi_elt))
    }

    fn shadow_mem_set_expr(
        &mut self,
        model: KaniModel,
        args: &[Operand],
        state: &ShadowMemExprs,
    ) -> Option<Expr> {
        let ptr = self.shadow_mem_ptr(args.first()?)?;
        if requires_fat_ptr(model) && ptr.fat_len.is_none() {
            return None;
        }
        let mask = layout_mask_from_operand(self.body, args.get(1)?)?;
        if mask.is_empty() {
            return Some(state.init.clone());
        }
        let num_elts_op = if matches!(model, KaniModel::SetSliceChunkPtrInitialized) {
            Some(args.get(2)?)
        } else {
            None
        };
        let value = self.shadow_mem_bool_operand(args.last()?)?;
        let multi_elt = ptr.fat_len.is_some() || num_elts_op.is_some();
        let total = self.shadow_mem_total_bytes(&ptr, mask.len(), num_elts_op)?;
        Some(state.set_expr(&ptr.obj, &ptr.off, &mask, &total, multi_elt, &value))
    }

    fn shadow_mem_copy_post(
        &mut self,
        model: KaniModel,
        fn_args: &rustc_public::ty::GenericArgs,
        args: &[Operand],
        state: &ShadowMemExprs,
    ) -> Option<ShadowMemExprs> {
        let layout_size = shadow_mem_layout_size(fn_args)?;
        if layout_size == 0 {
            return Some(state.clone());
        }
        let from = self.shadow_mem_ptr(args.first()?)?;
        let to = self.shadow_mem_ptr(args.get(1)?)?;
        let elem_bytes = Expr::bitvec_const(layout_size as u128, POINTER_WIDTH);
        let total = if matches!(model, KaniModel::CopyInitState) {
            let elts = self.shadow_mem_usize_operand(args.get(2)?)?;
            elem_bytes.clone().bvmul(elts)
        } else {
            elem_bytes.clone()
        };
        let should_reset = self.ctx.shadow_mem_nondet_bool("shmem_copy_reset");
        Some(state.copy_exprs(
            &from.obj,
            &from.off,
            &to.obj,
            &to.off,
            &total,
            &elem_bytes,
            &should_reset,
        ))
    }
}

/// `LAYOUT_SIZE` const generic (arg 0) of a mem-init model instance.
fn shadow_mem_layout_size(fn_args: &rustc_public::ty::GenericArgs) -> Option<u64> {
    if let Some(GenericArgKind::Const(size_const)) = fn_args.0.first().cloned() {
        size_const.eval_target_usize().into_option()
    } else {
        None
    }
}
