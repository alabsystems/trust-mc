// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC handlers for the `kani_core::mem_init` shadow-memory model calls
//! (MEMUB-24/25/27, `-Z uninit-checks`).
//!
//! Encodes Kani's scalar shadow state — one nondeterministically tracked
//! byte `(shmem_obj, shmem_off)` with init bit `shmem_val`, plus the
//! `ARGUMENT_BUFFER` triple — as guarded updates over the state vars
//! declared in `shadow_mem_state.rs`:
//!
//! - `Is*PtrInitialized`   → destination bound to the real `get` predicate.
//! - `Set*PtrInitialized`  → `shmem_val__out = ite(in_range, mask && v, shmem_val)`.
//! - `CopyInitState*`      → nondet retarget of the tracked byte (Kani `copy`).
//! - `Load/StoreArgument`  → argument-buffer transfer (Kani semantics).
//! - `InitializeMemoryInitializationState` → fresh nondet tracked byte, uninit.
//!
//! Fail-open policy: any shape the scalar model cannot represent degrades to
//! the pre-MEMUB behavior — reads return `true`, writes bless the tracked
//! byte (`shmem_val__out = true`). That can only hide bugs, never introduce
//! false failures on currently-passing harnesses.

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::shadow_mem::{ShadowMemExprs, layout_mask_from_operand};
use crate::codegen_ay::shared::IntoOption;
use crate::codegen_ay::types::{SignExtension, bool_sort, coerce_bitvec_width_safe};

use super::super::shadow_mem_state::{
    SHMEM_AB_ADDR, SHMEM_AB_SEL, SHMEM_AB_SOME, SHMEM_OBJ, SHMEM_OFF, SHMEM_VAL, shadow_in,
    shadow_out,
};
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use super::{ChcCtx, KaniModel, chc_fresh_name, declare_pending_var};

/// Raw-alloc route: whether `path` names the REFERENCE-FORMING
/// `slice::from_raw_parts{,_mut}` itself (which reads all `len` elements via
/// `&*` and therefore needs the uninit-formation check) — and not one of its
/// nested helpers (`::precondition_check` — a pure pointer-value predicate)
/// or the raw-pointer constructors (`ptr::slice_from_raw_parts`,
/// `ptr::from_raw_parts` — no read).
pub(in crate::codegen_ay::chc) fn is_slice_from_raw_parts_ref_former(path: &str) -> bool {
    path.contains("slice::from_raw_parts") && !path.contains("precondition_check")
}

/// Whether the model variant's pointer argument must be a fat pointer for the
/// accessed range to be known (slice/str variants without an explicit count).
fn mem_init_requires_fat_ptr(kani_model: KaniModel) -> bool {
    matches!(
        kani_model,
        KaniModel::IsSlicePtrInitialized
            | KaniModel::IsStrPtrInitialized
            | KaniModel::SetSlicePtrInitialized
            | KaniModel::SetStrPtrInitialized
    )
}

/// Split-pointer coordinates of a mem-init pointer argument, plus the
/// element count carried by fat (slice/str) pointers.
struct MemInitPtr {
    obj: Expr,
    off: Expr,
    /// `Some(len)` for fat `*const [T]` / `*const str` pointers (BV32).
    fat_len: Option<Expr>,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Entry point: encode one mem-init model call. Returns `true` when the
    /// call was fully handled (a goto/diverge was emitted).
    pub(in crate::codegen_ay::chc) fn codegen_mem_init_model(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        kani_model: KaniModel,
    ) {
        let Some(target) = dcx.target else {
            self.record_diverging_call_drop(
                dcx.func,
                Some(dcx.bb_idx),
                "kani_model::mem_init",
                None,
            );
            return;
        };
        let target = *target;

        if !self.shadow_mem_enabled() {
            // State vars absent (int-lift or flag off): keep legacy behavior.
            match kani_model {
                KaniModel::IsPtrInitialized
                | KaniModel::IsStrPtrInitialized
                | KaniModel::IsSliceChunkPtrInitialized
                | KaniModel::IsSlicePtrInitialized => {
                    // Missed-bug D fix (site #1): the shadow-memory model is off
                    // (int-lift, or the uninit flag disabled) so there is no state
                    // to consult — binding `is_init` to concrete `true` is a
                    // fail-OPEN under-approximation (a genuinely-uninitialized read
                    // would be vacuously proved SUCCESSFUL). Book a fail-close
                    // sound-fallback so a harness that reaches this bypass and
                    // otherwise proves is demoted to Unknown via harness_runner
                    // Step C (sound_fallback_count > 0), mirroring the shadow-model
                    // None-paths below (state_idx_missing_mem_init_is, etc.).
                    self.record_sound_fallback_reason("shadow_mem_disabled_is_ptr_init");
                    self.emit_dest_constrained_to_true(dcx, "Is*PtrInitialized");
                }
                _ => {
                    let args =
                        self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
                    self.emit_goto_rule(dcx.from_app, target, &args, dcx.stmt_constraints);
                }
            }
            return;
        }

        match kani_model {
            KaniModel::InitializeMemoryInitializationState => {
                // Fresh nondet tracked byte; value = false. Marking obj/off
                // modified without constraining their __out vars leaves them
                // universally quantified — exactly Kani's `any()`. The
                // argument buffer is cleared here too (this call is the
                // harness's first statement, standing in for program start —
                // the shadow state is intentionally not seeded in the entry
                // rule, see shadow_mem_state.rs).
                self.mark_shadow_mem_modified(&[SHMEM_OBJ, SHMEM_OFF, SHMEM_VAL, SHMEM_AB_SOME]);
                let args = self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
                let extra = [
                    shadow_out(SHMEM_VAL).eq(Expr::bool_const(false)),
                    shadow_out(SHMEM_AB_SOME).eq(Expr::bool_const(false)),
                ];
                self.emit_goto_rule_extra(dcx.from_app, target, &args, dcx.stmt_constraints, extra);
                debug!("mem_init: InitializeMemoryInitializationState encoded");
            }
            KaniModel::IsPtrInitialized
            | KaniModel::IsStrPtrInitialized
            | KaniModel::IsSliceChunkPtrInitialized
            | KaniModel::IsSlicePtrInitialized => {
                self.codegen_mem_init_is(dcx, kani_model, target);
            }
            KaniModel::SetPtrInitialized
            | KaniModel::SetStrPtrInitialized
            | KaniModel::SetSliceChunkPtrInitialized
            | KaniModel::SetSlicePtrInitialized => {
                self.codegen_mem_init_set(dcx, kani_model, target);
            }
            KaniModel::CopyInitState | KaniModel::CopyInitStateSingle => {
                self.codegen_mem_init_copy(dcx, kani_model, target);
            }
            KaniModel::StoreArgument => self.codegen_mem_init_store_argument(dcx, target),
            KaniModel::LoadArgument => self.codegen_mem_init_load_argument(dcx, target),
            _ => unreachable!("codegen_mem_init_model called with non-mem-init model"),
        }
    }

    /// Shadow-memory effect of an allocator stub (MEMUB-24/25/27).
    ///
    /// The `check_uninit` instrumentation attaches its alloc-family
    /// `Set*PtrInitialized` calls inside `std::alloc` bodies, which the CHC
    /// backend replaces with stubs — so the shadow effect must be applied at
    /// the stub itself: fresh (`__rust_alloc`) and reallocated
    /// (`__rust_realloc`) objects are uninitialized, zeroed allocations and
    /// `Box::new` payloads are initialized (matching `assign_analysis.rs`).
    /// Unknown shapes bless the tracked byte (fail-open).
    pub(in crate::codegen_ay::chc) fn append_alloc_shadow_constraints(
        &mut self,
        stub: crate::codegen_ay::stubs::StubKind,
        alloc_obj_id: Option<u32>,
        extra_constraints: &mut Vec<Expr>,
    ) {
        use crate::codegen_ay::stubs::StubKind;
        if !self.shadow_mem_enabled() {
            return;
        }
        let init_bit = match stub {
            StubKind::RustAlloc | StubKind::RustRealloc => false,
            StubKind::RustAllocZeroed | StubKind::BoxNew => true,
            // Dealloc/layout queries don't touch initialization state.
            _ => return,
        };
        let new_val = match alloc_obj_id {
            Some(id) => Expr::ite(
                shadow_in(SHMEM_OBJ).eq(Expr::bitvec_const(id as u64, 32)),
                Expr::bool_const(init_bit),
                shadow_in(SHMEM_VAL),
            ),
            // Object id unknown: fail-open (bless the tracked byte).
            None => Expr::bool_const(true),
        };
        self.mark_shadow_mem_modified(&[SHMEM_VAL]);
        extra_constraints.push(shadow_out(SHMEM_VAL).eq(new_val));
        debug!(?stub, ?alloc_obj_id, init_bit, "mem_init: alloc stub shadow update");
    }

    fn shadow_state_in(&self) -> ShadowMemExprs {
        ShadowMemExprs {
            obj: shadow_in(SHMEM_OBJ),
            off: shadow_in(SHMEM_OFF),
            init: shadow_in(SHMEM_VAL),
        }
    }

    /// Raw-alloc route: Kani semantics for `slice::from_raw_parts{,_mut}`
    /// under `-Z uninit-checks` — forming the `&[T]` reference reads the
    /// whole `*const [T]` place (`&*slice_from_raw_parts(data, len)`), so
    /// all `len * size_of::<T>()` bytes at `data` must be initialized.
    /// Kani's instrumentation attaches `IsSlicePtrInitialized` to that deref
    /// INSIDE the stdlib body, which trust-mc replaces with a model — so the
    /// check must be emitted at the call site, mirroring the alloc-stub
    /// shadow effect (`append_alloc_shadow_constraints`).
    ///
    /// Fail-closed: any untranslatable shape records a sound-fallback demotion
    /// (never a silent skip) — a PROOF must not rest on an uninit-formation
    /// check we never emitted. Restricted to padding-free scalar element
    /// types (the all-true layout mask); other element types demote.
    pub(in crate::codegen_ay::chc) fn emit_slice_from_raw_parts_uninit_check(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        data_ptr: &Expr,
        len: &Expr,
    ) {
        if !self.uninit_checks {
            return;
        }
        if !self.shadow_mem_enabled() {
            // No shadow state to consult (int-lift): same fail-close as the
            // Is*PtrInitialized bypass above.
            self.record_sound_fallback_reason("shadow_mem_disabled_from_raw_parts");
            return;
        }
        let elem_size = self
            .body
            .locals()
            .get(dcx.destination.local)
            .map(|decl| self.resolve_body_ty(decl.ty))
            .and_then(Self::deref_pointee_ty)
            .and_then(|pointee| match pointee.kind() {
                TyKind::RigidTy(RigidTy::Slice(elem)) => Some(elem),
                _ => None,
            })
            .and_then(|elem| self.padding_free_scalar_size(elem));
        let Some(elem_size) = elem_size else {
            self.record_sound_fallback_reason("from_raw_parts_uninit_shape_untranslatable");
            warn!(
                fn_name = %self.fn_name,
                "mem_init: slice::from_raw_parts element shape untranslatable — \
                 uninit-formation check not emitted (demoted)"
            );
            return;
        };
        if elem_size == 0 {
            // ZST elements carry no bytes — trivially initialized.
            return;
        }
        let data = match data_ptr.sort().bitvec_width() {
            Some(64) => data_ptr.clone(),
            // Fat value: concat(len, data) — data in the low lane.
            Some(128) => data_ptr.clone().extract(63, 0),
            _ => {
                self.record_sound_fallback_reason("from_raw_parts_uninit_ptr_untranslatable");
                return;
            }
        };
        let (Some((obj, off)), len32) = (
            self.split_pointer(&data),
            coerce_bitvec_width_safe(len.clone(), 32, SignExtension::ZeroExtend),
        ) else {
            self.record_sound_fallback_reason("from_raw_parts_uninit_ptr_untranslatable");
            return;
        };
        if len32.sort().bitvec_width() != Some(32) {
            self.record_sound_fallback_reason("from_raw_parts_uninit_len_untranslatable");
            return;
        }
        let total = Expr::bitvec_const(elem_size as u64, 32).bvmul(len32);
        // All-true single-byte mask: for padding-free scalars every byte is a
        // data byte, so `get_expr` reduces to `!in_range || tracked_init`.
        let check = self.shadow_state_in().get_expr(&obj, &off, &[true], &total, true);
        self.emit_error_rule_for_condition(dcx.from_app, check, dcx.stmt_constraints, dcx.bb_idx);
        debug!(
            fn_name = %self.fn_name,
            elem_size, "mem_init: slice::from_raw_parts uninit-formation check emitted"
        );
    }

    /// Size of a padding-free scalar type (every byte is a data byte), the
    /// only shapes whose from_raw_parts layout mask is all-true by
    /// construction. `None` for everything else (callers fail closed).
    fn padding_free_scalar_size(&self, ty: rustc_public::ty::Ty) -> Option<u64> {
        let ty = self.resolve_body_ty(ty);
        match ty.kind() {
            TyKind::RigidTy(
                RigidTy::Bool
                | RigidTy::Char
                | RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_)
                | RigidTy::RawPtr(..),
            ) => self.get_type_size(ty).map(|s| s as u64),
            _ => None,
        }
    }

    /// Translate and split a mem-init pointer operand.
    fn mem_init_ptr(&mut self, dcx: &DispatchCallContext<'_>, op: &Operand) -> Option<MemInitPtr> {
        let expr = self.translate_operand_with_modified(op, dcx.modified_locals)?;
        match expr.sort().bitvec_width()? {
            64 => {
                let (obj, off) = self.split_pointer(&expr)?;
                Some(MemInitPtr { obj, off, fat_len: None })
            }
            128 => {
                // Fat pointer: concat(len:BV64, data:BV64).
                let data = expr.clone().extract(63, 0);
                let len64 = expr.extract(127, 64);
                let (obj, off) = self.split_pointer(&data)?;
                let len32 = coerce_bitvec_width_safe(len64, 32, SignExtension::ZeroExtend);
                len32.sort().bitvec_width()?;
                Some(MemInitPtr { obj, off, fat_len: Some(len32) })
            }
            _ => None,
        }
    }

    /// Total byte length of the accessed range: `mask.len() * num_elts`.
    ///
    /// `num_elts` comes from (in priority order) the fat-pointer metadata, the
    /// explicit `num_elts` operand (SliceChunk variants), or 1.
    fn mem_init_total_bytes(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        ptr: &MemInitPtr,
        mask_len: usize,
        num_elts_op: Option<&Operand>,
    ) -> Option<Expr> {
        let n = Expr::bitvec_const(mask_len as u64, 32);
        let elts = if let Some(len) = &ptr.fat_len {
            Some(len.clone())
        } else if let Some(op) = num_elts_op {
            let expr = self.translate_operand_with_modified(op, dcx.modified_locals)?;
            let expr = coerce_bitvec_width_safe(expr, 32, SignExtension::ZeroExtend);
            expr.sort().bitvec_width()?;
            Some(expr)
        } else {
            None
        };
        Some(match elts {
            Some(elts) => n.bvmul(elts),
            None => n,
        })
    }

    /// Coerce a `bool`-typed MIR operand to a Bool expr.
    fn mem_init_bool_operand(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        op: &Operand,
    ) -> Option<Expr> {
        let expr = self.translate_operand_with_modified(op, dcx.modified_locals)?;
        if expr.sort().is_bool() {
            Some(expr)
        } else {
            let width = expr.sort().bitvec_width()?;
            Some(expr.eq(Expr::bitvec_const(0u64, width)).not())
        }
    }

    /// `LAYOUT_SIZE` const generic of the resolved model instance (arg 0).
    fn mem_init_layout_size(&self, func: &Operand) -> Option<u64> {
        let func_ty = func.ty(self.body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::FnDef(_, fn_args)) = func_ty.kind() else {
            return None;
        };
        if let Some(GenericArgKind::Const(size_const)) = fn_args.0.first().cloned() {
            size_const.eval_target_usize().into_option()
        } else {
            None
        }
    }

    /// `Is*PtrInitialized(ptr, layout[, num_elts]) -> bool`.
    fn codegen_mem_init_is(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        kani_model: KaniModel,
        target: usize,
    ) {
        let result = self.mem_init_get_expr(dcx, kani_model);
        let Some(result) = result else {
            self.record_sound_fallback_reason("shadow_mem_is_untranslatable");
            warn!(?kani_model, "mem_init: Is* shape untranslatable — fail-open (true)");
            self.emit_dest_constrained_to_true(dcx, "Is*PtrInitialized(fail-open)");
            return;
        };

        let dest_local = dcx.destination.local;
        let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
            self.record_sound_fallback_reason("state_idx_missing_mem_init_is");
            self.emit_dest_constrained_to_true(dcx, "Is*PtrInitialized(no-state-idx)");
            return;
        };
        let args = self.build_output_args(dcx.modified_locals, &[dest_local]);
        let out_sort = self.state_var_mgr.output_state_vars[dest_vec_idx].1.clone();
        let dest_var =
            Expr::var(&*self.state_var_mgr.output_state_vars[dest_vec_idx].0, out_sort.clone());
        let eq = self.make_coerced_eq_constraint(
            &dest_var,
            result,
            &out_sort,
            dest_local,
            "kani_model::mem_init::is",
        );
        self.emit_goto_rule_extra(dcx.from_app, target, &args, dcx.stmt_constraints, eq);
        debug!(?kani_model, "mem_init: Is* encoded as real shadow predicate");
    }

    fn mem_init_get_expr(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        kani_model: KaniModel,
    ) -> Option<Expr> {
        let ptr = self.mem_init_ptr(dcx, dcx.args.first()?)?;
        if mem_init_requires_fat_ptr(kani_model) && ptr.fat_len.is_none() {
            return None;
        }
        let mask = layout_mask_from_operand(self.body, dcx.args.get(1)?)?;
        if mask.is_empty() {
            // LAYOUT_SIZE == 0: the library short-circuits to `true`.
            return Some(Expr::bool_const(true));
        }
        let num_elts_op = if matches!(kani_model, KaniModel::IsSliceChunkPtrInitialized) {
            Some(dcx.args.get(2)?)
        } else {
            None
        };
        let multi_elt = ptr.fat_len.is_some() || num_elts_op.is_some();
        let total = self.mem_init_total_bytes(dcx, &ptr, mask.len(), num_elts_op)?;
        Some(self.shadow_state_in().get_expr(&ptr.obj, &ptr.off, &mask, &total, multi_elt))
    }

    /// `Set*PtrInitialized(ptr, layout[, num_elts], value)`.
    fn codegen_mem_init_set(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        kani_model: KaniModel,
        target: usize,
    ) {
        let new_val = self.mem_init_set_expr(dcx, kani_model);
        let new_val = new_val.unwrap_or_else(|| {
            // Fail-open: bless the tracked byte so later reads cannot
            // produce false failures.
            self.record_sound_fallback_reason("shadow_mem_set_untranslatable");
            warn!(?kani_model, "mem_init: Set* shape untranslatable — fail-open (bless)");
            Expr::bool_const(true)
        });
        self.emit_shadow_val_update(dcx, target, new_val);
        debug!(?kani_model, "mem_init: Set* encoded as guarded shadow update");
    }

    fn mem_init_set_expr(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        kani_model: KaniModel,
    ) -> Option<Expr> {
        let ptr = self.mem_init_ptr(dcx, dcx.args.first()?)?;
        if mem_init_requires_fat_ptr(kani_model) && ptr.fat_len.is_none() {
            return None;
        }
        let mask = layout_mask_from_operand(self.body, dcx.args.get(1)?)?;
        if mask.is_empty() {
            return Some(shadow_in(SHMEM_VAL));
        }
        let num_elts_op = if matches!(kani_model, KaniModel::SetSliceChunkPtrInitialized) {
            Some(dcx.args.get(2)?)
        } else {
            None
        };
        let value_op = dcx.args.last()?;
        let value = self.mem_init_bool_operand(dcx, value_op)?;
        let multi_elt = ptr.fat_len.is_some() || num_elts_op.is_some();
        let total = self.mem_init_total_bytes(dcx, &ptr, mask.len(), num_elts_op)?;
        Some(self.shadow_state_in().set_expr(&ptr.obj, &ptr.off, &mask, &total, multi_elt, &value))
    }

    /// Emit the successor rule with `shmem_val__out == new_val`.
    fn emit_shadow_val_update(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        new_val: Expr,
    ) {
        self.mark_shadow_mem_modified(&[SHMEM_VAL]);
        let args = self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
        let extra = [shadow_out(SHMEM_VAL).eq(new_val)];
        self.emit_goto_rule_extra(dcx.from_app, target, &args, dcx.stmt_constraints, extra);
    }

    /// `CopyInitState{,Single}(from, to[, num_elts])`.
    fn codegen_mem_init_copy(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        kani_model: KaniModel,
        target: usize,
    ) {
        let post = self.mem_init_copy_post(dcx, kani_model);
        let Some(post) = post else {
            self.record_sound_fallback_reason("shadow_mem_copy_untranslatable");
            warn!(?kani_model, "mem_init: Copy* shape untranslatable — fail-open (bless)");
            self.emit_shadow_val_update(dcx, target, Expr::bool_const(true));
            return;
        };
        self.mark_shadow_mem_modified(&[SHMEM_OBJ, SHMEM_OFF, SHMEM_VAL]);
        let args = self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
        let extra = [
            shadow_out(SHMEM_OBJ).eq(post.obj),
            shadow_out(SHMEM_OFF).eq(post.off),
            shadow_out(SHMEM_VAL).eq(post.init),
        ];
        self.emit_goto_rule_extra(dcx.from_app, target, &args, dcx.stmt_constraints, extra);
        debug!(?kani_model, "mem_init: Copy* encoded as nondet retarget");
    }

    fn mem_init_copy_post(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        kani_model: KaniModel,
    ) -> Option<ShadowMemExprs> {
        let layout_size = self.mem_init_layout_size(dcx.func)?;
        if layout_size == 0 {
            return Some(self.shadow_state_in());
        }
        let from = self.mem_init_ptr(dcx, dcx.args.first()?)?;
        let to = self.mem_init_ptr(dcx, dcx.args.get(1)?)?;
        let elem_bytes = Expr::bitvec_const(layout_size, 32);
        let total = if matches!(kani_model, KaniModel::CopyInitState) {
            let elts =
                self.translate_operand_with_modified(dcx.args.get(2)?, dcx.modified_locals)?;
            let elts = coerce_bitvec_width_safe(elts, 32, SignExtension::ZeroExtend);
            elts.sort().bitvec_width()?;
            elem_bytes.clone().bvmul(elts)
        } else {
            elem_bytes.clone()
        };
        let should_reset = declare_pending_var(chc_fresh_name("shmem_copy_reset"), bool_sort());
        Some(self.shadow_state_in().copy_exprs(
            &from.obj,
            &from.off,
            &to.obj,
            &to.off,
            &total,
            &elem_bytes,
            &should_reset,
        ))
    }

    /// `StoreArgument(from, selected_argument)`: nondeterministically latch
    /// the source address into the argument buffer.
    fn codegen_mem_init_store_argument(&mut self, dcx: &DispatchCallContext<'_>, target: usize) {
        let encoded = self.mem_init_store_argument_extra(dcx);
        let Some(extra) = encoded else {
            // Fail-open: an unencodable store leaves the buffer unusable, so
            // clear it AND bless the tracked byte (the matching LoadArgument
            // would otherwise re-check bytes we no longer track faithfully).
            self.record_sound_fallback_reason("shadow_mem_store_arg_untranslatable");
            warn!("mem_init: StoreArgument untranslatable — fail-open");
            self.mark_shadow_mem_modified(&[SHMEM_VAL, SHMEM_AB_SOME]);
            let args = self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
            let extra = [
                shadow_out(SHMEM_VAL).eq(Expr::bool_const(true)),
                shadow_out(SHMEM_AB_SOME).eq(Expr::bool_const(false)),
            ];
            self.emit_goto_rule_extra(dcx.from_app, target, &args, dcx.stmt_constraints, extra);
            return;
        };
        self.mark_shadow_mem_modified(&[SHMEM_AB_SOME, SHMEM_AB_SEL, SHMEM_AB_ADDR]);
        let args = self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
        self.emit_goto_rule_extra(dcx.from_app, target, &args, dcx.stmt_constraints, extra);
        debug!("mem_init: StoreArgument encoded (nondet latch)");
    }

    fn mem_init_store_argument_extra(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<[Expr; 3]> {
        let from = self.translate_operand_with_modified(dcx.args.first()?, dcx.modified_locals)?;
        // Thin data pointer only (unions are Sized).
        let from = match from.sort().bitvec_width()? {
            64 => from,
            128 => from.extract(63, 0),
            _ => return None,
        };
        let sel = self.translate_operand_with_modified(dcx.args.get(1)?, dcx.modified_locals)?;
        let sel = coerce_bitvec_width_safe(sel, 32, SignExtension::ZeroExtend);
        sel.sort().bitvec_width()?;
        let should_store = declare_pending_var(chc_fresh_name("shmem_ab_store"), bool_sort());
        Some([
            shadow_out(SHMEM_AB_SOME).eq(Expr::ite(
                should_store.clone(),
                Expr::bool_const(true),
                shadow_in(SHMEM_AB_SOME),
            )),
            shadow_out(SHMEM_AB_SEL).eq(Expr::ite(
                should_store.clone(),
                sel,
                shadow_in(SHMEM_AB_SEL),
            )),
            shadow_out(SHMEM_AB_ADDR).eq(Expr::ite(should_store, from, shadow_in(SHMEM_AB_ADDR))),
        ])
    }

    /// `LoadArgument(to, selected_argument)`: on a buffer hit, transfer init
    /// state from the latched address (copy-single semantics) and clear the
    /// buffer; otherwise bless the destination (checked via another branch).
    fn codegen_mem_init_load_argument(&mut self, dcx: &DispatchCallContext<'_>, target: usize) {
        let encoded = self.mem_init_load_argument_extra(dcx);
        let Some(extra) = encoded else {
            self.record_sound_fallback_reason("shadow_mem_load_arg_untranslatable");
            warn!("mem_init: LoadArgument untranslatable — fail-open (bless)");
            self.mark_shadow_mem_modified(&[SHMEM_VAL, SHMEM_AB_SOME]);
            let args = self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
            let extra = [
                shadow_out(SHMEM_VAL).eq(Expr::bool_const(true)),
                shadow_out(SHMEM_AB_SOME).eq(Expr::bool_const(false)),
            ];
            self.emit_goto_rule_extra(dcx.from_app, target, &args, dcx.stmt_constraints, extra);
            return;
        };
        self.mark_shadow_mem_modified(&[SHMEM_OBJ, SHMEM_OFF, SHMEM_VAL, SHMEM_AB_SOME]);
        let args = self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
        self.emit_goto_rule_extra(dcx.from_app, target, &args, dcx.stmt_constraints, extra);
        debug!("mem_init: LoadArgument encoded (buffer transfer)");
    }

    fn mem_init_load_argument_extra(&mut self, dcx: &DispatchCallContext<'_>) -> Option<[Expr; 4]> {
        let layout_size = self.mem_init_layout_size(dcx.func)?;
        let to = self.mem_init_ptr(dcx, dcx.args.first()?)?;
        let sel = self.translate_operand_with_modified(dcx.args.get(1)?, dcx.modified_locals)?;
        let sel = coerce_bitvec_width_safe(sel, 32, SignExtension::ZeroExtend);
        sel.sort().bitvec_width()?;

        let hit = shadow_in(SHMEM_AB_SOME).and(shadow_in(SHMEM_AB_SEL).eq(sel));
        let elem_bytes = Expr::bitvec_const(layout_size.max(1), 32);
        let (from_obj, from_off) = self.split_pointer(&shadow_in(SHMEM_AB_ADDR))?;
        let should_reset = declare_pending_var(chc_fresh_name("shmem_load_reset"), bool_sort());
        let state = self.shadow_state_in();
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
        Some([
            shadow_out(SHMEM_OBJ).eq(Expr::ite(hit.clone(), copied.obj, state.obj.clone())),
            shadow_out(SHMEM_OFF).eq(Expr::ite(hit.clone(), copied.off, state.off.clone())),
            shadow_out(SHMEM_VAL).eq(Expr::ite(hit.clone(), copied.init, blessed)),
            shadow_out(SHMEM_AB_SOME).eq(Expr::ite(
                hit,
                Expr::bool_const(false),
                shadow_in(SHMEM_AB_SOME),
            )),
        ])
    }
}
