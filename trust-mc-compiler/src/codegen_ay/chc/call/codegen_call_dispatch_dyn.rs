// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Dyn-dispatch helpers for pointer-wrapper constructors, deref, and vtable resolution.
//!
//! Part of #134: extracted from `codegen_call_dispatch_misc.rs` (D3).
//! Consumed by `codegen_call_dispatch_misc` and `codegen_call_cmp_string`.

use ay_bindings::{Expr, Sort};

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_rules::CodegenRules;
use super::dyn_coercion;
use crate::kani_middle::abi::LayoutOf;
use tracing::{debug, warn};

fn try_extract_data_obj_id(ptr_expr: &Expr) -> Option<u32> {
    ChcCtx::try_extract_obj_id(ptr_expr).or_else(|| {
        let width = ptr_expr.sort().bitvec_width()?;
        let ptr_width = crate::codegen_ay::types::POINTER_WIDTH;
        (width == 2 * ptr_width).then(|| {
            let data_ptr = ptr_expr.clone().extract(ptr_width - 1, 0);
            ChcCtx::try_extract_obj_id(&data_ptr)
        })?
    })
}

fn is_stack_obj_id(ctx: &ChcCtx<'_, '_>, obj_id: u32) -> bool {
    ctx.heap_state.stack_local_obj_ids().contains(&obj_id)
}

fn unique_known_heap_alloc_id(ctx: &ChcCtx<'_, '_>) -> Option<u32> {
    let stack_obj_ids = ctx.heap_state.stack_local_obj_ids();
    let mut found = None;
    for obj_id in ctx.known_alloc_ids.values().copied() {
        if stack_obj_ids.contains(&obj_id) {
            continue;
        }
        if found.is_some_and(|seen| seen != obj_id) {
            return None;
        }
        found = Some(obj_id);
    }
    found
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn resolve_unique_wrapped_dyn_vtable_id(
        &self,
        target_ty: rustc_public::ty::Ty,
    ) -> Option<u64> {
        let mut target_repr_ty = target_ty;
        loop {
            let peeled = dyn_coercion::peel_pointer_like_wrapper_ty(target_repr_ty);
            if peeled == target_repr_ty {
                break;
            }
            target_repr_ty = peeled;
        }
        let dyn_tail = dyn_coercion::find_dyn_trait_tail_ty(self, target_repr_ty)?;
        let trait_def_id = dyn_coercion::extract_dyn_trait_def_id(self, dyn_tail)?;
        let concrete_ty = dyn_coercion::resolve_unique_concrete_dyn_tail_ty(self, target_repr_ty)?;
        let candidates = dyn_coercion::collect_dyn_trait_candidates(self, trait_def_id);
        dyn_coercion::resolve_vtable_id(&candidates, concrete_ty)
    }

    pub(in crate::codegen_ay::chc) fn zst_unique_vtable_expr_for_local(
        &self,
        local_idx: usize,
    ) -> Option<Expr> {
        let local_ty = self.body.locals().get(local_idx)?.ty;
        let mut target_repr_ty = local_ty;
        loop {
            let peeled = dyn_coercion::peel_pointer_like_wrapper_ty(target_repr_ty);
            if peeled == target_repr_ty {
                break;
            }
            target_repr_ty = peeled;
        }
        let concrete_ty = dyn_coercion::resolve_unique_concrete_dyn_tail_ty(self, target_repr_ty)?;
        if LayoutOf::new(concrete_ty).size_of()? != 0 {
            return None;
        }
        let vtable_id = self.resolve_unique_wrapped_dyn_vtable_id(local_ty)?;
        Some(Expr::bitvec_const(vtable_id as u128, crate::codegen_ay::types::POINTER_WIDTH))
    }

    pub(in crate::codegen_ay::chc) fn capture_known_vtable_constraint(
        &mut self,
        local_idx: usize,
        vtable_expr: Expr,
    ) -> Option<Expr> {
        self.dyn_vtable_ids.insert(local_idx, vtable_expr.clone());

        let (in_name, out_name) = self.get_or_create_vtable_state_var(local_idx);
        if let Some(idx) = self.state_var_index_by_name(&in_name) {
            self.mark_state_var_modified(idx);
        }
        let out_var = Expr::var(&*out_name, Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH));
        Some(out_var.eq(vtable_expr))
    }

    pub(in crate::codegen_ay::chc) fn path_mentions_pointer_wrapper(
        path: &str,
        wrapper: &str,
    ) -> bool {
        path.contains(wrapper) || path.contains(&format!("{wrapper}::"))
    }

    pub(in crate::codegen_ay::chc) fn is_shared_pointer_wrapper_constructor_path(
        path: &str,
    ) -> bool {
        // Part of #3959: Recognize both `::from_inner_in` (with allocator) and
        // `::from_inner` (without allocator) variants. Both route to the same
        // lowering handler — the handler already extracts the pointer from the
        // first arg regardless of allocator presence.
        (path.ends_with("::from_inner_in") || path.ends_with("::from_inner"))
            && (Self::path_mentions_pointer_wrapper(path, "rc::Rc")
                || Self::path_mentions_pointer_wrapper(path, "sync::Arc"))
    }

    pub(in crate::codegen_ay::chc) fn is_pointer_wrapper_deref_path(path: &str) -> bool {
        path.ends_with("::deref")
            && path.contains("Deref>")
            && (Self::path_mentions_pointer_wrapper(path, "boxed::Box")
                || Self::path_mentions_pointer_wrapper(path, "rc::Rc")
                || Self::path_mentions_pointer_wrapper(path, "sync::Arc"))
    }

    pub(in crate::codegen_ay::chc) fn is_pointer_wrapper_as_ptr_path(path: &str) -> bool {
        (path.ends_with("::as_ptr") || path.ends_with("::as_mut_ptr"))
            && (Self::path_mentions_pointer_wrapper(path, "rc::Rc")
                || Self::path_mentions_pointer_wrapper(path, "sync::Arc"))
    }

    /// Part of #3871 D3: Resolve chained Box deref pointer through heap load.
    ///
    /// When `src_local` is a reference to a pointer-wrapper type (e.g.,
    /// `&Box<dyn T>` from a prior Box deref), `base_ptr` points to the
    /// intermediate wrapper value on the heap. Loading from memory at
    /// `base_ptr` recovers the inner data pointer stored in that wrapper.
    /// Returns `None` if no indirection is needed (single-level Box).
    fn resolve_chained_box_deref_ptr(&mut self, base_ptr: &Expr, src_local: usize) -> Option<Expr> {
        use rustc_public::CrateDef;
        use rustc_public::ty::{RigidTy, TyKind};
        let local_ty = self.body.locals().get(src_local)?.ty;
        let local_ty = self.resolve_body_ty(local_ty);
        // Determine the wrapper type to load. Either the local is a reference
        // to a wrapper (Ref/RawPtr → Box), or the local IS the wrapper directly
        // (when ref_targets resolved through the reference).
        let wrapper_ty = match local_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => self.resolve_body_ty(inner),
            TyKind::RigidTy(RigidTy::Adt(..)) => local_ty,
            _ => return None,
        };
        // Check if the wrapper type is a pointer-wrapper (Box, Unique, etc.)
        // that contains another level of indirection.
        let is_wrapper = match wrapper_ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                let name = def.trimmed_name();
                name == "Box" || name == "Unique" || name == "NonNull"
            }
            _ => false,
        };
        if !is_wrapper {
            return None;
        }
        // Load the stored pointer value from the heap at base_ptr.
        let loaded = self.load_from_memory(base_ptr.clone(), wrapper_ty)?;
        // Extract the data pointer from the loaded wrapper value.
        self.extract_pointer_storage_expr(&loaded).or(Some(loaded))
    }

    pub(in crate::codegen_ay::chc) fn extract_pointer_storage_expr(
        &self,
        expr: &Expr,
    ) -> Option<Expr> {
        dyn_coercion::extract_pointer_expr(expr)
            .map(|ptr| {
                // Part of #3589: When the expression is a packed BV fat pointer
                // (2×POINTER_WIDTH = BV128 on 64-bit), extract the data pointer
                // from the lower POINTER_WIDTH bits. The upper bits contain the
                // vtable discriminant, handled separately by vtable propagation.
                if let Some(w) = ptr.sort().bitvec_width() {
                    if w == 2 * crate::codegen_ay::types::POINTER_WIDTH {
                        return ptr.extract(crate::codegen_ay::types::POINTER_WIDTH - 1, 0);
                    }
                }
                ptr
            })
            .or_else(|| {
                let dt = expr.sort().datatype_sort()?;
                let cons = dt.constructors.first()?;
                let first = cons.fields.first()?;
                if first.sort.is_bitvec() {
                    Some(expr.clone().field_select(&dt.name, &first.name, first.sort.clone()))
                } else {
                    None
                }
            })
    }

    fn pointer_wrapper_deref_result_ptr(
        &mut self,
        callee_path: &str,
        dest_local: usize,
        ptr_expr: Expr,
    ) -> Option<Expr> {
        if Self::path_mentions_pointer_wrapper(callee_path, "boxed::Box") {
            return Some(ptr_expr);
        }

        if Self::path_mentions_pointer_wrapper(callee_path, "rc::Rc")
            || Self::path_mentions_pointer_wrapper(callee_path, "sync::Arc")
        {
            let dest_ty = self.body.locals()[dest_local].ty;
            let pointee_ty = match dest_ty.kind() {
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(_, inner, _))
                | rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::RawPtr(inner, _)) => {
                    inner
                }
                _ => return None,
            };
            // Part of #3975: use shared dyn-tail normalization.
            let effective_pointee_ty = self.normalize_unique_dyn_tail_ty(pointee_ty);

            // Rc/Arc store a pointer to the shared header; Deref returns a
            // pointer to the trailing `value: T` field after the two refcount words.
            let header_size = 2u64 * (crate::codegen_ay::types::POINTER_WIDTH as u64 / 8);
            // Part of #4014: For dyn Trait pointees whose alignment is unknown
            // (e.g., when the Rc was created inside a wrapper fn and the Unsize
            // cast is not in the harness body), default to header_size. This is
            // correct because header_size (16) is already a multiple of all
            // common alignments (1, 2, 4, 8, 16), so
            // header_size.div_ceil(align) * align == header_size.
            let align = self.get_type_align(effective_pointee_ty).unwrap_or(1);
            let value_offset =
                if align <= 1 { header_size } else { header_size.div_ceil(align) * align };

            return Some(if value_offset == 0 {
                ptr_expr
            } else {
                ptr_expr.bvadd(Expr::bitvec_const(
                    value_offset as u128,
                    crate::codegen_ay::types::POINTER_WIDTH,
                ))
            });
        }

        None
    }

    pub(in crate::codegen_ay::chc) fn codegen_pointer_wrapper_from_inner_in(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) {
        let DispatchCallContext {
            func,
            args,
            destination,
            target,
            from_app,
            stmt_constraints,
            bb_idx,
            modified_locals,
            ..
        } = dcx;

        let Some(target) = target else {
            self.record_diverging_call_drop(
                func,
                Some(*bb_idx),
                "misc::pointer_wrapper_from_inner_in",
                None,
            );
            return;
        };

        let dest_local: usize = destination.local;
        let ptr_expr = args
            .first()
            .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals))
            .and_then(|expr| self.extract_pointer_storage_expr(&expr));

        if let Some(ptr_expr) = ptr_expr
            && let Some((_, dest_var)) = self.resolve_destination(dest_local)
        {
            let ptr_obj_id = try_extract_data_obj_id(&ptr_expr);
            // Part of #3589: Rc/Arc stores the value after a header
            // (strong + weak refcounts = 2×pointer_size = 16 bytes on
            // 64-bit). Shift the pointer forward so that subsequent
            // statement-level extractions from the Rc wrapper local
            // (e.g., `_3 = extract(63,0, _4)`) already include the
            // header offset, matching the store-side field layout where
            // the value is written at `alloc_base + 16`.
            //
            // Without this, the Rc local points to the RcInner base
            // (offset 0), but stores write the value at offset 16,
            // causing a 16-byte address mismatch → Genuine CTREX.
            let ptr_expr = if let Some(ptr_width) = ptr_expr.sort().bitvec_width() {
                let rc_header_size = 2u64 * (crate::codegen_ay::types::POINTER_WIDTH as u64 / 8);
                debug!(
                    rc_header_size,
                    ptr_width, dest_local, "from_inner_in: adding Rc header offset to pointer"
                );
                ptr_expr.bvadd(Expr::bitvec_const(rc_header_size as u128, ptr_width))
            } else {
                warn!(?ptr_expr, "from_inner_in: ptr_expr is NOT bitvec, cannot add header offset");
                ptr_expr
            };

            let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                ptr_expr,
                dest_var.sort(),
                dest_local,
                "codegen_call_pointer_wrapper_from_inner_in",
            ) else {
                self.known_alloc_ids.remove(&dest_local);
                self.clear_known_vtable_discriminant(dest_local);
                #[rustfmt::skip]
                emit_sound_fallback_goto(self, from_app, *target, modified_locals, &[dest_local], stmt_constraints);
                return;
            };
            let mut extra = vec![eq];

            self.clear_known_vtable_discriminant(dest_local);
            let dest_ty = self.body.locals()[dest_local].ty;
            if let Some(vtable_id) = self.resolve_unique_wrapped_dyn_vtable_id(dest_ty) {
                let vtable_expr =
                    Expr::bitvec_const(vtable_id as u128, crate::codegen_ay::types::POINTER_WIDTH);
                if let Some(vc) = self.capture_known_vtable_constraint(dest_local, vtable_expr) {
                    extra.push(vc);
                }
            }

            // Part of #3589: Propagate allocation identity from the source arg
            // (the raw pointer from exchange_malloc) to the Rc/Arc local. Without
            // this, Rc::deref cannot recover the alloc identity for store-to-load
            // forwarding, causing CTREX in rc_outer_coercion.
            let src_local = match args.first() {
                Some(rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p)) => {
                    Some(p.local)
                }
                _ => None,
            };
            if let Some(obj_id) = src_local
                .and_then(|sl| self.known_alloc_ids.get(&sl).copied())
                .filter(|obj_id| !is_stack_obj_id(self, *obj_id))
                .or_else(|| src_local.and_then(|sl| self.trace_deref_store_alloc_id(sl)))
                .filter(|obj_id| !is_stack_obj_id(self, *obj_id))
                .or(ptr_obj_id)
                .filter(|obj_id| !is_stack_obj_id(self, *obj_id))
                .or_else(|| unique_known_heap_alloc_id(self))
            {
                self.known_alloc_ids.insert(dest_local, obj_id);
                self.ref_resolution.alloc_result_locals.insert(dest_local);
                debug!(
                    bb_idx,
                    dest_local, src_local, obj_id, "from_inner_in: preserved allocation identity"
                );
            } else {
                self.known_alloc_ids.remove(&dest_local);
            }

            let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(from_app, *target, &new_output_args, stmt_constraints, extra);
        } else {
            self.known_alloc_ids.remove(&dest_local);
            self.clear_known_vtable_discriminant(dest_local);
            #[rustfmt::skip]
            emit_sound_fallback_goto(self, from_app, *target, modified_locals, &[dest_local], stmt_constraints);
        }
    }

    /// Pointer-wrapper Deref::deref call handler — extracts pointer identity and propagates vtable.
    ///
    /// Part of #3608: Box is modeled as the pointee pointer. Rc/Arc store a
    /// pointer to the shared header, so their deref result must shift to the
    /// trailing `value` field before returning `&T`. Running std's Deref MIR body
    /// through fn_inline can lose the vtable side metadata for wrapper `dyn Trait`
    /// chains, so this handler also recovers the vtable discriminant.
    pub(in crate::codegen_ay::chc) fn codegen_pointer_wrapper_deref_call(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) {
        let DispatchCallContext {
            func,
            args,
            destination,
            target,
            from_app,
            stmt_constraints,
            bb_idx,
            modified_locals,
            ..
        } = dcx;

        let Some(target) = target else {
            self.record_diverging_call_drop(
                func,
                Some(*bb_idx),
                "misc::pointer_wrapper_deref_call",
                None,
            );
            return;
        };

        let dest_local: usize = destination.local;
        let resolved_callee_path =
            dcx.callee_path.clone().or_else(|| self.resolve_callee_path(func));
        let Some(ref callee_path) = resolved_callee_path else {
            #[rustfmt::skip]
            emit_sound_fallback_goto(self, from_app, *target, modified_locals, &[dest_local], stmt_constraints);
            return;
        };

        let raw_arg_expr = args.first().and_then(|arg| {
            self.resolve_ref_operand(arg, modified_locals)
                .or_else(|| self.translate_operand_with_modified(arg, modified_locals))
        });
        let src_local = args.first().and_then(|arg| match arg {
            rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)
                if place.projection.is_empty() =>
            {
                self.ref_resolution
                    .ref_targets
                    .get(&place.local)
                    .map(|rt| rt.local)
                    .or(Some(place.local))
            }
            _ => None,
        });
        let concrete_deref_ptr = src_local.and_then(|sl| {
            let obj_id = self.known_alloc_ids.get(&sl).copied()?;
            let base_ptr =
                Expr::bitvec_const(obj_id as u128, 32).concat(Expr::bitvec_const(0u128, 32));
            // Part of #3871 D3: For chained Box deref (e.g., Box<Box<dyn T>>),
            // the first deref propagates known_alloc_ids to the result. The
            // second deref then computes base_ptr = obj_outer << 32, which is
            // the address of the INNER Box value in memory. But deref should
            // return the data pointer INSIDE that inner Box — not the inner
            // Box's address. Load from memory to resolve the indirection.
            //
            // Detect: if the source local's type is a reference/pointer to a
            // pointer-wrapper (Box/Unique), load the stored pointer value.
            let effective_ptr =
                self.resolve_chained_box_deref_ptr(&base_ptr, sl).unwrap_or(base_ptr);
            self.pointer_wrapper_deref_result_ptr(&callee_path, dest_local, effective_ptr)
        });
        // Part of #3589: The fallback path extracts the pointer stored in
        // the wrapper local. For Rc/Arc, `from_inner_in` already shifted
        // the pointer forward by the header size (16 bytes), so the
        // extracted value points directly to the value field. Calling
        // `pointer_wrapper_deref_result_ptr` here would add the header
        // offset a second time. For Box, the pointer is identity (no
        // offset), so extraction alone is also correct.
        let ptr_expr = concrete_deref_ptr.or_else(|| {
            raw_arg_expr.as_ref().and_then(|expr| self.extract_pointer_storage_expr(expr))
        });

        if let Some(ptr_expr) = ptr_expr
            && let Some((_, dest_var)) = self.resolve_destination(dest_local)
        {
            let mut extra: Vec<Expr> = self
                .make_coerced_eq_constraint(
                    &dest_var,
                    ptr_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_pointer_wrapper_deref",
                )
                .into_iter()
                .collect();

            // Part of #3608, #3589: Preserve concrete allocation identity across
            // Deref::deref ONLY for Box (identity deref). For Rc/Arc, the deref
            // result pointer is `alloc_addr + header_offset` (skipping refcount
            // fields), not `alloc_addr`. Propagating the raw obj_id causes the
            // load side (translate_place_with_deref) to resolve the address as
            // `alloc_addr + 0`, while the store side wrote at
            // `alloc_addr + header_offset + field_offset`. This 16-byte mismatch
            // produces Genuine CTREX for rc_outer_coercion.
            //
            // Instead, when the source wrapper local already has a concrete
            // allocation id we bake the exact `alloc_addr + header_offset`
            // constant into `ptr_expr` above, so later loads see a concrete
            // value-field address without reusing the raw allocation-base map.
            let is_box_deref = Self::path_mentions_pointer_wrapper(&callee_path, "boxed::Box");
            if is_box_deref {
                if let Some(obj_id) =
                    src_local.and_then(|sl| self.known_alloc_ids.get(&sl).copied())
                {
                    self.known_alloc_ids.insert(dest_local, obj_id);
                    debug!(
                        bb_idx = dcx.bb_idx,
                        dest_local,
                        src_local,
                        obj_id,
                        "pointer_wrapper_deref: preserved allocation identity (Box)"
                    );
                } else {
                    self.known_alloc_ids.remove(&dest_local);
                }
            } else {
                // Rc/Arc: do NOT propagate alloc_id — the deref result pointer
                // includes the header offset and must not be replaced by the raw
                // allocation base address at load time.
                self.known_alloc_ids.remove(&dest_local);
                debug!(
                    bb_idx = dcx.bb_idx,
                    dest_local,
                    src_local,
                    "pointer_wrapper_deref: cleared alloc_id for Rc/Arc (header offset)"
                );
            }

            // Propagate vtable discriminant through pointer wrapper deref.
            // Priority 1: source local has a known vtable (direct propagation).
            // Priority 2: extract vtable from packed BV128 fat pointer (#3589).
            // Priority 3: recover from unique coercion site for chained wrapper
            // types (e.g., deref of Box<Box<dyn Trait>> produces &Box<dyn Trait>,
            // which needs recursive wrapper peeling to find the dyn Trait core).
            // Part of #3608: Priority 3 fixes double_coercion CTREX.
            let vtable_from_source =
                src_local.and_then(|sl| self.dyn_vtable_ids.get(&sl).cloned()).and_then(
                    |vtable_expr| self.capture_known_vtable_constraint(dest_local, vtable_expr),
                );
            if let Some(vtable_constraint) = vtable_from_source {
                debug!(
                    bb_idx = dcx.bb_idx,
                    dest_local, "pointer_wrapper_deref: vtable from source"
                );
                extra.push(vtable_constraint);
            } else if let Some(vtable_constraint) = raw_arg_expr
                .as_ref()
                .and_then(|expr| {
                    // Part of #3589: Extract vtable from packed BV128 fat pointer.
                    // Rc<dyn Trait> values are encoded as BV128 = [vtable:64 | ptr:64].
                    // The upper POINTER_WIDTH bits carry the vtable discriminant.
                    let w = expr.sort().bitvec_width()?;
                    if w == 2 * crate::codegen_ay::types::POINTER_WIDTH {
                        let pw = crate::codegen_ay::types::POINTER_WIDTH;
                        Some(expr.clone().extract(2 * pw - 1, pw))
                    } else {
                        None
                    }
                })
                .and_then(|vtable_expr| {
                    self.capture_known_vtable_constraint(dest_local, vtable_expr)
                })
            {
                debug!(
                    bb_idx = dcx.bb_idx,
                    dest_local, "pointer_wrapper_deref: vtable from BV128 fat pointer (#3589)"
                );
                extra.push(vtable_constraint);
            } else {
                let dest_ty = self.body.locals()[dest_local].ty;
                if let Some(vtable_id) = self.resolve_unique_wrapped_dyn_vtable_id(dest_ty) {
                    debug!(
                        bb_idx = dcx.bb_idx,
                        vtable_id,
                        dest_local,
                        "pointer_wrapper_deref: recovered vtable via wrapper peeling"
                    );
                    let vtable_expr = Expr::bitvec_const(
                        vtable_id as u128,
                        crate::codegen_ay::types::POINTER_WIDTH,
                    );
                    if let Some(vc) = self.capture_known_vtable_constraint(dest_local, vtable_expr)
                    {
                        extra.push(vc);
                    }
                }
            }

            let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(from_app, *target, &new_output_args, stmt_constraints, extra);
        } else {
            #[rustfmt::skip]
            emit_sound_fallback_goto(self, from_app, *target, modified_locals, &[dest_local], stmt_constraints);
        }
    }
}
