// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rc/Arc lifecycle stubs: clone, new.
//!
//! Extracted from `codegen_call_dispatch_dyn.rs` — Part of #4206.

use ay_bindings::Expr;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_rules::CodegenRules;
use crate::codegen_ay::stubs::StubKind;
use tracing::{debug, warn};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Detect `Rc::clone` / `Arc::clone` / `<Rc<T> as Clone>::clone` callee paths.
    ///
    /// Rc::clone increments the refcount and returns a copy of the same pointer.
    /// Refcount is irrelevant for verification, so this is semantically `dest = src`
    /// with allocation identity and vtable metadata propagation. Part of #3978.
    pub(in crate::codegen_ay::chc) fn is_rc_arc_clone_path(path: &str) -> bool {
        path.ends_with("::clone")
            && (Self::path_mentions_pointer_wrapper(path, "rc::Rc")
                || Self::path_mentions_pointer_wrapper(path, "sync::Arc"))
    }

    /// Handle `Rc::clone(&rc)` / `Arc::clone(&arc)` as pointer identity.
    ///
    /// Semantics: dest = src (same heap pointer). Refcount manipulation is
    /// irrelevant for formal verification. Propagates allocation identity and
    /// vtable discriminant from source to destination. Part of #3978.
    pub(in crate::codegen_ay::chc) fn codegen_rc_arc_clone(
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
            self.record_diverging_call_drop(func, Some(*bb_idx), "misc::rc_arc_clone", None);
            return;
        };

        let dest_local: usize = destination.local;

        // Resolve the source Rc/Arc operand. The argument is &Rc<T>,
        // so we need to dereference through the reference to get the Rc value.
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

        let src_expr = args.first().and_then(|arg| {
            self.resolve_ref_operand(arg, modified_locals)
                .or_else(|| self.translate_operand_with_modified(arg, modified_locals))
        });

        if let Some(src_expr) = src_expr
            && let Some((_, dest_var)) = self.resolve_destination(dest_local)
        {
            let mut extra: Vec<Expr> = self
                .make_coerced_eq_constraint(
                    &dest_var,
                    src_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_rc_arc_clone",
                )
                .into_iter()
                .collect();

            // Propagate allocation identity: Rc::clone returns the same
            // heap pointer as the source.
            if let Some(obj_id) = src_local.and_then(|sl| self.known_alloc_ids.get(&sl).copied()) {
                self.known_alloc_ids.insert(dest_local, obj_id);
                self.rc_arc_shared_alloc_ids.insert(obj_id);
                debug!(
                    bb_idx,
                    dest_local,
                    src_local,
                    obj_id,
                    "rc_arc_clone: preserved shared allocation identity"
                );
            }

            // Propagate vtable discriminant: clone of Rc<dyn T> has the
            // same vtable as the source.
            if let Some(vtable_constraint) =
                src_local.and_then(|sl| self.dyn_vtable_ids.get(&sl).cloned()).and_then(
                    |vtable_expr| self.capture_known_vtable_constraint(dest_local, vtable_expr),
                )
            {
                debug!(bb_idx, dest_local, "rc_arc_clone: propagated vtable from source");
                extra.push(vtable_constraint);
            }

            let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(from_app, *target, &new_output_args, stmt_constraints, extra);
        } else {
            // Sound fallback if we can't resolve source or destination.
            #[rustfmt::skip]
            emit_sound_fallback_goto(self, from_app, *target, modified_locals, &[dest_local], stmt_constraints);
        }

        debug!(bb_idx, dest_local, "CHC: Rc/Arc::clone modeled as pointer identity (#3978)");
    }

    /// Detect `Rc::new` / `Arc::new` callee paths.
    ///
    /// These need dedicated dispatch because their MIR body constructs
    /// `RcInner { strong: Cell::new(1), weak: Cell::new(1), value }` which
    /// the inline walker cannot translate (nested Cell aggregate). Part of #3977.
    pub(in crate::codegen_ay::chc) fn is_rc_arc_new_path(path: &str) -> bool {
        path.ends_with("::new")
            && (Self::path_mentions_pointer_wrapper(path, "rc::Rc")
                || Self::path_mentions_pointer_wrapper(path, "sync::Arc"))
    }

    /// Handle `Rc::new(value)` / `Arc::new(value)` as:
    ///   allocate heap → store value at alloc_ptr + header_offset → return value pointer.
    ///
    /// Semantically equivalent to `Box::new(RcInner { strong, weak, value })` followed
    /// by `Rc::from_inner(box_result)`, but avoids the inline walker entirely.
    /// The refcount fields (strong, weak) are irrelevant for verification.
    /// Part of #3977.
    pub(in crate::codegen_ay::chc) fn codegen_rc_arc_new(&mut self, dcx: &DispatchCallContext<'_>) {
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
            self.record_diverging_call_drop(func, Some(*bb_idx), "misc::rc_arc_new", None);
            return;
        };

        let dest_local: usize = destination.local;

        // Step 1: Allocate heap memory using the BoxNew infrastructure.
        // BoxNew resolves concrete size/align from the argument's Rust type.
        let alloc_result = self.translate_alloc_call(StubKind::BoxNew, args, modified_locals);

        let Some(alloc) = alloc_result else {
            warn!(bb_idx, "Rc/Arc::new: translate_alloc_call returned None — sound fallback");
            self.record_sound_fallback_reason("rc_arc_new_alloc_failed");
            self.known_alloc_ids.remove(&dest_local);
            self.clear_known_vtable_discriminant(dest_local);
            #[rustfmt::skip]
            emit_sound_fallback_goto(self, from_app, *target, modified_locals, &[dest_local], stmt_constraints);
            return;
        };

        let super::AllocCallResult {
            result: alloc_ptr,
            heap_constraints,
            safety_checks,
            alloc_obj_id,
            transition_branches: _,
        } = alloc;

        // Emit safety checks for allocation preconditions.
        for check in safety_checks {
            self.emit_error_rule_for_condition(from_app, check, stmt_constraints, *bb_idx);
        }

        let Some(alloc_ptr) = alloc_ptr else {
            warn!(bb_idx, "Rc/Arc::new: allocation returned no pointer — sound fallback");
            self.record_sound_fallback_reason("rc_arc_new_no_ptr");
            self.known_alloc_ids.remove(&dest_local);
            self.clear_known_vtable_discriminant(dest_local);
            #[rustfmt::skip]
            emit_sound_fallback_goto(self, from_app, *target, modified_locals, &[dest_local], stmt_constraints);
            return;
        };

        let mut extra = Vec::new();
        extra.extend(heap_constraints);

        // Step 2: Compute value pointer = alloc_ptr + header_offset.
        // Rc/Arc header = strong + weak = 2 × pointer_size = 16 bytes on 64-bit.
        let header_size = 2u64 * (crate::codegen_ay::types::POINTER_WIDTH as u64 / 8);
        let value_ptr = if let Some(ptr_width) = alloc_ptr.sort().bitvec_width() {
            alloc_ptr.clone().bvadd(Expr::bitvec_const(header_size as u128, ptr_width))
        } else {
            alloc_ptr.clone()
        };

        // Step 3: Store the value argument at the value pointer.
        // Suppress heap store checks during alloc (same as emit_boxnew_heap_stores).
        let prev_suppress = self.suppress_heap_store_checks;
        self.suppress_heap_store_checks = true;
        if let Some(arg0) = args.first()
            && let Ok(arg_ty) = arg0.ty(self.body.locals())
        {
            let value_expr = self.translate_operand_with_modified(arg0, modified_locals);
            if let Some(value_expr) = value_expr {
                let store_ty = self.resolve_body_ty(arg_ty);
                self.mirror_array_elements_to_flat_memory(
                    &value_expr,
                    store_ty,
                    &value_ptr,
                    &mut extra,
                );
                // Part of #4059: Always emit both per-field AND whole-struct
                // stores. Virtual dispatch reads individual fields (e.g.,
                // `mem_bool` for `self.fancy`), but whole-struct loads via
                // `load_from_memory(addr, StructTy)` also occur. Previously,
                // decomposition success skipped the whole-struct store,
                // causing `mem_Table[addr]` to be unconstrained → instant
                // CTREX. Mirrors the inline walker fix from #4014.
                self.try_decompose_struct_store(&value_ptr, &value_expr, store_ty, &mut extra);
                if let Some(store_constraint) =
                    self.build_memory_store(value_ptr.clone(), value_expr, store_ty)
                {
                    extra.push(store_constraint);
                }
            }
        }
        self.suppress_heap_store_checks = prev_suppress;
        extra.append(&mut self.heap_state.drain_store_chains(&self.diagnostics));

        // Step 4: Set destination = alloc_ptr (base pointer WITHOUT header offset).
        // The virtual dispatch path adds the Rc header offset when resolving the
        // self pointer for dyn method calls. If we bake the offset into the Rc
        // local here, it gets added twice → double offset → store/load mismatch.
        // The Rc deref handler also adds the offset via pointer_wrapper_deref_result_ptr.
        let result_expr_for_bridge = alloc_ptr.clone();
        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                alloc_ptr,
                dest_var.sort(),
                dest_local,
                "codegen_rc_arc_new",
            ) {
                extra.push(eq);
            }
        }

        // Part of #4067 D2: Mirror the Rc allocation pointer to the destination
        // local's typed memory address. MIR-inlined Deref::deref for Rc reads
        // `self` through `&_4` → `*(&_4)`, which at Mem level loads from
        // `mem_Rc_u8[local_address(_4)]`. Without this mirror store, the load
        // returns an unconstrained value, breaking the deref value roundtrip.
        {
            let mut bridge_modified: std::collections::HashSet<usize> =
                modified_locals.iter().copied().collect();
            bridge_modified.insert(dest_local);
            extra.extend(
                super::codegen_call_result_mem::build_call_result_memory_bridge_constraints(
                    self,
                    dest_local,
                    &result_expr_for_bridge,
                    &bridge_modified,
                ),
            );
        }

        // Step 5: Record allocation identity.
        self.ref_resolution.alloc_result_locals.insert(dest_local);
        if let Some(obj_id) = alloc_obj_id {
            self.known_alloc_ids.insert(dest_local, obj_id);
            debug!(bb_idx, dest_local, obj_id, "Rc/Arc::new: recorded allocation identity");
        }

        // Step 6: Propagate vtable for dyn types.
        self.clear_known_vtable_discriminant(dest_local);
        let dest_ty = self.body.locals()[dest_local].ty;
        if let Some(vtable_id) = self.resolve_unique_wrapped_dyn_vtable_id(dest_ty) {
            let vtable_expr =
                Expr::bitvec_const(vtable_id as u128, crate::codegen_ay::types::POINTER_WIDTH);
            if let Some(vc) = self.capture_known_vtable_constraint(dest_local, vtable_expr) {
                extra.push(vc);
            }
            debug!(bb_idx, dest_local, vtable_id, "Rc/Arc::new: propagated vtable");
        }

        self.emit_alloc_pending_checks(from_app, stmt_constraints, *target);
        let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(from_app, *target, &new_output_args, stmt_constraints, extra);
    }
}
