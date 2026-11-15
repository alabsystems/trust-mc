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
use crate::codegen_ay::chc::rc_strong_count::rc_strong_const;
use crate::codegen_ay::stubs::StubKind;
use tracing::{debug, warn};


/// The byte offset of the value in an `RcInner<T>` / `ArcInner<T>` whose `T`
/// has alignment `align`: the 16-byte header (strong, weak) rounded up to the
/// alignment, the field offset of the real layout, which every reader of the
/// value computes (the `Rc` deref and `as_ptr` lanes, the drop glue, a MIR
/// field projection of the inner struct).
pub(in crate::codegen_ay::chc) fn rc_value_offset(align: u64) -> u64 {
    let header = 2u64 * (crate::codegen_ay::types::POINTER_WIDTH as u64 / 8);
    let align = align.max(1);
    header.div_ceil(align) * align
}

/// The size of an `RcInner<T>` / `ArcInner<T>` holding a `T` of `size` bytes
/// and alignment `align`: the value's offset plus its size, rounded up to the
/// inner alignment (that of the refcount words or of `T`).
pub(in crate::codegen_ay::chc) fn rc_inner_model_size(size: u64, align: u64) -> u64 {
    let header = 2u64 * (crate::codegen_ay::types::POINTER_WIDTH as u64 / 8);
    let inner_align = align.max(1).max(header / 2);
    (rc_value_offset(align) + size).div_ceil(inner_align) * inner_align
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Detect `Rc::clone` / `Arc::clone` / `<Rc<T> as Clone>::clone` callee paths.
    ///
    /// Rc::clone increments the refcount and returns a copy of the same pointer:
    /// `dest = src` with allocation identity and vtable metadata propagation
    /// (Part of #3978), and the strong count of a counted allocation
    /// (`rc_strong_count.rs`) gains one.
    pub(in crate::codegen_ay::chc) fn is_rc_arc_clone_path(path: &str) -> bool {
        path.ends_with("::clone")
            && (Self::path_mentions_pointer_wrapper(path, "rc::Rc")
                || Self::path_mentions_pointer_wrapper(path, "sync::Arc"))
    }

    /// Handle `Rc::clone(&rc)` / `Arc::clone(&arc)` as pointer identity.
    ///
    /// Semantics: dest = src (same heap pointer). Propagates allocation identity
    /// and vtable discriminant from source to destination (Part of #3978); a
    /// counted allocation's strong count gains one (`rc_strong_count.rs`).
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

            // A counted allocation gains a handle (rc_strong_count.rs).
            if let Some(count) = self.rc_strong_count_for_local(dest_local) {
                let incremented = count.current.clone().bvadd(rc_strong_const(1));
                extra.push(self.write_rc_strong_count(&count, incremented));
                debug!(bb_idx, dest_local, "rc_arc_clone: strong count + 1");
            }

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
    /// The refcount fields (strong, weak) are not stored; a counted allocation
    /// keeps its strong count in a state variable (`rc_strong_count.rs`).
    /// Part of #3977.
    /// The `RcInner` / `ArcInner` allocation is `strong + weak + value`, but
    /// the `BoxNew` infrastructure sizes it from the argument alone, so the
    /// object's recorded size missed the 16-byte header the value is stored
    /// after (`value_ptr = alloc_ptr + 16` below): `obj_size` of an `Rc<u8>`
    /// read 1 where the value's byte sits at offset 16. An access through a
    /// pointer whose object lane does not fold is bounded by `obj_size`
    /// (`heap_access_checks`), and `rc.eq(0)` through `Rc<dyn Byte>` failed
    /// that bound, certified Genuine (kani/DynTrait/unsized_rc_cast.rs, found
    /// by the 737-unit run of review of fix/chc-lost-writes, lostwrite round
    /// 1, finding 4). The recorded size is now the inner layout's, seen from
    /// the model's value offset.
    ///
    ///
    /// The value sits at the real layout's field offset, the header rounded
    /// up to `T`'s alignment (`rc_value_offset`): 32 for an align-32 `T`.
    /// The readers (the `Rc` deref and `as_ptr` lanes, the drop glue, a MIR
    /// projection of the inner struct's `value` field) round, and the writer
    /// stored the value at 16, so `Rc::as_ptr` of an `Rc<A32>` pointed 16
    /// bytes past the stored value and `*p.wrapping_add(31)` read a cell
    /// nothing wrote, certified Genuine on a program Kani proves (lostwrite
    /// track round 1, finding 10). The writer now rounds too, and the size is
    /// the real inner layout's (`rc_inner_model_size`).
    fn rc_inner_allocation_size(
        &mut self,
        args: &[rustc_public::mir::Operand],
        alloc_obj_id: Option<u32>,
        heap_constraints: Vec<Expr>,
    ) -> Vec<Expr> {
        use ay_bindings::ExprValue;
        let header = 2u64 * (crate::codegen_ay::types::POINTER_WIDTH as u64 / 8);
        let Some(obj_id) = alloc_obj_id else { return heap_constraints };
        let Some(arg_ty) = args.first().and_then(|a| a.ty(self.body.locals()).ok()) else {
            return heap_constraints;
        };
        let arg_ty = self.resolve_body_ty(arg_ty);
        let (Some(size), Some(align)) = (self.get_type_size(arg_ty), self.get_type_align(arg_ty))
        else {
            return heap_constraints;
        };
        let Ok(inner) = u32::try_from(rc_inner_model_size(size as u64, align)) else {
            return heap_constraints;
        };
        self.heap_state.record_heap_alloc_size(obj_id, inner);
        let obj_size_out = crate::codegen_ay::chc::codegen_expr_heap::obj_size_out();
        heap_constraints
            .into_iter()
            .map(|c| match c.value() {
                ExprValue::Eq(lhs, rhs) if *lhs == obj_size_out => match rhs.value() {
                    ExprValue::Store { array, index, .. }
                        if ChcCtx::const_obj_id_u32(index) == Some(obj_id) =>
                    {
                        let size = Expr::bitvec_const(inner as i128, 32);
                        lhs.clone().eq(array.clone().store(index.clone(), size))
                    }
                    _ => c.clone(),
                },
                _ => c.clone(),
            })
            .collect()
    }

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
        let heap_constraints = self.rc_inner_allocation_size(args, alloc_obj_id, heap_constraints);

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

        // Step 2: Compute value pointer = alloc_ptr + the value's field offset:
        // the strong + weak header (16 bytes on 64-bit) rounded up to the
        // value's alignment (`rc_value_offset`).
        let value_align = args
            .first()
            .and_then(|a| a.ty(self.body.locals()).ok())
            .and_then(|ty| self.get_type_align(self.resolve_body_ty(ty)))
            .unwrap_or(1);
        let value_offset = rc_value_offset(value_align);
        if value_offset > 16 {
            self.record_sound_fallback_reason(RC_VALUE_OVERALIGNED);
        }
        let value_ptr = if let Some(ptr_width) = alloc_ptr.sort().bitvec_width() {
            alloc_ptr.clone().bvadd(Expr::bitvec_const(value_offset as u128, ptr_width))
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
                // A fresh allocation's initializer: both views together
                // (`heap_unsize_alias.rs`).
                self.with_coherent_object_stores(|ctx| {
                    ctx.try_decompose_struct_store(&value_ptr, &value_expr, store_ty, &mut extra);
                    if let Some(store_constraint) =
                        ctx.build_memory_store_untyped(value_ptr.clone(), value_expr, store_ty)
                    {
                        extra.push(store_constraint);
                    }
                });
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

        // A counted allocation starts with one handle (rc_strong_count.rs).
        if let Some(count) = self.rc_strong_count_for_new_site(*bb_idx) {
            extra.push(self.write_rc_strong_count(&count, rc_strong_const(1)));
            debug!(bb_idx, dest_local, "Rc/Arc::new: strong count = 1");
        }

        self.emit_alloc_pending_checks(from_app, stmt_constraints, *target);
        let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(from_app, *target, &new_output_args, stmt_constraints, extra);
    }
}

/// FailClose: an `Rc`/`Arc` value aligned beyond the 16-byte header, so it
/// sits past the header (`rc_value_offset`). A reader that does not know the
/// value's type (a dyn pointee) takes the header as its offset, and an
/// align-32 payload's last byte read back a cell nothing wrote, certified
/// Genuine on a program Kani proves (lostwrite track round 1, finding 10).
/// Such a value is rare; the harness fails closed.
pub(in crate::codegen_ay::chc) const RC_VALUE_OVERALIGNED: &str = "rc_value_overaligned";

#[cfg(test)]
mod rc_inner_size_tests {
    use super::{rc_inner_model_size, rc_value_offset};

    #[test]
    fn the_inner_size_is_the_real_layout_s() {
        // `RcInner<u8>`: 16 + 1, rounded to the inner alignment 8.
        assert_eq!(rc_value_offset(8), 16);
        assert_eq!(rc_inner_model_size(1, 1), 24);
        assert_eq!(rc_inner_model_size(8, 8), 24);
        assert_eq!(rc_inner_model_size(16, 16), 32);
        // An align-32 value sits at 32 in the real layout, whose size is 64.
        assert_eq!(rc_value_offset(32), 32);
        assert_eq!(rc_inner_model_size(32, 32), 64);
        assert_eq!(rc_inner_model_size(8, 32), 64);
        // A zero-sized value: the header alone.
        assert_eq!(rc_inner_model_size(0, 1), 16);
    }
}
