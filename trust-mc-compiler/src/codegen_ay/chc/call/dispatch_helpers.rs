// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared helpers for dispatch-layer call handlers.
//!
//! Part of #134: dispatch_misc decomposition (D1).

use ay_bindings::Expr;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_rules::CodegenRules;
use super::codegen_stmt_flatten::collect_leaf_exprs;
use tracing::debug;

/// Extension trait for identity-call dispatch helpers.
///
/// An "identity call" is a call where `dest = f(arg0)` with optional coercion.
/// Examples: `slice::as_ptr`, `Cell::new`, `downcast_unchecked_ref`.
pub(in crate::codegen_ay::chc) trait DispatchHelpers {
    /// Emit a value/pointer identity call: `dest = resolve(arg0)`, with coercion.
    ///
    /// `operand_resolver` transforms the first argument into the expression to
    /// assign. For simple identity (slice_as_ptr, Cell::new) this is just
    /// `translate_operand_with_modified`. For downcast_unchecked_ref it extracts
    /// the thin pointer from a fat pointer.
    ///
    /// Returns `true` if the call was handled (even via sound_fallback).
    fn emit_identity_call(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        label: &'static str,
        operand_resolver: impl FnOnce(&mut Self, &DispatchCallContext<'_>) -> Option<Expr>,
    ) -> bool;

    /// Emit an identity call and run `on_success` only after the call has been
    /// modeled with a concrete destination assignment.
    fn emit_identity_call_with_success(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        label: &'static str,
        operand_resolver: impl FnOnce(&mut Self, &DispatchCallContext<'_>) -> Option<Expr>,
        on_success: impl FnMut(&mut Self, &DispatchCallContext<'_>),
    ) -> bool;

    /// Emit an identity call and preserve the receiver's vtable on the result.
    ///
    /// Used for pointer-wrapper identity calls like `Pin::as_mut` where the
    /// value-level result is unchanged but dyn-dispatch metadata must still be
    /// threaded to the destination local.
    fn emit_identity_call_preserving_receiver_vtable(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        label: &'static str,
        operand_resolver: impl FnOnce(&mut Self, &DispatchCallContext<'_>) -> Option<Expr>,
    ) -> bool;
}

impl<'tcx, 'body> DispatchHelpers for ChcCtx<'tcx, 'body> {
    fn emit_identity_call(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        label: &'static str,
        operand_resolver: impl FnOnce(&mut Self, &DispatchCallContext<'_>) -> Option<Expr>,
    ) -> bool {
        self.emit_identity_call_impl(dcx, label, false, operand_resolver, |_, _| {})
    }

    fn emit_identity_call_with_success(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        label: &'static str,
        operand_resolver: impl FnOnce(&mut Self, &DispatchCallContext<'_>) -> Option<Expr>,
        on_success: impl FnMut(&mut Self, &DispatchCallContext<'_>),
    ) -> bool {
        self.emit_identity_call_impl(dcx, label, false, operand_resolver, on_success)
    }

    fn emit_identity_call_preserving_receiver_vtable(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        label: &'static str,
        operand_resolver: impl FnOnce(&mut Self, &DispatchCallContext<'_>) -> Option<Expr>,
    ) -> bool {
        self.emit_identity_call_impl(dcx, label, true, operand_resolver, |_, _| {})
    }
}

/// Detect platform-level sync foreign calls that are no-ops in single-threaded
/// CHC verification (Part of #4067).
pub(super) fn is_pthread_noop_foreign_call(path: &str) -> bool {
    let leaf = path.rsplit("::").next().unwrap_or(path);
    matches!(
        leaf,
        "pthread_mutex_trylock"
            | "pthread_mutex_unlock"
            | "pthread_mutex_lock"
            | "pthread_mutex_init"
            | "pthread_mutex_destroy"
            | "pthread_mutexattr_init"
            | "pthread_mutexattr_settype"
            | "pthread_mutexattr_destroy"
            | "pthread_rwlock_rdlock"
            | "pthread_rwlock_wrlock"
            | "pthread_rwlock_unlock"
            | "pthread_rwlock_destroy"
            | "pthread_rwlock_init"
    )
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn emit_identity_call_impl(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        label: &'static str,
        preserve_receiver_vtable: bool,
        operand_resolver: impl FnOnce(&mut Self, &DispatchCallContext<'_>) -> Option<Expr>,
        mut on_success: impl FnMut(&mut Self, &DispatchCallContext<'_>),
    ) -> bool {
        let Some(target) = dcx.target else {
            self.record_diverging_call_drop(dcx.func, Some(dcx.bb_idx), label, None);
            return true;
        };

        let dest_local: usize = dcx.destination.local;
        let val_expr = operand_resolver(self, dcx);
        let receiver_vtable = if preserve_receiver_vtable {
            dcx.args
                .first()
                .and_then(|arg| match arg {
                    rustc_public::mir::Operand::Copy(place)
                    | rustc_public::mir::Operand::Move(place)
                        if place.projection.is_empty() =>
                    {
                        Some(place.local)
                    }
                    _ => None,
                })
                .and_then(|local_idx| self.known_vtable_expr_for_local(local_idx))
        } else {
            None
        };

        if let Some(val_expr) = val_expr {
            let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
                on_success(self, dcx);
                emit_sound_fallback_goto(
                    self,
                    dcx.from_app,
                    *target,
                    dcx.modified_locals,
                    &[dest_local],
                    dcx.stmt_constraints,
                );
                debug!("modeled {label} as metadata-only identity (bb{})", dcx.bb_idx);
                return true;
            };

            // Part of #3984: When the destination is a flattened local (e.g.,
            // ManuallyDrop<PolymorphicIter>), resolve_destination returns only
            // the first leaf state var (BV64). Scalar coercion would fail
            // against the full DT value and increment the coercion-drop
            // counter. Check for flattened destinations first and decompose
            // the value into leaf scalars, constraining each output state var.
            if self.flatten.flattened_tuple_locals.contains(&dest_local)
                && val_expr.sort() != dest_var.sort()
            {
                let mut leaf_values: Vec<Option<Expr>> = Vec::new();
                collect_leaf_exprs(&val_expr, &mut leaf_values);
                let field_count = self.flattened_field_count(dest_local);
                if leaf_values.len() == field_count {
                    let mut extra_constraints = Vec::new();
                    if let Some(vtable_expr) = receiver_vtable.clone()
                        && let Some(vtable_constraint) =
                            self.capture_known_vtable_constraint(dest_local, vtable_expr)
                    {
                        extra_constraints.push(vtable_constraint);
                    }
                    self.constrain_flattened_fields_for_call(
                        dest_local,
                        &leaf_values,
                        &mut extra_constraints,
                    );
                    let new_output_args =
                        self.build_output_args(dcx.modified_locals, &[dest_local]);
                    on_success(self, dcx);
                    self.emit_goto_rule_extra(
                        dcx.from_app,
                        *target,
                        &new_output_args,
                        dcx.stmt_constraints,
                        extra_constraints,
                    );
                } else {
                    debug!(
                        dest_local,
                        leaf_count = leaf_values.len(),
                        field_count,
                        "identity call: flattened leaf count mismatch, falling back"
                    );
                    emit_sound_fallback_goto(
                        self,
                        dcx.from_app,
                        *target,
                        dcx.modified_locals,
                        &[dest_local],
                        dcx.stmt_constraints,
                    );
                }
            } else if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                val_expr,
                dest_var.sort(),
                dest_local,
                label,
            ) {
                let mut extra_constraints = Vec::new();
                if let Some(vtable_expr) = receiver_vtable
                    && let Some(vtable_constraint) =
                        self.capture_known_vtable_constraint(dest_local, vtable_expr)
                {
                    extra_constraints.push(vtable_constraint);
                }
                extra_constraints.push(eq);
                let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
                on_success(self, dcx);
                self.emit_goto_rule_extra(
                    dcx.from_app,
                    *target,
                    &new_output_args,
                    dcx.stmt_constraints,
                    extra_constraints,
                );
            } else {
                emit_sound_fallback_goto(
                    self,
                    dcx.from_app,
                    *target,
                    dcx.modified_locals,
                    &[dest_local],
                    dcx.stmt_constraints,
                );
            }
            debug!("modeled {label} as identity (bb{})", dcx.bb_idx);
        } else {
            emit_sound_fallback_goto(
                self,
                dcx.from_app,
                *target,
                dcx.modified_locals,
                &[dest_local],
                dcx.stmt_constraints,
            );
        }
        true
    }
}
