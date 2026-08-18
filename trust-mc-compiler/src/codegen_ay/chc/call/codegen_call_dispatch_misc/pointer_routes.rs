// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer-specific routes: ptr::metadata, DynMetadata::vtable_ptr,
//! raw-pointer to_raw_parts, Rc/Arc new/clone, pointer-wrapper Deref/as_ptr,
//! Box into_raw/from_raw.
//! Extracted from codegen_call_dispatch_misc (Part of #4010).

use crate::codegen_ay::stubs::StubKind;

use super::super::ChcCtx;
use super::super::chc_call_context::{ChcCallContext, DispatchCallContext};
use super::super::codegen_call_ptr_identity::CallPtrIdentity;
use super::super::dispatch_helpers::DispatchHelpers;

pub(super) fn is_raw_ptr_to_raw_parts_path(path: &str) -> bool {
    path.ends_with("::to_raw_parts")
        && (path.contains("ptr::const_ptr::<impl *const")
            || path.contains("ptr::mut_ptr::<impl *mut"))
}

/// Part of #4153: detect `NonNull::from_raw_parts` — the inverse of `to_raw_parts`.
pub(super) fn is_nonnull_from_raw_parts_path(path: &str) -> bool {
    let lower = path.to_ascii_lowercase();
    path.ends_with("::from_raw_parts")
        && (path.contains("NonNull") || lower.contains("non_null") || lower.contains("nonnull"))
}

pub(super) fn is_raw_ptr_from_raw_parts_path(path: &str) -> bool {
    (path.ends_with("::from_raw_parts") || path.ends_with("::from_raw_parts_mut"))
        && !path.contains("NonNull")
        && (path.contains("ptr::const_ptr::<impl *const")
            || path.contains("ptr::mut_ptr::<impl *mut")
            || path.contains("::ptr::"))
}

pub(super) fn is_ptr_metadata_path(path: &str) -> bool {
    path.ends_with("::metadata")
        && (path == "core::ptr::metadata"
            || path == "std::ptr::metadata"
            || path.contains("::ptr::metadata"))
}

pub(super) fn is_dyn_metadata_vtable_ptr_path(path: &str) -> bool {
    path.contains("DynMetadata")
        && (path.ends_with(">::vtable_ptr") || path.ends_with("::vtable_ptr"))
}

/// Extension trait for pointer-specific misc dispatch routes.
pub(super) trait CallDispatchMiscPointerRoutes {
    fn try_dispatch_misc_pointer_routes(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchMiscPointerRoutes for ChcCtx<'tcx, 'body> {
    fn try_dispatch_misc_pointer_routes(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let func = dcx.func;
        let callee_path = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(func))
            .or_else(|| self.resolve_fn_def_name(func));

        // `std::ptr::metadata` — resolve metadata through the dedicated
        // ptr-metadata path instead of falling through to `P_inf_*`.
        if callee_path.as_deref().is_some_and(is_ptr_metadata_path) {
            return self.emit_identity_call(dcx, "misc::ptr_metadata", |ctx, d| {
                d.args
                    .first()
                    .and_then(|arg| ctx.translate_ptr_metadata(arg, d.modified_locals))
                    .map(|meta| meta.into_expr())
            });
        }

        // `DynMetadata::<Dyn>::vtable_ptr` — the CHC metadata value already is
        // the vtable-id/pointer discriminant, so this is an identity cast.
        if callee_path.as_deref().is_some_and(is_dyn_metadata_vtable_ptr_path) {
            return self.emit_identity_call(dcx, "misc::dyn_metadata_vtable_ptr", |ctx, d| {
                d.args.first().and_then(|arg| {
                    ctx.translate_operand_with_modified(arg, d.modified_locals)
                        .or_else(|| ctx.resolve_ref_operand(arg, d.modified_locals))
                })
            });
        }

        // Part of #4004: raw-pointer `to_raw_parts()` must not fall through to
        // an inferable summary. The returned tuple is just the pointer's thin
        // component plus existing metadata (`std::ptr::metadata`).
        if callee_path.as_deref().is_some_and(is_raw_ptr_to_raw_parts_path) {
            self.codegen_raw_ptr_to_raw_parts_call(dcx);
            return true;
        }

        // Part of #4187: raw `ptr::from_raw_parts(data, len)` for `*const str`
        // / `*const [T]` is represented in CHC as a thin pointer value plus the
        // `subslice_len` side table, not as an inlined stdlib body.
        if callee_path.as_deref().is_some_and(is_raw_ptr_from_raw_parts_path) {
            self.codegen_raw_ptr_from_raw_parts_call(dcx);
            return true;
        }

        // Part of #4153: `NonNull::from_raw_parts(data_ptr, metadata)` — the
        // inverse of `to_raw_parts()`. Reassemble a wide `NonNull<dyn Trait>`
        // from the two explicit call arguments.
        if callee_path.as_deref().is_some_and(is_nonnull_from_raw_parts_path) {
            self.codegen_nonnull_from_raw_parts_call(dcx);
            return true;
        }

        // Part of #3977: Rc::new / Arc::new — dedicated alloc + value store.
        if callee_path.as_deref().is_some_and(Self::is_rc_arc_new_path) {
            self.codegen_rc_arc_new(dcx);
            return true;
        }

        // Part of #3978: Rc::clone / Arc::clone — pointer identity with metadata.
        if callee_path.as_deref().is_some_and(Self::is_rc_arc_clone_path) {
            self.codegen_rc_arc_clone(dcx);
            return true;
        }

        // Pointer-wrapper Deref::deref — wrapper-peeling pointer identity.
        if callee_path.as_deref().is_some_and(Self::is_shared_pointer_wrapper_constructor_path) {
            self.codegen_pointer_wrapper_from_inner_in(dcx);
            return true;
        }

        if callee_path
            .as_deref()
            .is_some_and(|path| path.ends_with("::into_raw") && path.contains("boxed::Box"))
        {
            if let Some(target) = dcx.target {
                let cx = ChcCallContext {
                    stub: StubKind::PrimitiveClone,
                    args: dcx.args,
                    destination: dcx.destination,
                    target: *target,
                    from_app: dcx.from_app,
                    stmt_constraints: dcx.stmt_constraints,
                    modified_locals: dcx.modified_locals,
                };
                self.codegen_call_box_into_raw(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(dcx.bb_idx),
                    "misc::box_into_raw_call",
                    None,
                );
            }
            return true;
        }

        if callee_path.as_deref().is_some_and(|path| {
            (path.ends_with("::from_raw_in") || path.ends_with("::from_raw"))
                && path.contains("boxed::Box")
        }) {
            if let Some(target) = dcx.target {
                let cx = ChcCallContext {
                    stub: StubKind::PrimitiveClone,
                    args: dcx.args,
                    destination: dcx.destination,
                    target: *target,
                    from_app: dcx.from_app,
                    stmt_constraints: dcx.stmt_constraints,
                    modified_locals: dcx.modified_locals,
                };
                self.codegen_call_box_from_raw_in(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(dcx.bb_idx),
                    "misc::box_from_raw_in_call",
                    None,
                );
            }
            return true;
        }

        // Part of #4139: Rc/Arc::into_raw — pointer identity (same as Box::into_raw).
        if callee_path.as_deref().is_some_and(|path| {
            path.ends_with("::into_raw") && (path.contains("rc::Rc") || path.contains("sync::Arc"))
        }) {
            if let Some(target) = dcx.target {
                let cx = ChcCallContext {
                    stub: StubKind::PrimitiveClone,
                    args: dcx.args,
                    destination: dcx.destination,
                    target: *target,
                    from_app: dcx.from_app,
                    stmt_constraints: dcx.stmt_constraints,
                    modified_locals: dcx.modified_locals,
                };
                self.codegen_call_rc_arc_into_raw(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(dcx.bb_idx),
                    "misc::rc_arc_into_raw_call",
                    None,
                );
            }
            return true;
        }

        // Part of #4139: Rc/Arc::from_raw — reconstruct wrapper from raw pointer.
        // The public `from_raw` path can monomorphize through allocator-aware
        // `from_raw_in`; model both before stdlib layout arithmetic is inlined.
        if callee_path.as_deref().is_some_and(|path| {
            (path.ends_with("::from_raw") || path.ends_with("::from_raw_in"))
                && (path.contains("rc::Rc") || path.contains("sync::Arc"))
        }) {
            if let Some(target) = dcx.target {
                let cx = ChcCallContext {
                    stub: StubKind::PrimitiveClone,
                    args: dcx.args,
                    destination: dcx.destination,
                    target: *target,
                    from_app: dcx.from_app,
                    stmt_constraints: dcx.stmt_constraints,
                    modified_locals: dcx.modified_locals,
                };
                self.codegen_call_rc_arc_from_raw(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(dcx.bb_idx),
                    "misc::rc_arc_from_raw_call",
                    None,
                );
            }
            return true;
        }

        if callee_path.as_deref().is_some_and(Self::is_pointer_wrapper_deref_path) {
            self.codegen_pointer_wrapper_deref_call(dcx);
            return true;
        }

        // Part of #3768: Rc/Arc `as_ptr`/`as_mut_ptr` expose the same value-field
        // pointer as Deref and must preserve dyn vtable side metadata.
        if callee_path.as_deref().is_some_and(Self::is_pointer_wrapper_as_ptr_path) {
            self.codegen_pointer_wrapper_deref_call(dcx);
            return true;
        }

        false
    }
}
