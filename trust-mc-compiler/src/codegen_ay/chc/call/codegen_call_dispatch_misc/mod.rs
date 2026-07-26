// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Miscellaneous call dispatch helpers for CHC call terminators.
//! Part of #2306: include!() to proper module migration.
//! UnsafeCell::get handler split to codegen_call_unsafe_cell.rs.
//! IndexRange::len handler split to codegen_call_index_range_len.rs.
//! Dyn-dispatch helpers split to codegen_call_dispatch_dyn.rs (D3).
//! Generic pre-routes split to generic_preroutes.rs (Part of #4010).
//! Pointer-specific routes split to pointer_routes.rs (Part of #4010).
//! Raw-parts result helpers split to raw_parts_result.rs (Part of #4010).
//! Raw `ptr::from_raw_parts` helpers split to raw_ptr_from_raw_parts.rs (Part of #4187).

mod generic_preroutes;
mod pointer_routes;
mod raw_parts_ref_target;
mod raw_parts_result;
mod raw_ptr_from_raw_parts;

use crate::codegen_ay::stubs::StubKind;

use super::chc_call_context::{ChcCallContext, DispatchCallContext};
use super::codegen_call_cmp::CallCmp;
use super::codegen_call_iterator_adapter::CallIteratorAdapter;
use super::codegen_call_misc::CallMisc;
use super::codegen_call_ptr::CallPtr;
use super::codegen_call_ptr_identity::CallPtrIdentity;
use super::{ChcCtx, RelationApp, Rule, RuleBody};
use tracing::debug;

use generic_preroutes::CallDispatchMiscGenericPreroutes;
use pointer_routes::CallDispatchMiscPointerRoutes;

/// Extension trait for miscellaneous call dispatch in call-terminator codegen.
pub(in crate::codegen_ay::chc) trait CallDispatchMisc {
    fn try_dispatch_call_misc(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchMisc for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_misc(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let (bb_idx, func, args, destination, target, from_app, stmt_constraints, modified_locals) = (
            dcx.bb_idx,
            dcx.func,
            dcx.args,
            dcx.destination,
            dcx.target,
            dcx.from_app,
            dcx.stmt_constraints,
            dcx.modified_locals,
        );
        // Pre-routes: special detectors bypassing stub registry (Part of #2408 T4).

        // Generic pre-routes (early): trivial drop, Box drop, copy, raw_eq, slice::as_ptr.
        if self.try_dispatch_misc_generic_preroutes_early(dcx) {
            return true;
        }

        // Pointer-specific routes: ptr::metadata, DynMetadata::vtable_ptr,
        // to_raw_parts, Rc/Arc new/clone, wrapper Deref/as_ptr, Box into_raw/from_raw.
        if self.try_dispatch_misc_pointer_routes(dcx) {
            return true;
        }

        // Generic pre-routes (late): str::len, UnsafeCell::get, Cell::new,
        // ManuallyDrop::new, downcast_unchecked_ref, vtable intrinsics, IndexRange len.
        if self.try_dispatch_misc_generic_preroutes_late(dcx) {
            return true;
        }

        // === Single-detect route: one callee-path resolve for all stub-registry routes ===
        // Part of #2408 T4: ordered route table + explicit special-case branches.
        type Predicate = fn(StubKind) -> bool;
        type Handler<'ctx, 'mir> = fn(&mut ChcCtx<'ctx, 'mir>, &ChcCallContext<'_>);

        let stub = match self.detect_stub(func) {
            Some(s) => s,
            None => return false,
        };

        // Ordered route table for handlers with uniform ChcCallContext signature.
        // Preserves original dispatch priority for overlapping predicates.
        // NonNull identity ops (AsNonNullPtr, New, Cast) MUST precede is_nonnull_extra
        // (catch-all) — Part of #3184, Part of #3136, Part of #3589.
        let routes: [(Predicate, Handler<'tcx, 'body>); 12] = [
            (StubKind::is_primitive_clone, Self::codegen_call_primitive_clone),
            (StubKind::is_rawvec, Self::codegen_call_rawvec),
            (StubKind::is_try_residual, Self::codegen_call_try_residual),
            (StubKind::is_ptr_cast, Self::codegen_call_ptr_cast),
            (StubKind::is_display_cow, Self::codegen_call_display_cow),
            (
                |s| matches!(s, StubKind::NonNullAsNonNullPtr),
                Self::codegen_call_nonnull_passthrough,
            ),
            // Part of #3589: NonNull::new_unchecked and NonNull::cast are pointer
            // identity operations. Without explicit routing they fall through to
            // is_nonnull_extra → unconstrained, losing the pointer value and
            // allocation identity (breaks Rc store-to-load forwarding chain).
            (|s| matches!(s, StubKind::NonNullNew), Self::codegen_call_nonnull_passthrough),
            (|s| matches!(s, StubKind::NonNullCast), Self::codegen_call_nonnull_passthrough),
            (|s| matches!(s, StubKind::NonNullDangling), Self::codegen_call_nonnull_dangling),
            (StubKind::is_nonnull_extra, Self::codegen_call_unconstrained_stub),
            (StubKind::is_btreemap_internal, Self::codegen_call_unconstrained_stub),
            (StubKind::is_iterator_adapter, Self::codegen_call_iterator_adapter),
        ];
        let handler =
            routes.into_iter().find_map(|(predicate, handler)| predicate(stub).then_some(handler));

        if let Some(handler) = handler {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                handler(self, &cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "misc::route_table",
                    Some(stub),
                );
            }
            return true;
        }

        // === Special-case branches: handlers needing extra params beyond ChcCallContext ===

        if stub.is_mem_intrinsic() {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_mem_intrinsic(func, &cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "misc::mem_intrinsic",
                    Some(stub),
                );
            }
            return true;
        }

        if stub.is_layout_extra() {
            if let Some(target) = target {
                // Semantic construction for layout constructors;
                // unconstrained for the rest (Part of #2196, Bug 1 fix Part of #1739).
                // Part of #3641: LayoutFromSizeAlign added — checked constructor
                // now routes to layout_semantic.rs which handles the validity
                // guard and Result wrapping, matching the unchecked path.
                let is_semantic = matches!(
                    stub,
                    StubKind::LayoutNew
                        | StubKind::LayoutArray
                        | StubKind::LayoutArrayInner
                        | StubKind::LayoutFromSizeAlignUnchecked
                        | StubKind::LayoutFromSizeAlign
                        | StubKind::LayoutForValueRaw
                );
                if is_semantic {
                    let cx = ChcCallContext {
                        stub,
                        args,
                        destination,
                        target: *target,
                        from_app,
                        stmt_constraints,
                        modified_locals,
                    };
                    self.codegen_call_layout_semantic(func, &cx);
                } else {
                    let cx = ChcCallContext {
                        stub,
                        args,
                        destination,
                        target: *target,
                        from_app,
                        stmt_constraints,
                        modified_locals,
                    };
                    self.codegen_call_unconstrained_stub(&cx);
                }
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "misc::layout_extra",
                    Some(stub),
                );
            }
            return true;
        }

        if stub.is_alloc_extra() {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_alloc_extra(bb_idx, &cx);
            } else if stub == StubKind::HandleAllocError {
                // HandleAllocError is a reachable diverging path — emit error()
                // so the verifier flags it if reached (#2587).
                debug!("HandleAllocError in bb{} (no target) — emitting error()", bb_idx);
                let error_app = RelationApp::new("error", Vec::new());
                let body =
                    RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, []);
                self.vc.add_rule(Rule::new(body, error_app));
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "misc::alloc_extra",
                    Some(stub),
                );
            }
            return true;
        }

        if stub.is_primitive_cmp() {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                // Part of #3041: The cmp stub returns false when it cannot
                // resolve operands, declining the call so fn_inline can try
                // to inline the actual method body (e.g., derived PartialEq).
                if !self.codegen_call_primitive_cmp_stub(bb_idx, &cx) {
                    return false;
                }
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "misc::primitive_cmp",
                    Some(stub),
                );
            }
            return true;
        }

        false
    }
}
