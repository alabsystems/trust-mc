// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// CHC heap operation implementations: alloc, dealloc, realloc.
// Extracted from stubs_alloc.rs per #2408 (500 LOC decomposition target).
use super::stubs::StubKind;
use super::types::{POINTER_WIDTH, bv8_sort};
use super::{AllocCallResult, ChcCtx, chc_fresh_name, codegen_expr_heap, declare_pending_var};
use crate::args::ChcTrackLevel;
use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::Operand;
use std::collections::HashSet;
use std::sync::Arc;
use tracing::{debug, warn};
impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Alignment a C `malloc` result is guaranteed to carry.
    ///
    /// C requires the returned block to be suitably aligned for any object with
    /// a fundamental alignment requirement (`_Alignof(max_align_t)`), which is
    /// 16 on every 64-bit target trust-mc encodes. The `libc::malloc` ABI has no
    /// alignment ARGUMENT, so this is a property of the callee, not of the call
    /// site — modelling it as anything weaker would under-align the result and
    /// produce spurious alignment violations on the first typed access.
    ///
    /// Part of #3175: direct `libc::malloc` FFI model.
    pub(in crate::codegen_ay::chc) const LIBC_MALLOC_ALIGN: u64 = 16;

    /// Translate `libc::malloc(size)` to CHC constraints.
    ///
    /// Same object model as [`Self::translate_rust_alloc`] with two differences
    /// that come straight from the C contract rather than from Rust's:
    /// - the alignment is [`Self::LIBC_MALLOC_ALIGN`], not a call argument;
    /// - `malloc(0)` is LEGAL (implementation-defined result), so the
    ///   `size != 0` precondition Rust's allocator carries is not emitted.
    ///
    /// Returns `None` when the size operand does not translate — the caller
    /// then falls through to the fail-closed undefined-foreign `error()` path
    /// rather than inventing an allocation.
    ///
    /// Part of #3175.
    pub(in crate::codegen_ay::chc) fn translate_libc_malloc(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<AllocCallResult> {
        self.translate_alloc_object(
            StubKind::RustAlloc,
            args,
            modified_locals,
            Some(Self::LIBC_MALLOC_ALIGN),
        )
    }

    /// Translate `__rust_alloc` / `__rust_alloc_zeroed` to CHC constraints.
    ///
    /// Per design:
    /// - Returns fresh pointer: (obj_id << 32) | 0
    /// - Sets obj_valid[obj_id] = true
    /// - Sets obj_size[obj_id] = size
    /// - Assumes allocation never fails (--no-malloc-may-fail)
    pub(in crate::codegen_ay::chc) fn translate_rust_alloc(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<AllocCallResult> {
        self.translate_alloc_object(stub, args, modified_locals, None)
    }

    /// Shared allocation-object model behind `translate_rust_alloc` and
    /// `translate_libc_malloc`.
    ///
    /// `callee_align` is `Some(a)` only for an ABI whose alignment is fixed by
    /// the CALLEE (C `malloc`) instead of passed as an argument; it also selects
    /// the C zero-size rule. `None` reproduces the Rust allocator contract
    /// byte-for-byte, so every pre-existing caller is unaffected.
    fn translate_alloc_object(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        callee_align: Option<u64>,
    ) -> Option<AllocCallResult> {
        // Support both alloc ABIs:
        // - __rust_alloc(size, align)
        // - std::alloc::alloc(layout) / alloc_zeroed(layout)
        let arg0_expr =
            args.first().and_then(|arg| self.resolve_layout_operand_expr(arg, modified_locals));
        let arg1_expr =
            args.get(1).and_then(|arg| self.resolve_layout_operand_expr(arg, modified_locals));
        let (size_expr, align_expr, args_resolved) = if let Some(align) = callee_align {
            // C `malloc(size)`: one argument, alignment fixed by the callee.
            let size = args
                .first()
                .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals))?;
            let size = crate::codegen_ay::types::coerce_bitvec_width_safe(
                size,
                POINTER_WIDTH,
                crate::codegen_ay::types::SignExtension::ZeroExtend,
            );
            size.sort().bitvec_width()?;
            (size, Expr::bitvec_const(u128::from(align), POINTER_WIDTH), true)
        } else if let Some((size, align)) = arg0_expr
            .clone()
            .and_then(Self::extract_layout_size_align)
            .or_else(|| arg1_expr.clone().and_then(Self::extract_layout_size_align))
        {
            // Part of #3841: When extract_layout_size_align succeeds but the
            // extracted size is symbolic (not a concrete BV constant), try to
            // recover concrete values from known_layout_sizes. This handles the
            // case where Layout::from_size_align(CONST, CONST).unwrap() goes
            // through a Result merge point that prevents constant propagation,
            // leaving the Layout local symbolic even though the concrete values
            // are cached from the LayoutFromSizeAlign stub.
            if !matches!(size.value(), ExprValue::BitVecConst { .. }) {
                if let Some(arg0) = args.first() {
                    if let Some((s, a)) = self.trace_arg_to_layout_pair(arg0) {
                        debug!(
                            size = s,
                            align = a,
                            "translate_rust_alloc: recovered concrete layout from trace"
                        );
                        (
                            Expr::bitvec_const(s as u128, POINTER_WIDTH),
                            Expr::bitvec_const(a as u128, POINTER_WIDTH),
                            true,
                        )
                    } else {
                        (size, align, true)
                    }
                } else {
                    (size, align, true)
                }
            } else {
                (size, align, true)
            }
        } else if let (Some(size_expr), Some(align_expr)) = (arg0_expr, arg1_expr) {
            (size_expr, align_expr, true)
        } else if stub == StubKind::BoxNew {
            // Part of #3159: BoxNew args are the value to box, not (size, align).
            // Resolve concrete size/align from the boxed value's Rust type.
            // Without this, obj_size is symbolic and dealloc size checks fail
            // (e.g., dyn_fn_once.rs "dealloc size mismatch").
            if let Some(arg0) = args.first()
                && let Ok(arg_ty) = arg0.ty(self.body.locals())
            {
                if let Ok(layout) = arg_ty.layout() {
                    let shape = layout.shape();
                    let type_size = shape.size.bytes();
                    let type_align: usize = shape.abi_align.try_into().unwrap_or(1);
                    debug!(
                        type_size,
                        type_align,
                        ?arg_ty,
                        "BoxNew: resolved concrete size/align from argument type"
                    );
                    let size = Expr::bitvec_const(type_size as u128, 64);
                    let align = Expr::bitvec_const(type_align as u128, 64);
                    (size, align, true)
                } else if let Some(type_size) = self.get_type_size(arg_ty) {
                    // Part of #4067: DST fallback — arg_ty.layout() fails for
                    // dynamically-sized types like Mutex<dyn Trait>. Use
                    // get_type_size/get_type_align which have DST fallback chains
                    // (transparent wrapper unwrapping, dyn-tail normalization,
                    // vtable metadata resolution).
                    let type_align = self.get_type_align(arg_ty).unwrap_or(8);
                    debug!(
                        type_size,
                        type_align,
                        ?arg_ty,
                        "BoxNew: resolved DST size/align via get_type_size (#4067)"
                    );
                    let size = Expr::bitvec_const(type_size as u128, 64);
                    let align = Expr::bitvec_const(type_align as u128, 64);
                    (size, align, true)
                } else {
                    // Part of #3447 diagnostic
                    warn!(
                        ?arg_ty,
                        "BoxNew: failed to resolve argument type layout; \
                         allocating with symbolic size"
                    );
                    // Part of #3447: Record that allocation size/align are unconstrained.
                    self.record_sound_fallback_reason("box_new_layout_unknown");
                    let symbolic_size =
                        declare_pending_var(chc_fresh_name("__alloc_size"), Sort::bitvec(64));
                    let symbolic_align =
                        declare_pending_var(chc_fresh_name("__alloc_align"), Sort::bitvec(64));
                    (symbolic_size, symbolic_align, false)
                }
            } else {
                // Part of #3447 diagnostic
                warn!(
                    "BoxNew: failed to resolve argument type; \
                     allocating with symbolic size"
                );
                self.record_sound_fallback_reason("box_new_layout_unknown");
                let symbolic_size =
                    declare_pending_var(chc_fresh_name("__alloc_size"), Sort::bitvec(64));
                let symbolic_align =
                    declare_pending_var(chc_fresh_name("__alloc_align"), Sort::bitvec(64));
                (symbolic_size, symbolic_align, false)
            }
        } else {
            // Fix #2745: When arguments can't be resolved, still allocate an
            // object. Returning None here leaves the pointer destination
            // unconstrained, causing false-positive dealloc safety checks
            // (offset != 0 on an unconstrained symbolic pointer).
            // Use declare_pending_var so the symbolic vars are declared in SMT.
            warn!(
                "RustAlloc: failed to resolve size/align arguments; \
                 allocating with symbolic size to preserve pointer constraints"
            );
            // Part of #3447: Record that alloc size/align are unconstrained.
            self.record_sound_fallback_reason("alloc_args_unresolved");
            let symbolic_size =
                declare_pending_var(chc_fresh_name("__alloc_size"), Sort::bitvec(64));
            let symbolic_align =
                declare_pending_var(chc_fresh_name("__alloc_align"), Sort::bitvec(64));
            (symbolic_size, symbolic_align, false)
        };

        // Allocate fresh object ID
        let obj_id = self.heap_state.next_heap_alloc_id().or_else(|| {
            warn!("RustAlloc: allocation ID overflow; falling back to unconstrained call");
            self.record_sound_fallback_reason("alloc_id_overflow");
            None
        })?;

        // Create pointer expression: (obj_id << 32) | 0
        let obj_id_expr = Expr::bitvec_const(obj_id as i128, 32);
        let ptr = Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32));
        let explicit_ptr_align = Self::try_extract_concrete_usize(&align_expr)
            .and_then(|align| u64::try_from(align).ok())
            .or_else(|| {
                args.first()
                    .and_then(|arg| self.trace_arg_to_layout_pair(arg).map(|(_, align)| align))
            })
            .or_else(|| {
                (stub == StubKind::BoxNew)
                    .then(|| {
                        args.first()
                            .and_then(|arg| arg.ty(self.body.locals()).ok())
                            .and_then(|arg_ty| self.get_type_align(arg_ty))
                    })
                    .flatten()
            })
            .filter(|align| *align > 1);

        // Build heap constraints using store() pattern (SSA-style update)
        let obj_valid_in = codegen_expr_heap::obj_valid_in();
        let obj_valid_out = codegen_expr_heap::obj_valid_out();
        let obj_size_in = codegen_expr_heap::obj_size_in();
        let obj_size_out = codegen_expr_heap::obj_size_out();

        // Constraint: obj_size__out = store(obj_size, obj_id, size)
        let is_zeroed = stub == StubKind::RustAllocZeroed;
        // Fix #2745: coerce size to BV32 for heap array index. When args were
        // not resolved, use a symbolic BV32 size (over-approximation: any size
        // is valid). The critical constraint is the pointer value, not the size.
        let size_32_for_heap = self.coerce_to_heap_bv32(size_expr.clone()).unwrap_or_else(|| {
            // Part of #3447: Record that heap object size BV32 coercion failed
            // — size is unconstrained (weakens dealloc size-mismatch checks).
            self.record_sound_fallback_reason("alloc_size_bv32_coercion_failed");
            declare_pending_var(
                crate::codegen_ay::names::alloc_obj_size_name(obj_id),
                Sort::bitvec(32),
            )
        });
        self.record_known_heap_alloc_size_expr(obj_id, &size_32_for_heap);
        // Constraint: obj_valid__out = store(obj_valid, obj_id, true)
        // Emit valid constraint first so obj_id_expr's last use is in size constraint (no clone).
        let valid_constraint =
            obj_valid_out.eq(obj_valid_in.store(obj_id_expr.clone(), Expr::bool_const(true)));
        let size_constraint = obj_size_out.eq(obj_size_in.store(obj_id_expr, size_32_for_heap));
        let mut heap_constraints = vec![valid_constraint, size_constraint];
        if let Some(align_bytes) = explicit_ptr_align {
            let align_expr = Expr::bitvec_const(align_bytes as u128, POINTER_WIDTH);
            let zero_expr = Expr::bitvec_const(0u64, POINTER_WIDTH);
            heap_constraints.push(ptr.clone().bvurem(align_expr).eq(zero_expr));
        }

        // Mark metadata arrays as modified (#1100 follow-up)
        self.mark_heap_metadata_modified();

        // Part of #1443: Assign region array for this allocation.
        // Region arrays are only meaningful at Ptr+ level where the full memory
        // model (store/load of heap content) is active. At Reg level, only
        // obj_valid/obj_size are needed for dealloc safety checks. (Fix #2736)
        let region_arr: Arc<str> = if self.track_level >= ChcTrackLevel::Ptr {
            let (arr, _out) = self.assign_region_array_to_relation(
                obj_id,
                bv8_sort(), // Raw allocation uses bytes
            );
            arr
        } else {
            Arc::from("(none)")
        };

        debug!(
            obj_id,
            stub = ?stub,
            args_resolved,
            region = %region_arr,
            "CHC: RustAlloc - allocated heap object with store constraints"
        );
        if is_zeroed {
            self.heap_state.mark_heap_obj_zeroed(obj_id);
        }

        // Keep alloc precondition checks enabled only when args are resolved.
        let mut safety_checks = Vec::new();
        if args_resolved {
            // Part of #3159: Skip nonzero size check for ZST allocations.
            // Box::new(ZST) goes through the generic allocation path in
            // unoptimized MIR but doesn't call the allocator at runtime.
            // Checking size != 0 for ZSTs generates a trivially-false error
            // rule that causes spurious CTREX.
            let is_zero_size = matches!(
                size_expr.value(),
                ExprValue::BitVecConst { value, .. }
                    if u64::try_from(value).ok() == Some(0)
            );
            // C `malloc(0)` is legal (implementation-defined result), so the
            // Rust-allocator `size != 0` precondition must not be emitted for
            // it — doing so reports a violation on a well-defined program.
            if !is_zero_size && callee_align.is_none() {
                safety_checks.extend(self.nonzero_bv_check(size_expr.clone(), 64));
            }
            safety_checks.extend(self.power_of_two_bv_check(align_expr.clone(), POINTER_WIDTH));
            // Last use of align_expr — moved directly.
            safety_checks.extend(self.nonzero_bv_check(align_expr, 64));
            if is_zeroed {
                safety_checks.extend(self.fits_in_bv32_check(&size_expr));
                // Part of #3107: Look up concrete Layout size from the LayoutNew cache.
                // When the Layout arg was created by LayoutNew<T>(), the cache holds
                // the compile-time (size, align). This avoids falling back to the full
                // ITE-capped window when size_expr is BvExtract(Var(...)) — symbolic.
                let layout_concrete_size = args
                    .first()
                    .and_then(|arg| {
                        if let Operand::Copy(place) | Operand::Move(place) = arg {
                            self.known_layout_sizes
                                .get(&place.local)
                                .map(|(size, _align)| *size as usize)
                        } else {
                            None
                        }
                    })
                    .or_else(|| {
                        // Part of #3273: After MIR inlining, alloc_zeroed(Layout) becomes
                        // __rust_alloc_zeroed(layout.size(), layout.align()). The first
                        // arg's local was extracted from the Layout local via field projection.
                        // Trace through MIR assignments to find the Layout source.
                        self.trace_arg_to_layout_size(args.first()?)
                    });
                // Last use of size_expr — moved into zero-init.
                self.add_bounded_zero_init_constraints(
                    ptr.clone(),
                    size_expr,
                    layout_concrete_size,
                    &mut heap_constraints,
                );
            } else {
                // Last use of size_expr — moved directly.
                safety_checks.extend(self.fits_in_bv32_check(&size_expr));
            }
        }

        Some(AllocCallResult {
            result: Some(ptr),
            heap_constraints,
            safety_checks,
            alloc_obj_id: Some(obj_id),
            transition_branches: Vec::new(),
        })
    }
}
