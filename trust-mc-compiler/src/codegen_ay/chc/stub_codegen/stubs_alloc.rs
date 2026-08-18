// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// CHC stub implementations for heap allocation intrinsics (converted from include!() per #2595).
// Heap operation method bodies (alloc, dealloc, realloc) in stubs_alloc_heap_ops.rs per #2408.
use super::stubs::StubKind;
use super::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort};
use super::{AllocCallResult, ChcCtx, StubTranslateArgs};
use crate::codegen_ay::ptr_repr::PtrRepr;
use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::Operand;
use std::collections::HashSet;
use tracing::{debug, warn};
impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Byte window copied/initialized for heap-model array overlays during alloc/realloc.
    /// 64 bytes covers 16 i32 elements, 8 i64 elements — sufficient for typical unit test
    /// Vec sizes. Trade-off: each byte_offset step emits one store constraint per tracked
    /// type array; at 64 bytes with 4-byte elements this is 16 stores per array.
    const ALLOC_ARRAY_WINDOW_BYTES: usize = 64;

    /// Safety cap on ITE-guarded zero-init/copy iterations when concrete allocation
    /// size is unknown. Each ITE guard creates a two-reference fan-out in the
    /// expression DAG (one in the store's array arg, one in the ITE's else-branch
    /// select). For N iterations the DAG-to-tree serialization expands to 2^N leaf
    /// nodes. Part of #3273: 64 iterations → 2^64 nodes → 39.6 GB .smt2 file.
    /// 16 iterations → 2^16 ≈ 65K nodes → ~3 MB per type array (safe).
    const ALLOC_ITE_CAP_BYTES: usize = 16;

    /// Accepted allocation-related stub variants.
    const ALLOC_STUBS: &'static [StubKind] = &[
        StubKind::BoxNew,
        StubKind::RustAlloc,
        StubKind::RustAllocZeroed,
        StubKind::RustDealloc,
        StubKind::RustRealloc,
        StubKind::LayoutSize,
        StubKind::LayoutAlign,
        StubKind::LayoutIsSizeAlignValid,
        StubKind::LayoutPaddingNeededFor,
    ];

    /// Detects if a function call is a heap allocation intrinsic.
    /// Part of #1100: AY heap allocation model.
    ///
    /// Returns the StubKind if detected, None otherwise.
    pub(in crate::codegen_ay::chc) fn detect_alloc_stub(&self, func: &Operand) -> Option<StubKind> {
        self.detect_stub_filtered(func, Self::ALLOC_STUBS, "alloc")
    }

    /// Extracts `(size, align)` from a packed `Layout` bitvector.
    ///
    /// Layout values are encoded as `bv128 = concat(size:bv64, align:bv64)`.
    pub(in crate::codegen_ay::chc) fn extract_layout_size_align(
        layout_expr: Expr,
    ) -> Option<(Expr, Expr)> {
        (layout_expr.sort().bitvec_width() == Some(128))
            .then(|| (layout_expr.clone().extract(127, 64), layout_expr.extract(63, 0)))
    }

    /// Build `Layout::is_size_align_valid(size, align)` as a symbolic bool.
    ///
    /// Rust layout validity requires:
    /// - non-zero power-of-two alignment
    /// - rounding `size` up to alignment does not wrap
    pub(in crate::codegen_ay::chc) fn layout_size_align_validity_expr(
        &self,
        size_expr: Expr,
        align_expr: Expr,
    ) -> Option<Expr> {
        let size = coerce_bitvec_width_safe(size_expr, POINTER_WIDTH, SignExtension::ZeroExtend);
        let align = coerce_bitvec_width_safe(align_expr, POINTER_WIDTH, SignExtension::ZeroExtend);
        size.sort().bitvec_width()?;
        align.sort().bitvec_width()?;

        let align_nonzero = self.nonzero_bv_check(align.clone(), POINTER_WIDTH)?;
        let align_pow2 = self.power_of_two_bv_check(align.clone(), POINTER_WIDTH)?;
        // Last use of align — moved into bvsub.
        let align_minus_one = align.bvsub(Expr::bitvec_const(1, POINTER_WIDTH));
        let rounded_size = size.clone().bvadd(align_minus_one);
        // Last use of size — moved into bvuge.
        let no_round_overflow = rounded_size.bvuge(size);

        Some(align_nonzero.and(align_pow2).and(no_round_overflow))
    }

    /// Resolves an operand that may represent `Layout` into a concrete expression.
    ///
    /// For `&Layout`/`*const Layout` arguments, this loads the pointee value from
    /// memory so callers can extract `(size, align)` from the packed `bv128`.
    ///
    /// Part of #3641: When the raw expression is not already a packed bv128,
    /// consults `known_layout_sizes` and MIR tracing to rebuild the packed
    /// layout from cached concrete `(size, align)` pairs.
    pub(in crate::codegen_ay::chc) fn resolve_layout_operand_expr(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if let Some(layout) = self.resolve_ref_operand(operand, modified_locals) {
            if layout.sort().bitvec_width() == Some(128)
                && !matches!(
                    layout.value(),
                    ExprValue::BitVecConst { .. } | ExprValue::BvConcat(..)
                )
                && let Some((size, align)) = self.trace_arg_to_layout_pair(operand)
            {
                debug!(
                    size,
                    align, "resolve_layout_operand_expr: recovered concrete referenced Layout"
                );
                return Some(
                    Expr::bitvec_const(size as i128, POINTER_WIDTH)
                        .concat(Expr::bitvec_const(align as i128, POINTER_WIDTH)),
                );
            }
            return Some(layout);
        }

        let raw_expr = self.translate_operand_with_modified(operand, modified_locals)?;
        if raw_expr.sort().bitvec_width() == Some(128) {
            // Part of #3841: When the Layout local is BV128 but symbolic (not a
            // concrete constant), check known_layout_sizes for a cached concrete
            // value. This handles Layout::from_size_align(CONST, CONST).unwrap()
            // where the Result merge point prevents constant propagation from
            // making the Layout local concrete.
            if !matches!(raw_expr.value(), ExprValue::BitVecConst { .. } | ExprValue::BvConcat(..))
            {
                if let Some((size, align)) = self.trace_arg_to_layout_pair(operand) {
                    debug!(
                        size,
                        align, "resolve_layout_operand_expr: recovered concrete bv128 from trace"
                    );
                    let layout = Expr::bitvec_const(size as i128, POINTER_WIDTH)
                        .concat(Expr::bitvec_const(align as i128, POINTER_WIDTH));
                    return Some(layout);
                }
            }
            return Some(raw_expr);
        }

        // Part of #3641: Prefer cached layout-pair reconstruction before any
        // memory load. MIR often forwards `Layout` through `&Layout` / local
        // addresses, and loading those addresses via `load_from_memory` injects
        // heap-style safety checks that do not apply to stack-local layouts.
        if let Some((size, align)) = self.trace_arg_to_layout_pair(operand) {
            debug!(
                size,
                align, "resolve_layout_operand_expr: rebuilt packed bv128 from known_layout_sizes"
            );
            let layout = Expr::bitvec_const(size as i128, POINTER_WIDTH)
                .concat(Expr::bitvec_const(align as i128, POINTER_WIDTH));
            return Some(layout);
        }

        // The MIR type decides whether this operand is a pointer — it is a
        // `&Layout` / `*const Layout` or it is not, and that is knowable without
        // looking at the term. The width test that used to lead this condition
        // decided the same thing by measuring the term, which is the inference
        // this campaign deletes; `PtrRepr::thin_address` now supplies only the
        // *shape* (the same predicate, in the register where it is honest) and
        // hands back a `Loc` for the load.
        if let Some(op_ty) = operand.ty(self.body.locals()).ok() {
            let pointee_ty = match op_ty.kind() {
                rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(_, inner, _))
                | rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::RawPtr(inner, _)) => {
                    Some(inner)
                }
                _ => None, // external enum: TyKind
            };
            if let Some(inner) = pointee_ty
                && let Some(layout_addr) = PtrRepr::thin_address(&raw_expr)
                && let Some(loaded) = self.load_from_memory(layout_addr, inner)
                && loaded.as_expr().sort().bitvec_width() == Some(128)
            {
                return Some(loaded.into_expr());
            }
        }

        Some(raw_expr)
    }

    // Helper functions (copyable_elem_bytes, sorted_type_array_keys, zero_value_for_sort,
    // should_overlay_type_array, try_extract_concrete_usize) extracted to
    // stubs_alloc_overlay_helpers.rs per #3107.

    /// Encode zero-initialization for a fresh allocation over tracked type arrays.
    ///
    /// This is intentionally bounded to a fixed byte window and guarded by `size_expr`.
    /// It is sound (over-approximating) and covers small-object harnesses like std_alloc.
    ///
    /// When `size_expr` is a concrete constant, the byte window is capped to the actual
    /// allocation size, avoiding dead ITE guards and skipping type arrays whose element
    /// size exceeds the allocation. This reduces CHC formula size for small allocations.
    pub(in crate::codegen_ay::chc) fn add_bounded_zero_init_constraints(
        &mut self,
        ptr: Expr,
        size_expr: Expr,
        layout_concrete_size: Option<usize>,
        heap_constraints: &mut Vec<Expr>,
    ) {
        // Extract concrete size before coercion for window bounding.
        // Part of #3107: Prefer layout_concrete_size from the LayoutNew cache when
        // try_extract_concrete_usize can't resolve the symbolic expression (e.g.,
        // BvExtract over Var from a previous basic block).
        let concrete_size = Self::try_extract_concrete_usize(&size_expr).or(layout_concrete_size);
        // Part of #3273: When concrete_size is unknown, use the ITE safety cap
        // instead of the full 64-byte window to prevent exponential DAG-to-tree
        // blowup in Expr serialization (see ALLOC_ITE_CAP_BYTES doc).
        let effective_window = concrete_size
            .map(|s| s.min(Self::ALLOC_ARRAY_WINDOW_BYTES))
            .unwrap_or(Self::ALLOC_ITE_CAP_BYTES);
        if let Some(s) = concrete_size {
            debug!(concrete_size = s, effective_window, "zero_init: size-bounded window");
        } else {
            debug!(effective_window, "zero_init: ITE-capped window (concrete_size unknown)");
        }

        // Part of #3685: Pre-create typed arrays so the zero-init loop below can
        // write zeros to arrays (e.g., bv32 for i32) that don't exist yet.
        self.seed_typed_arrays_for_zeroed_alloc(effective_window);

        let size = coerce_bitvec_width_safe(size_expr, POINTER_WIDTH, SignExtension::ZeroExtend);
        let keys = self.sorted_type_array_keys();
        let mut modified_keys: Vec<String> = Vec::with_capacity(keys.len());

        for type_key in &keys {
            let (arr_name, elem_sort) = &self.heap_state.type_arrays[*type_key];
            if !Self::should_overlay_type_array(type_key, elem_sort) {
                continue;
            }
            let Some(elem_bytes) = Self::copyable_elem_bytes(elem_sort) else {
                continue;
            };
            // Skip type arrays whose element size exceeds the effective window.
            // No correctly-typed store/load can be in-bounds for such elements.
            if elem_bytes > effective_window {
                continue;
            }
            let Some(zero_value) = Self::zero_value_for_sort(elem_sort) else {
                continue;
            };

            let arr_sort = Sort::array(ptr_sort(), elem_sort.clone());
            let arr_in = Expr::var(arr_name.as_ref(), arr_sort.clone());
            let mut zeroed_arr = arr_in;
            let mut touched = false;

            for byte_offset in (0..effective_window).step_by(elem_bytes) {
                let bytes_needed = byte_offset + elem_bytes;
                let addr =
                    ptr.clone().bvadd(Expr::bitvec_const(byte_offset as i128, POINTER_WIDTH));
                // When the offset is provably in-bounds, emit unconditional zero store
                // instead of an ITE guard, reducing expression tree depth.
                let next_value = if concrete_size.is_some_and(|s| bytes_needed <= s) {
                    zero_value.clone()
                } else {
                    let in_bounds =
                        Expr::bitvec_const(bytes_needed as i128, POINTER_WIDTH).bvule(size.clone());
                    let keep_value = zeroed_arr.clone().select(addr.clone());
                    Expr::ite(in_bounds, zero_value.clone(), keep_value)
                };
                zeroed_arr = zeroed_arr.store(addr, next_value);
                touched = true;
            }

            if !touched {
                continue;
            }

            let arr_out = Expr::var(crate::codegen_ay::names::out_name(arr_name), arr_sort);
            heap_constraints.push(arr_out.eq(zeroed_arr));
            modified_keys.push(type_key.to_string());
        }

        for key in &modified_keys {
            self.mark_type_array_modified(key);
        }
    }

    /// #3728: Always-moved realloc copy constraints.
    /// Copies data from old allocation to new allocation for each tracked type
    /// array AND region array. No in-place branch — used by the always-moved
    /// realloc model.
    ///
    /// Fix #3677: Region arrays are indexed by full 64-bit pointer (obj_id<<32 |
    /// offset). After alias_region, the new obj_id shares the same region array
    /// variable, but loads use (new_id<<32|off) which is a different key than
    /// where the original store wrote (old_id<<32|off). Without explicit region
    /// copy constraints, the region load returns an unconstrained value and the
    /// solver produces a spurious CTREX.
    pub(in crate::codegen_ay::chc) fn add_always_moved_realloc_copy_constraints(
        &mut self,
        old_ptr: Expr,
        new_ptr: Expr,
        old_size_expr: Expr,
        layout_concrete_old_size: Option<usize>,
        constraints: &mut Vec<Expr>,
    ) {
        let new_obj_id = Self::try_extract_obj_id(&new_ptr);
        let concrete_old_size =
            Self::try_extract_concrete_usize(&old_size_expr).or(layout_concrete_old_size);
        let effective_window = concrete_old_size
            .map(|s| s.min(Self::ALLOC_ARRAY_WINDOW_BYTES))
            .unwrap_or(Self::ALLOC_ITE_CAP_BYTES);

        let old_size =
            coerce_bitvec_width_safe(old_size_expr, POINTER_WIDTH, SignExtension::ZeroExtend);
        let keys = self.sorted_type_array_keys();
        let mut modified_keys: Vec<String> = Vec::with_capacity(keys.len());

        for type_key in &keys {
            let (arr_name, elem_sort) = &self.heap_state.type_arrays[*type_key];
            if !Self::should_overlay_type_array(type_key, elem_sort) {
                continue;
            }
            let Some(elem_bytes) = Self::copyable_elem_bytes(elem_sort) else {
                continue;
            };
            if elem_bytes > effective_window {
                continue;
            }

            let arr_sort = Sort::array(ptr_sort(), elem_sort.clone());
            // Preserve same-block writes (e.g. `ptr.write(42)`) that still live in the
            // store chain when realloc runs before block-end drain.
            let arr_in = self
                .heap_state
                .get_store_chain(type_key)
                .cloned()
                .unwrap_or_else(|| Expr::var(arr_name.as_ref(), arr_sort.clone()));
            let mut moved_arr = arr_in.clone();
            let mut touched = false;

            for byte_offset in (0..effective_window).step_by(elem_bytes) {
                let bytes_needed = byte_offset + elem_bytes;
                let off_expr = Expr::bitvec_const(byte_offset as i128, POINTER_WIDTH);
                let old_addr = old_ptr.clone().bvadd(off_expr.clone());
                let new_addr = new_ptr.clone().bvadd(off_expr);
                let old_value = arr_in.clone().select(old_addr);
                let next_value = if concrete_old_size.is_some_and(|s| bytes_needed <= s) {
                    old_value
                } else {
                    let can_copy = Expr::bitvec_const(bytes_needed as i128, POINTER_WIDTH)
                        .bvule(old_size.clone());
                    let keep_value = moved_arr.clone().select(new_addr.clone());
                    Expr::ite(can_copy, old_value, keep_value)
                };
                moved_arr = moved_arr.store(new_addr, next_value);
                touched = true;
            }

            if !touched {
                continue;
            }

            let arr_out = Expr::var(crate::codegen_ay::names::out_name(arr_name), arr_sort);
            constraints.push(arr_out.eq(moved_arr));
            modified_keys.push(type_key.to_string());
        }

        for key in &modified_keys {
            self.mark_type_array_modified(key);
            if let Some(new_obj_id) = new_obj_id {
                self.heap_state.mark_heap_obj_type_overlay(new_obj_id, key);
            }
        }

        // Fix #3677: Region array copy constraints (see stubs_alloc_overlay_helpers.rs).
        self.add_realloc_region_copy_constraints(
            &old_ptr,
            &new_ptr,
            &old_size,
            concrete_old_size,
            effective_window,
            constraints,
        );
    }

    /// Translates a heap allocation intrinsic call to CHC constraints.
    ///
    /// Part of #1100: AY heap allocation model.
    ///
    /// D3 table-driven dispatch (Part of #2304): routes via declarative
    /// `stub_dispatch!` table instead of a hand-written match block.
    pub(in crate::codegen_ay::chc) fn translate_alloc_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<AllocCallResult> {
        let ctx = StubTranslateArgs { args, modified_locals, dest_local: None };
        stub_dispatch!(self, stub, &ctx, "translate_alloc_call",
            StubKind::BoxNew               => translate_box_new_alloc,
            StubKind::RustAlloc            => translate_rust_alloc_dispatch,
            StubKind::RustAllocZeroed      => translate_rust_alloc_zeroed_dispatch,
            StubKind::RustDealloc          => translate_rust_dealloc_dispatch,
            StubKind::RustRealloc          => translate_rust_realloc_dispatch,
            StubKind::LayoutSize           => translate_layout_size_dispatch,
            StubKind::LayoutAlign          => translate_layout_align_dispatch,
            StubKind::LayoutIsSizeAlignValid => translate_layout_is_size_align_valid_dispatch,
            StubKind::LayoutPaddingNeededFor => translate_layout_padding_needed_for_dispatch,
        )
    }

    fn translate_box_new_alloc(&mut self, ctx: &StubTranslateArgs<'_>) -> Option<AllocCallResult> {
        // BoxNew: opaque Box::new call when MIR doesn't desugar to exchange_malloc.
        // Args are the value to box (not size/align). translate_rust_alloc has a
        // BoxNew-specific path that resolves concrete size/align from the argument's
        // Rust type (Part of #3159: fixes dealloc size mismatch for Box<dyn Trait>).
        self.translate_rust_alloc(StubKind::BoxNew, ctx.args, ctx.modified_locals)
    }

    fn translate_rust_alloc_dispatch(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<AllocCallResult> {
        self.translate_rust_alloc(StubKind::RustAlloc, ctx.args, ctx.modified_locals)
    }

    fn translate_rust_alloc_zeroed_dispatch(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<AllocCallResult> {
        self.translate_rust_alloc(StubKind::RustAllocZeroed, ctx.args, ctx.modified_locals)
    }

    fn translate_rust_dealloc_dispatch(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<AllocCallResult> {
        self.translate_rust_dealloc(ctx.args, ctx.modified_locals)
    }

    fn translate_rust_realloc_dispatch(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<AllocCallResult> {
        self.translate_rust_realloc(ctx.args, ctx.modified_locals)
    }

    fn translate_layout_size_dispatch(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<AllocCallResult> {
        let layout_expr = ctx
            .args
            .first()
            .and_then(|arg| self.resolve_layout_operand_expr(arg, ctx.modified_locals))?;
        let layout_width = layout_expr.sort().bitvec_width();
        let Some((size, _)) = Self::extract_layout_size_align(layout_expr) else {
            warn!(
                width = ?layout_width,
                "LayoutSize: expected packed bv128 layout operand; falling back to unconstrained call"
            );
            self.record_sound_fallback_reason("layout_size_not_bv128");
            return None;
        };
        debug!("CHC: LayoutSize - extracted size from layout");
        Some(AllocCallResult {
            result: Some(size),
            heap_constraints: Vec::new(),
            safety_checks: Vec::new(),
            alloc_obj_id: None,
            transition_branches: Vec::new(),
        })
    }

    fn translate_layout_align_dispatch(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<AllocCallResult> {
        let layout_expr = ctx
            .args
            .first()
            .and_then(|arg| self.resolve_layout_operand_expr(arg, ctx.modified_locals))?;
        let layout_width = layout_expr.sort().bitvec_width();
        let Some((_, align)) = Self::extract_layout_size_align(layout_expr) else {
            warn!(
                width = ?layout_width,
                "LayoutAlign: expected packed bv128 layout operand; falling back to unconstrained call"
            );
            self.record_sound_fallback_reason("layout_align_not_bv128");
            return None;
        };
        debug!("CHC: LayoutAlign - extracted align from layout");
        Some(AllocCallResult {
            result: Some(align),
            heap_constraints: Vec::new(),
            safety_checks: Vec::new(),
            alloc_obj_id: None,
            transition_branches: Vec::new(),
        })
    }

    fn translate_layout_is_size_align_valid_dispatch(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<AllocCallResult> {
        let Some(size_expr) = ctx
            .args
            .first()
            .and_then(|arg| self.resolve_layout_operand_expr(arg, ctx.modified_locals))
        else {
            warn!(
                "LayoutIsSizeAlignValid: failed to resolve size operand; \
                 falling back to unconstrained call"
            );
            self.record_sound_fallback_reason("layout_valid_size_unresolved");
            return None;
        };
        let Some(align_expr) = ctx
            .args
            .get(1)
            .and_then(|arg| self.resolve_layout_operand_expr(arg, ctx.modified_locals))
        else {
            warn!(
                "LayoutIsSizeAlignValid: failed to resolve align operand; \
                 falling back to unconstrained call"
            );
            self.record_sound_fallback_reason("layout_valid_align_unresolved");
            return None;
        };
        let Some(validity) = self.layout_size_align_validity_expr(size_expr, align_expr) else {
            warn!(
                "LayoutIsSizeAlignValid: non-bitvec size/align operand; \
                 falling back to unconstrained call"
            );
            self.record_sound_fallback_reason("layout_valid_non_bitvec");
            return None;
        };
        debug!("CHC: LayoutIsSizeAlignValid - encoded symbolic validity expression");
        Some(AllocCallResult {
            result: Some(validity),
            heap_constraints: Vec::new(),
            safety_checks: Vec::new(),
            alloc_obj_id: None,
            transition_branches: Vec::new(),
        })
    }

    fn translate_layout_padding_needed_for_dispatch(
        &mut self,
        ctx: &StubTranslateArgs<'_>,
    ) -> Option<AllocCallResult> {
        let layout_expr = ctx
            .args
            .first()
            .and_then(|arg| self.resolve_layout_operand_expr(arg, ctx.modified_locals))?;
        let layout_width = layout_expr.sort().bitvec_width();
        let Some((size_expr, _)) = Self::extract_layout_size_align(layout_expr) else {
            warn!(
                width = ?layout_width,
                "LayoutPaddingNeededFor: expected packed bv128 layout operand; \
                 falling back to unconstrained call"
            );
            self.record_sound_fallback_reason("layout_padding_not_bv128");
            return None;
        };
        let Some(raw_align) = ctx
            .args
            .get(1)
            .and_then(|arg| self.resolve_layout_operand_expr(arg, ctx.modified_locals))
        else {
            warn!(
                "LayoutPaddingNeededFor: failed to resolve alignment operand; \
                 falling back to unconstrained call"
            );
            self.record_sound_fallback_reason("layout_padding_align_unresolved");
            return None;
        };

        let size = coerce_bitvec_width_safe(size_expr, POINTER_WIDTH, SignExtension::ZeroExtend);
        let align = coerce_bitvec_width_safe(raw_align, POINTER_WIDTH, SignExtension::ZeroExtend);
        if size.sort().bitvec_width().is_none() || align.sort().bitvec_width().is_none() {
            warn!(
                "LayoutPaddingNeededFor: non-bitvec size/alignment operand; \
                 falling back to unconstrained call"
            );
            self.record_sound_fallback_reason("layout_padding_non_bitvec");
            return None;
        }

        if let (Some(size), Some(align)) =
            (Self::try_extract_concrete_usize(&size), Self::try_extract_concrete_usize(&align))
            && align != 0
        {
            let padding = (align - (size % align)) % align;
            debug!(size, align, padding, "CHC: LayoutPaddingNeededFor - computed concrete padding");
            return Some(AllocCallResult {
                result: Some(Expr::bitvec_const(padding as i128, POINTER_WIDTH)),
                heap_constraints: Vec::new(),
                safety_checks: Vec::new(),
                alloc_obj_id: None,
                transition_branches: Vec::new(),
            });
        }

        let one = Expr::bitvec_const(1, POINTER_WIDTH);
        let align_minus_one = align.bvsub(one);
        let rounded = size.clone().bvadd(align_minus_one.clone()).bvand(align_minus_one.bvnot());
        let padding = rounded.bvsub(size);

        debug!("CHC: LayoutPaddingNeededFor - encoded symbolic round-up padding");
        Some(AllocCallResult {
            result: Some(padding),
            heap_constraints: Vec::new(),
            safety_checks: Vec::new(),
            alloc_obj_id: None,
            transition_branches: Vec::new(),
        })
    }
}
