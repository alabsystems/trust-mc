// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Layout struct helpers for AY codegen (#1112).
//!
//! Extracted from alloc.rs per #2231 — Layout::size, Layout::align,
//! Layout::dangling, Layout::is_size_align_valid,
//! Layout::from_size_align_unchecked, Layout::array<T>.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use super::StatementCodegen;
use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen `Layout::size(&self) -> usize`.
    ///
    /// Extracts the size field from a Layout struct.
    ///
    /// REQUIRES: args[0] is a Layout datatype or bitvec
    /// ENSURES: destination receives size as BitVec(POINTER_WIDTH)
    pub(super) fn codegen_layout_size(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Layout::size takes &self as argument
        if args.is_empty() {
            debug!("codegen_layout_size: missing layout arg — fail-closed (#2455)");
            return None;
        }

        let layout = if let Some(l) = self.codegen_operand(&args[0]) {
            l
        } else {
            debug!("codegen_layout_size: codegen_operand failed — fail-closed (#2455)");
            return None;
        };

        // Try to extract fld_size from Layout datatype
        let size = if let Some((s, _)) = self.try_extract_layout_fields(&layout) {
            s
        } else if layout.sort().is_bitvec() {
            // Already a bitvec, use directly
            layout
        } else {
            // Non-Layout, non-bitvec: use unconstrained symbolic (#2455)
            let name = self.ctx.fresh_name("layout_size");
            warn!("codegen_layout_size: unexpected sort {:?}, using symbolic", layout.sort());
            Expr::var(name, ptr_sort())
        };

        let size = self.coerce_to_ptr_width(size);
        self.assign_value_to_place(destination, size);
        debug!("codegen_layout_size: extracted size from layout");
        target
    }

    /// Codegen `Layout::align(&self) -> usize`.
    ///
    /// Extracts the alignment from a Layout struct.
    ///
    /// REQUIRES: args[0] is a Layout datatype or bitvec (optional)
    /// ENSURES: destination receives alignment as BitVec(POINTER_WIDTH)
    /// ENSURES: alignment is a power of 2
    pub(super) fn codegen_layout_align(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_layout_align: no args — fail-closed (#2455)");
            return None;
        }

        let align = if let Some(layout) = self.codegen_operand(&args[0]) {
            if let Some((_size, a)) = self.try_extract_layout_fields(&layout) {
                a
            } else {
                // Non-Layout sort: use unconstrained symbolic (#2455)
                let name = self.ctx.fresh_name("layout_align");
                warn!("codegen_layout_align: unexpected sort {:?}, using symbolic", layout.sort());
                Expr::var(name, ptr_sort())
            }
        } else {
            debug!("codegen_layout_align: codegen_operand failed — fail-closed (#2455)");
            return None;
        };

        let align = self.coerce_to_ptr_width(align);
        self.assign_value_to_place(destination, align);
        debug!("codegen_layout_align: returned alignment");
        target
    }

    /// Codegen `Layout::dangling(&self) -> NonNull<u8>`.
    ///
    /// Returns a dangling (but well-aligned, non-null) pointer.
    /// Used for zero-sized allocations where no real memory is needed.
    ///
    /// REQUIRES: args[0] is a Layout datatype (self)
    /// ENSURES: destination receives non-null pointer aligned to Layout's alignment
    /// ENSURES: pointer value == alignment (mirrors NonNull::dangling parity)
    pub(super) fn codegen_layout_dangling(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Extract alignment from the Layout self argument (#3412).
        // NonNull::dangling returns a pointer whose address equals the type's
        // alignment — this must match for types with align > 8.
        let align = args
            .first()
            .and_then(|arg| self.codegen_operand(arg))
            .and_then(|layout| self.try_extract_layout_fields(&layout).map(|(_, a)| a))
            .unwrap_or_else(|| {
                debug!("codegen_layout_dangling: no layout arg, falling back to 0x8");
                Expr::bitvec_const(0x8, POINTER_WIDTH)
            });
        let dangling_ptr = self.coerce_to_ptr_width(align);
        if self.ctx.config.extra_pointer_checks {
            self.ctx.heap_invalidate_no_provenance(dangling_ptr.clone());
        }
        self.assign_value_to_place(destination, dangling_ptr);
        debug!("codegen_layout_dangling: returned alignment-derived dangling pointer");
        target
    }

    /// Codegen `Layout::is_size_align_valid(size, align) -> bool`.
    ///
    /// Validates that size and alignment form a valid layout.
    /// For verification, we assume all layouts constructed by safe code are valid.
    ///
    /// ENSURES: destination receives Bool(true)
    pub(super) fn codegen_layout_is_size_align_valid(
        &mut self,
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Return true - safe Rust guarantees valid layouts
        let result = Expr::bool_const(true);
        self.assign_value_to_place(destination, result);
        debug!("codegen_layout_is_size_align_valid: returned true");
        target
    }

    /// Codegen `Layout::from_size_align_unchecked(size, align) -> Layout`.
    ///
    /// Creates a Layout from size and alignment without validation.
    /// This is the unsafe constructor used in hot allocation paths.
    ///
    /// REQUIRES: args.len() >= 2 (size, align)
    /// ENSURES: destination receives Layout Datatype with (fld_size, fld_align)
    pub(super) fn codegen_layout_from_size_align_unchecked(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Args: (size: usize, align: usize)
        if args.is_empty() {
            debug!("codegen_layout_from_size_align_unchecked: no args — fail-closed (#2455)");
            return None;
        }

        let size = if let Some(s) = self.codegen_operand(&args[0]) {
            s
        } else {
            // Size is the critical field — use unconstrained symbolic (#2455)
            let name = self.ctx.fresh_name("layout_unc_size");
            warn!("codegen_layout_from_size_align_unchecked: size codegen failed, using symbolic");
            Expr::var(name, ptr_sort())
        };

        // Sound over-approximation (#3285): leave destination unconstrained
        // rather than substituting align=1 on resolution failure.
        let align = match args.get(1).and_then(|arg| self.codegen_operand(arg)) {
            Some(a) => a,
            None => {
                warn!(
                    "codegen_layout_from_size_align_unchecked: align operand resolution failed — destination unconstrained (#3285)"
                );
                return target;
            }
        };

        let size = self.coerce_to_ptr_width(size);
        let align = self.coerce_to_ptr_width(align);

        let layout = self.create_layout_struct(size, align);
        self.assign_value_to_place(destination, layout);
        debug!("codegen_layout_from_size_align_unchecked: created layout");
        target
    }

    /// Codegen `Layout::array<T>(n) -> Result<Layout, LayoutError>`.
    ///
    /// Computes the layout for an array of `n` elements of type `T`.
    /// - size = sizeof(T) * n
    /// - align = alignof(T)
    ///
    /// Since allocation never fails (per --no-malloc-may-fail), we assume the
    /// result is always Ok(Layout).
    /// Codegen `Layout::array<T>(n)` with known element type info.
    ///
    /// This variant receives the element's size and alignment from the caller
    /// (extracted from the function's generic args in dispatch.rs).
    ///
    /// REQUIRES: args[0] is the element count `n`
    /// ENSURES: destination receives Layout struct or Ok(Layout)
    pub(in crate::codegen_ay::statement) fn codegen_layout_array_with_type(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        elem_size: usize,
        elem_align: usize,
    ) -> Option<BasicBlockIdx> {
        // Get the count argument — sound over-approximation (#3285):
        // leave destination unconstrained rather than substituting count=1.
        let count = match args.first().and_then(|arg| self.codegen_operand(arg)) {
            Some(c) => c,
            None => {
                warn!(
                    "codegen_layout_array_with_type: count operand resolution failed — destination unconstrained (#3285)"
                );
                return target;
            }
        };

        // Compute array size: sizeof(T) * n
        let elem_size_expr = Expr::bitvec_const(elem_size as u128, POINTER_WIDTH);
        let count_coerced = self.coerce_to_ptr_width(count);
        let array_size = elem_size_expr.bvmul(count_coerced.clone());

        // Part of #3408: overflow detection — Rust uses checked_mul.
        // Guard: total / elem_size == n (no wrapping). On overflow, leave
        // destination unconstrained via fresh symbolic (sound over-approximation).
        let no_overflow = if elem_size > 0 {
            Some(
                array_size
                    .clone()
                    .bvudiv(Expr::bitvec_const(elem_size as u128, POINTER_WIDTH))
                    .eq(count_coerced),
            )
        } else {
            None // ZST: size * n = 0 always, no overflow
        };

        let elem_align_expr = Expr::bitvec_const(elem_align as u128, POINTER_WIDTH);
        let layout = self.create_layout_struct(array_size, elem_align_expr);
        let layout = if let Some(guard) = no_overflow {
            let fresh = Expr::var(self.ctx.fresh_name("layout_overflow"), layout.sort().clone());
            Expr::ite(guard, layout, fresh)
        } else {
            layout
        };
        self.assign_value_to_place(destination, layout);
        debug!(
            "codegen_layout_array: computed layout with elem_size={} elem_align={}",
            elem_size, elem_align
        );
        target
    }

    /// Codegen `Layout::array::inner(element_layout, n)` (Part of #3273).
    ///
    /// Unlike `codegen_layout_array_with_type`, this takes runtime args for the Layout and count.
    ///
    /// The actual nightly signature is: `inner(element_layout: Layout, n: usize)`.
    /// REQUIRES: args[0] = element_layout (Layout struct), args[1] = n (count)
    /// ENSURES: destination receives Layout struct or Ok(Layout)
    pub(in crate::codegen_ay::statement) fn codegen_layout_array_inner(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let layout_expr = match args.first().and_then(|arg| self.codegen_operand(arg)) {
            Some(e) => e,
            None => {
                warn!(
                    "codegen_layout_array_inner: layout operand resolution failed — destination unconstrained (#3285)"
                );
                return target;
            }
        };
        let count = match args.get(1).and_then(|arg| self.codegen_operand(arg)) {
            Some(c) => c,
            None => {
                warn!(
                    "codegen_layout_array_inner: count operand resolution failed — destination unconstrained (#3285)"
                );
                return target;
            }
        };

        // Extract element_size and align from the Layout struct.
        let (elem_size, align) = if let Some((s, a)) = self.try_extract_layout_fields(&layout_expr)
        {
            (s, a)
        } else {
            warn!(
                "codegen_layout_array_inner: layout field extraction failed — destination unconstrained"
            );
            return target;
        };

        let elem_size_coerced = self.coerce_to_ptr_width(elem_size);
        let count_coerced = self.coerce_to_ptr_width(count);
        let array_size = elem_size_coerced.clone().bvmul(count_coerced.clone());

        // Part of #3408: overflow detection for runtime elem_size.
        // size_nonzero => (total / size == n) — no wrapping.
        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let size_nonzero = elem_size_coerced.clone().eq(zero).not();
        let no_wrap = array_size.clone().bvudiv(elem_size_coerced).eq(count_coerced);
        let no_overflow = size_nonzero.implies(no_wrap);

        let align_coerced = self.coerce_to_ptr_width(align);
        let layout = self.create_layout_struct(array_size, align_coerced);
        let fresh = Expr::var(self.ctx.fresh_name("layout_overflow"), layout.sort().clone());
        let layout = Expr::ite(no_overflow, layout, fresh);
        self.assign_value_to_place(destination, layout);
        debug!("codegen_layout_array_inner: computed layout from runtime args");
        target
    }

    /// Codegen `Layout::from_size_align(size, align) -> Result<Layout, LayoutError>`.
    ///
    /// Creates a Layout after validating size and alignment.
    /// For verification, we assume all layouts are valid (safe Rust guarantee)
    /// and return Ok(Layout), identical to `from_size_align_unchecked`.
    ///
    /// REQUIRES: args.len() >= 2 (size, align)
    /// ENSURES: destination receives Layout Datatype with (fld_size, fld_align)
    pub(super) fn codegen_layout_from_size_align(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Safe variant delegates to unchecked — validation is assumed to pass
        self.codegen_layout_from_size_align_unchecked(args, destination, target)
    }

    /// Codegen `Layout::calculate_layout_for(n) -> Option<(Layout, usize)>`.
    ///
    /// Computes the layout for `n` instances of a type, returning the layout
    /// and the offset of the next instance. Semantically similar to `Layout::array`
    /// but returns `(Layout, usize)` instead of `Result<Layout, LayoutError>`.
    ///
    /// For verification, we construct the Layout using element type info from
    /// generic args and return it. The offset is `n * sizeof(T)`.
    ///
    /// REQUIRES: args.len() >= 1 (count n)
    /// ENSURES: destination receives Layout struct
    pub(super) fn codegen_layout_calculate_layout_for(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let (elem_size, elem_align) = self.extract_element_type_layout(func);
        self.codegen_layout_array_with_type(args, destination, target, elem_size, elem_align)
    }

    /// Codegen `Layout::for_value_raw(ptr) -> Layout`.
    ///
    /// Returns the layout of the value pointed to by `ptr`.
    /// For sized types, this is compile-time known from the pointee type.
    /// For verification, we extract type info from the function's generic args.
    ///
    /// ENSURES: destination receives Layout struct with (sizeof(T), alignof(T))
    pub(super) fn codegen_layout_for_value_raw(
        &mut self,
        func: &Operand,
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let (size, align) = self.extract_element_type_layout(func);
        let size_expr = Expr::bitvec_const(size as u128, POINTER_WIDTH);
        let align_expr = Expr::bitvec_const(align as u128, POINTER_WIDTH);
        let layout = self.create_layout_struct(size_expr, align_expr);
        self.assign_value_to_place(destination, layout);
        debug!("codegen_layout_for_value_raw: size={} align={}", size, align);
        target
    }

    /// Helper: Create a Layout struct expression.
    ///
    /// Layout has two fields: fld_size (usize) and fld_align (usize).
    /// Returns a proper AY Datatype so `try_extract_layout_fields` can
    /// recover both fields downstream.
    #[must_use]
    pub(super) fn create_layout_struct(&self, size: Expr, align: Expr) -> Expr {
        let layout_sort = struct_sort("Layout", names::layout_fields());
        Expr::datatype_constructor("Layout", "Layout_mk", vec![size, align], layout_sort)
    }
}
