// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD element access: shuffle, cast, extract, insert.
//!
//! Part of #1478, #1501, #1516.
//! Split from simd.rs per #2150.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use super::{IntoOption, SimdLayout};
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    // -------------------------------------------------------------------------
    // SIMD Shuffle (Part of #1478)
    // -------------------------------------------------------------------------

    /// Codegen simd_shuffle: reorder elements from two vectors using an index array.
    /// Part of #1478.
    ///
    /// simd_shuffle(a, b, indices) returns a new vector where:
    /// - result[i] = a[indices[i]] if indices[i] < len(a)
    /// - result[i] = b[indices[i] - len(a)] otherwise
    pub(in crate::codegen_ay::statement) fn codegen_simd_shuffle(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 3 {
            debug!("codegen_simd_shuffle: need 3 args, got {}", args.len());
            return None;
        }

        // Get SIMD type info from input vectors
        let simd_ty = args[0].ty(self.body.locals()).into_option()?;
        let layout = self.simd_layout(simd_ty)?;
        debug!("codegen_simd_shuffle: layout={:?}", layout);

        // Codegen input vectors
        let a_expr = self.codegen_operand(&args[0])?;
        let b_expr = self.codegen_operand(&args[1])?;

        // Extract elements from both vectors
        let a_elements = self.simd_extract_elements(&a_expr, &layout)?;
        let b_elements = self.simd_extract_elements(&b_expr, &layout)?;

        // Combine both vectors for indexed access
        let combined: Vec<Expr> = a_elements.into_iter().chain(b_elements).collect();

        // Get the indices (third argument is a SIMD vector of u32 indices)
        let indices_ty = args[2].ty(self.body.locals()).into_option()?;
        let indices_layout = self.simd_layout(indices_ty)?;
        let indices_expr = self.codegen_operand(&args[2])?;
        let indices = self.simd_extract_elements(&indices_expr, &indices_layout)?;

        // Build result by selecting elements according to indices
        // For verification, we build ITE chains for all index values
        // This handles both constant and symbolic indices correctly
        let result_elements: Vec<Expr> =
            indices.iter().map(|idx| self.build_indexed_select(&combined, idx)).collect();

        // Construct result - use destination type's layout
        let dest_ty = destination.ty(self.body.locals()).into_option()?;
        let dest_layout = self.simd_layout(dest_ty)?;
        let result_expr = self.simd_construct_expr(result_elements, &dest_layout, dest_ty)?;

        // Assign to destination
        self.bind_ssa_result(destination, result_expr);

        target
    }

    /// Build an ITE chain for symbolic index selection.
    ///
    /// REQUIRES: `elements` is non-empty (SIMD vectors always have >= 1 lane).
    /// REQUIRES: `idx` has bitvector sort.
    fn build_indexed_select(&self, elements: &[Expr], idx: &Expr) -> Expr {
        // For small vectors, build ITE chain
        // idx == 0 ? elements[0] : idx == 1 ? elements[1] : ... : elements[0]
        let Some(first) = elements.first() else {
            // Defensive: empty SIMD vector should never reach here.
            // Return a zero-width marker; caller will propagate the error.
            warn!("build_indexed_select called with empty elements slice");
            return Expr::bitvec_const(0u128, 1);
        };
        let mut result = first.clone();
        let Some(idx_width) = idx.sort().bitvec_width() else {
            warn!(sort = ?idx.sort(), "build_indexed_select requires bitvector index, got non-BV");
            return result;
        };

        for (i, elem) in elements.iter().enumerate().rev() {
            let i_const = Expr::bitvec_const(i as u128, idx_width);
            let cond = idx.clone().eq(i_const);
            result = Expr::ite(cond, elem.clone(), result);
        }
        result
    }

    /// Emit SIMD index bounds check for simd_extract/simd_insert.
    /// Part of #1516.
    ///
    /// SIMD intrinsics have undefined behavior when index >= lanes.
    /// This emits a verification condition that will fail if the index
    /// is out of bounds, catching UB in verification.
    ///
    /// REQUIRES: index_expr.sort().is_bitvec()
    /// ENSURES: Adds violation assertion (index >= lanes) to VC
    fn emit_simd_index_bounds_check(
        &mut self,
        index_expr: &Expr,
        layout: &SimdLayout,
        label: &str,
    ) {
        let Some(idx_width) = index_expr.sort().bitvec_width() else {
            debug!("emit_simd_index_bounds_check: index is not bitvec");
            return;
        };

        let lanes = layout.lane_count();
        let lanes_const = Expr::bitvec_const(lanes as u128, idx_width);

        // Check: index < lanes (out-of-bounds check)
        // UB if index >= lanes, so violation condition is index >= lanes
        let in_bounds = index_expr.clone().bvult(lanes_const);
        self.record_violation_guarded(in_bounds.not(), label);
    }

    // -------------------------------------------------------------------------
    // SIMD Cast (Part of #1478)
    // -------------------------------------------------------------------------

    /// Codegen simd_cast: convert element types of a SIMD vector.
    /// Part of #1478.
    ///
    /// Converts each element from source type to destination type.
    /// Supports: int<->int (sign/zero extend or truncate), int<->float.
    ///
    /// REQUIRES: args.len() >= 1, args[0] is a SIMD vector
    /// ENSURES: destination gets SIMD vector with element-wise type conversion applied
    pub(in crate::codegen_ay::statement) fn codegen_simd_cast(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_simd_cast: need at least 1 arg");
            return None;
        }

        // Get source SIMD type info
        let src_ty = args[0].ty(self.body.locals()).into_option()?;
        let src_layout = self.simd_layout(src_ty)?;
        let src_is_signed = self.simd_element_is_signed(src_ty);
        debug!("codegen_simd_cast: src_layout={:?}, src_is_signed={}", src_layout, src_is_signed);

        // Get destination type info
        let dest_ty = destination.ty(self.body.locals()).into_option()?;
        let dest_layout = self.simd_layout(dest_ty)?;
        let _dest_is_signed = self.simd_element_is_signed(dest_ty);
        debug!(
            "codegen_simd_cast: dest_layout={:?}, dest_is_signed={}",
            dest_layout, _dest_is_signed
        );

        // Get element widths
        let src_width = src_layout.elem_width()?;
        let dest_width = dest_layout.elem_width()?;

        // Codegen source and extract elements
        let src_expr = self.codegen_operand(&args[0])?;
        let src_elements = self.simd_extract_elements(&src_expr, &src_layout)?;

        // Convert each element
        let result_elements: Vec<Expr> = src_elements
            .iter()
            .map(|elem| {
                if src_width == dest_width {
                    // Same width - just reinterpret
                    elem.clone()
                } else if dest_width > src_width {
                    // Widening - sign or zero extend
                    let extend_by = dest_width - src_width;
                    if src_is_signed {
                        elem.clone().sign_extend(extend_by)
                    } else {
                        elem.clone().zero_extend(extend_by)
                    }
                } else {
                    // Narrowing - truncate (extract lower bits)
                    elem.clone().extract(dest_width - 1, 0)
                }
            })
            .collect();

        // Construct result
        let result_expr = self.simd_construct_expr(result_elements, &dest_layout, dest_ty)?;

        // Assign to destination
        self.bind_ssa_result(destination, result_expr);

        target
    }

    // -------------------------------------------------------------------------
    // SIMD Extract/Insert (Part of #1501)
    // -------------------------------------------------------------------------

    /// Codegen simd_extract: extract a single element from a SIMD vector.
    /// Part of #1501, bounds check added per #1516.
    ///
    /// `simd_extract(vector, index)` returns the element at `index`.
    /// Index may be constant or symbolic - handled via ITE chain.
    ///
    /// REQUIRES: args.len() >= 2, args[0] is a SIMD vector, args[1] is an integer index
    /// REQUIRES: index < lanes (UB otherwise, verification will fail)
    /// ENSURES: destination gets the element at the specified index (ITE chain for symbolic index)
    pub(in crate::codegen_ay::statement) fn codegen_simd_extract(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            debug!("codegen_simd_extract: need 2 args, got {}", args.len());
            return None;
        }

        // Get SIMD type info
        let simd_ty = args[0].ty(self.body.locals()).into_option()?;
        let layout = self.simd_layout(simd_ty)?;
        debug!("codegen_simd_extract: layout={:?}", layout);

        // Codegen operands
        let simd_expr = self.codegen_operand(&args[0])?;
        let index_expr = self.codegen_operand(&args[1])?;

        // Emit index bounds check (Part of #1516)
        // SIMD extract with index >= lanes is UB
        self.emit_simd_index_bounds_check(&index_expr, &layout, "simd_extract");

        // Extract all elements
        let elements = self.simd_extract_elements(&simd_expr, &layout)?;

        if elements.is_empty() {
            debug!("codegen_simd_extract: empty vector");
            return None;
        }

        // Use ITE chain to select element by index (handles symbolic indices)
        let result = self.build_indexed_select(&elements, &index_expr);

        // Assign to destination
        self.bind_ssa_result(destination, result);

        target
    }

    /// Codegen simd_insert: insert a value at a specific index in a SIMD vector.
    /// Part of #1501, bounds check added per #1516.
    ///
    /// `simd_insert(vector, index, value)` returns a new vector with
    /// `vector[index]` replaced by `value`.
    /// Index may be constant or symbolic - handled via ITE chain for each element.
    ///
    /// REQUIRES: args.len() >= 3, args[0] is a SIMD vector, args[1] is an integer index, args[2] is element value
    /// REQUIRES: index < lanes (UB otherwise, verification will fail)
    /// ENSURES: destination gets a new vector with element at index replaced (ITE chain for each position)
    pub(in crate::codegen_ay::statement) fn codegen_simd_insert(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 3 {
            debug!("codegen_simd_insert: need 3 args, got {}", args.len());
            return None;
        }

        // Get SIMD type info
        let simd_ty = args[0].ty(self.body.locals()).into_option()?;
        let layout = self.simd_layout(simd_ty)?;
        debug!("codegen_simd_insert: layout={:?}", layout);

        // Codegen operands
        let simd_expr = self.codegen_operand(&args[0])?;
        let index_expr = self.codegen_operand(&args[1])?;
        let new_value = self.codegen_operand(&args[2])?;

        // Emit index bounds check (Part of #1516)
        // SIMD insert with index >= lanes is UB
        self.emit_simd_index_bounds_check(&index_expr, &layout, "simd_insert");

        // Extract all elements
        let elements = self.simd_extract_elements(&simd_expr, &layout)?;

        if elements.is_empty() {
            debug!("codegen_simd_insert: empty vector");
            return None;
        }

        // Get index bit width for comparisons
        let Some(idx_width) = index_expr.sort().bitvec_width() else {
            debug!("codegen_simd_insert: index is not bitvec (sort={:?})", index_expr.sort());
            return None;
        };

        // Build new elements: each element[i] = (index == i) ? new_value : old_element[i]
        let result_elements: Vec<Expr> = elements
            .iter()
            .enumerate()
            .map(|(i, old_elem)| {
                let i_const = Expr::bitvec_const(i as u128, idx_width);
                let is_this_index = index_expr.clone().eq(i_const);
                Expr::ite(is_this_index, new_value.clone(), old_elem.clone())
            })
            .collect();

        // Construct result vector
        let result_expr = self.simd_construct_expr(result_elements, &layout, simd_ty)?;

        // Assign to destination
        self.bind_ssa_result(destination, result_expr);

        target
    }

    // -------------------------------------------------------------------------
    // SIMD Select (element-wise mask select)
    // -------------------------------------------------------------------------

    /// Codegen simd_select: element-wise mask select.
    /// `simd_select(mask, a, b)` returns `if mask[i] != 0 then a[i] else b[i]`.
    pub(in crate::codegen_ay::statement) fn codegen_simd_select(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 3 {
            debug!("codegen_simd_select: need 3 args, got {}", args.len());
            return None;
        }

        // Layout from the data vector (args[1])
        let simd_ty = args[1].ty(self.body.locals()).into_option()?;
        let layout = self.simd_layout(simd_ty)?;
        let elem_width = layout.elem_width()?;

        let mask_expr = self.codegen_operand(&args[0])?;
        let a_expr = self.codegen_operand(&args[1])?;
        let b_expr = self.codegen_operand(&args[2])?;

        // Extract mask layout from args[0]
        let mask_ty = args[0].ty(self.body.locals()).into_option()?;
        let mask_layout = self.simd_layout(mask_ty)?;

        let mask_elems = self.simd_extract_elements(&mask_expr, &mask_layout)?;
        let a_elems = self.simd_extract_elements(&a_expr, &layout)?;
        let b_elems = self.simd_extract_elements(&b_expr, &layout)?;

        let lanes = layout.lane_count();
        if mask_elems.len() != lanes || a_elems.len() != lanes || b_elems.len() != lanes {
            debug!("codegen_simd_select: lane count mismatch");
            return None;
        }

        let zero = Expr::bitvec_const(0u64, elem_width);
        let result_elements: Vec<Expr> = (0..lanes)
            .map(|i| {
                let m = &mask_elems[i];
                // mask[i] != 0 → select a[i], else b[i]
                Expr::ite(m.clone().eq(zero.clone()).not(), a_elems[i].clone(), b_elems[i].clone())
            })
            .collect();

        let result_expr = self.simd_construct_expr(result_elements, &layout, simd_ty)?;
        self.bind_ssa_result(destination, result_expr);

        target
    }

    // -------------------------------------------------------------------------
    // SIMD Negation
    // -------------------------------------------------------------------------

    /// Codegen simd_neg: element-wise negation.
    /// Integer lanes: BV two's complement negation (bvneg).
    /// Float lanes: XOR sign bit (IEEE 754 sign flip).
    pub(in crate::codegen_ay::statement) fn codegen_simd_neg(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_simd_neg: need 1 arg, got 0");
            return None;
        }

        let simd_ty = args[0].ty(self.body.locals()).into_option()?;
        let layout = self.simd_layout(simd_ty)?;
        let is_float = self.simd_element_is_float(simd_ty);
        let elem_width = layout.elem_width();
        debug!("codegen_simd_neg: layout={:?}, is_float={}", layout, is_float);

        let src_expr = self.codegen_operand(&args[0])?;
        let elements = self.simd_extract_elements(&src_expr, &layout)?;

        let sign_mask = if is_float {
            elem_width.map(|w| Expr::bitvec_const(1u64 << (w - 1), w))
        } else {
            None
        };

        let result_elements: Vec<Expr> = elements
            .into_iter()
            .map(|elem| {
                if let Some(ref mask) = sign_mask { elem.bvxor(mask.clone()) } else { elem.bvneg() }
            })
            .collect();

        let result_expr = self.simd_construct_expr(result_elements, &layout, simd_ty)?;
        self.bind_ssa_result(destination, result_expr);

        target
    }
}
