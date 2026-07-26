// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD reduction operations: reduce a SIMD vector to a single scalar.
//!
//! Part of #1478.
//! Split from simd.rs per #2150.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::{IntoOption, SimdReduceOp};
use crate::codegen_ay::float_arithmetic::bv_float_binop;
use crate::codegen_ay::float_compare::{bv_float_gt, bv_float_lt};
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    // -------------------------------------------------------------------------
    // SIMD Reduce Operations (Part of #1478)
    // -------------------------------------------------------------------------
    // Reduce a SIMD vector to a single scalar value by applying an operation
    // across all elements.

    /// Codegen simd_reduce_add_ordered: sum all elements in order.
    /// Part of #1478.
    pub(in crate::codegen_ay::statement) fn codegen_simd_reduce_add(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_reduce(args, destination, target, SimdReduceOp::Add)
    }

    /// Codegen simd_reduce_mul_ordered: multiply all elements in order.
    /// Part of #1478.
    pub(in crate::codegen_ay::statement) fn codegen_simd_reduce_mul(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_reduce(args, destination, target, SimdReduceOp::Mul)
    }

    /// Codegen simd_reduce_and: bitwise AND all elements.
    /// Part of #1478.
    pub(in crate::codegen_ay::statement) fn codegen_simd_reduce_and(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_reduce(args, destination, target, SimdReduceOp::And)
    }

    /// Codegen simd_reduce_or: bitwise OR all elements.
    /// Part of #1478.
    pub(in crate::codegen_ay::statement) fn codegen_simd_reduce_or(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_reduce(args, destination, target, SimdReduceOp::Or)
    }

    /// Codegen simd_reduce_xor: bitwise XOR all elements.
    /// Part of #1478.
    pub(in crate::codegen_ay::statement) fn codegen_simd_reduce_xor(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_reduce(args, destination, target, SimdReduceOp::Xor)
    }

    /// Codegen simd_reduce_min: find minimum element.
    /// Part of #1478.
    pub(in crate::codegen_ay::statement) fn codegen_simd_reduce_min(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_reduce(args, destination, target, SimdReduceOp::Min)
    }

    /// Codegen simd_reduce_max: find maximum element.
    /// Part of #1478.
    pub(in crate::codegen_ay::statement) fn codegen_simd_reduce_max(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_reduce(args, destination, target, SimdReduceOp::Max)
    }

    /// Codegen simd_reduce_all: returns true if all elements are non-zero.
    /// Part of #1478.
    pub(in crate::codegen_ay::statement) fn codegen_simd_reduce_all(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_reduce_bool(args, destination, target, true)
    }

    /// Codegen simd_reduce_any: returns true if any element is non-zero.
    /// Part of #1478.
    pub(in crate::codegen_ay::statement) fn codegen_simd_reduce_any(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_reduce_bool(args, destination, target, false)
    }

    /// Common implementation for SIMD reduce operations.
    fn codegen_simd_reduce(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        op: SimdReduceOp,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_simd_reduce: need at least 1 arg");
            return None;
        }

        // Get SIMD type info
        let simd_ty = args[0].ty(self.body.locals()).into_option()?;
        let layout = self.simd_layout(simd_ty)?;
        let is_signed = self.simd_element_is_signed(simd_ty);
        let is_float = self.simd_element_is_float(simd_ty);
        let elem_width = layout.elem_width().unwrap_or(0);
        debug!(
            "codegen_simd_reduce: op={:?}, layout={:?}, is_signed={}, is_float={}",
            op, layout, is_signed, is_float
        );

        // Codegen operand and extract elements
        let simd_expr = self.codegen_operand(&args[0])?;
        let elements = self.simd_extract_elements(&simd_expr, &layout)?;

        if elements.is_empty() {
            debug!("codegen_simd_reduce: empty vector");
            return None;
        }

        // Fold elements with the reduction operation.
        // Part of #3882: float lanes route through IEEE-754-aware helpers
        // for dual-encoding parity with CHC path (per #3186).
        let mut result = elements[0].clone();
        for elem in &elements[1..] {
            result = match op {
                SimdReduceOp::Add if is_float => {
                    // Sound fallback: BV addition (over-approximation for floats,
                    // but never under-approximation). Part of #3882.
                    bv_float_binop(
                        rustc_public::mir::BinOp::Add,
                        result.clone(),
                        elem.clone(),
                        elem_width,
                    )
                    .unwrap_or_else(|| result.bvadd(elem.clone()))
                }
                SimdReduceOp::Add => result.bvadd(elem.clone()),
                SimdReduceOp::Mul if is_float => bv_float_binop(
                    rustc_public::mir::BinOp::Mul,
                    result.clone(),
                    elem.clone(),
                    elem_width,
                )
                .unwrap_or_else(|| result.bvmul(elem.clone())),
                SimdReduceOp::Mul => result.bvmul(elem.clone()),
                SimdReduceOp::And => result.bvand(elem.clone()),
                SimdReduceOp::Or => result.bvor(elem.clone()),
                SimdReduceOp::Xor => result.bvxor(elem.clone()),
                SimdReduceOp::Min | SimdReduceOp::Max => {
                    let is_min = matches!(op, SimdReduceOp::Min);
                    let cmp = if is_float {
                        if is_min {
                            bv_float_lt(&result, elem, elem_width)
                        } else {
                            bv_float_gt(&result, elem, elem_width)
                        }
                    } else if is_signed {
                        if is_min {
                            result.clone().bvslt(elem.clone())
                        } else {
                            result.clone().bvsgt(elem.clone())
                        }
                    } else if is_min {
                        result.clone().bvult(elem.clone())
                    } else {
                        result.clone().bvugt(elem.clone())
                    };
                    Expr::ite(cmp, result, elem.clone())
                }
            };
        }

        // Assign to destination
        self.bind_ssa_result(destination, result);

        target
    }

    /// Common implementation for boolean SIMD reduce operations (all/any).
    fn codegen_simd_reduce_bool(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        is_all: bool, // true = all, false = any
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_simd_reduce_bool: need at least 1 arg");
            return None;
        }

        // Get SIMD type info
        let simd_ty = args[0].ty(self.body.locals()).into_option()?;
        let layout = self.simd_layout(simd_ty)?;
        debug!("codegen_simd_reduce_bool: is_all={}, layout={:?}", is_all, layout);

        // Codegen operand and extract elements
        let simd_expr = self.codegen_operand(&args[0])?;
        let elements = self.simd_extract_elements(&simd_expr, &layout)?;

        if elements.is_empty() {
            // Empty vector: all() = true, any() = false
            let result = Expr::bool_const(is_all);
            self.assign_value_to_place(destination, result);
            return target;
        }

        // Get element bit width
        let elem_width = layout.elem_width()?;
        let zero = Expr::bitvec_const(0u128, elem_width);

        // For SIMD masks, non-zero means true (typically all-ones = -1)
        // all: all elements non-zero
        // any: at least one element non-zero
        let mut result = if is_all { Expr::bool_const(true) } else { Expr::bool_const(false) };

        for elem in &elements {
            let is_nonzero = elem.clone().eq(zero.clone()).not();
            result = if is_all { result.and(is_nonzero) } else { result.or(is_nonzero) };
        }

        // Assign to destination
        self.assign_value_to_place(destination, result);

        target
    }
}
