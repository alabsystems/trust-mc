// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD core operations: bitwise, shift, arithmetic, comparison.
//!
//! Part of #1415, #1348, #1478.
//! Split from simd.rs per #2150.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::{IntoOption, SimdArithOp, SimdCmpOp};
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen simd_and: element-wise bitwise AND.
    pub(in crate::codegen_ay::statement) fn codegen_simd_and(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_bitwise(args, destination, target, ay_bindings::Expr::bvand)
    }

    /// Codegen simd_or: element-wise bitwise OR.
    pub(in crate::codegen_ay::statement) fn codegen_simd_or(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_bitwise(args, destination, target, ay_bindings::Expr::bvor)
    }

    /// Codegen simd_xor: element-wise bitwise XOR.
    pub(in crate::codegen_ay::statement) fn codegen_simd_xor(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_bitwise(args, destination, target, ay_bindings::Expr::bvxor)
    }

    /// Common implementation for simd bitwise operations.
    fn codegen_simd_bitwise<F>(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        op: F,
    ) -> Option<BasicBlockIdx>
    where
        F: Fn(Expr, Expr) -> Expr,
    {
        if args.len() < 2 {
            debug!("codegen_simd_bitwise: need 2 args, got {}", args.len());
            return None;
        }

        // Get SIMD type info
        let simd_ty = args[0].ty(self.body.locals()).into_option()?;
        let layout = self.simd_layout(simd_ty)?;
        debug!("codegen_simd_bitwise: layout={:?}", layout);

        // Codegen operands
        let a_expr = self.codegen_operand(&args[0])?;
        let b_expr = self.codegen_operand(&args[1])?;
        debug!("codegen_simd_bitwise: a_sort={:?}, b_sort={:?}", a_expr.sort(), b_expr.sort());

        // Extract arrays from SIMD datatypes
        let a_elements = self.simd_extract_elements(&a_expr, &layout)?;
        let b_elements = self.simd_extract_elements(&b_expr, &layout)?;

        // Apply operation element-wise
        let result_elements: Vec<Expr> =
            a_elements.into_iter().zip(b_elements).map(|(x, y)| op(x, y)).collect();

        // Construct result array and wrap in datatype
        let result_expr = self.simd_construct_expr(result_elements, &layout, simd_ty)?;

        // Assign to destination
        self.bind_ssa_result(destination, result_expr);

        target
    }

    /// Codegen simd_shl: element-wise left shift.
    pub(in crate::codegen_ay::statement) fn codegen_simd_shl(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_shift(args, destination, target, true)
    }

    /// Codegen simd_shr: element-wise right shift.
    pub(in crate::codegen_ay::statement) fn codegen_simd_shr(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_shift(args, destination, target, false)
    }

    /// Common implementation for simd shift operations.
    fn codegen_simd_shift(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        is_left: bool,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            debug!("codegen_simd_shift: need 2 args, got {}", args.len());
            return None;
        }

        // Get SIMD type info
        let simd_ty = args[0].ty(self.body.locals()).into_option()?;
        let layout = self.simd_layout(simd_ty)?;
        let is_signed = self.simd_element_is_signed(simd_ty);
        debug!(
            "codegen_simd_shift: layout={:?}, is_left={}, is_signed={}",
            layout, is_left, is_signed
        );

        // Codegen operands
        let value_expr = self.codegen_operand(&args[0])?;
        let shift_expr = self.codegen_operand(&args[1])?;

        // Extract arrays
        let value_elements = self.simd_extract_elements(&value_expr, &layout)?;
        let shift_elements = self.simd_extract_elements(&shift_expr, &layout)?;

        let op_name = if is_left { "simd_shl" } else { "simd_shr" };
        for (value, distance) in value_elements.iter().zip(shift_elements.iter()) {
            self.emit_shift_distance_check_named(value, distance, Some(is_signed), Some(op_name));
        }

        // Apply shift element-wise
        let result_elements: Vec<Expr> = value_elements
            .into_iter()
            .zip(shift_elements)
            .map(|(v, s)| {
                if is_left {
                    v.bvshl(s)
                } else if is_signed {
                    v.bvashr(s)
                } else {
                    v.bvlshr(s)
                }
            })
            .collect();

        // Construct result
        let result_expr = self.simd_construct_expr(result_elements, &layout, simd_ty)?;

        // Assign to destination
        self.bind_ssa_result(destination, result_expr);

        target
    }

    // ========================================================================
    // SIMD Arithmetic Operations (Part of #1478)
    // ========================================================================

    /// Codegen simd_add: element-wise addition.
    pub(in crate::codegen_ay::statement) fn codegen_simd_add(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_arith(args, destination, target, SimdArithOp::Add)
    }

    /// Codegen simd_sub: element-wise subtraction.
    pub(in crate::codegen_ay::statement) fn codegen_simd_sub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_arith(args, destination, target, SimdArithOp::Sub)
    }

    /// Codegen simd_mul: element-wise multiplication.
    pub(in crate::codegen_ay::statement) fn codegen_simd_mul(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_arith(args, destination, target, SimdArithOp::Mul)
    }

    /// Codegen simd_div: element-wise division.
    pub(in crate::codegen_ay::statement) fn codegen_simd_div(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_arith(args, destination, target, SimdArithOp::Div)
    }

    /// Codegen simd_rem: element-wise remainder.
    /// Part of #1478 (SIMD arithmetic intrinsics).
    pub(in crate::codegen_ay::statement) fn codegen_simd_rem(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_arith(args, destination, target, SimdArithOp::Rem)
    }

    /// Common implementation for SIMD arithmetic operations.
    fn codegen_simd_arith(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        op: SimdArithOp,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            debug!("codegen_simd_arith: need 2 args, got {}", args.len());
            return None;
        }

        // Get SIMD type info
        let simd_ty = args[0].ty(self.body.locals()).into_option()?;
        let layout = self.simd_layout(simd_ty)?;
        let is_signed = self.simd_element_is_signed(simd_ty);
        let is_float = self.simd_element_is_float(simd_ty);
        let elem_width = layout.elem_width();
        debug!(
            "codegen_simd_arith: op={:?}, layout={:?}, is_signed={}, is_float={}",
            op, layout, is_signed, is_float
        );

        // Codegen operands
        let a_expr = self.codegen_operand(&args[0])?;
        let b_expr = self.codegen_operand(&args[1])?;

        // Extract arrays from SIMD datatypes
        let a_elements = self.simd_extract_elements(&a_expr, &layout)?;
        let b_elements = self.simd_extract_elements(&b_expr, &layout)?;

        // Integer simd_div / simd_rem are UB on a zero divisor and (signed)
        // on INT_MIN / -1 overflow. Kani checks each lane with
        // assert-assume semantics ("division by zero" / "attempt to compute
        // simd_div which would overflow"); a missing check here proved
        // `simd_div(i32::MIN, -1)` SAFE (a false proof — this corpus test:
        // tests/expected/intrinsics/simd-div-rem-overflow).
        let int_div_rem = !is_float && matches!(op, SimdArithOp::Div | SimdArithOp::Rem);
        if int_div_rem {
            let op_name = match op {
                SimdArithOp::Div => "simd_div",
                SimdArithOp::Rem => "simd_rem",
                _ => unreachable!("int_div_rem implies Div | Rem"),
            };
            for (x, y) in a_elements.iter().zip(b_elements.iter()) {
                let Some(width) = y.sort().bitvec_width() else {
                    continue;
                };
                let zero = Expr::bitvec_const(0u128, width);
                let div_zero = y.clone().eq(zero);
                // Kani's SIMD lane check text is "division by zero" (the
                // corpus expected files demand it); the bare label default
                // renders the SCALAR text "attempt to divide by zero", so
                // carry the message explicitly.
                self.record_violation_guarded_with_message(
                    div_zero.clone(),
                    "div_by_zero_check",
                    Some("division by zero".to_string()),
                );
                let mut no_ub = div_zero.not();
                if is_signed {
                    let int_min = Expr::bitvec_const(1u128 << (width - 1), width);
                    let neg_one = Expr::bitvec_const(!0u128, width);
                    let overflow = x.clone().eq(int_min).and(y.clone().eq(neg_one));
                    self.record_violation_guarded_with_message(
                        overflow.clone(),
                        "overflow_check_simd_div_rem",
                        Some(format!("attempt to compute {op_name} which would overflow")),
                    );
                    no_ub = no_ub.and(overflow.not());
                }
                // Kani lowers these checks assert-then-assume: code after a
                // failed lane check is path-constrained (UNREACHABLE, not
                // SUCCESS). Ordered so it cannot mask the checks above.
                let constraint = match &self.current_path_condition {
                    None => no_ub,
                    Some(pc) => pc.clone().implies(no_ub),
                };
                self.ctx.add_ordered_assumption(constraint);
            }
        }

        // Integer simd_add / simd_sub / simd_mul are UB on lane overflow.
        // Kani checks each lane with assert-assume semantics ("attempt to
        // compute simd_add which would overflow"); a missing check here
        // emitted NO obligation at all, so a harness whose whole point is
        // that overflow reported VACUOUS no-checks (corpus:
        // tests/expected/intrinsics/simd-arith-overflows). The lane
        // predicates are the same house `overflow_check` the scalar
        // Add/Sub/Mul path uses.
        let int_arith = !is_float && matches!(op, SimdArithOp::Add | SimdArithOp::Sub | SimdArithOp::Mul);
        if int_arith {
            use rustc_public::mir::BinOp;
            let (mir_op, op_name) = match op {
                SimdArithOp::Add => (BinOp::Add, "simd_add"),
                SimdArithOp::Sub => (BinOp::Sub, "simd_sub"),
                SimdArithOp::Mul => (BinOp::Mul, "simd_mul"),
                _ => unreachable!("int_arith implies Add | Sub | Mul"),
            };
            for (x, y) in a_elements.iter().zip(b_elements.iter()) {
                let Some((no_overflow, _)) = self.overflow_check(mir_op, x, y, is_signed) else {
                    continue;
                };
                self.record_violation_guarded_with_message(
                    no_overflow.clone().not(),
                    "overflow_check_simd_arith",
                    Some(format!("attempt to compute {op_name} which would overflow")),
                );
                // Kani lowers these checks assert-then-assume: code after a
                // failed lane check is path-constrained (UNREACHABLE, not
                // SUCCESS). Ordered so it cannot mask the checks above.
                let constraint = match &self.current_path_condition {
                    None => no_overflow,
                    Some(pc) => pc.clone().implies(no_overflow),
                };
                self.ctx.add_ordered_assumption(constraint);
            }
        }

        // Apply operation element-wise.
        // Part of #3857: float SIMD lanes use FP theory operations via bv_float_binop
        // instead of BV integer ops, matching the scalar float arithmetic path.
        let result_elements: Vec<Expr> = a_elements
            .into_iter()
            .zip(b_elements)
            .map(|(x, y)| {
                if is_float {
                    if let Some(w) = elem_width {
                        use crate::codegen_ay::float_arithmetic::bv_float_binop;
                        let mir_op = match op {
                            SimdArithOp::Add => rustc_public::mir::BinOp::Add,
                            SimdArithOp::Sub => rustc_public::mir::BinOp::Sub,
                            SimdArithOp::Mul => rustc_public::mir::BinOp::Mul,
                            SimdArithOp::Div => rustc_public::mir::BinOp::Div,
                            SimdArithOp::Rem => rustc_public::mir::BinOp::Rem,
                        };
                        if let Some(result) = bv_float_binop(mir_op, x.clone(), y.clone(), w) {
                            return result;
                        }
                    }
                    // Fallback to BV ops if FP theory unavailable (unsupported width)
                    debug!("codegen_simd_arith: float FP theory unavailable, BV fallback");
                }
                match op {
                    SimdArithOp::Add => x.bvadd(y),
                    SimdArithOp::Sub => x.bvsub(y),
                    SimdArithOp::Mul => x.bvmul(y),
                    // Division and remainder keep the RAW op out of the
                    // zero-divisor path. The UB obligation above already fires
                    // there, and the ordered assumption makes everything after
                    // it unreachable — but the solver still MODEL-CHECKS the
                    // term, and ay's validator rejects a model containing
                    // `bvsdiv x 0`, degrading the whole harness to
                    // UndecidedModel. An `ite` on the divisor leaves the
                    // poisoned case a fresh unconstrained value the validator
                    // never has to evaluate a division for. Sound both ways:
                    // that value is only reachable past a check that has
                    // already failed the harness.
                    SimdArithOp::Div | SimdArithOp::Rem => {
                        let width = y.sort().bitvec_width().unwrap_or(32);
                        let zero = Expr::bitvec_const(0u128, width);
                        let raw = match (op, is_signed) {
                            (SimdArithOp::Div, true) => x.clone().bvsdiv(y.clone()),
                            (SimdArithOp::Div, false) => x.clone().bvudiv(y.clone()),
                            (_, true) => x.clone().bvsrem(y.clone()),
                            (_, false) => x.clone().bvurem(y.clone()),
                        };
                        let poisoned_name = self.ctx.fresh_name("simd_divrem_poison");
                        let poisoned = self.ctx.declare_var(&poisoned_name, raw.sort().clone());
                        Expr::ite(y.eq(zero), poisoned, raw)
                    }
                }
            })
            .collect();

        // Construct result array and wrap in datatype
        let result_expr = self.simd_construct_expr(result_elements, &layout, simd_ty)?;

        // Assign to destination
        self.bind_ssa_result(destination, result_expr);

        target
    }

    // ========================================================================
    // SIMD Comparison Operations (Part of #1478)
    // ========================================================================

    /// Codegen simd_eq: element-wise equality comparison.
    pub(in crate::codegen_ay::statement) fn codegen_simd_eq(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_cmp(args, destination, target, SimdCmpOp::Eq)
    }

    /// Codegen simd_ne: element-wise inequality comparison.
    pub(in crate::codegen_ay::statement) fn codegen_simd_ne(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_cmp(args, destination, target, SimdCmpOp::Ne)
    }

    /// Codegen simd_lt: element-wise less-than comparison.
    pub(in crate::codegen_ay::statement) fn codegen_simd_lt(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_cmp(args, destination, target, SimdCmpOp::Lt)
    }

    /// Codegen simd_le: element-wise less-than-or-equal comparison.
    pub(in crate::codegen_ay::statement) fn codegen_simd_le(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_cmp(args, destination, target, SimdCmpOp::Le)
    }

    /// Codegen simd_gt: element-wise greater-than comparison.
    pub(in crate::codegen_ay::statement) fn codegen_simd_gt(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_cmp(args, destination, target, SimdCmpOp::Gt)
    }

    /// Codegen simd_ge: element-wise greater-than-or-equal comparison.
    pub(in crate::codegen_ay::statement) fn codegen_simd_ge(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_simd_cmp(args, destination, target, SimdCmpOp::Ge)
    }

    /// Common implementation for SIMD comparison operations.
    /// Returns a mask with all 1s (-1 for signed) for true, all 0s for false.
    fn codegen_simd_cmp(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        op: SimdCmpOp,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            debug!("codegen_simd_cmp: need 2 args, got {}", args.len());
            return None;
        }

        // Get SIMD type info from input (for source element extraction)
        let src_ty = args[0].ty(self.body.locals()).into_option()?;
        let src_layout = self.simd_layout(src_ty)?;
        let is_signed = self.simd_element_is_signed(src_ty);
        // Part of #3882: detect float lanes for IEEE-754-aware comparison.
        let is_float = self.simd_element_is_float(src_ty);
        let src_elem_width = src_layout.elem_width();

        // Part of #3453: derive mask width from destination type, not input type.
        // For cross-type comparisons (e.g. simd_eq::<u64x2, u32x2>), the mask
        // element width must match the destination, not the source operands.
        let dest_ty = destination.ty(self.body.locals()).into_option()?;
        let dest_layout = self.simd_layout(dest_ty)?;
        debug!(
            "codegen_simd_cmp: op={:?}, src_layout={:?}, dest_layout={:?}, is_signed={}",
            op, src_layout, dest_layout, is_signed
        );

        // Codegen operands
        let a_expr = self.codegen_operand(&args[0])?;
        let b_expr = self.codegen_operand(&args[1])?;

        // Extract arrays from SIMD datatypes (using source layout)
        let a_elements = self.simd_extract_elements(&a_expr, &src_layout)?;
        let b_elements = self.simd_extract_elements(&b_expr, &src_layout)?;

        // Get element bit width from DESTINATION for mask values
        let mask_width = dest_layout.elem_width()?;

        // Part of #3453: overflow-safe all-ones for up to 128-bit elements.
        let all_ones = if mask_width >= 128 {
            Expr::bitvec_const(u128::MAX, mask_width)
        } else {
            Expr::bitvec_const((1u128 << mask_width) - 1, mask_width)
        };
        let all_zeros = Expr::bitvec_const(0u64, mask_width);

        // Part of #3882: route float lanes through IEEE-754-aware BV comparison
        // helpers, matching CHC apply_simd_comparison (W1:4049).
        let result_elements: Vec<Expr> = a_elements
            .into_iter()
            .zip(b_elements)
            .map(|(x, y)| {
                let cmp_result = if is_float {
                    if let Some(w) = src_elem_width {
                        use crate::codegen_ay::float_compare::{
                            bv_float_eq, bv_float_ge, bv_float_gt, bv_float_le, bv_float_lt,
                            bv_float_ne,
                        };
                        match op {
                            SimdCmpOp::Eq => bv_float_eq(&x, &y, w),
                            SimdCmpOp::Ne => bv_float_ne(&x, &y, w),
                            SimdCmpOp::Lt => bv_float_lt(&x, &y, w),
                            SimdCmpOp::Le => bv_float_le(&x, &y, w),
                            SimdCmpOp::Gt => bv_float_gt(&x, &y, w),
                            SimdCmpOp::Ge => bv_float_ge(&x, &y, w),
                        }
                    } else {
                        // Fallback to raw BV if width unknown
                        x.eq(y)
                    }
                } else {
                    match op {
                        SimdCmpOp::Eq => x.eq(y),
                        SimdCmpOp::Ne => x.eq(y).not(),
                        SimdCmpOp::Lt => {
                            if is_signed {
                                x.bvslt(y)
                            } else {
                                x.bvult(y)
                            }
                        }
                        SimdCmpOp::Le => {
                            if is_signed {
                                x.bvsle(y)
                            } else {
                                x.bvule(y)
                            }
                        }
                        SimdCmpOp::Gt => {
                            if is_signed {
                                x.bvsgt(y)
                            } else {
                                x.bvugt(y)
                            }
                        }
                        SimdCmpOp::Ge => {
                            if is_signed {
                                x.bvsge(y)
                            } else {
                                x.bvuge(y)
                            }
                        }
                    }
                };
                // ITE(cmp_result, all_ones, all_zeros)
                Expr::ite(cmp_result, all_ones.clone(), all_zeros.clone())
            })
            .collect();

        // Construct result using DESTINATION layout and type
        let result_expr = self.simd_construct_expr(result_elements, &dest_layout, dest_ty)?;

        // Assign to destination
        self.bind_ssa_result(destination, result_expr);

        target
    }
}
