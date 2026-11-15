// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Math intrinsics for AY codegen.
//!
//! This module implements Rust math intrinsics:
//! - Fast-math: fadd_fast, fsub_fast, fmul_fast, fdiv_fast
//! - f32/f64 variants:
//!   - Basic: sqrt, fabs, copysign
//!   - Trigonometric: sin, cos
//!   - Exponential/log: exp, exp2, log, log2, log10, pow, powi, fma
//!   - Rounding: floor, ceil, trunc, round, round_ties_even
//!   - Min/max: minnum, maxnum
//!
//! Math intrinsics (#1362) return fresh symbolic values when there is no exact
//! BV encoding available. Fast-math intrinsics now route through FP theory
//! (bv_to_fp → fp.op → fp_to_ieee_bv) matching normal float BinOp (Part of #3693).
//! Transcendental functions (sin, cos, exp, etc.) still use symbolic fallback.
//!
//! Extracted from intrinsics.rs per #1735.

use ay_bindings::{Expr, RoundingMode, Sort};
use rustc_public::mir::{BasicBlockIdx, BinOp, Operand, Place};
use tracing::debug;

use super::bmc_fp_theory::{bmc_fp_fma, bmc_fp_round_to_integral, bmc_fp_sqrt};
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen fast-math intrinsics (fadd_fast, fsub_fast, fmul_fast, fdiv_fast).
    ///
    /// For verification, we:
    /// - Require operands to be finite (no NaN/Inf), recording a UB violation otherwise.
    /// - Model arithmetic via FP theory (bv_to_fp → fp.op → fp_to_ieee_bv),
    ///   matching the normal float BinOp encoding (Part of #3693).
    ///
    /// REQUIRES: args contains float operands matching the intrinsic signature
    /// ENSURES: destination gets float result of the fast-math operation (NaN/Inf handling relaxed)
    pub(in crate::codegen_ay::statement) fn codegen_fast_math_intrinsic(
        &mut self,
        intrinsic_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let lhs = self.codegen_operand(&args[0])?;
        let rhs = self.codegen_operand(&args[1])?;

        self.record_fast_float_finite(&lhs, intrinsic_name, "lhs");
        self.record_fast_float_finite(&rhs, intrinsic_name, "rhs");

        let op = if intrinsic_name.ends_with("fadd_fast") {
            BinOp::Add
        } else if intrinsic_name.ends_with("fsub_fast") {
            BinOp::Sub
        } else if intrinsic_name.ends_with("fmul_fast") {
            BinOp::Mul
        } else if intrinsic_name.ends_with("fdiv_fast") {
            BinOp::Div
        } else {
            return None;
        };

        // Part of #3693: Route fast-math through FP theory to match normal float ops.
        let result = if lhs.sort().is_bitvec() {
            use crate::codegen_ay::float_arithmetic::bv_float_binop;
            let width = lhs.sort().bitvec_width()?;
            // Kani `--nan-check` parity: Kani lowers these intrinsics to the
            // plain float operator, which the NaN check instruments. With the
            // operand-finiteness violations above, the only NaN left to catch
            // is fdiv_fast(±0, ±0); the exact predicate captures just that.
            if self.ctx.config.nan_checks {
                self.emit_float_nan_check(op, &lhs, &rhs, width);
            }
            bv_float_binop(op, lhs, rhs, width)?
        } else {
            let is_signed = self.is_signed_integer_op(&args[0], &args[1]);
            self.codegen_binop_typed(op, lhs, rhs, is_signed)
        };
        self.assign_value_to_place(destination, result);
        target
    }

    fn record_fast_float_finite(&mut self, value: &Expr, intrinsic_name: &str, label: &str) {
        let Some(width) = value.sort().bitvec_width() else {
            return;
        };

        let (exp_hi, exp_lo, exp_all_ones) = match width {
            32 => (30u32, 23u32, 0xFFu64),
            64 => (62u32, 52u32, 0x7FFu64),
            _ => return, // non-enum: u32 (float width)
        };
        let exp = value.clone().extract(exp_hi, exp_lo);
        let exp_is_all_ones = exp.eq(Expr::bitvec_const(exp_all_ones, exp_hi - exp_lo + 1));
        let violation_label = {
            let mut s = String::with_capacity(intrinsic_name.len() + 13 + label.len());
            s.push_str(intrinsic_name);
            s.push_str("_non_finite_");
            s.push_str(label);
            s
        };
        self.record_violation_guarded(exp_is_all_ones, &violation_label);
    }

    /// Codegen f32 math intrinsics (sqrt, sin, cos, exp, log, etc.).
    ///
    /// For constant inputs, computes the result at compile time (constant folding).
    /// For symbolic inputs, returns a fresh symbolic bitvector (sound but imprecise).
    ///
    /// Part of #1362
    ///
    /// REQUIRES: Destination type is f32 (32-bit)
    /// ENSURES: Destination gets computed value (if constant) or fresh symbolic value
    pub(in crate::codegen_ay::statement) fn codegen_math_intrinsic_f32(
        &mut self,
        intrinsic_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Try constant folding: if arg is a constant, compute the result
        if let Some(result_bits) = self.try_fold_math_f32(intrinsic_name, args) {
            debug!("codegen_math_intrinsic_f32: {} folded to {:08x}", intrinsic_name, result_bits);
            let result_const = Expr::bitvec_const(result_bits as u128, 32);
            self.bind_ssa_result(destination, result_const);
            return target;
        }

        // Try exact BV encoding for bit-level intrinsics (Part of #3323).
        if let Some(result) = self.try_exact_bv_math(intrinsic_name, args, 32) {
            debug!("codegen_math_intrinsic_f32: {} exact BV encoding", intrinsic_name);
            self.bind_ssa_result(destination, result);
            return target;
        }

        // Fallback: fresh symbolic value for non-constant args
        debug!("codegen_math_intrinsic_f32: {} (symbolic, non-constant args)", intrinsic_name);
        let base_name = self.ssa_base_name(destination);
        let dest_name = self.ssa_name_from_base(&base_name, true);
        let dest_expr = self.ctx.declare_var(&dest_name, Sort::bitvec(32));
        self.env_update(base_name, dest_expr);
        // The fresh value stands in for the intrinsic's real result, so a proof
        // over it is sound but a counterexample that reads it is not evidence of
        // a bug: `x.powf(2.0) >= 0.0` for `x` in (1, 65535) was certified Genuine
        // (kani/Intrinsics/Math/Arith/powf32.rs, exposed once `u16 as f32` stopped
        // reinterpreting bits and the assumption stopped being vacuous). SAT-only
        // taint, like the other false-certificate sites.
        self.ctx.bmc_sound_havoc("math_intrinsic_fresh_value");
        target
    }

    /// Codegen f64 math intrinsics (sqrt, sin, cos, exp, log, etc.).
    ///
    /// For constant inputs, computes the result at compile time (constant folding).
    /// For symbolic inputs, returns a fresh symbolic bitvector (sound but imprecise).
    ///
    /// Part of #1362
    ///
    /// REQUIRES: Destination type is f64 (64-bit)
    /// ENSURES: Destination gets computed value (if constant) or fresh symbolic value
    pub(in crate::codegen_ay::statement) fn codegen_math_intrinsic_f64(
        &mut self,
        intrinsic_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Try constant folding: if arg is a constant, compute the result
        if let Some(result_bits) = self.try_fold_math_f64(intrinsic_name, args) {
            debug!("codegen_math_intrinsic_f64: {} folded to {:016x}", intrinsic_name, result_bits);
            let result_const = Expr::bitvec_const(result_bits as u128, 64);
            self.bind_ssa_result(destination, result_const);
            return target;
        }

        // Try exact BV encoding for bit-level intrinsics (Part of #3323).
        if let Some(result) = self.try_exact_bv_math(intrinsic_name, args, 64) {
            debug!("codegen_math_intrinsic_f64: {} exact BV encoding", intrinsic_name);
            self.bind_ssa_result(destination, result);
            return target;
        }

        // Fallback: fresh symbolic value for non-constant args
        debug!("codegen_math_intrinsic_f64: {} (symbolic, non-constant args)", intrinsic_name);
        let base_name = self.ssa_base_name(destination);
        let dest_name = self.ssa_name_from_base(&base_name, true);
        let dest_expr = self.ctx.declare_var(&dest_name, Sort::bitvec(64));
        self.env_update(base_name, dest_expr);
        // The fresh value stands in for the intrinsic's real result, so a proof
        // over it is sound but a counterexample that reads it is not evidence of
        // a bug: `x.powf(2.0) >= 0.0` for `x` in (1, 65535) was certified Genuine
        // (kani/Intrinsics/Math/Arith/powf32.rs, exposed once `u16 as f32` stopped
        // reinterpreting bits and the assumption stopped being vacuous). SAT-only
        // taint, like the other false-certificate sites.
        self.ctx.bmc_sound_havoc("math_intrinsic_fresh_value");
        target
    }

    /// Try to fold an f32 math intrinsic with constant arguments.
    /// Returns the result as raw bits if successful, None if args are symbolic.
    fn try_fold_math_f32(&mut self, intrinsic_name: &str, args: &[Operand]) -> Option<u32> {
        // Extract constant f32 value from first argument
        let arg0 = args.first()?;
        let bits0 = self.try_extract_f32_const(arg0)?;
        let val0 = f32::from_bits(bits0);

        // Some intrinsics need a second argument
        let compute_result = |val: f32| -> f32 {
            if intrinsic_name.ends_with("sqrtf32") {
                val.sqrt()
            } else if intrinsic_name.ends_with("sinf32") {
                val.sin()
            } else if intrinsic_name.ends_with("cosf32") {
                val.cos()
            } else if intrinsic_name.ends_with("expf32") {
                val.exp()
            } else if intrinsic_name.ends_with("exp2f32") {
                val.exp2()
            } else if intrinsic_name.ends_with("logf32") {
                val.ln()
            } else if intrinsic_name.ends_with("log2f32") {
                val.log2()
            } else if intrinsic_name.ends_with("log10f32") {
                val.log10()
            } else if intrinsic_name.ends_with("fabsf32") {
                val.abs()
            } else if intrinsic_name.ends_with("floorf32") {
                val.floor()
            } else if intrinsic_name.ends_with("ceilf32") {
                val.ceil()
            } else if intrinsic_name.ends_with("truncf32") {
                val.trunc()
            } else if intrinsic_name.ends_with("roundf32") {
                val.round()
            } else if intrinsic_name.ends_with("round_ties_even_f32") {
                // #1383: Use ties-to-even rounding, not ties-away-from-zero
                val.round_ties_even()
            } else {
                // Unknown intrinsic, can't fold
                f32::NAN
            }
        };

        // Handle binary intrinsics (pow, copysign, minnum, maxnum)
        if intrinsic_name.ends_with("powf32") {
            let arg1 = args.get(1)?;
            let bits1 = self.try_extract_f32_const(arg1)?;
            let val1 = f32::from_bits(bits1);
            return Some(val0.powf(val1).to_bits());
        } else if intrinsic_name.ends_with("powi32") || intrinsic_name.ends_with("powif32") {
            // powi takes f32 and i32
            let arg1 = args.get(1)?;
            if let Some(i32_val) = self.try_extract_i32_const(arg1) {
                return Some(val0.powi(i32_val).to_bits());
            }
            return None;
        } else if intrinsic_name.ends_with("copysignf32") {
            let arg1 = args.get(1)?;
            let bits1 = self.try_extract_f32_const(arg1)?;
            let val1 = f32::from_bits(bits1);
            return Some(val0.copysign(val1).to_bits());
        } else if intrinsic_name.ends_with("minnumf32") || intrinsic_name.ends_with("maxnumf32") {
            let arg1 = args.get(1)?;
            let bits1 = self.try_extract_f32_const(arg1)?;
            let val1 = f32::from_bits(bits1);
            // Decided by IEEE comparison where every toolchain agrees; opposite zeros, two NaNs
            // and a signalling NaN have no single constant (`float_minmax`), so
            // `try_exact_bv_math` encodes the choice or the relation. Never the host's `min`.
            let is_min = intrinsic_name.ends_with("minnumf32");
            return crate::codegen_ay::float_minmax::minmax_num_fold_f32(is_min, val0, val1)
                .map(f32::to_bits);
        } else if intrinsic_name.ends_with("fmaf32") {
            // fma(a, b, c) = a * b + c
            let arg1 = args.get(1)?;
            let arg2 = args.get(2)?;
            let bits1 = self.try_extract_f32_const(arg1)?;
            let bits2 = self.try_extract_f32_const(arg2)?;
            let val1 = f32::from_bits(bits1);
            let val2 = f32::from_bits(bits2);
            return Some(val0.mul_add(val1, val2).to_bits());
        }

        let result = compute_result(val0);
        if result.is_nan() && !val0.is_nan() {
            // Unknown intrinsic returned NAN - don't fold
            return None;
        }
        Some(result.to_bits())
    }

    /// Try to fold an f64 math intrinsic with constant arguments.
    /// Returns the result as raw bits if successful, None if args are symbolic.
    fn try_fold_math_f64(&mut self, intrinsic_name: &str, args: &[Operand]) -> Option<u64> {
        // Extract constant f64 value from first argument
        let arg0 = args.first()?;
        let bits0 = self.try_extract_f64_const(arg0)?;
        let val0 = f64::from_bits(bits0);

        let compute_result = |val: f64| -> f64 {
            if intrinsic_name.ends_with("sqrtf64") {
                val.sqrt()
            } else if intrinsic_name.ends_with("sinf64") {
                val.sin()
            } else if intrinsic_name.ends_with("cosf64") {
                val.cos()
            } else if intrinsic_name.ends_with("expf64") {
                val.exp()
            } else if intrinsic_name.ends_with("exp2f64") {
                val.exp2()
            } else if intrinsic_name.ends_with("logf64") {
                val.ln()
            } else if intrinsic_name.ends_with("log2f64") {
                val.log2()
            } else if intrinsic_name.ends_with("log10f64") {
                val.log10()
            } else if intrinsic_name.ends_with("fabsf64") {
                val.abs()
            } else if intrinsic_name.ends_with("floorf64") {
                val.floor()
            } else if intrinsic_name.ends_with("ceilf64") {
                val.ceil()
            } else if intrinsic_name.ends_with("truncf64") {
                val.trunc()
            } else if intrinsic_name.ends_with("roundf64") {
                val.round()
            } else if intrinsic_name.ends_with("round_ties_even_f64") {
                // #1383: Use ties-to-even rounding, not ties-away-from-zero
                val.round_ties_even()
            } else {
                // Unknown intrinsic, can't fold
                f64::NAN
            }
        };

        // Handle binary intrinsics (pow, copysign, minnum, maxnum)
        if intrinsic_name.ends_with("powf64") {
            let arg1 = args.get(1)?;
            let bits1 = self.try_extract_f64_const(arg1)?;
            let val1 = f64::from_bits(bits1);
            return Some(val0.powf(val1).to_bits());
        } else if intrinsic_name.ends_with("powi64") || intrinsic_name.ends_with("powif64") {
            // powi takes f64 and i32
            let arg1 = args.get(1)?;
            if let Some(i32_val) = self.try_extract_i32_const(arg1) {
                return Some(val0.powi(i32_val).to_bits());
            }
            return None;
        } else if intrinsic_name.ends_with("copysignf64") {
            let arg1 = args.get(1)?;
            let bits1 = self.try_extract_f64_const(arg1)?;
            let val1 = f64::from_bits(bits1);
            return Some(val0.copysign(val1).to_bits());
        } else if intrinsic_name.ends_with("minnumf64") || intrinsic_name.ends_with("maxnumf64") {
            let arg1 = args.get(1)?;
            let bits1 = self.try_extract_f64_const(arg1)?;
            let val1 = f64::from_bits(bits1);
            // See the f32 arm.
            let is_min = intrinsic_name.ends_with("minnumf64");
            return crate::codegen_ay::float_minmax::minmax_num_fold_f64(is_min, val0, val1)
                .map(f64::to_bits);
        } else if intrinsic_name.ends_with("fmaf64") {
            // fma(a, b, c) = a * b + c
            let arg1 = args.get(1)?;
            let arg2 = args.get(2)?;
            let bits1 = self.try_extract_f64_const(arg1)?;
            let bits2 = self.try_extract_f64_const(arg2)?;
            let val1 = f64::from_bits(bits1);
            let val2 = f64::from_bits(bits2);
            return Some(val0.mul_add(val1, val2).to_bits());
        }

        let result = compute_result(val0);
        if result.is_nan() && !val0.is_nan() {
            // Unknown intrinsic returned NAN - don't fold
            return None;
        }
        Some(result.to_bits())
    }

    /// Try exact BV encoding for math intrinsics with bit-level definitions (Part of #3323).
    ///
    /// Returns `Some(result_expr)` for intrinsics that can be precisely encoded
    /// in BV arithmetic without FP theory. Falls back to `None` for intrinsics
    /// that need transcendental functions or FP comparisons.
    fn try_exact_bv_math(
        &mut self,
        intrinsic_name: &str,
        args: &[Operand],
        width: u32,
    ) -> Option<Expr> {
        let arg0_expr = self.codegen_operand(args.first()?)?;

        // fabs: clear sign bit (exact for all IEEE 754 values).
        if intrinsic_name.ends_with("fabsf32") || intrinsic_name.ends_with("fabsf64") {
            let sign_mask = match width {
                32 => Expr::bitvec_const(0x7FFF_FFFFu64, 32),
                64 => Expr::bitvec_const(0x7FFF_FFFF_FFFF_FFFFu64, 64),
                _ => return None,
            };
            return Some(arg0_expr.bvand(sign_mask));
        }

        // copysign(mag, sig): replace mag's sign bit with sig's (exact).
        if intrinsic_name.ends_with("copysignf32") || intrinsic_name.ends_with("copysignf64") {
            let arg1_expr = self.codegen_operand(args.get(1)?)?;
            let (mantissa_mask, sign_bit_mask) = match width {
                32 => {
                    (Expr::bitvec_const(0x7FFF_FFFFu64, 32), Expr::bitvec_const(0x8000_0000u64, 32))
                }
                64 => (
                    Expr::bitvec_const(0x7FFF_FFFF_FFFF_FFFFu64, 64),
                    Expr::bitvec_const(0x8000_0000_0000_0000u64, 64),
                ),
                _ => return None,
            };
            let mag_bits = arg0_expr.bvand(mantissa_mask);
            let sig_sign = arg1_expr.bvand(sign_bit_mask);
            return Some(mag_bits.bvor(sig_sign));
        }

        // Part of #3094: BMC parity — rounding intrinsics via FP theory.
        // These use fp.roundToIntegral with rounding-mode constants, which work
        // in SMT/BMC but not in Z3's CHC parser. The CHC path uses pure BV
        // encoding in float_rounding.rs instead.
        if intrinsic_name.ends_with("truncf32") || intrinsic_name.ends_with("truncf64") {
            return bmc_fp_round_to_integral(arg0_expr, width, RoundingMode::RTZ);
        }
        if intrinsic_name.ends_with("floorf32") || intrinsic_name.ends_with("floorf64") {
            return bmc_fp_round_to_integral(arg0_expr, width, RoundingMode::RTN);
        }
        if intrinsic_name.ends_with("ceilf32") || intrinsic_name.ends_with("ceilf64") {
            return bmc_fp_round_to_integral(arg0_expr, width, RoundingMode::RTP);
        }
        if intrinsic_name.ends_with("roundf32") || intrinsic_name.ends_with("roundf64") {
            return bmc_fp_round_to_integral(arg0_expr, width, RoundingMode::RNA);
        }
        if intrinsic_name.ends_with("round_ties_even_f32")
            || intrinsic_name.ends_with("round_ties_even_f64")
        {
            return bmc_fp_round_to_integral(arg0_expr, width, RoundingMode::RNE);
        }

        // sqrt: exact FP theory encoding (not transcendental).
        if intrinsic_name.ends_with("sqrtf32") || intrinsic_name.ends_with("sqrtf64") {
            return bmc_fp_sqrt(arg0_expr, width);
        }

        // fma(a, b, c): ternary FP theory encoding.
        if intrinsic_name.ends_with("fmaf32") || intrinsic_name.ends_with("fmaf64") {
            let arg1_expr = self.codegen_operand(args.get(1)?)?;
            let arg2_expr = self.codegen_operand(args.get(2)?)?;
            return bmc_fp_fma(arg0_expr, arg1_expr, arg2_expr, width);
        }

        // minnum/maxnum (Trust: minimum_number_nsz_* / maximum_number_nsz_*): the exact
        // result where the contract determines it, and a fresh choice where it does not
        // (opposite zeros, two NaNs), in bitvector form. `fp.min` / `fp.max` left opposite
        // zeros to the solver's discretion, and a solver or its simplifier may pick one. See
        // `float_minmax`.
        let minmax_kind = if intrinsic_name.ends_with("minnumf32")
            || intrinsic_name.ends_with("minnumf64")
        {
            Some(true)
        } else if intrinsic_name.ends_with("maxnumf32") || intrinsic_name.ends_with("maxnumf64") {
            Some(false)
        } else {
            None
        };
        if let Some(is_min) = minmax_kind {
            let arg1_expr = self.codegen_operand(args.get(1)?)?;
            // Both arguments known bit for bit (the operands are often SSA names bound to
            // constants that `try_fold_math_*` does not see through): decide the case here.
            // A determined result is exact on the host (one NaN returns the other argument,
            // unequal values the smaller/larger, identical zeros themselves), and a
            // non-deterministic one needs no FP term at all. Keeping FP ops off ground inputs
            // matters: the solver decided `fp.min` of constants, and stopped deciding it once
            // the term also carried the fresh choices below.
            let ground = |expr: &Expr| match self.resolve_concrete_expr(expr).value() {
                ay_bindings::ExprValue::BitVecConst { value, width: w } if *w == width => {
                    value.to_u64_digits().1.first().copied().or(Some(0))
                }
                _ => None,
            };
            if let (Some(bits0), Some(bits1)) = (ground(&arg0_expr), ground(&arg1_expr)) {
                // Decided by IEEE comparison, never the host's `min` / `max` (`float_minmax`).
                let (concrete, nondeterministic, both_nan) = match width {
                    32 => {
                        let (a, b) = (f32::from_bits(bits0 as u32), f32::from_bits(bits1 as u32));
                        (
                            crate::codegen_ay::float_minmax::minmax_num_fold_f32(is_min, a, b)
                                .map(|r| u64::from(r.to_bits())),
                            crate::codegen_ay::float_minmax::minmax_num_result_is_nondeterministic_f32(a, b),
                            a.is_nan() && b.is_nan(),
                        )
                    }
                    64 => {
                        let (a, b) = (f64::from_bits(bits0), f64::from_bits(bits1));
                        (
                            crate::codegen_ay::float_minmax::minmax_num_fold_f64(is_min, a, b)
                                .map(f64::to_bits),
                            crate::codegen_ay::float_minmax::minmax_num_result_is_nondeterministic_f64(a, b),
                            a.is_nan() && b.is_nan(),
                        )
                    }
                    _ => return None,
                };
                if let Some(bits) = concrete {
                    return Some(Expr::bitvec_const(bits as u128, width));
                }
                if nondeterministic {
                    // Opposite zeros (either argument) or two NaNs (any NaN).
                    if both_nan {
                        let nan_name = self.ctx.fresh_name("minmax_num_nan_result");
                        let nan_result = self.ctx.declare_var(&nan_name, Sort::bitvec(width));
                        self.ctx.assert(crate::codegen_ay::float_minmax::ieee_is_nan_bv(
                            &nan_result,
                            width,
                        )?);
                        return Some(nan_result);
                    }
                    let choice_name = self.ctx.fresh_name("minmax_num_equal_choice");
                    let choice = self.ctx.declare_var(&choice_name, Sort::bool());
                    return Some(Expr::ite(choice, arg0_expr, arg1_expr));
                }
                // A signalling NaN argument: the toolchains' run times differ on it, so the
                // symbolic term below decides it as the contract does (the other argument),
                // identically on both routes.
            }
            let choice_name = self.ctx.fresh_name("minmax_num_equal_choice");
            let choice = self.ctx.declare_var(&choice_name, Sort::bool());
            let nan_name = self.ctx.fresh_name("minmax_num_nan_result");
            let nan_result = self.ctx.declare_var(&nan_name, Sort::bitvec(width));
            let (term, nan_result_is_nan) = crate::codegen_ay::float_minmax::minmax_num_bv_term(
                is_min, &arg0_expr, &arg1_expr, choice, nan_result, width,
            )?;
            // Only constrains a fresh variable, so it can never make the query infeasible.
            self.ctx.assert(nan_result_is_nan);
            return Some(term);
        }

        None
    }
}
