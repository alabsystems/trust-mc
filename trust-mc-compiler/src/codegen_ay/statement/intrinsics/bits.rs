// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Bit manipulation intrinsics for AY codegen.
//!
//! This module implements Rust bit intrinsics:
//! - Rotation: rotate_left, rotate_right
//! - Funnel shift: unchecked_funnel_shl, unchecked_funnel_shr
//! - Bit counting: ctlz, cttz, ctpop
//! - Byte/bit reversal: bswap, bitreverse
//! - Identity: codegen_identity_intrinsic (passthrough, dest = arg)
//!
//! Note: identity is here because it's a simple bitwise operation (no transformation).
//!
//! Extracted from intrinsics.rs per #1735.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};

use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen an identity intrinsic (destination = argument).
    ///
    /// REQUIRES: `args.len()` >= 1
    /// ENSURES: destination is constrained equal to `args[0]`
    pub(in crate::codegen_ay::statement) fn codegen_identity_intrinsic(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            return None;
        }
        let arg_expr = self.codegen_operand(&args[0])?;
        self.bind_ssa_result(destination, arg_expr);
        target
    }

    /// Codegen bit rotation: rotate_left (left=true) or rotate_right (left=false).
    /// rotate_left(x, n) = (x << n') | (x >> (width - n')) where n' = n % width
    /// rotate_right(x, n) = (x >> n') | (x << (width - n')) where n' = n % width
    ///
    /// REQUIRES: `args.len()` >= 2, `args[0]` and `args[1]` are bitvectors
    /// ENSURES: destination gets rotation result with same width as `args[0]`
    pub(in crate::codegen_ay::statement) fn codegen_rotate(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        left: bool,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }
        let x = self.codegen_operand(&args[0])?;
        let n = self.codegen_operand(&args[1])?;
        let width = x.sort().bitvec_width()?;

        // Ensure n is the same width as x
        let n = Self::coerce_to_width(n, width);
        let width_const = Expr::bitvec_const(width as u64, width);

        // Rust integer widths are powers of two, so n % width is n & (width - 1).
        // Avoiding bvurem keeps rotate VCs in the cheaper bitwise fragment.
        let rotate_mask = Expr::bitvec_const(width as u64 - 1, width);
        let n_mod = n.bvand(rotate_mask);
        let width_minus_n = width_const.bvsub(n_mod.clone());

        let result = if left {
            // rotate_left: (x << n') | (x >> (width - n'))
            x.clone().bvshl(n_mod).bvor(x.bvlshr(width_minus_n))
        } else {
            // rotate_right: (x >> n') | (x << (width - n'))
            x.clone().bvlshr(n_mod).bvor(x.bvshl(width_minus_n))
        };

        self.bind_ssa_result(destination, result);
        target
    }

    /// Codegen funnel shift: unchecked_funnel_shl (left=true) or unchecked_funnel_shr (left=false).
    ///
    /// Funnel shift concatenates two values and shifts across them:
    /// - funnel_shl(a, b, n) = (a << n) | (b >> (width - n))  (high bits of double-wide left shift)
    /// - funnel_shr(a, b, n) = (a << (width - n)) | (b >> n)  (low bits of double-wide right shift)
    ///
    /// The "unchecked" variant assumes n is in range [0, width) - no bounds checking needed.
    /// This is sound because exceeding the range is UB in Rust (similar to unchecked_shl/shr).
    ///
    /// REQUIRES: `args.len()` >= 3, `args[0]`, `args[1]`, `args[2]` are bitvectors
    /// REQUIRES: `args[0]` and `args[1]` have the same width
    /// ENSURES: destination gets funnel shift result with same width as inputs
    pub(in crate::codegen_ay::statement) fn codegen_funnel_shift(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        left: bool,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 3 {
            return None;
        }
        let a = self.codegen_operand(&args[0])?;
        let b = self.codegen_operand(&args[1])?;
        let n = self.codegen_operand(&args[2])?;
        let width = a.sort().bitvec_width()?;

        // Ensure n is the same width as a and b
        let n = Self::coerce_to_width(n, width);
        let width_const = Expr::bitvec_const(width as u64, width);

        // width - n (for the complementary shift)
        let width_minus_n = width_const.bvsub(n.clone());

        let result = if left {
            // funnel_shl: (a << n) | (b >> (width - n))
            // Takes high bits from a shifted left, low bits from b shifted right
            a.bvshl(n).bvor(b.bvlshr(width_minus_n))
        } else {
            // funnel_shr: (a << (width - n)) | (b >> n)
            // Takes high bits from a shifted left by complement, low bits from b shifted right
            a.bvshl(width_minus_n).bvor(b.bvlshr(n))
        };

        self.bind_ssa_result(destination, result);
        target
    }

    /// Codegen ctlz (count leading zeros).
    /// Uses an ITE cascade: if `bit[width-1]` then 0 else if `bit[width-2]` then 1 ...
    /// When `assert_nonzero` is true, adds an assertion that input != 0 (for ctlz_nonzero).
    ///
    /// REQUIRES: `args.len()` >= 1, `args[0].sort().is_bitvec()`
    /// ENSURES: destination gets count in range `[0, width]`, same width as input
    /// ENSURES: If `assert_nonzero`, records path-guarded violation when input == 0
    pub(in crate::codegen_ay::statement) fn codegen_ctlz(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        assert_nonzero: bool,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            return None;
        }
        let x = self.codegen_operand(&args[0])?;
        let width = x.sort().bitvec_width()?;

        // ctlz_nonzero has UB when input is zero - add violation check
        if assert_nonzero {
            let zero = Expr::bitvec_const(0, width);
            let is_zero = x.clone().eq(zero); // violation when x == 0
            self.record_violation_guarded(is_zero, "ctlz_nonzero_ub");
        }

        // Build ITE cascade from LSB (inner) to MSB (outer)
        // This ensures MSB is checked first during evaluation.
        // If x == 0, result is width; otherwise count leading zeros
        let mut result = Expr::bitvec_const(width as u64, width);
        for i in 0..width {
            // i is bit position from LSB (i=0 is LSB, i=width-1 is MSB)
            let bit = x.clone().extract(i, i);
            let bit_is_one = bit.eq(Expr::bitvec_const(1, 1));
            // ctlz count for bit at position i: (width - 1 - i) leading zeros
            let count = (width - 1 - i) as u64;
            result = Expr::ite(bit_is_one, Expr::bitvec_const(count, width), result);
        }

        self.bind_ssa_result(destination, result);
        target
    }

    /// Codegen cttz (count trailing zeros).
    /// Uses an ITE cascade: if `bit[0]` then 0 else if `bit[1]` then 1 ...
    /// When `assert_nonzero` is true, adds an assertion that input != 0 (for cttz_nonzero).
    ///
    /// REQUIRES: `args.len()` >= 1, `args[0].sort().is_bitvec()`
    /// ENSURES: destination gets count in range `[0, width]`, same width as input
    /// ENSURES: If `assert_nonzero`, records path-guarded violation when input == 0
    pub(in crate::codegen_ay::statement) fn codegen_cttz(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        assert_nonzero: bool,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            return None;
        }
        let x = self.codegen_operand(&args[0])?;
        let width = x.sort().bitvec_width()?;

        // cttz_nonzero has UB when input is zero - add violation check
        if assert_nonzero {
            let zero = Expr::bitvec_const(0, width);
            let is_zero = x.clone().eq(zero); // violation when x == 0
            self.record_violation_guarded(is_zero, "cttz_nonzero_ub");
        }

        // Build ITE cascade from MSB (inner) to LSB (outer)
        // This ensures LSB is checked first during evaluation.
        // If x == 0, result is width; otherwise count trailing zeros
        let mut result = Expr::bitvec_const(width as u64, width);
        for i in (0..width).rev() {
            // i is bit position from LSB (i=0 is LSB, i=width-1 is MSB)
            // We iterate in reverse so LSB becomes outermost in ITE
            let bit = x.clone().extract(i, i);
            let bit_is_one = bit.eq(Expr::bitvec_const(1, 1));
            // cttz count for bit at position i: i trailing zeros
            result = Expr::ite(bit_is_one, Expr::bitvec_const(i as u64, width), result);
        }

        self.bind_ssa_result(destination, result);
        target
    }

    /// Codegen ctpop (population count / count ones).
    /// Uses balanced binary tree reduction for O(log N) formula depth instead
    /// of O(N). Critical for solver performance on u32/u64 where linear chains
    /// cause timeouts.
    ///
    /// REQUIRES: `args.len()` >= 1, `args[0].sort().is_bitvec()`
    /// ENSURES: destination gets count in range `[0, width]` as BV32
    pub(in crate::codegen_ay::statement) fn codegen_ctpop(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            return None;
        }
        let x = self.codegen_operand(&args[0])?;
        let width = x.sort().bitvec_width()?;
        let out_width = 32;
        let acc_width = ctpop_accumulator_width(width, out_width);

        // Sum in the smallest BV width that can represent `width`. The final
        // result is BV32 because Rust's ctpop intrinsic returns u32.
        let mut bits: Vec<Expr> = (0..width)
            .map(|i| {
                let bit = x.clone().extract(i, i);
                if acc_width == 1 { bit } else { bit.zero_extend(acc_width - 1) }
            })
            .collect();

        // Tree reduction: pairwise sum until one value remains
        while bits.len() > 1 {
            let mut next = Vec::new();
            let mut i = 0;
            while i + 1 < bits.len() {
                next.push(bits[i].clone().bvadd(bits[i + 1].clone()));
                i += 2;
            }
            if i < bits.len() {
                next.push(bits[i].clone());
            }
            bits = next;
        }

        let result = bits.into_iter().next().unwrap_or_else(|| Expr::bitvec_const(0, acc_width));
        let result =
            if acc_width == out_width { result } else { result.zero_extend(out_width - acc_width) };
        self.bind_ssa_result(destination, result);
        target
    }

    /// Codegen byte swap intrinsic (bswap).
    ///
    /// Reverses the byte order of an integer:
    /// - bswap(0x12345678) = 0x78563412 for u32
    /// - bswap(0x1234) = 0x3412 for u16
    ///
    /// REQUIRES: `args.len()` >= 1, `args[0].sort().is_bitvec()` with width % 8 == 0
    /// ENSURES: destination gets reversed-byte value with same width as input
    pub(in crate::codegen_ay::statement) fn codegen_bswap(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            return None;
        }
        let x = self.codegen_operand(&args[0])?;
        let width = x.sort().bitvec_width()?;

        // Width must be multiple of 8 bits
        if width % 8 != 0 {
            return None;
        }

        let num_bytes = width / 8;

        // For single byte, bswap is identity
        if num_bytes == 1 {
            self.bind_ssa_result(destination, x);
            return target;
        }

        // Extract each byte and concatenate in reverse order
        // byte[0] is LSB, byte[num_bytes-1] is MSB
        // Result: byte[0] || byte[1] || ... || byte[num_bytes-1]
        let mut result: Option<Expr> = None;
        for i in 0..num_bytes {
            let low = i * 8;
            let high = low + 7;
            let byte = x.clone().extract(high, low);
            result = Some(match result {
                None => byte,
                Some(acc) => acc.concat(byte), // acc becomes high bits, byte becomes low bits
            });
        }

        let result = result?;
        self.bind_ssa_result(destination, result);
        target
    }

    /// Codegen bit reversal intrinsic (bitreverse).
    ///
    /// Reverses all bits in an integer:
    /// - bitreverse(0b1100) = 0b0011 for u4
    ///
    /// REQUIRES: `args.len()` >= 1, `args[0].sort().is_bitvec()`
    /// ENSURES: destination gets reversed-bit value with same width as input
    pub(in crate::codegen_ay::statement) fn codegen_bitreverse(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            return None;
        }
        let x = self.codegen_operand(&args[0])?;
        let width = x.sort().bitvec_width()?;

        // Extract each bit and concatenate in reverse order
        // bit[0] is LSB, bit[width-1] is MSB
        // Result: bit[0] || bit[1] || ... || bit[width-1]
        let mut result: Option<Expr> = None;
        for i in 0..width {
            let bit = x.clone().extract(i, i);
            result = Some(match result {
                None => bit,
                Some(acc) => acc.concat(bit), // acc becomes high bits, bit becomes low bits
            });
        }

        let result = result?;
        self.bind_ssa_result(destination, result);
        target
    }
}

fn ctpop_accumulator_width(input_width: u32, out_width: u32) -> u32 {
    if input_width <= 32 { bit_width_for_unsigned_max(input_width) } else { out_width }
}

fn bit_width_for_unsigned_max(max: u32) -> u32 {
    (u32::BITS - max.leading_zeros()).max(1).next_power_of_two().min(32)
}
