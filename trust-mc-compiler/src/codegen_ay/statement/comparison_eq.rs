// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PartialEq, PartialOrd, and min/max/clamp comparison codegen.
//!
//! Extracted from `comparison.rs` — Part of #4206.

use crate::codegen_ay::option_like_eq::option_like_datatype_eq;
use crate::codegen_ay::types::unwrap_single_field_datatype_to_sort;
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use super::StatementCodegen;
use super::comparison::try_wrap_bv_as_option_some;

mod partial_ord_array;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen PartialEq::eq method call.
    ///
    /// For types implementing PartialEq (including Option, Result, structs),
    /// translates to SMT equality. The method signature is `fn eq(&self, other: &Rhs) -> bool`,
    /// so `args[0]` is `&self` and `args[1]` is `&other`.
    ///
    /// Part of #407: Option/datatype equality comparison.
    /// Part of #408: ZST array equality - always returns true for ZST types.
    ///
    /// REQUIRES: args.len() >= 2
    /// ENSURES: destination gets boolean result of equality comparison
    pub(super) fn codegen_partial_eq(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        // #408: Check for ZST types first - equality on ZST always returns true
        // This handles zero-length arrays, arrays of unit type, and unit type itself
        let is_zst_0 = self.is_raw_eq_zst(&args[0]);
        let is_zst_1 = self.is_raw_eq_zst(&args[1]);
        debug!("codegen_partial_eq: is_zst_0={}, is_zst_1={}", is_zst_0, is_zst_1);
        let is_zst = is_zst_0 && is_zst_1;
        if is_zst {
            debug!("codegen_partial_eq: ZST detected, returning true");
            self.bind_ssa_result(destination, Expr::bool_const(true));
            return target;
        }

        // PartialEq::eq takes &self and &other, so args are references.
        // Use get_value_through_ref to dereference and get actual values.
        let lhs = self.codegen_ord_operand_value(&args[0])?;
        let rhs = self.codegen_ord_operand_value(&args[1])?;
        let lhs = unwrap_single_field_datatype_to_sort(&lhs, rhs.sort()).unwrap_or(lhs);
        let rhs = unwrap_single_field_datatype_to_sort(&rhs, lhs.sort()).unwrap_or(rhs);

        // #3133: Normalize Option Datatype↔BV mismatches. When iter.next() returns
        // a Datatype Option and the comparison target is a bare BV from flattened
        // encoding, wrap the BV in Some() to bridge the sort mismatch.
        let (lhs, rhs) = if lhs.sort() != rhs.sort() {
            if let Some(wrapped) = try_wrap_bv_as_option_some(lhs.sort(), &rhs) {
                (lhs, wrapped)
            } else if let Some(wrapped) = try_wrap_bv_as_option_some(rhs.sort(), &lhs) {
                (wrapped, rhs)
            } else {
                (lhs, rhs)
            }
        } else {
            (lhs, rhs)
        };

        debug!("codegen_partial_eq: lhs.sort={:?}, rhs.sort={:?}", lhs.sort(), rhs.sort());

        // #703: Check for sort mismatch before comparison. This can happen when
        // get_value_through_ref fails to dereference (returning pointer bitvec)
        // while the other side successfully dereferences (returning array/struct).
        // Return None to signal unsupported construct rather than panicking.
        // #1043: Allow Int/BitVec mixed comparisons (BigInt types)
        if lhs.sort() != rhs.sort() {
            let both_bitvec = lhs.sort().is_bitvec() && rhs.sort().is_bitvec();
            let int_bitvec_mix = (lhs.sort().is_int() || rhs.sort().is_int())
                && (lhs.sort().is_int() || lhs.sort().is_bitvec())
                && (rhs.sort().is_int() || rhs.sort().is_bitvec());
            if !both_bitvec && !int_bitvec_mix {
                warn!(
                    lhs_sort = ?lhs.sort(),
                    rhs_sort = ?rhs.sort(),
                    "codegen_partial_eq: sort mismatch, cannot compare"
                );
                return None;
            }
        }

        // Use SMT equality - works for all sorts including datatypes
        // Coerce to match widths for bitvector comparisons
        let eq_result = if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
            // Part of #3041: For equal-width bitvecs, signedness is irrelevant —
            // equality is bitwise identical regardless of signed/unsigned interpretation,
            // and coerce_to_match_widths_typed is a no-op when widths match.
            // Skip the signedness check to avoid false demotion from signedness_fallback.
            if lhs.sort().bitvec_width() == rhs.sort().bitvec_width() {
                lhs.eq(rhs)
            } else {
                let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                    crate::codegen_ay::shared::signedness_fallback("codegen_partial_eq")
                });
                let (lhs_coerced, rhs_coerced) =
                    Self::coerce_to_match_widths_typed(lhs, rhs, is_signed);
                lhs_coerced.eq(rhs_coerced)
            }
        } else {
            // #1043: Handle Int/BitVec mixed comparisons (BigInt types)
            if lhs.sort().is_int() || rhs.sort().is_int() {
                // Part of #2757: Use signed bv2int when operand is signed.
                let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                    crate::codegen_ay::shared::signedness_fallback("codegen_partial_eq_int_mix")
                });
                let lhs_int = if lhs.sort().is_int() {
                    lhs
                } else if lhs.sort().is_bitvec() {
                    if is_signed { lhs.bv2int_signed() } else { lhs.bv2int() }
                } else {
                    lhs
                };
                let rhs_int = if rhs.sort().is_int() {
                    rhs
                } else if rhs.sort().is_bitvec() {
                    if is_signed { rhs.bv2int_signed() } else { rhs.bv2int() }
                } else {
                    rhs
                };
                lhs_int.eq(rhs_int)
            } else {
                // For datatypes and other sorts, direct equality
                option_like_datatype_eq(&lhs, &rhs, true).unwrap_or_else(|| lhs.eq(rhs))
            }
        };

        self.bind_ssa_result(destination, eq_result);

        target
    }

    /// Codegen PartialEq::ne method call (not equal).
    ///
    /// Similar to codegen_partial_eq but returns negated result.
    ///
    /// Part of #407: Option/datatype inequality comparison.
    /// Part of #408: ZST array inequality - always returns false for ZST types.
    ///
    /// REQUIRES: args.len() >= 2
    /// ENSURES: destination gets boolean result of inequality comparison
    pub(super) fn codegen_partial_ne(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        // #408: Check for ZST types first - inequality on ZST always returns false
        // This handles zero-length arrays, arrays of unit type, and unit type itself
        let is_zst = self.is_raw_eq_zst(&args[0]) && self.is_raw_eq_zst(&args[1]);
        if is_zst {
            debug!("codegen_partial_ne: ZST detected, returning false");
            self.bind_ssa_result(destination, Expr::bool_const(false));
            return target;
        }

        let lhs = self.codegen_ord_operand_value(&args[0])?;
        let rhs = self.codegen_ord_operand_value(&args[1])?;
        let lhs = unwrap_single_field_datatype_to_sort(&lhs, rhs.sort()).unwrap_or(lhs);
        let rhs = unwrap_single_field_datatype_to_sort(&rhs, lhs.sort()).unwrap_or(rhs);

        // #3133: Same Option Datatype↔BV normalization as codegen_partial_eq.
        let (lhs, rhs) = if lhs.sort() != rhs.sort() {
            if let Some(wrapped) = try_wrap_bv_as_option_some(lhs.sort(), &rhs) {
                (lhs, wrapped)
            } else if let Some(wrapped) = try_wrap_bv_as_option_some(rhs.sort(), &lhs) {
                (wrapped, rhs)
            } else {
                (lhs, rhs)
            }
        } else {
            (lhs, rhs)
        };

        debug!("codegen_partial_ne: lhs.sort={:?}, rhs.sort={:?}", lhs.sort(), rhs.sort());

        // #703: Check for sort mismatch before comparison (same as codegen_partial_eq)
        // #1043: Allow Int/BitVec mixed comparisons (BigInt types)
        if lhs.sort() != rhs.sort() {
            let both_bitvec = lhs.sort().is_bitvec() && rhs.sort().is_bitvec();
            let int_bitvec_mix = (lhs.sort().is_int() || rhs.sort().is_int())
                && (lhs.sort().is_int() || lhs.sort().is_bitvec())
                && (rhs.sort().is_int() || rhs.sort().is_bitvec());
            if !both_bitvec && !int_bitvec_mix {
                warn!(
                    lhs_sort = ?lhs.sort(),
                    rhs_sort = ?rhs.sort(),
                    "codegen_partial_ne: sort mismatch, cannot compare"
                );
                return None;
            }
        }

        // Use SMT inequality - works for all sorts including datatypes
        let ne_result = if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
            // Part of #3041: Same equal-width optimization as codegen_partial_eq.
            if lhs.sort().bitvec_width() == rhs.sort().bitvec_width() {
                lhs.ne(rhs)
            } else {
                let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                    crate::codegen_ay::shared::signedness_fallback("codegen_partial_ne")
                });
                let (lhs_coerced, rhs_coerced) =
                    Self::coerce_to_match_widths_typed(lhs, rhs, is_signed);
                lhs_coerced.ne(rhs_coerced)
            }
        } else {
            // #1043: Handle Int/BitVec mixed comparisons (BigInt types)
            if lhs.sort().is_int() || rhs.sort().is_int() {
                // Part of #2757: Use signed bv2int when operand is signed.
                let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                    crate::codegen_ay::shared::signedness_fallback("codegen_partial_ne_int_mix")
                });
                let lhs_int = if lhs.sort().is_int() {
                    lhs
                } else if lhs.sort().is_bitvec() {
                    if is_signed { lhs.bv2int_signed() } else { lhs.bv2int() }
                } else {
                    lhs
                };
                let rhs_int = if rhs.sort().is_int() {
                    rhs
                } else if rhs.sort().is_bitvec() {
                    if is_signed { rhs.bv2int_signed() } else { rhs.bv2int() }
                } else {
                    rhs
                };
                lhs_int.ne(rhs_int)
            } else {
                // For datatypes and other sorts, direct inequality
                option_like_datatype_eq(&lhs, &rhs, false).unwrap_or_else(|| lhs.ne(rhs))
            }
        };
        self.bind_ssa_result(destination, ne_result);

        target
    }

    /// Codegen PartialOrd comparison operations (lt, le, gt, ge).
    ///
    /// Part of #1482: Handle primitive PartialOrd trait methods for comparison.
    ///
    /// REQUIRES: args.len() >= 2
    /// ENSURES: destination gets boolean result of ordered comparison
    pub(super) fn codegen_partial_ord_cmp(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        op: &str,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let lhs = self.codegen_ord_operand_value(&args[0])?;
        let rhs = self.codegen_ord_operand_value(&args[1])?;
        let raw_pointer = self.operand_is_raw_pointer_like(&args[0])
            || self.operand_is_raw_pointer_like(&args[1]);

        debug!(
            "codegen_partial_ord_cmp({op}): lhs.sort={:?}, rhs.sort={:?}",
            lhs.sort(),
            rhs.sort()
        );

        if let Some(cmp_result) =
            self.codegen_slice_or_array_partial_ord_cmp(&args[0], &args[1], &lhs, &rhs, op)
        {
            self.bind_ssa_result(destination, cmp_result);
            return target;
        }

        if raw_pointer {
            let cmp_result =
                self.codegen_total_order_relation_expr(lhs, rhs, &args[0], true, op)?;
            self.bind_ssa_result(destination, cmp_result);
            return target;
        }

        // Check for bitvec or int types
        let cmp_result = if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
            // Determine signedness from operand type
            let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                crate::codegen_ay::shared::signedness_fallback("codegen_partial_ord_cmp")
            });
            let (lhs_coerced, rhs_coerced) =
                Self::coerce_to_match_widths_typed(lhs, rhs, is_signed);

            match op {
                "lt" if is_signed => lhs_coerced.bvslt(rhs_coerced),
                "lt" => lhs_coerced.bvult(rhs_coerced),
                "le" if is_signed => lhs_coerced.bvsle(rhs_coerced),
                "le" => lhs_coerced.bvule(rhs_coerced),
                "gt" if is_signed => lhs_coerced.bvsgt(rhs_coerced),
                "gt" => lhs_coerced.bvugt(rhs_coerced),
                "ge" if is_signed => lhs_coerced.bvsge(rhs_coerced),
                "ge" => lhs_coerced.bvuge(rhs_coerced),
                _ => {
                    // external enum: BinOp
                    warn!("codegen_partial_ord_cmp: unknown op {op}");
                    // Part of #3211: Track constraint drop in demotion pipeline.
                    self.ctx.unsupported_with_fallback(
                        "partial_ord_cmp_unknown_op",
                        "unknown comparison op for bitvec",
                    );
                    return None;
                }
            }
        } else if lhs.sort().is_int() || rhs.sort().is_int() {
            // Integer (BigInt) comparison
            // Part of #2757: Use signed bv2int when operand is signed.
            let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                crate::codegen_ay::shared::signedness_fallback("codegen_partial_ord_cmp_int_mix")
            });
            let lhs_int = if lhs.sort().is_int() {
                lhs
            } else if lhs.sort().is_bitvec() {
                if is_signed { lhs.bv2int_signed() } else { lhs.bv2int() }
            } else {
                return None;
            };
            let rhs_int = if rhs.sort().is_int() {
                rhs
            } else if rhs.sort().is_bitvec() {
                if is_signed { rhs.bv2int_signed() } else { rhs.bv2int() }
            } else {
                return None;
            };

            match op {
                "lt" => lhs_int.int_lt(rhs_int),
                "le" => lhs_int.int_le(rhs_int),
                "gt" => lhs_int.int_gt(rhs_int),
                "ge" => lhs_int.int_ge(rhs_int),
                _ => {
                    // external enum: BinOp
                    warn!("codegen_partial_ord_cmp: unknown op {op}");
                    // Part of #3211: Track constraint drop in demotion pipeline.
                    self.ctx.unsupported_with_fallback(
                        "partial_ord_cmp_unknown_op",
                        "unknown comparison op for int",
                    );
                    return None;
                }
            }
        } else {
            warn!(
                lhs_sort = ?lhs.sort(),
                rhs_sort = ?rhs.sort(),
                "codegen_partial_ord_cmp: unsupported sort combination"
            );
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback(
                "partial_ord_cmp_unsupported_sorts",
                "unsupported sort combination",
            );
            return None;
        };

        self.bind_ssa_result(destination, cmp_result);

        target
    }

    pub(super) fn codegen_ord_minmax(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        is_min: bool,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let lhs = self.codegen_ord_operand_value(&args[0])?;
        let rhs = self.codegen_ord_operand_value(&args[1])?;
        let raw_pointer = self.operand_is_raw_pointer_like(&args[0])
            || self.operand_is_raw_pointer_like(&args[1]);
        let select_lhs = self.codegen_total_order_relation_expr(
            lhs.clone(),
            rhs.clone(),
            &args[0],
            raw_pointer,
            if is_min { "le" } else { "ge" },
        )?;
        let result = Expr::ite(select_lhs, lhs, rhs);
        self.bind_ssa_result(destination, result);
        target
    }

    pub(super) fn codegen_ord_clamp(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 3 {
            return None;
        }

        let value = self.codegen_ord_operand_value(&args[0])?;
        let min_value = self.codegen_ord_operand_value(&args[1])?;
        let max_value = self.codegen_ord_operand_value(&args[2])?;
        let raw_pointer = self.operand_is_raw_pointer_like(&args[0])
            || self.operand_is_raw_pointer_like(&args[1])
            || self.operand_is_raw_pointer_like(&args[2]);
        let below_min = self.codegen_total_order_relation_expr(
            value.clone(),
            min_value.clone(),
            &args[0],
            raw_pointer,
            "lt",
        )?;
        let above_max = self.codegen_total_order_relation_expr(
            value.clone(),
            max_value.clone(),
            &args[0],
            raw_pointer,
            "gt",
        )?;
        let result = Expr::ite(below_min, min_value, Expr::ite(above_max, max_value, value));
        self.bind_ssa_result(destination, result);
        target
    }
}
