// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Comparison operations for AY codegen.
//!
//! This module implements Ord::cmp, PartialEq::eq/ne, and raw_eq intrinsics
//! used for trait-based comparisons.
//!
//! Extracted from statement/mod.rs per #717.

use crate::codegen_ay::types::{CtorFieldExt, bool_sort, int_sort};
use ay_bindings::sort::SortInner;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use super::{IntoOption, StatementCodegen};

mod ord_array;
mod raw_eq;

/// #3133: Try to wrap a bare BV expression as `Some(bv)` in an Option Datatype sort.
///
/// When one comparison operand is a Datatype Option (from value-semantic encoding)
/// and the other is a bare BV (from flattened encoding fallback), this bridges the
/// sort mismatch by wrapping the BV in the matching Option's Some constructor.
///
/// Returns `Some(wrapped)` when `option_sort` has exactly 2 constructors (None + Some)
/// and `bv_expr`'s sort matches the Some payload sort. Returns `None` otherwise.
pub(super) fn try_wrap_bv_as_option_some(option_sort: &Sort, bv_expr: &Expr) -> Option<Expr> {
    let SortInner::Datatype(dt) = option_sort.inner() else {
        return None;
    };

    // Option has exactly 2 constructors: None (0 fields) and Some (1 field)
    if dt.constructors.len() != 2 {
        return None;
    }

    // Find the Some constructor (has exactly 1 field)
    let some_cons = dt.constructors.iter().find(|c| c.fields.len() == 1)?;
    let payload_sort = &some_cons.fields[0].sort;

    // BV must match the payload sort
    if bv_expr.sort() != payload_sort {
        return None;
    }

    debug!(
        option_sort = ?option_sort,
        bv_sort = ?bv_expr.sort(),
        "normalize_option_for_comparison: wrapping BV in Some()"
    );

    Some(Expr::datatype_constructor(
        &dt.name,
        &some_cons.name,
        vec![bv_expr.clone()],
        option_sort.clone(),
    ))
}

fn extract_raw_pointer_order_components(expr: &Expr) -> Option<(Expr, Option<Expr>)> {
    if expr.sort().is_bitvec() {
        return Some((expr.clone(), None));
    }

    let SortInner::Datatype(dt) = expr.sort().inner() else {
        return None;
    };
    let cons = dt.constructors.first()?;
    let ptr_field =
        cons.field("fld_ptr").or_else(|| cons.field("ptr")).or_else(|| cons.field("fld_data"))?;
    let ptr = expr.clone().field_select(&*dt.name, &*ptr_field.name, ptr_field.sort.clone());
    let metadata = cons
        .field("fld_len")
        .or_else(|| cons.field("fld_vtable"))
        .or_else(|| cons.field("fld_meta"))
        .map(|field| expr.clone().field_select(&*dt.name, &*field.name, field.sort.clone()));
    Some((ptr, metadata))
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    fn ty_contains_raw_pointer(ty: rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(..)) => true,
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Self::ty_contains_raw_pointer(pointee),
            _ => false,
        }
    }

    pub(super) fn operand_is_raw_pointer_like(&self, operand: &Operand) -> bool {
        operand.ty(self.body.locals()).into_option().is_some_and(Self::ty_contains_raw_pointer)
    }

    pub(super) fn codegen_ord_operand_value(&mut self, operand: &Operand) -> Option<Expr> {
        match operand.ty(self.body.locals()).into_option()?.kind() {
            TyKind::RigidTy(RigidTy::Ref(..)) => self.get_value_through_ref(operand),
            _ => self.codegen_operand(operand),
        }
    }

    fn raw_pointer_strict_order_exprs(lhs: Expr, rhs: Expr) -> Option<(Expr, Expr)> {
        let (lhs_ptr, lhs_meta) = extract_raw_pointer_order_components(&lhs)?;
        let (rhs_ptr, rhs_meta) = extract_raw_pointer_order_components(&rhs)?;
        let (lhs_ptr, rhs_ptr) = Self::coerce_to_match_widths_typed(lhs_ptr, rhs_ptr, false);
        let ptr_lt = lhs_ptr.clone().bvult(rhs_ptr.clone());
        let ptr_gt = lhs_ptr.clone().bvugt(rhs_ptr.clone());
        let ptr_eq = lhs_ptr.eq(rhs_ptr);

        match (lhs_meta, rhs_meta) {
            (Some(lhs_meta), Some(rhs_meta)) => {
                let (lhs_meta, rhs_meta) =
                    Self::coerce_to_match_widths_typed(lhs_meta, rhs_meta, false);
                let meta_lt = lhs_meta.clone().bvult(rhs_meta.clone());
                let meta_gt = lhs_meta.bvugt(rhs_meta);
                let lhs_lt =
                    Expr::or(ptr_lt, Expr::ite(ptr_eq.clone(), meta_lt, Expr::bool_const(false)));
                let lhs_gt = Expr::or(ptr_gt, Expr::ite(ptr_eq, meta_gt, Expr::bool_const(false)));
                Some((lhs_lt, lhs_gt))
            }
            (None, None) => Some((ptr_lt, ptr_gt)),
            _ => None,
        }
    }

    pub(super) fn codegen_total_order_relation_expr(
        &mut self,
        lhs: Expr,
        rhs: Expr,
        reference_operand: &Operand,
        raw_pointer: bool,
        op: &str,
    ) -> Option<Expr> {
        let (lt, gt) = if raw_pointer {
            Self::raw_pointer_strict_order_exprs(lhs, rhs)?
        } else if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
            let is_signed = self.operand_signedness(reference_operand).unwrap_or_else(|| {
                crate::codegen_ay::shared::signedness_fallback("codegen_total_order_relation_expr")
            });
            let (lhs_coerced, rhs_coerced) =
                Self::coerce_to_match_widths_typed(lhs, rhs, is_signed);
            if lhs_coerced.sort() != rhs_coerced.sort() {
                warn!(
                    lhs_sort = ?lhs_coerced.sort(),
                    rhs_sort = ?rhs_coerced.sort(),
                    "codegen_total_order_relation_expr: sort mismatch after coercion"
                );
                return None;
            }
            let lt = if is_signed {
                lhs_coerced.clone().bvslt(rhs_coerced.clone())
            } else {
                lhs_coerced.clone().bvult(rhs_coerced.clone())
            };
            let gt = if is_signed {
                lhs_coerced.bvsgt(rhs_coerced)
            } else {
                lhs_coerced.bvugt(rhs_coerced)
            };
            (lt, gt)
        } else if lhs.sort().is_int() || rhs.sort().is_int() {
            let is_signed = self.operand_signedness(reference_operand).unwrap_or_else(|| {
                crate::codegen_ay::shared::signedness_fallback(
                    "codegen_total_order_relation_expr_int_mix",
                )
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
            let lt = lhs_int.clone().int_lt(rhs_int.clone());
            let gt = lhs_int.int_gt(rhs_int);
            (lt, gt)
        } else {
            warn!(
                lhs_sort = ?lhs.sort(),
                rhs_sort = ?rhs.sort(),
                "codegen_total_order_relation_expr: unsupported sort combination"
            );
            return None;
        };

        match op {
            "lt" => Some(lt),
            "le" => Some(gt.not()),
            "gt" => Some(gt),
            "ge" => Some(lt.not()),
            "eq" => Some(Expr::ite(lt, Expr::bool_const(false), gt.not())),
            _ => {
                warn!(op, "codegen_total_order_relation_expr: unknown comparison op");
                None
            }
        }
    }

    /// Codegen Ord::cmp method call as three-way comparison.
    /// Returns Ordering enum encoded as 32-bit bitvec to match sort_inference.rs
    /// unit enum encoding: Less=0xFFFFFFFF (-1), Equal=0, Greater=1.
    ///
    /// Part of #752: Handles Int/BitVec mixed comparisons for BigInt types.
    /// Part of #1229: Fix width mismatch (was 8-bit, sort_inference uses 32-bit for unit enums).
    pub(super) fn codegen_ord_cmp(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // cmp takes &self and &other, so args[0] is &self, args[1] is &other
        if args.len() < 2 {
            return None;
        }

        let lhs = self.codegen_ord_operand_value(&args[0])?;
        let rhs = self.codegen_ord_operand_value(&args[1])?;
        let raw_pointer = self.operand_is_raw_pointer_like(&args[0])
            || self.operand_is_raw_pointer_like(&args[1]);

        if raw_pointer {
            let lt = self.codegen_total_order_relation_expr(
                lhs.clone(),
                rhs.clone(),
                &args[0],
                true,
                "lt",
            )?;
            let eq = self.codegen_total_order_relation_expr(lhs, rhs, &args[0], true, "eq")?;
            // Fix #4213: Less = 0xFFFFFFFF (-1 in BV32), not 0xFF (255).
            let cmp_result = Expr::ite(
                lt,
                Expr::bitvec_const(0xFFFF_FFFFu128, 32),
                Expr::ite(eq, Expr::bitvec_const(0u128, 32), Expr::bitvec_const(1u128, 32)),
            );
            self.bind_ssa_result(destination, cmp_result);
            return target;
        }

        // Determine signedness from operand types
        let is_signed = self
            .operand_signedness(&args[0])
            .unwrap_or_else(|| crate::codegen_ay::shared::signedness_fallback("codegen_ord_cmp"));

        if let Some(cmp_result) =
            self.codegen_slice_or_array_ord_cmp(&args[0], &args[1], &lhs, &rhs, is_signed)
        {
            self.bind_ssa_result(destination, cmp_result);
            return target;
        }

        // #752: Handle Int/BitVec mixed comparisons for BigInt types
        // If either operand is Int (from BigInt), use Int comparison operators
        let lhs_is_int = lhs.sort().is_int();
        let rhs_is_int = rhs.sort().is_int();
        debug!(
            "codegen_ord_cmp: lhs_sort={:?}, rhs_sort={:?}, lhs_is_int={}, rhs_is_int={}",
            lhs.sort(),
            rhs.sort(),
            lhs_is_int,
            rhs_is_int
        );

        let (lhs_cmp, rhs_cmp, lt) = if lhs_is_int || rhs_is_int {
            // Convert both to Int for comparison (BigInt path)
            // Part of #2757: Use signed bv2int when operand is signed.
            let lhs_int = if lhs_is_int {
                lhs
            } else if lhs.sort().is_bitvec() {
                if is_signed { lhs.bv2int_signed() } else { lhs.bv2int() }
            } else {
                // #1043: Non-Int/non-BitVec sort - create fresh Int symbol to avoid sort mismatch
                warn!(sort = ?lhs.sort(), "Unexpected sort in codegen_ord_cmp, creating Int symbol");
                let sym_name = self.ctx.fresh_name("ay_ord_cmp_lhs_int");
                self.ctx.declare_var(&sym_name, int_sort())
            };
            let rhs_int = if rhs_is_int {
                rhs
            } else if rhs.sort().is_bitvec() {
                if is_signed { rhs.bv2int_signed() } else { rhs.bv2int() }
            } else {
                // #1043: Non-Int/non-BitVec sort - create fresh Int symbol to avoid sort mismatch
                warn!(sort = ?rhs.sort(), "Unexpected sort in codegen_ord_cmp, creating Int symbol");
                let sym_name = self.ctx.fresh_name("ay_ord_cmp_rhs_int");
                self.ctx.declare_var(&sym_name, int_sort())
            };
            // Int comparison: use arithmetic < operator
            let lt_expr = lhs_int.clone().int_lt(rhs_int.clone());
            (lhs_int, rhs_int, lt_expr)
        } else {
            // Both are BitVec - use original logic
            let (lhs_coerced, rhs_coerced) =
                Self::coerce_to_match_widths_typed(lhs, rhs, is_signed);
            debug!(
                "codegen_ord_cmp: after coercion lhs_sort={:?}, rhs_sort={:?}",
                lhs_coerced.sort(),
                rhs_coerced.sort()
            );
            // Verify both operands are same-width bitvectors before using BV comparison.
            if !lhs_coerced.sort().is_bitvec()
                || !rhs_coerced.sort().is_bitvec()
                || lhs_coerced.sort().bitvec_width() != rhs_coerced.sort().bitvec_width()
            {
                warn!(
                    lhs_sort = ?lhs_coerced.sort(),
                    rhs_sort = ?rhs_coerced.sort(),
                    "codegen_ord_cmp: non-BV or width mismatch after coercion, using Int comparison"
                );
                // Convert to Int and use Int comparison as fallback
                // Part of #2757: Use signed bv2int when operand is signed.
                let lhs_int = if lhs_coerced.sort().is_bitvec() {
                    if is_signed { lhs_coerced.bv2int_signed() } else { lhs_coerced.bv2int() }
                } else if lhs_coerced.sort().is_int() {
                    lhs_coerced
                } else {
                    // Unsupported sort - create symbolic result
                    let sym_name = self.ctx.fresh_name("ay_ord_cmp_lhs");
                    self.ctx.declare_var(&sym_name, int_sort())
                };
                let rhs_int = if rhs_coerced.sort().is_bitvec() {
                    if is_signed { rhs_coerced.bv2int_signed() } else { rhs_coerced.bv2int() }
                } else if rhs_coerced.sort().is_int() {
                    rhs_coerced
                } else {
                    let sym_name = self.ctx.fresh_name("ay_ord_cmp_rhs");
                    self.ctx.declare_var(&sym_name, int_sort())
                };
                let lt_expr = lhs_int.clone().int_lt(rhs_int.clone());
                (lhs_int, rhs_int, lt_expr)
            } else {
                let lt_expr = if is_signed {
                    lhs_coerced.clone().bvslt(rhs_coerced.clone())
                } else {
                    lhs_coerced.clone().bvult(rhs_coerced.clone())
                };
                (lhs_coerced, rhs_coerced, lt_expr)
            }
        };

        // #1043: Verify sorts match before calling eq() to prevent panic
        let eq_cond = if lhs_cmp.sort() == rhs_cmp.sort() {
            lhs_cmp.eq(rhs_cmp)
        } else {
            // Sort mismatch - this shouldn't happen but handle gracefully
            warn!(
                lhs_sort = ?lhs_cmp.sort(),
                rhs_sort = ?rhs_cmp.sort(),
                "codegen_ord_cmp: sort mismatch in eq comparison, returning symbolic"
            );
            let sym_name = self.ctx.fresh_name("ay_ord_cmp_eq");
            self.ctx.declare_var(&sym_name, bool_sort())
        };

        // Ordering discriminant values as 32-bit bitvecs to match sort_inference.rs
        // unit enum encoding (all unit enums with <= 65536 variants use bitvec(32)).
        // Rust Ordering: Less=-1, Equal=0, Greater=1 (repr(i8)).
        // In 32-bit BV: Less=0xFFFFFFFF (-1 in two's complement), Equal=0, Greater=1.
        // Fix #4213: was 0xFF (255) which never matched SwitchInt's 0xFFFFFFFF.
        let cmp_result = Expr::ite(
            lt,
            Expr::bitvec_const(0xFFFF_FFFFu128, 32), // Less = -1 in BV32
            Expr::ite(
                eq_cond,
                Expr::bitvec_const(0u128, 32), // Equal = 0
                Expr::bitvec_const(1u128, 32), // Greater = 1
            ),
        );

        self.bind_ssa_result(destination, cmp_result);

        target
    }
}

// PartialEq/PartialOrd/min/max/clamp methods moved to comparison_eq.rs per #4206.
