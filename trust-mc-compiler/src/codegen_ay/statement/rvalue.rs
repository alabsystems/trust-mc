// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Rvalue codegen for AY - Part of #1354.
//!
//! This module handles translation of MIR Rvalues to AY expressions.
//! Includes:
//! - `codegen_rvalue`: Main rvalue translation dispatch
//! - `codegen_ptr_metadata`: Pointer metadata extraction
//!
//! Binary/unary operations are in `rvalue_binop.rs`.

use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::{BinOp, NullOp, Operand, RuntimeChecks, Rvalue, UnOp};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use super::{IntoOption, StatementCodegen, extract_fat_ptr_metadata};
use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};
use crate::kani_middle::abi::LayoutOf;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Returns pointee size for pointer-offset scaling, if layout metadata is available.
    ///
    /// Sized pointees use `size_of_head()`. Unsized slice/str tails use the tail
    /// element size. Other unsized tails and non-pointer types return `None`.
    pub(super) fn pointee_size_for_offset_ty(ptr_ty: rustc_public::ty::Ty) -> Option<usize> {
        match ptr_ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
            | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
                let layout = LayoutOf::new(pointee);
                if layout.is_sized() {
                    Some(layout.size_of_head())
                } else {
                    layout
                        .unsized_tail_elem_ty()
                        .map(|elem_ty| LayoutOf::new(elem_ty).size_of_head())
                }
            }
            _ => None, // external enum: TyKind
        }
    }

    /// Extract metadata from a wide pointer operand.
    ///
    /// For thin pointers, returns 0. For fat pointers (slices, trait objects),
    /// extracts the metadata field (length or vtable pointer).
    pub(super) fn codegen_ptr_metadata(&mut self, operand: &Operand) -> Option<Expr> {
        let ty = operand.ty(self.body.locals()).into_option()?;
        if !Self::is_wide_pointer_ty(ty) {
            return Some(Expr::bitvec_const(0, POINTER_WIDTH));
        }

        // Prefer extracting metadata from a fat pointer datatype (slice/str).
        if let Some(expr) = self.codegen_operand(operand)
            && let Some(meta) = extract_fat_ptr_metadata(&expr)
        {
            return Some(meta);
        }

        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let name = self.ssa_name(place, false);
                let meta_name = crate::codegen_ay::names::meta_name(&name);
                Some(self.ctx.declare_var(&meta_name, ptr_sort()))
            }
            Operand::Constant(_) => Some(Expr::bitvec_const(0, POINTER_WIDTH)),
        }
    }

    /// Translate an MIR Rvalue into a AY expression.
    /// REQUIRES: operands referenced by the rvalue are codegen-compatible.
    /// ENSURES: on Some, result sort matches inferred MIR type when available.
    pub(super) fn codegen_rvalue(&mut self, rvalue: &Rvalue) -> Option<Expr> {
        match rvalue {
            Rvalue::Use(operand) => self.codegen_operand(operand),

            Rvalue::BinaryOp(bin_op, lhs, rhs) => {
                let operand_ty =
                    rvalue.ty(self.body.locals()).into_option().and_then(|result_ty| {
                        match Self::infer_sort_from_ty(result_ty) {
                            Some(sort) if sort.is_bool() => {
                                lhs.ty(self.body.locals()).into_option()
                            }
                            Some(_) => Some(result_ty),
                            None => None,
                        }
                    });

                let (lhs_expr, rhs_expr) = if let Some(ty) = operand_ty {
                    (self.codegen_cast(lhs, ty)?, self.codegen_cast(rhs, ty)?)
                } else {
                    (self.codegen_operand(lhs)?, self.codegen_operand(rhs)?)
                };
                let is_float = lhs
                    .ty(self.body.locals())
                    .into_option()
                    .is_some_and(|ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Float(_))));

                // For shift operations, only the value operand's (LHS) signedness
                // matters; the shift amount may have a different type in MIR.
                let is_signed = if matches!(
                    bin_op,
                    BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked
                ) {
                    self.operand_signedness(lhs)
                } else {
                    self.is_signed_integer_op(lhs, rhs)
                };

                // Emit division-by-zero check for all division/remainder operations.
                // Integer division by zero is UB in Rust. Float div/rem fail
                // closed below instead of reusing integer UB checks.
                if !is_float && matches!(bin_op, BinOp::Div | BinOp::Rem) {
                    let label = if matches!(bin_op, BinOp::Rem) {
                        "mod_by_zero_check"
                    } else {
                        "div_by_zero_check"
                    };
                    self.emit_division_by_zero_check(&rhs_expr, label);
                }

                // Emit overflow check for signed division/remainder
                // (INT_MIN / -1 overflows because |INT_MIN| > INT_MAX)
                if !is_float && matches!(bin_op, BinOp::Div | BinOp::Rem) && is_signed == Some(true)
                {
                    self.emit_overflow_check(*bin_op, &lhs_expr, &rhs_expr, true);
                }

                // Emit overflow check for unchecked arithmetic operations.
                // These operations assume no overflow (UB if it occurs), so we emit
                // an assertion that overflow does not occur for verification.
                if matches!(bin_op, BinOp::AddUnchecked | BinOp::SubUnchecked | BinOp::MulUnchecked)
                {
                    let is_signed_val = is_signed.unwrap_or_else(|| {
                        crate::codegen_ay::shared::signedness_fallback_for_arithmetic(
                            "codegen_rvalue_unchecked",
                        )
                    });
                    self.emit_overflow_check(*bin_op, &lhs_expr, &rhs_expr, is_signed_val);
                }

                // Emit shift distance check for unchecked shift operations.
                // Shifting by >= bit width or negative amount is UB.
                if matches!(bin_op, BinOp::ShlUnchecked | BinOp::ShrUnchecked) {
                    let rhs_signed = self.operand_signedness(rhs);
                    self.emit_shift_distance_check(&lhs_expr, &rhs_expr, rhs_signed);
                }

                // Handle BinOp::Offset specially - must scale count by pointee size.
                // MIR BinOp::Offset receives element count, not byte offset.
                // See: https://doc.rust-lang.org/std/primitive.pointer.html#method.offset
                // See: https://github.com/rust-lang/rust/pull/110822
                // Fixes #314.
                if matches!(bin_op, BinOp::Offset) {
                    let ptr_width = lhs_expr.sort().bitvec_width().unwrap_or(POINTER_WIDTH);

                    // Get pointee size from layout metadata.
                    // Unknown sizes are fail-closed: returning None keeps the assignment
                    // unconstrained rather than encoding unsound byte-scaled arithmetic (#2315).
                    let ptr_ty = lhs.ty(self.body.locals()).into_option();
                    let pointee_size = ptr_ty.and_then(Self::pointee_size_for_offset_ty);
                    let Some(pointee_size) = pointee_size else {
                        warn!(
                            ?ptr_ty,
                            ?lhs,
                            "BinOp::Offset: unable to determine pointee size; dropping translation"
                        );
                        return None;
                    };

                    debug!("BinOp::Offset: ptr_width={}, pointee_size={}", ptr_width, pointee_size);

                    // Fix #1224: Assert base pointer is non-null.
                    // Pointer arithmetic on null is undefined behavior in Rust.
                    // This prevents the solver from picking base = 0 to satisfy
                    // the offset computation, which would cause false null-pointer
                    // failures on the resulting pointer dereference.
                    let zero = Expr::bitvec_const(0u128, ptr_width);
                    let base_non_null = lhs_expr.clone().eq(zero.clone()).not();
                    self.assert_guarded(base_non_null.clone());

                    // Fix #761: Add upper-bound constraint on base pointer to prevent
                    // false positive overflow checks. Valid pointers (from stack allocations,
                    // heap allocations, or slice data pointers) are not in the extreme upper
                    // range of the address space. We assume base <= MAX - isize::MAX so that
                    // adding any valid offset won't wrap around.
                    //
                    // Without this constraint, the solver can pick adversarial base address
                    // values (e.g., 0xFFFFFFFFFFFFFFFD) that cause wrap-around for small
                    // positive offsets, triggering false overflow violations.
                    let isize_max = (1u128 << (ptr_width - 1)) - 1;
                    let max_valid_base = if ptr_width >= 128 {
                        u128::MAX - isize_max
                    } else {
                        ((1u128 << ptr_width) - 1) - isize_max
                    };
                    let max_valid_expr = Expr::bitvec_const(max_valid_base, ptr_width);
                    let base_in_range = lhs_expr.clone().bvule(max_valid_expr);
                    self.assert_guarded(base_in_range);

                    // Emit overflow checks for the offset operation.
                    //
                    // `pointee_size_for_offset_ty` already established that the
                    // lhs operand's MIR type is `*T` / `&T`, so its term is an
                    // ADDRESS; `BinOp::Offset`'s rhs is an element count, a
                    // VALUE. That is where the provenance is known — not at the
                    // check emitter, which used to re-derive it from the width.
                    let base = Loc::of_address(lhs_expr.clone());
                    let count = Val::of_value(rhs_expr.clone());
                    self.emit_offset_overflow_check(&base, &count, pointee_size);

                    // Compute byte offset: count * size_of::<T>()
                    let byte_offset = match pointee_size {
                        0 => {
                            // ZST: byte offset is always zero.
                            Expr::bitvec_const(0u128, ptr_width)
                        }
                        1 => {
                            // Size 1 (e.g., u8): element count equals byte count.
                            Self::coerce_to_width_typed(rhs_expr, ptr_width, true)
                        }
                        _ => {
                            // non-enum: usize (pointee_size)
                            let count_extended =
                                Self::coerce_to_width_typed(rhs_expr, ptr_width, true);
                            let size_expr = Expr::bitvec_const(pointee_size as u128, ptr_width);
                            count_extended.bvmul(size_expr)
                        }
                    };

                    let result = lhs_expr.bvadd(byte_offset);

                    // Fix #761: Propagate non-null constraint for pointer arithmetic.
                    // If the base pointer is non-null (which is guaranteed for pointers derived
                    // from stack allocations via Ref/AddressOf), and the offset doesn't cause
                    // wrap-around (checked by emit_offset_overflow_check above), then the
                    // result pointer is also non-null. This prevents the solver from picking
                    // adversarial base address values that wrap around to zero.
                    // Note: Reuse `zero` and `base_non_null` from the #1224 non-null assertion above.
                    let result_non_null = result.clone().eq(zero).not();
                    // Assert: base != 0 => result != 0 (pointer arithmetic preserves validity)
                    let constraint = base_non_null.implies(result_non_null);
                    self.assert_guarded(constraint);

                    return Some(result);
                }

                // Part of #3140: IEEE 754 float comparison override.
                // Floats are encoded as unsigned bitvectors, but bvult/bvule is
                // unsound for negative IEEE 754 values. Use sign-aware comparison
                // helpers for ordered comparisons on float operands.
                if is_float
                    && matches!(
                        bin_op,
                        BinOp::Lt
                            | BinOp::Le
                            | BinOp::Gt
                            | BinOp::Ge
                            | BinOp::Cmp
                            | BinOp::Eq
                            | BinOp::Ne
                    )
                    && lhs_expr.sort().is_bitvec()
                {
                    use crate::codegen_ay::float_compare::{
                        bv_float_cmp, bv_float_eq, bv_float_ge, bv_float_gt, bv_float_le,
                        bv_float_lt, bv_float_ne,
                    };
                    let width = lhs_expr
                        .sort()
                        .bitvec_width()
                        .expect("invariant: sort is bitvec (guarded by is_bitvec check)");
                    return Some(match bin_op {
                        BinOp::Lt => bv_float_lt(&lhs_expr, &rhs_expr, width),
                        BinOp::Le => bv_float_le(&lhs_expr, &rhs_expr, width),
                        BinOp::Gt => bv_float_gt(&lhs_expr, &rhs_expr, width),
                        BinOp::Ge => bv_float_ge(&lhs_expr, &rhs_expr, width),
                        BinOp::Cmp => bv_float_cmp(&lhs_expr, &rhs_expr, width),
                        BinOp::Eq => bv_float_eq(&lhs_expr, &rhs_expr, width),
                        BinOp::Ne => bv_float_ne(&lhs_expr, &rhs_expr, width),
                        // INVARIANT: float comparison BinOps are exhausted above;
                        // arithmetic ops (Add/Sub/Mul/Div) take a separate path.
                        _ => unreachable!(),
                    });
                }

                // Part of #3693: Route float arithmetic through AY FP theory.
                if is_float && lhs_expr.sort().is_bitvec() {
                    use crate::codegen_ay::float_arithmetic::{
                        bv_float_binop, is_float_arithmetic_op,
                    };
                    if is_float_arithmetic_op(*bin_op) {
                        let width = lhs_expr
                            .sort()
                            .bitvec_width()
                            .expect("invariant: sort is bitvec (guarded by is_bitvec check)");
                        return bv_float_binop(*bin_op, lhs_expr, rhs_expr, width);
                    }
                }

                Some(self.codegen_binop_typed(*bin_op, lhs_expr, rhs_expr, is_signed))
            }

            // CheckedBinaryOp is intercepted in codegen_assign and handled with
            // split SSA variables (codegen_assign_checked_binary_op), so this
            // case is unreachable.
            Rvalue::CheckedBinaryOp(..) => unreachable!(
                "CheckedBinaryOp should be handled by codegen_assign_checked_binary_op"
            ),

            Rvalue::UnaryOp(UnOp::PtrMetadata, operand) => self.codegen_ptr_metadata(operand),

            Rvalue::UnaryOp(un_op, operand) => {
                let operand_expr = self.codegen_operand(operand)?;
                // Emit negation overflow check for signed integer negation (#272)
                // Signed negation of INT_MIN overflows (e.g., -(-128i8))
                if *un_op == UnOp::Neg && self.operand_signedness(operand) == Some(true) {
                    self.emit_neg_overflow_check(&operand_expr);
                }
                // Part of #3693: float negation is sign-bit flip, not two's complement.
                if *un_op == UnOp::Neg
                    && matches!(
                        operand.ty(self.body.locals()).into_option().map(|t| t.kind()),
                        Some(TyKind::RigidTy(RigidTy::Float(_)))
                    )
                {
                    let width = operand_expr
                        .sort()
                        .bitvec_width()
                        .expect("invariant: float negation operand sort is bitvec");
                    let sign_mask = match width {
                        32 => Expr::bitvec_const(0x8000_0000_i128, 32),
                        64 => Expr::bitvec_const(0x8000_0000_0000_0000_u64 as i128, 64),
                        _ => return Some(self.codegen_unop(*un_op, operand_expr)),
                    };
                    Some(operand_expr.bvxor(sign_mask))
                } else {
                    Some(self.codegen_unop(*un_op, operand_expr))
                }
            }

            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                self.codegen_address_of(place, rvalue)
            }

            Rvalue::Len(place) => {
                // #1316: Per Kani semantics, handle arrays and slices differently:
                // - Arrays: compile-time constant from type
                // - Slices: length from fat pointer metadata
                let ty = place.ty(self.body.locals()).into_option();

                // Check for array type - use compile-time constant length
                if let Some(ty) = &ty
                    && let TyKind::RigidTy(RigidTy::Array(_, const_len)) = ty.kind()
                    && let Some(len) = const_len.eval_target_usize().into_option()
                {
                    debug!("Rvalue::Len on array: compile-time length = {}", len);
                    return Some(Expr::bitvec_const(len as u128, POINTER_WIDTH));
                }

                // Check for slice type - extract from fat pointer metadata
                if let Some(ty) = &ty {
                    match ty.kind() {
                        TyKind::RigidTy(RigidTy::Slice(_)) | TyKind::RigidTy(RigidTy::Str) => {
                            // Try to get fat pointer expression and extract metadata (length)
                            // Call codegen_place directly to avoid cloning place into an Operand.
                            if let Some(meta) = self
                                .codegen_place(place)
                                .and_then(|expr| extract_fat_ptr_metadata(&expr))
                            {
                                debug!("Rvalue::Len on slice: extracted metadata from fat pointer");
                                return Some(meta);
                            }
                        }
                        // Reference to slice/str - dereference and extract metadata
                        TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                            if matches!(
                                inner.kind(),
                                TyKind::RigidTy(RigidTy::Slice(_)) | TyKind::RigidTy(RigidTy::Str)
                            ) =>
                        {
                            if let Some(meta) = self
                                .codegen_place(place)
                                .and_then(|expr| extract_fat_ptr_metadata(&expr))
                            {
                                debug!(
                                    "Rvalue::Len on &[T]/&str: extracted metadata from fat pointer"
                                );
                                return Some(meta);
                            }
                        }
                        _ => {} // external enum: TyKind
                    }
                }

                // Fallback to symbolic length for unhandled cases
                let name = self.ssa_name(place, false);
                let len_name = crate::codegen_ay::names::len_name(&name);
                debug!("Rvalue::Len fallback to symbolic: {}", len_name);
                Some(self.ctx.declare_var(&len_name, ptr_sort()))
            }

            Rvalue::Cast(kind, operand, ty) => self.codegen_cast_with_kind(kind, operand, *ty),

            Rvalue::Aggregate(kind, operands) => self.codegen_aggregate(kind, operands),

            Rvalue::Discriminant(place) => self.codegen_discriminant(place, rvalue),

            Rvalue::ShallowInitBox(operand, _ty) => {
                // Box initialization: treat as address
                self.codegen_operand(operand)
            }

            Rvalue::CopyForDeref(place) => {
                // Copy through a pointer: get the current value
                let name = self.ssa_name(place, false);
                self.ctx.lookup_var(&name).cloned()
            }

            Rvalue::Repeat(operand, len_const) => {
                // Array initialization: [value; count]
                // Create a const_array where all elements have the same value.
                // SMT arrays are unbounded, so we don't use len directly - bounds are
                // checked via array_bounds assertions elsewhere. We still validate len
                // to ensure it's a valid constant.
                let elem_expr = self.codegen_operand(operand)?;
                let len = len_const.eval_target_usize().into_option()?;
                debug!("codegen Repeat: elem_sort={:?}, len={}", elem_expr.sort(), len);
                // Native AY can return `unknown` on datatype-valued const arrays and
                // store chains. The assignment path tracks the repeated element for
                // direct indexed projections; keep the array value symbolic here.
                let result = if elem_expr.sort().is_datatype() && len <= 64 {
                    let array_sort = Sort::array(ptr_sort(), elem_expr.sort().clone());
                    let backing_name = self.ctx.fresh_name("repeat_array_symbolic");
                    self.ctx.declare_var(&backing_name, array_sort)
                } else {
                    Expr::const_array(ptr_sort(), elem_expr)
                };
                Some(result)
            }

            Rvalue::ThreadLocalRef(item) => {
                let item_name = item.name();
                let sort = rvalue
                    .ty(self.body.locals())
                    .into_option()
                    .and_then(Self::infer_sort_from_ty)
                    .unwrap_or_else(ptr_sort);
                debug!(
                    %item_name,
                    ?sort,
                    "ThreadLocalRef: symbolic variable (single-thread model)"
                );
                let var_name = self.ctx.fresh_name(&format!("__tls_{item_name}"));
                Some(self.ctx.declare_var(&var_name, sort))
            }

            Rvalue::NullaryOp(null_op) => {
                match null_op {
                    NullOp::RuntimeChecks(RuntimeChecks::UbChecks) => {
                        // Return true so MIR-generated UB assertions are reachable.
                        // Part of #3186: Parity with CHC path (Fixes #3299). Returning
                        // false makes Assert terminators for AddUnchecked/SubUnchecked/
                        // MulUnchecked dead code, producing false PROOF verdicts.
                        debug!("codegen_rvalue: UbChecks -> true (#3186 parity with CHC #3299)");
                        Some(Expr::bool_const(true))
                    }
                    NullOp::RuntimeChecks(RuntimeChecks::ContractChecks) => {
                        // Contract checks are enabled in verification mode
                        debug!("codegen_rvalue: ContractChecks -> true");
                        Some(Expr::bool_const(true))
                    }
                    NullOp::RuntimeChecks(RuntimeChecks::OverflowChecks) => {
                        // Overflow checks: verification handles overflow explicitly
                        // Return false to skip redundant runtime overflow checks
                        debug!("codegen_rvalue: OverflowChecks -> false");
                        Some(Expr::bool_const(false))
                    }
                }
            }
        }
    }
}
