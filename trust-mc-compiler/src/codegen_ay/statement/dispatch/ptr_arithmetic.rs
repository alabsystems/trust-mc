// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pointer offset arithmetic intrinsics.
//!
//! Extracted from helpers.rs per design D1 (file-decomposition-500loc-compliance).

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};

use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::abi::LayoutOf;

use super::super::IntoOption;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(in crate::codegen_ay::statement) fn codegen_ptr_offset_intrinsic(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let ptr_expr = self.codegen_operand(&args[0])?;
        let count_expr = self.codegen_operand(&args[1])?;

        let ptr_expr = self.coerce_to_ptr_width(ptr_expr);
        let ptr_width = ptr_expr.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
        // Sign-extend count (isize) — negative offsets must preserve sign.
        let count_expr = Self::coerce_to_width_typed(count_expr, ptr_width, true);

        let pointee_size = if let Some(ptr_ty) = args[0].ty(self.body.locals()).into_option() {
            match ptr_ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
                | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
                    let layout = LayoutOf::new(pointee);
                    if layout.is_sized() {
                        layout.size_of_head()
                    } else if let Some(elem_ty) = layout.unsized_tail_elem_ty() {
                        LayoutOf::new(elem_ty).size_of_head()
                    } else {
                        1
                    }
                }
                _ => 1, // external enum: TyKind
            }
        } else {
            1
        };

        let zero = Expr::bitvec_const(0u128, ptr_width);
        let base_non_null = ptr_expr.clone().eq(zero).not();
        self.assert_guarded(base_non_null);

        let isize_max = (1u128 << (ptr_width - 1)) - 1;
        let max_valid_base = if ptr_width >= 128 {
            u128::MAX - isize_max
        } else {
            ((1u128 << ptr_width) - 1) - isize_max
        };
        let max_valid_expr = Expr::bitvec_const(max_valid_base, ptr_width);
        let base_in_range = ptr_expr.clone().bvule(max_valid_expr);
        self.assert_guarded(base_in_range);

        self.emit_offset_overflow_check(&ptr_expr, &count_expr, pointee_size);

        let byte_offset = match pointee_size {
            0 => Expr::bitvec_const(0u128, ptr_width),
            1 => count_expr,
            _ => {
                // non-enum: usize (pointee_size)
                let size_expr = Expr::bitvec_const(pointee_size as u128, ptr_width);
                count_expr.bvmul(size_expr)
            }
        };

        let result = ptr_expr.bvadd(byte_offset);
        self.assign_value_to_place(destination, result);
        target
    }

    /// Codegen ptr_offset_from intrinsic.
    ///
    /// Part of #1490: Made pub(super) for use by KaniModel handlers.
    pub(in crate::codegen_ay::statement) fn codegen_ptr_offset_from(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        unsigned: bool,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let lhs_expr = self.codegen_operand(&args[0])?;
        let rhs_expr = self.codegen_operand(&args[1])?;
        let lhs_ptr = self.coerce_to_ptr_width(lhs_expr);
        let rhs_ptr = self.coerce_to_ptr_width(rhs_expr);
        let ptr_width = lhs_ptr.sort().bitvec_width().unwrap_or(POINTER_WIDTH);

        let pointee_size = if let Some(ptr_ty) = args[0].ty(self.body.locals()).into_option() {
            match ptr_ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
                | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
                    let layout = LayoutOf::new(pointee);
                    if layout.is_sized() {
                        layout.size_of_head()
                    } else if let Some(elem_ty) = layout.unsized_tail_elem_ty() {
                        LayoutOf::new(elem_ty).size_of_head()
                    } else {
                        1
                    }
                }
                _ => 1, // external enum: TyKind
            }
        } else {
            1
        };

        let diff_bytes = lhs_ptr.bvsub(rhs_ptr);
        let elem_size = if pointee_size == 0 { 1 } else { pointee_size };
        let size_expr = Expr::bitvec_const(elem_size as u128, ptr_width);
        let offset =
            if unsigned { diff_bytes.bvudiv(size_expr) } else { diff_bytes.bvsdiv(size_expr) };

        self.assign_value_to_place(destination, offset);
        target
    }

    /// Codegen `KaniModel::Offset` — `ptr::offset(ptr, count)`.
    ///
    /// Part of #2912: Kani rewrites `core::ptr::offset` to this model function.
    /// Computes `ptr + count * sizeof(T)` where T is the pointee type.
    /// Essential for inlined `IntoIter::next()` which advances the read pointer.
    pub(in crate::codegen_ay::statement) fn codegen_model_offset(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        _instance: &Option<rustc_public::mir::mono::Instance>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            tracing::warn!("Model(Offset): expected 2 args, got {}", args.len());
            self.codegen_symbolic_result(destination);
            return target;
        }

        let ptr_expr = self.codegen_operand(&args[0])?;
        let count_expr = self.codegen_operand(&args[1])?;
        let ptr_coerced = self.coerce_to_ptr_width(ptr_expr);
        let ptr_width = ptr_coerced.sort().bitvec_width().unwrap_or(POINTER_WIDTH);

        // Determine pointee size from the first argument's type.
        // Mirrors codegen_ptr_offset_intrinsic logic including unsized tail handling.
        let pointee_size = if let Some(ptr_ty) = args[0].ty(self.body.locals()).into_option() {
            match ptr_ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
                | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
                    let layout = LayoutOf::new(pointee);
                    if layout.is_sized() {
                        layout.size_of_head()
                    } else if let Some(elem_ty) = layout.unsized_tail_elem_ty() {
                        LayoutOf::new(elem_ty).size_of_head()
                    } else {
                        1
                    }
                }
                _ => 1, // external enum: TyKind
            }
        } else {
            1
        };

        // Sign-extend count (isize) — negative offsets must preserve sign.
        let count_extended = Self::coerce_to_width_typed(count_expr, ptr_width, true);

        // Safety checks matching codegen_ptr_offset_intrinsic:
        // ptr::offset requires non-null base and no wrapping overflow.
        let zero = Expr::bitvec_const(0u128, ptr_width);
        self.assert_guarded(ptr_coerced.clone().eq(zero).not());
        self.emit_offset_overflow_check(&ptr_coerced, &count_extended, pointee_size);

        let byte_offset = match pointee_size {
            0 => Expr::bitvec_const(0u128, ptr_width),
            1 => count_extended,
            _ => {
                let size_expr = Expr::bitvec_const(pointee_size as u128, ptr_width);
                count_extended.bvmul(size_expr)
            }
        };

        let result = ptr_coerced.bvadd(byte_offset);

        tracing::debug!(
            pointee_size,
            "codegen Model(Offset): ptr + count * {} = result",
            pointee_size
        );

        self.assign_value_to_place(destination, result);
        target
    }

    /// Try to codegen `offset_from_unsigned::runtime_ptr_ge(self, origin) -> bool`.
    ///
    /// Part of #3783: BMC-side handler for the internal runtime check within
    /// `offset_from_unsigned`. Without this, the BMC path records an unsupported
    /// construct that taints the CHC verdict via demotion.
    ///
    /// Encodes as `bvuge(lhs, rhs)` — unsigned pointer comparison.
    pub(in crate::codegen_ay::statement) fn try_codegen_runtime_ptr_ge(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let callee_path = self.resolve_callee_path(func)?;
        if !(callee_path.ends_with("::runtime_ptr_ge") && callee_path.contains("::ptr::")) {
            return None;
        }
        if args.len() < 2 {
            return None;
        }

        let lhs = self.codegen_operand(&args[0])?;
        let rhs = self.codegen_operand(&args[1])?;
        let lhs = self.coerce_to_ptr_width(lhs);
        let rhs = self.coerce_to_ptr_width(rhs);

        // runtime_ptr_ge returns bool: true if self >= origin.
        let result = lhs.bvuge(rhs);
        self.assign_value_to_place(destination, result);
        target
    }
}
