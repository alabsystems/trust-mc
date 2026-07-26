// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Constant extraction and folding helpers for math intrinsics.
//!
//! Extracted from `math.rs`. These functions extract constant values from MIR
//! operands and AY expressions for compile-time evaluation of math intrinsics.

use ay_bindings::Expr;
use rustc_public::mir::{ConstOperand, Operand};
use rustc_public::ty::{ConstantKind, RigidTy, TyConstKind, TyKind};

use super::IntoOption;
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Try to extract a constant f32 value from an operand.
    /// Returns the raw bits as u32 if successful.
    ///
    /// Handles two cases:
    /// 1. Operand::Constant - directly extracts from MIR constant
    /// 2. Operand::Copy/Move - looks up SSA env for simple locals (no projections)
    pub(in crate::codegen_ay::statement) fn try_extract_f32_const(
        &mut self,
        operand: &Operand,
    ) -> Option<u32> {
        match operand {
            Operand::Constant(c) => self.extract_f32_from_const_operand(c),
            Operand::Copy(place) | Operand::Move(place) => {
                // Only handle simple locals (no projections) for constant propagation
                if !place.projection.is_empty() {
                    return None;
                }
                // Look up the local's current expression in SSA environment
                // Use ssa_base_name to get the correct name format: fn::local_N
                let base_name = self.ssa_base_name(place);
                let expr = self.env_lookup(&base_name)?.clone();
                self.extract_f32_from_expr(&expr)
            }
        }
    }

    /// Try to extract a constant f64 value from an operand.
    /// Returns the raw bits as u64 if successful.
    ///
    /// Handles two cases:
    /// 1. Operand::Constant - directly extracts from MIR constant
    /// 2. Operand::Copy/Move - looks up SSA env for simple locals (no projections)
    pub(in crate::codegen_ay::statement) fn try_extract_f64_const(
        &mut self,
        operand: &Operand,
    ) -> Option<u64> {
        match operand {
            Operand::Constant(c) => self.extract_f64_from_const_operand(c),
            Operand::Copy(place) | Operand::Move(place) => {
                // Only handle simple locals (no projections) for constant propagation
                if !place.projection.is_empty() {
                    return None;
                }
                // Look up the local's current expression in SSA environment
                // Use ssa_base_name to get the correct name format: fn::local_N
                let base_name = self.ssa_base_name(place);
                let expr = self.env_lookup(&base_name)?.clone();
                self.extract_f64_from_expr(&expr)
            }
        }
    }

    /// Try to extract a constant i32 value from an operand (for powi).
    ///
    /// Handles two cases:
    /// 1. Operand::Constant - directly extracts from MIR constant
    /// 2. Operand::Copy/Move - looks up SSA env for simple locals (no projections)
    pub(in crate::codegen_ay::statement) fn try_extract_i32_const(
        &mut self,
        operand: &Operand,
    ) -> Option<i32> {
        match operand {
            Operand::Constant(c) => {
                let mir_const = &c.const_;
                let alloc = match mir_const.kind() {
                    ConstantKind::Allocated(alloc) => alloc.clone(),
                    ConstantKind::Ty(ty_const) => match ty_const.kind() {
                        TyConstKind::Value(_ty, alloc) => alloc.clone(),
                        _ => return None, // external enum: TyConstKind
                    },
                    _ => return None, // external enum: ConstantKind
                };
                alloc.read_int().into_option().map(|v| v as i32)
            }
            Operand::Copy(place) | Operand::Move(place) => {
                // Only handle simple locals (no projections)
                if !place.projection.is_empty() {
                    return None;
                }
                let base_name = self.ssa_base_name(place);
                let expr = self.env_lookup(&base_name)?.clone();
                self.extract_i32_from_expr(&expr)
            }
        }
    }

    /// Extract f32 bits from a AY expression if it's a bitvec constant.
    fn extract_f32_from_expr(&self, expr: &Expr) -> Option<u32> {
        use ay_bindings::ExprValue;
        // Check if expression is a 32-bit bitvec constant
        if let ExprValue::BitVecConst { value, width } = expr.value()
            && *width == 32
        {
            return u32::try_from(value).ok();
        }
        None
    }

    /// Extract f64 bits from a AY expression if it's a bitvec constant.
    fn extract_f64_from_expr(&self, expr: &Expr) -> Option<u64> {
        use ay_bindings::ExprValue;
        // Check if expression is a 64-bit bitvec constant
        if let ExprValue::BitVecConst { value, width } = expr.value()
            && *width == 64
        {
            return u64::try_from(value).ok();
        }
        None
    }

    /// Extract i32 from a AY expression if it's a bitvec constant.
    ///
    /// BitVecConst stores values as unsigned BigInt in two's complement form.
    /// For negative i32 values like -1, the BigInt is 4294967295.
    /// We extract as u32 first, then reinterpret the bits as i32.
    fn extract_i32_from_expr(&self, expr: &Expr) -> Option<i32> {
        use ay_bindings::ExprValue;
        // Check if expression is a 32-bit bitvec constant
        if let ExprValue::BitVecConst { value, width } = expr.value()
            && *width == 32
        {
            // Extract as u32 first (BigInt stores unsigned value)
            // then reinterpret bits as i32 for signed semantics
            let unsigned = u32::try_from(value).ok()?;
            return Some(unsigned as i32);
        }
        None
    }

    /// Extract f32 bits from a ConstOperand.
    fn extract_f32_from_const_operand(&self, const_op: &ConstOperand) -> Option<u32> {
        let mir_const = &const_op.const_;
        let ty = mir_const.ty();

        // Verify it's actually an f32
        if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Float(rustc_public::ty::FloatTy::F32))) {
            return None;
        }

        let alloc = match mir_const.kind() {
            ConstantKind::Allocated(alloc) => alloc.clone(),
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_ty, alloc) => alloc.clone(),
                _ => return None, // external enum: TyConstKind
            },
            _ => return None, // external enum: ConstantKind
        };

        // Read the bytes and interpret as f32 bits
        // f32 is 4 bytes in little-endian
        let bytes = alloc.bytes;
        if bytes.len() < 4 {
            return None;
        }
        let mut arr = [0u8; 4];
        for (i, b) in bytes.iter().take(4).enumerate() {
            arr[i] = (*b)?;
        }
        Some(u32::from_le_bytes(arr))
    }

    /// Extract f64 bits from a ConstOperand.
    fn extract_f64_from_const_operand(&self, const_op: &ConstOperand) -> Option<u64> {
        let mir_const = &const_op.const_;
        let ty = mir_const.ty();

        // Verify it's actually an f64
        if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Float(rustc_public::ty::FloatTy::F64))) {
            return None;
        }

        let alloc = match mir_const.kind() {
            ConstantKind::Allocated(alloc) => alloc.clone(),
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_ty, alloc) => alloc.clone(),
                _ => return None, // external enum: TyConstKind
            },
            _ => return None, // external enum: ConstantKind
        };

        // Read the bytes and interpret as f64 bits
        // f64 is 8 bytes in little-endian
        let bytes = alloc.bytes;
        if bytes.len() < 8 {
            return None;
        }
        let mut arr = [0u8; 8];
        for (i, b) in bytes.iter().take(8).enumerate() {
            arr[i] = (*b)?;
        }
        Some(u64::from_le_bytes(arr))
    }
}
