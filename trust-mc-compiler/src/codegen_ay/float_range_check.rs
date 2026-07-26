// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Float-to-int range checking helpers shared between BMC and CHC codegen.
//!
//! Part of #3840: concrete fast path for `kani::float::float_to_int_in_range`.
//! Split from `float_arithmetic.rs` per 500-line file limit.

use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};

/// Evaluate whether a concrete float value (after truncation) fits in a target
/// integer range. Returns `Some(true/false)` when the float mantissa can exactly
/// represent all values of the target width, `None` otherwise.
///
/// Part of #3840: shared between BMC (`kani_float.rs`) and CHC (`codegen_call_kani.rs`).
///
/// - `value_f64`: the float value (upcast to f64 if originally f32)
/// - `mantissa_bits`: 24 for f32, 53 for f64
/// - `target_width`: integer bit width (e.g. 8 for i8, 16 for u16)
/// - `signed`: true for signed integer target
pub(in crate::codegen_ay) fn eval_float_in_int_range(
    value_f64: f64,
    mantissa_bits: u32,
    target_width: u32,
    signed: bool,
) -> Option<bool> {
    // Only handle widths exactly representable by the source float.
    if target_width > mantissa_bits {
        return None;
    }
    if !value_f64.is_finite() {
        return Some(false);
    }
    let truncated = value_f64.trunc();
    let in_range = if signed {
        let min = -(1_i128 << (target_width - 1));
        let max = (1_i128 << (target_width - 1)) - 1;
        truncated >= min as f64 && truncated <= max as f64
    } else {
        let max = (1_u128 << target_width) - 1;
        truncated >= 0.0 && truncated <= max as f64
    };
    Some(in_range)
}

/// Extract a concrete f64 value and mantissa bits from a MIR `Operand::Constant`.
/// Returns `(value_f64, mantissa_bits)` or `None` for non-constant/non-float operands.
///
/// Part of #3840: used by CHC path for float_to_int_in_range concrete evaluation.
pub(in crate::codegen_ay) fn extract_const_float(
    operand: &Operand,
    float_ty: &rustc_public::ty::Ty,
) -> Option<(f64, u32)> {
    use rustc_public::ty::TyConstKind;

    let const_op = match operand {
        Operand::Constant(c) => c,
        _ => return None, // Copy/Move — not a literal constant in MIR
    };

    let mir_const = &const_op.const_;
    let alloc = match mir_const.kind() {
        rustc_public::ty::ConstantKind::Allocated(alloc) => alloc.clone(),
        rustc_public::ty::ConstantKind::Ty(ty_const) => match ty_const.kind() {
            TyConstKind::Value(_ty, alloc) => alloc.clone(),
            _ => return None,
        },
        _ => return None,
    };

    match float_ty.kind() {
        TyKind::RigidTy(RigidTy::Float(rustc_public::ty::FloatTy::F32)) => {
            if alloc.bytes.len() < 4 {
                return None;
            }
            let mut arr = [0u8; 4];
            for (i, b) in alloc.bytes.iter().take(4).enumerate() {
                arr[i] = (*b)?;
            }
            let bits = u32::from_le_bytes(arr);
            Some((f32::from_bits(bits) as f64, 24))
        }
        TyKind::RigidTy(RigidTy::Float(rustc_public::ty::FloatTy::F64)) => {
            if alloc.bytes.len() < 8 {
                return None;
            }
            let mut arr = [0u8; 8];
            for (i, b) in alloc.bytes.iter().take(8).enumerate() {
                arr[i] = (*b)?;
            }
            let bits = u64::from_le_bytes(arr);
            Some((f64::from_bits(bits), 53))
        }
        _ => None,
    }
}

/// Trace a Move/Copy operand back to its defining MIR assignment to find a
/// constant float value. Scans basic blocks for `_N = const <float>`.
///
/// Part of #3840: MIR typically assigns `let f: f32 = 5.6;` to a local before
/// passing it as `Move(_N)` to `float_to_int_in_range`. This function resolves
/// the indirection so the concrete fast path works for typical Rust patterns.
pub(in crate::codegen_ay) fn trace_local_const_float(
    blocks: &[rustc_public::mir::BasicBlock],
    operand: &Operand,
    float_ty: &rustc_public::ty::Ty,
) -> Option<(f64, u32)> {
    use rustc_public::mir::{Rvalue, StatementKind};

    let local_idx = match operand {
        Operand::Move(place) | Operand::Copy(place) if place.projection.is_empty() => place.local,
        _ => return None,
    };

    for bb in blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                if place.local == local_idx && place.projection.is_empty() {
                    if let Rvalue::Use(rhs_operand) = rvalue {
                        return extract_const_float(rhs_operand, float_ty);
                    }
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_f32_5_6_fits_in_u16() {
        assert_eq!(eval_float_in_int_range(5.6, 24, 16, false), Some(true));
    }

    #[test]
    fn test_f32_145_7_does_not_fit_in_i8() {
        assert_eq!(eval_float_in_int_range(145.7, 24, 8, true), Some(false));
    }

    #[test]
    fn test_f64_1e6_fits_in_u32() {
        assert_eq!(eval_float_in_int_range(1e6, 53, 32, false), Some(true));
    }

    #[test]
    fn test_nan_is_out_of_range() {
        assert_eq!(eval_float_in_int_range(f64::NAN, 53, 32, false), Some(false));
    }

    #[test]
    fn test_inf_is_out_of_range() {
        assert_eq!(eval_float_in_int_range(f64::INFINITY, 53, 32, false), Some(false));
    }

    #[test]
    fn test_wide_target_returns_none() {
        // f32 mantissa (24) can't represent all u32 values (32 bits)
        assert_eq!(eval_float_in_int_range(5.0, 24, 32, false), None);
    }

    #[test]
    fn test_neg_value_out_of_unsigned_range() {
        assert_eq!(eval_float_in_int_range(-1.0, 53, 16, false), Some(false));
    }

    #[test]
    fn test_i8_boundary_max() {
        assert_eq!(eval_float_in_int_range(127.0, 24, 8, true), Some(true));
    }

    #[test]
    fn test_i8_boundary_min() {
        assert_eq!(eval_float_in_int_range(-128.0, 24, 8, true), Some(true));
    }

    #[test]
    fn test_i8_boundary_overflow() {
        assert_eq!(eval_float_in_int_range(128.0, 24, 8, true), Some(false));
    }
}
