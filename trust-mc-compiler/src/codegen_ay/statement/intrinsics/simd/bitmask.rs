// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD bitmask: BMC parity for KaniModel::SimdBitmask.
//!
//! Part of #3912. Split from access.rs per file size limit.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Place};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::debug;

use super::IntoOption;
use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::types::{int_ty_to_bitvec_width, uint_ty_to_bitvec_width};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen KaniModel::SimdBitmask: extract lane nonzero-ness into a bitmask integer.
    /// BMC parity for the CHC encoding in codegen_call_kani_model.rs.
    ///
    /// The model signature is `simd_bitmask<T, U, E, const LANES: usize>(input: T) -> U`
    /// where T is the SIMD struct, U is the mask integer (u8/u16/etc.),
    /// E is the element type, and LANES is the lane count.
    ///
    /// For each lane i, if element[i] != 0 then bit i of the result is set.
    pub(in crate::codegen_ay::statement) fn codegen_simd_bitmask_model(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
    ) {
        // Extract LANES from the 4th generic arg (index 3).
        let lanes = (|| -> Option<usize> {
            let func_ty = func.ty(self.body.locals()).into_option()?;
            let (_fn_def, fn_args) = match func_ty.kind() {
                TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
                _ => return None,
            };
            if let Some(GenericArgKind::Const(len_const)) = fn_args.0.get(3).cloned() {
                len_const.eval_target_usize().into_option().map(|v| v as usize)
            } else {
                None
            }
        })();

        let Some(lanes) = lanes else {
            debug!("codegen_simd_bitmask_model: cannot extract LANES");
            return;
        };

        if args.is_empty() {
            debug!("codegen_simd_bitmask_model: no args");
            return;
        }

        let Some(simd_ty) = args[0].ty(self.body.locals()).into_option() else {
            debug!("codegen_simd_bitmask_model: cannot get SIMD type");
            return;
        };
        let Some(layout) = self.simd_layout(simd_ty) else {
            debug!("codegen_simd_bitmask_model: cannot infer SIMD layout");
            return;
        };
        let Some(simd_expr) = self.codegen_operand(&args[0]) else {
            debug!("codegen_simd_bitmask_model: cannot codegen SIMD operand");
            return;
        };
        let Some(elements) = self.simd_extract_elements(&simd_expr, &layout) else {
            debug!("codegen_simd_bitmask_model: cannot extract SIMD elements");
            return;
        };

        // Determine mask width from destination type.
        let Some(dest_ty) = destination.ty(self.body.locals()).into_option() else {
            debug!("codegen_simd_bitmask_model: cannot get dest type");
            return;
        };
        let mask_width = match dest_ty.kind() {
            TyKind::RigidTy(RigidTy::Uint(k)) => uint_ty_to_bitvec_width(k),
            TyKind::RigidTy(RigidTy::Int(k)) => int_ty_to_bitvec_width(k),
            _ => {
                debug!("codegen_simd_bitmask_model: dest is not integer type");
                return;
            }
        };

        let Some(elem_width) = layout.elem_width() else {
            debug!("codegen_simd_bitmask_model: cannot get element width");
            return;
        };

        // Build bitmask: mask = OR_i ite(elem_i != 0, 1 << i, 0)
        let zero_elem = Expr::bitvec_const(0u64, elem_width);
        let mut mask_expr = Expr::bitvec_const(0u64, mask_width);

        for i in 0..lanes.min(mask_width as usize) {
            if i >= elements.len() {
                break;
            }
            let lane_set = elements[i].clone().ne(zero_elem.clone());
            let bit = Expr::ite(
                lane_set,
                Expr::bitvec_const(1u128 << i, mask_width),
                Expr::bitvec_const(0u64, mask_width),
            );
            mask_expr = mask_expr.bvor(bit);
        }

        self.bind_ssa_result(destination, mask_expr);
        debug!("codegen_simd_bitmask_model: encoded {} lanes into {}-bit mask", lanes, mask_width);
    }
}
