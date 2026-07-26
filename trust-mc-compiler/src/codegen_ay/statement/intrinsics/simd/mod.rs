// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD intrinsics for AY codegen.
//!
//! This module implements Rust SIMD intrinsics:
//! - Bitwise: simd_and, simd_or, simd_xor
//! - Shifts: simd_shl, simd_shr
//! - Arithmetic: simd_add, simd_sub, simd_mul, simd_div, simd_rem
//! - Comparison: simd_eq, simd_ne, simd_lt, simd_le, simd_gt, simd_ge
//! - Reductions: simd_reduce_add, simd_reduce_mul, simd_reduce_and, etc.
//! - Element access: simd_extract, simd_insert, simd_shuffle, simd_cast
//!
//! SIMD vectors in Rust are #[repr(simd)] types containing arrays.
//! In SMT, they're modeled as datatypes containing SMT arrays.
//! Element access uses array select/store operations.
//!
//! Part of #1415, #1348, #1478, #1501.
//!
//! Extracted from intrinsics.rs per #1735.
//! Split into submodules per #2150.

mod access;
mod bitmask;
mod ops;
mod reduce;

use crate::codegen_ay::names::struct_sort;
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::ty::{RigidTy, TyKind};

use super::IntoOption;
use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::types::{
    POINTER_WIDTH, float_ty_to_bitvec_width, int_ty_to_bitvec_width, ptr_sort,
    uint_ty_to_bitvec_width,
};

#[derive(Clone, Debug)]
pub(in crate::codegen_ay::statement) enum SimdLayout {
    Array { elem_sort: Sort, len: usize, field_name: String },
    MultiField { elem_sort: Sort, field_names: Vec<String> },
}

impl SimdLayout {
    /// Get the number of lanes in this SIMD layout.
    pub(in crate::codegen_ay::statement) fn lane_count(&self) -> usize {
        match self {
            SimdLayout::Array { len, .. } => *len,
            SimdLayout::MultiField { field_names, .. } => field_names.len(),
        }
    }

    /// Get the element bit width for this SIMD layout.
    pub(in crate::codegen_ay::statement) fn elem_width(&self) -> Option<u32> {
        match self {
            SimdLayout::Array { elem_sort, .. } => elem_sort.bitvec_width(),
            SimdLayout::MultiField { elem_sort, .. } => elem_sort.bitvec_width(),
        }
    }
}

/// SIMD arithmetic operation types (Part of #1478).
#[derive(Clone, Copy, Debug)]
pub(in crate::codegen_ay::statement) enum SimdArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

/// SIMD comparison operation types (Part of #1478).
#[derive(Clone, Copy, Debug)]
pub(in crate::codegen_ay::statement) enum SimdCmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// SIMD reduce operation types (Part of #1478).
#[derive(Clone, Copy, Debug)]
pub(in crate::codegen_ay::statement) enum SimdReduceOp {
    Add,
    Mul,
    And,
    Or,
    Xor,
    Min,
    Max,
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    // ========================================================================
    // SIMD Infrastructure (Part of #1415, #1348)
    // ========================================================================
    // SIMD vectors in Rust are #[repr(simd)] types containing arrays.
    // In SMT, they're modeled as datatypes containing SMT arrays.
    // Element access uses array select/store operations.
    // ========================================================================

    /// Infer SIMD layout from the type.
    ///
    /// Handles:
    /// - Array-based SIMD: single field that is an array
    /// - Multi-field SIMD: multiple fields (tuple struct)
    pub(in crate::codegen_ay::statement) fn simd_layout(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Option<SimdLayout> {
        let TyKind::RigidTy(RigidTy::Adt(adt_def, args)) = ty.kind() else {
            return None;
        };
        let variants = adt_def.variants();
        if variants.len() != 1 || variants[0].fields().is_empty() {
            return None;
        }
        let fields = variants[0].fields();

        if fields.len() == 1 {
            let field = &fields[0];
            let field_ty = field.ty_with_args(&args);
            if let TyKind::RigidTy(RigidTy::Array(elem_ty, len_const)) = field_ty.kind() {
                let len = len_const.eval_target_usize().into_option()? as usize;
                let elem_sort = Self::infer_simd_sort_from_ty(elem_ty)?;
                let field_name = crate::codegen_ay::names::adt_struct_field_name(&field.name);
                return Some(SimdLayout::Array { elem_sort, len, field_name });
            }
        }

        let mut field_names = Vec::with_capacity(fields.len());
        let mut elem_sort: Option<Sort> = None;
        for field in fields {
            let field_ty = field.ty_with_args(&args);
            let field_sort = Self::infer_simd_sort_from_ty(field_ty)?;
            if let Some(existing) = &elem_sort {
                if *existing != field_sort {
                    return None;
                }
            } else {
                elem_sort = Some(field_sort.clone());
            }
            field_names.push(crate::codegen_ay::names::adt_struct_field_name(&field.name));
        }

        Some(SimdLayout::MultiField { elem_sort: elem_sort?, field_names })
    }

    /// Infer sort from Rust type for SIMD elements.
    fn infer_simd_sort_from_ty(ty: rustc_public::ty::Ty) -> Option<Sort> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Int(k)) => Some(Sort::bitvec(int_ty_to_bitvec_width(k))),
            TyKind::RigidTy(RigidTy::Uint(k)) => Some(Sort::bitvec(uint_ty_to_bitvec_width(k))),
            TyKind::RigidTy(RigidTy::Float(k)) => Some(Sort::bitvec(float_ty_to_bitvec_width(k))),
            _ => None, // external enum: TyKind
        }
    }

    /// Extract elements from a SIMD expression based on its layout.
    pub(in crate::codegen_ay::statement) fn simd_extract_elements(
        &self,
        simd_expr: &Expr,
        layout: &SimdLayout,
    ) -> Option<Vec<Expr>> {
        match layout {
            SimdLayout::Array { elem_sort, len, field_name } => {
                let array_expr = if simd_expr.sort().is_array() {
                    simd_expr.clone()
                } else {
                    let dt_name = simd_expr.sort().datatype_name()?;
                    let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
                    simd_expr.clone().field_select(dt_name, field_name, array_sort)
                };
                let elements = (0..*len)
                    .map(|i| {
                        let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        array_expr.clone().select(idx)
                    })
                    .collect();
                Some(elements)
            }
            SimdLayout::MultiField { elem_sort, field_names } => {
                let dt_name = simd_expr.sort().datatype_name()?;
                let elements = field_names
                    .iter()
                    .map(|field| simd_expr.clone().field_select(dt_name, field, elem_sort.clone()))
                    .collect();
                Some(elements)
            }
        }
    }

    /// Construct a SIMD expression from elements based on its layout.
    pub(in crate::codegen_ay::statement) fn simd_construct_expr(
        &mut self,
        elements: Vec<Expr>,
        layout: &SimdLayout,
        simd_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let TyKind::RigidTy(RigidTy::Adt(adt_def, _)) = simd_ty.kind() else {
            return None;
        };
        let adt_name = adt_def.name();
        let cons_name = crate::codegen_ay::names::cons_name(&adt_name);

        match layout {
            SimdLayout::Array { elem_sort, len, field_name } => {
                if elements.len() != *len {
                    return None;
                }
                let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
                let base_name = self.ctx.fresh_name("simd_arr");
                let mut array_expr = self.ctx.declare_var(&base_name, array_sort.clone());
                for (i, elem) in elements.into_iter().enumerate() {
                    let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                    array_expr = array_expr.store(idx, elem);
                }
                let simd_sort = struct_sort(&adt_name, [(field_name.clone(), array_sort)]);
                Some(Expr::datatype_constructor(adt_name, cons_name, vec![array_expr], simd_sort))
            }
            SimdLayout::MultiField { elem_sort, field_names } => {
                if elements.len() != field_names.len() {
                    return None;
                }
                let simd_sort = struct_sort(
                    &adt_name,
                    field_names.iter().map(|name| (name.clone(), elem_sort.clone())),
                );
                Some(Expr::datatype_constructor(adt_name, cons_name, elements, simd_sort))
            }
        }
    }

    /// Check if SIMD element type is signed.
    pub(in crate::codegen_ay::statement) fn simd_element_is_signed(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> bool {
        let TyKind::RigidTy(RigidTy::Adt(adt_def, args)) = ty.kind() else {
            return false;
        };
        let variants = adt_def.variants();
        if variants.len() != 1 || variants[0].fields().is_empty() {
            return false;
        }
        let field = &variants[0].fields()[0];
        let field_ty = field.ty_with_args(&args);
        match field_ty.kind() {
            TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => {
                matches!(elem_ty.kind(), TyKind::RigidTy(RigidTy::Int(_)))
            }
            _ => matches!(field_ty.kind(), TyKind::RigidTy(RigidTy::Int(_))), // external enum: TyKind
        }
    }

    /// Check if SIMD element type is a float (f16/f32/f64/f128). Part of #3857.
    pub(in crate::codegen_ay::statement) fn simd_element_is_float(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> bool {
        let TyKind::RigidTy(RigidTy::Adt(adt_def, args)) = ty.kind() else {
            return false;
        };
        let variants = adt_def.variants();
        if variants.len() != 1 || variants[0].fields().is_empty() {
            return false;
        }
        let field = &variants[0].fields()[0];
        let field_ty = field.ty_with_args(&args);
        match field_ty.kind() {
            TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => {
                matches!(elem_ty.kind(), TyKind::RigidTy(RigidTy::Float(_)))
            }
            _ => matches!(field_ty.kind(), TyKind::RigidTy(RigidTy::Float(_))),
        }
    }
}
