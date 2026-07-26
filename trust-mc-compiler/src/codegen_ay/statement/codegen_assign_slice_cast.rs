// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Slice-cast assignment helpers.

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::{POINTER_WIDTH, bv8_sort, ptr_sort};
use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Construct a precise slice datatype for array-to-slice coercions (#1140).
    ///
    /// When casting `&[T; N]` to `&[T]`, build `Slice_T(fld_ptr, fld_len, fld_data)`.
    /// `fld_data` is included only when a tracked backing array proves the data identity.
    pub(super) fn try_construct_slice_datatype_from_cast(
        &mut self,
        operand: &Operand,
        target_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let src_ty = operand.ty(self.body.locals()).into_option()?;
        let len = Self::array_len_from_pointer_ty(src_ty)?;

        let pointee = match target_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => pointee,
            _ => return None,
        };
        let elem_sort = match pointee.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem)) => Self::infer_sort_from_ty(elem)?,
            TyKind::RigidTy(RigidTy::Str) => bv8_sort(),
            _ => return None,
        };

        let (operand_place, ref_base) = match operand {
            Operand::Copy(place) | Operand::Move(place) => (place, self.ssa_base_name(place)),
            Operand::Constant(_) => return None,
        };

        let ptr_expr = self.slice_cast_known_pointer_identity(&ref_base);

        let expected_data_sort = Sort::array(ptr_sort(), elem_sort.clone());
        let data = if let Some(pointee_base) = self
            .ref_pointees
            .get(ref_base.as_str())
            .cloned()
            .or_else(|| self.ensure_ref_pointee_for_place(operand_place))
        {
            self.slice_cast_backing_from_pointee_base(
                &ref_base,
                &pointee_base,
                &expected_data_sort,
            )?
        } else if let Some(data) = self.try_ref_pointee_from_env_value(&ref_base, operand_place) {
            if data.sort() == &expected_data_sort {
                data
            } else {
                self.ctx.unsupported_with_fallback(
                    "slice_cast_env_backing_sort_mismatch",
                    format!(
                        "ref_base={ref_base}, expected={expected_data_sort:?}, actual={:?}",
                        data.sort()
                    ),
                );
                return None;
            }
        } else {
            self.ctx.unsupported_with_fallback(
                "slice_cast_backing_untracked",
                format!("ref_base={ref_base}, target_ty={target_ty:?}"),
            );
            return None;
        };

        let slice_sort = Self::slice_sort(elem_sort);
        let sort_name = slice_sort.datatype_name().unwrap_or("Slice");
        let cons_name = crate::codegen_ay::names::resolve_ctor_name(&slice_sort, sort_name);
        Some(Expr::datatype_constructor(
            sort_name,
            cons_name,
            vec![ptr_expr, Expr::bitvec_const(len as i128, POINTER_WIDTH), data],
            slice_sort.clone(),
        ))
    }

    fn slice_cast_backing_from_pointee_base(
        &mut self,
        ref_base: &str,
        pointee_base: &str,
        expected_data_sort: &Sort,
    ) -> Option<Expr> {
        let Some(data) = self.env_lookup(pointee_base).cloned().or_else(|| {
            let pointee_var = format!("{pointee_base}_0");
            let sort_matches = self
                .ctx
                .program
                .get_sort(&pointee_var)
                .is_some_and(|sort| sort == expected_data_sort);
            if sort_matches {
                let data = self.ctx.declare_var(&pointee_var, expected_data_sort.clone());
                self.env_update(std::sync::Arc::<str>::from(pointee_base), data.clone());
                Some(data)
            } else {
                None
            }
        }) else {
            self.ctx.unsupported_with_fallback(
                "slice_cast_backing_missing",
                format!("ref_base={ref_base}, pointee_base={pointee_base}"),
            );
            return None;
        };
        if data.sort() != expected_data_sort {
            self.ctx.unsupported_with_fallback(
                "slice_cast_backing_sort_mismatch",
                format!(
                    "ref_base={ref_base}, pointee_base={pointee_base}, expected={expected_data_sort:?}, actual={:?}",
                    data.sort()
                ),
            );
            return None;
        }
        Some(data)
    }

    fn slice_cast_known_pointer_identity(&mut self, ref_base: &str) -> Expr {
        if let Some(env_expr) = self.env_lookup(ref_base)
            && env_expr.sort() == &ptr_sort()
        {
            return env_expr.clone();
        }

        if let Some(addr) = self.addr_symbols.get(ref_base) {
            return addr.clone();
        }

        let addr_name = crate::codegen_ay::names::addr_name(ref_base);
        let addr = self.ctx.declare_var(&addr_name, ptr_sort());
        self.ctx.assert(addr.clone().ne(Expr::bitvec_const(0u128, POINTER_WIDTH)));
        self.addr_symbols.insert(std::sync::Arc::from(ref_base), addr.clone());
        addr
    }
}
