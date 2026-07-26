// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Vec field extraction and sort inference helpers.
//!
//! Extracted from vec.rs per #4206 (500 LOC threshold).

use crate::codegen_ay::types::{CtorFieldExt, ptr_sort};
use ay_bindings::{Expr, Sort, SortInner};
use rustc_public::CrateDef;
use rustc_public::mir::Place;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

use std::sync::atomic::{AtomicU64, Ordering};

use super::super::{IntoOption, StatementCodegen};

/// Counter for Vec fallback names when vec_field_select encounters non-datatype sorts.
/// Hoisted from function-local static for session reset support (Part of #2360).
pub(super) static VEC_FIELD_FALLBACK_COUNTER: AtomicU64 = AtomicU64::new(0);

/// All four Vec datatype fields extracted in a single pass. Part of #2267.
pub(super) struct VecFields {
    pub(super) dt_name: String,
    pub(super) ctor_name: String,
    pub(super) sort: Sort,
    pub(super) ptr: Expr,
    pub(super) len: Expr,
    pub(super) cap: Expr,
    pub(super) data: Expr,
}

/// Reset the Vec field fallback counter, returning the previous value (Part of #2360).
pub(in crate::codegen_ay) fn take_vec_field_fallback_counter() -> u64 {
    VEC_FIELD_FALLBACK_COUNTER.swap(0, Ordering::Relaxed)
}

/// Non-destructive read of the Vec field fallback counter (Part of #3080).
pub(in crate::codegen_ay) fn get_vec_field_fallback_count() -> u64 {
    VEC_FIELD_FALLBACK_COUNTER.load(Ordering::Relaxed)
}

/// Set Vec field fallback counter for test isolation (Part of #3369).
#[cfg(test)]
#[allow(dead_code)]
pub(in crate::codegen_ay) fn set_vec_field_fallback_count_for_test(count: u64) {
    VEC_FIELD_FALLBACK_COUNTER.store(count, Ordering::Relaxed);
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Infer Vec element sort from destination type.
    ///
    /// Extracts the element type from `Vec<T>` and converts to AY Sort.
    #[must_use]
    pub(in super::super) fn infer_vec_elem_sort(&self, destination: &Place) -> Option<Sort> {
        let dest_ty = destination.ty(self.body.locals()).into_option()?;

        // Handle references: &Vec<T> or &mut Vec<T>
        let inner_ty = match dest_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
            _ => dest_ty, // external enum: TyKind
        };

        // Extract T from Vec<T> or alloc::vec::Vec<T>
        let TyKind::RigidTy(RigidTy::Adt(adt_def, args)) = inner_ty.kind() else {
            return None;
        };

        // Check if it's a Vec
        let name = adt_def.name();
        if !name.ends_with("Vec") {
            return None;
        }

        // Get the first generic argument (element type)
        let elem_ty = args.0.first().and_then(|arg| match arg {
            GenericArgKind::Type(ty) => Some(*ty),
            _ => None, // external enum: GenericArgKind
        })?;

        Self::infer_sort_from_ty(elem_ty)
    }

    /// Extract all Vec fields in one pass. Returns `None` for non-datatype exprs.
    #[must_use]
    pub(super) fn extract_all_vec_fields(vec: &Expr) -> Option<VecFields> {
        let sort = vec.sort().clone();
        let dt = sort.datatype_sort()?;
        let dt_name = dt.name.clone();
        let ctor = dt.constructors.first()?;
        let ctor_name = ctor.name.clone();
        let fsort =
            |name: &str, default: Sort| -> Sort { ctor.field_sort(name).unwrap_or(default) };
        let bv = || ptr_sort();
        let ptr = vec.clone().field_select(&dt_name, "fld_ptr", fsort("fld_ptr", bv()));
        let len = vec.clone().field_select(&dt_name, "fld_len", fsort("fld_len", bv()));
        let cap = vec.clone().field_select(&dt_name, "fld_cap", fsort("fld_cap", bv()));
        let data_default = Sort::array(bv(), ptr_sort());
        let data = vec.clone().field_select(&dt_name, "fld_data", fsort("fld_data", data_default));
        Some(VecFields { dt_name, ctor_name, sort, ptr, len, cap, data })
    }

    /// Extract a field from a Vec expression using the correct datatype name.
    /// Part of #1632: Helper for typed Vec names (Vec_bv32, Vec_Int, etc.)
    #[must_use]
    pub(in crate::codegen_ay::statement) fn vec_field_select(
        vec: &Expr,
        field_name: &str,
        field_sort: Sort,
    ) -> Expr {
        // Guard: env lookup can return a primitive instead of Vec datatype.
        if !vec.sort().is_datatype() {
            let id = VEC_FIELD_FALLBACK_COUNTER.fetch_add(1, Ordering::Relaxed);
            tracing::warn!(
                "vec_field_select: non-datatype sort {:?}, symbolic {} fallback #{}",
                vec.sort(),
                field_name,
                id
            );
            return Expr::var(
                {
                    use std::fmt::Write;
                    let mut s = String::with_capacity(4 + field_name.len() + 12);
                    s.push_str("vec_");
                    s.push_str(field_name);
                    s.push_str("_fallback_");
                    let _ = write!(s, "{id}");
                    s
                },
                field_sort,
            );
        }
        let sort_ref = vec.sort().clone();
        let dt_name = sort_ref.datatype_sort().map_or("Vec", |dt| &*dt.name);
        vec.clone().field_select(dt_name, field_name, field_sort)
    }

    #[must_use]
    pub(in crate::codegen_ay::statement) fn vec_field_select_declared(
        &mut self,
        vec: &Expr,
        field_name: &str,
        field_sort: Sort,
    ) -> Expr {
        let expr = Self::vec_field_select(vec, field_name, field_sort);
        self.declare_fresh_fallback_var_if_needed(&expr);
        expr
    }

    /// Extract the data array from a Vec expression.
    ///
    /// Returns the fld_data field if present, otherwise creates a symbolic array.
    /// Part of #1632: Updated to handle typed Vec names (Vec_bv32, Vec_Int, etc.)
    #[must_use]
    pub(in super::super) fn extract_vec_data(&mut self, vec: &Expr) -> Expr {
        let sort = vec.sort().clone();
        if let SortInner::Datatype(dt) = sort.inner()
            && let Some(field) = dt.constructors.first().and_then(|ctor| ctor.field("fld_data"))
        {
            return vec.clone().field_select(&*dt.name, "fld_data", field.sort.clone());
        }

        // Fallback: create a symbolic array with bitvec(POINTER_WIDTH) elements
        // This fallback handles legacy Vec without fld_data or erased types
        let name = self.ctx.fresh_name("vec_data");
        let array_sort = Sort::array(ptr_sort(), ptr_sort());
        self.ctx.declare_var(&name, array_sort)
    }
}
