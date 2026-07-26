// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Dedicated PointerCoercion::Unsize cast path for boxed dyn targets.
//!
//! Part of #3793: Box<T> → Box<dyn Trait> unsize coercion requires a wrapper-walk
//! path that constructs the fat-pointer leaf first, then rebuilds outer wrappers.
//! The generic `coerce_datatype_structural` cannot handle field-count mismatches
//! (thin → fat pointer) so this module provides a dedicated path.
//!
//! Design: `designs/2026-03-14-issue-3793-box-dyn-unsize-cast-fat-pointer.md`

// W5:3963 wired into codegen_cast_with_kind (Part of #3848/#3793).

use ay_bindings::{Expr, Sort, SortInner};

use super::StatementCodegen;
use crate::codegen_ay::types::{
    POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, construct_dyn_fat_pointer,
};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Attempt to encode a `PointerCoercion::Unsize` cast.
    ///
    /// Handles wrapper-walked paths like `Box<Concrete> → Box<dyn Trait>` by:
    /// 1. Walking matching outer wrapper layers (same constructor, same field count)
    /// 2. Finding the differing leaf field
    /// 3. Constructing a Dyn fat pointer at the leaf via `construct_dyn_fat_pointer`
    /// 4. Rebuilding the wrapper chain outward
    ///
    /// Returns `None` if the cast is not a recognized unsize pattern, allowing
    /// fallback to `codegen_cast`.
    pub(super) fn codegen_unsize_cast(
        &mut self,
        operand: &super::Operand,
        src_ty: Option<rustc_public::ty::Ty>,
        target_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let target_sort = Self::infer_sort_from_ty(target_ty)?;
        let expr = self.codegen_operand(operand)?;
        let src_sort = expr.sort().clone();

        // Only handle DT → DT where structural coercion would fail.
        let (SortInner::Datatype(src_dt), SortInner::Datatype(tgt_dt)) =
            (src_sort.inner(), target_sort.inner())
        else {
            // BV → DT unsize (thin pointer → fat pointer wrapper).
            if let SortInner::BitVec(_) = src_sort.inner() {
                if let SortInner::Datatype(tgt_dt) = target_sort.inner() {
                    if tgt_dt.name.starts_with("Dyn_") {
                        // Direct BV → Dyn_Trait: construct fat pointer.
                        let vtable_dummy = self.resolve_vtable_value_for_unsize(src_ty);
                        return construct_dyn_fat_pointer(
                            expr,
                            tgt_dt,
                            target_sort.clone(),
                            vtable_dummy,
                        );
                    }
                    // BV → wrapper DT (e.g. Box<dyn Trait>): wrap thin ptr in
                    // wrapper chain with fat pointer at the Dyn leaf.
                    let vtable_val = self.resolve_vtable_value_for_unsize(src_ty);
                    return self.wrap_thin_ptr_in_target(expr, tgt_dt, &target_sort, vtable_val);
                }
            }
            return None;
        };

        // Same sort name → no coercion needed.
        if src_dt.name == tgt_dt.name {
            return Some(expr);
        }

        // Walk wrapper layers to find the differing leaf.
        self.walk_unsize_wrappers(expr, src_dt, tgt_dt, &target_sort, src_ty)
    }

    /// Walk matching wrapper layers, find the differing leaf, construct fat pointer,
    /// and rebuild the wrapper chain.
    fn walk_unsize_wrappers(
        &mut self,
        expr: Expr,
        src_dt: &ay_bindings::DatatypeSort,
        tgt_dt: &ay_bindings::DatatypeSort,
        tgt_sort: &Sort,
        src_ty: Option<rustc_public::ty::Ty>,
    ) -> Option<Expr> {
        // Both must be single-constructor.
        if src_dt.constructors.len() != 1 || tgt_dt.constructors.len() != 1 {
            return None;
        }
        let src_ctor = src_dt.constructors.first()?;
        let tgt_ctor = tgt_dt.constructors.first()?;

        // If field counts match, try field-by-field with recursive unsize on mismatches.
        if src_ctor.fields.len() == tgt_ctor.fields.len() {
            return self.coerce_fields_with_unsize(
                expr, src_dt, src_ctor, tgt_dt, tgt_ctor, tgt_sort, src_ty,
            );
        }

        // Field count mismatch: source is thin wrapper, target is fat wrapper.
        // Try to extract a thin pointer from source and build fat pointer target.
        if tgt_dt.name.starts_with("Dyn_") {
            let thin_ptr = self.extract_thin_pointer(&expr, src_dt)?;
            let vtable_val = self.resolve_vtable_value_for_unsize(src_ty);
            return construct_dyn_fat_pointer(thin_ptr, tgt_dt, tgt_sort.clone(), vtable_val);
        }

        // `Vec<T> -> [T]` (and `[T; N] -> [T]`) unsize: the source struct is a
        // SUPERSET of the target's fields (`Vec{fld_ptr,fld_len,fld_cap,fld_data}`
        // -> `Slice{fld_ptr,fld_len,fld_data}`). Map the target's fields by NAME,
        // dropping the extra source field(s) (e.g. `fld_cap`). This THREADS the
        // CONCRETE `vec![..]` length (`Vec::fld_len`) into the slice's `fld_len`
        // instead of synthesising a fresh symbolic metadata length — required so
        // `resolve_iter_concrete_range` can bound-unroll a `slice.iter()`. Sound:
        // each target field is an exact projection of the same-named source field;
        // fails closed (returns None) on any missing/incompatible field.
        if src_ctor.fields.len() > tgt_ctor.fields.len()
            && let Some(coerced) =
                self.coerce_fields_by_name(&expr, src_dt, src_ctor, tgt_dt, tgt_ctor, tgt_sort)
        {
            return Some(coerced);
        }

        // Target is a wrapper (e.g. Box) that contains a Dyn field.
        // Find the first field in src that differs from tgt and recurse.
        if src_ctor.fields.len() < tgt_ctor.fields.len() {
            // Source has fewer fields — try extracting a pointer and wrapping.
            // Common case: Box<T> has 1 field (Unique<T>), Box<dyn Trait> has 1 field (Unique<dyn>)
            // but the inner Unique field itself differs.
            return None;
        }

        None
    }

    /// Coerce matching-arity constructor fields, using recursive unsize for mismatched fields.
    fn coerce_fields_with_unsize(
        &mut self,
        expr: Expr,
        src_dt: &ay_bindings::DatatypeSort,
        src_ctor: &ay_bindings::DatatypeConstructor,
        tgt_dt: &ay_bindings::DatatypeSort,
        tgt_ctor: &ay_bindings::DatatypeConstructor,
        tgt_sort: &Sort,
        src_ty: Option<rustc_public::ty::Ty>,
    ) -> Option<Expr> {
        let mut field_exprs = Vec::with_capacity(src_ctor.fields.len());
        for (sf, tf) in src_ctor.fields.iter().zip(tgt_ctor.fields.iter()) {
            let extracted = expr.clone().field_select(&*src_dt.name, &*sf.name, sf.sort.clone());
            if sf.sort == tf.sort {
                field_exprs.push(extracted);
            } else if let (SortInner::BitVec(sb), SortInner::BitVec(tb)) =
                (sf.sort.inner(), tf.sort.inner())
            {
                let _ = sb;
                field_exprs.push(coerce_bitvec_width_safe(
                    extracted,
                    tb.width,
                    SignExtension::ZeroExtend,
                ));
            } else if let (SortInner::Datatype(inner_src), SortInner::Datatype(inner_tgt)) =
                (sf.sort.inner(), tf.sort.inner())
            {
                // Recurse into nested wrapper (e.g., Unique<T> → Unique<dyn Trait>).
                if let Some(coerced) =
                    self.walk_unsize_wrappers(extracted, inner_src, inner_tgt, &tf.sort, src_ty)
                {
                    field_exprs.push(coerced);
                } else {
                    return None;
                }
            } else if let SortInner::BitVec(_) = sf.sort.inner() {
                // Source is BV, target is DT (thin ptr → fat ptr at leaf).
                if let SortInner::Datatype(inner_tgt) = tf.sort.inner() {
                    if inner_tgt.name.starts_with("Dyn_") {
                        let vtable_val = self.resolve_vtable_value_for_unsize(src_ty);
                        if let Some(fat) = construct_dyn_fat_pointer(
                            extracted,
                            inner_tgt,
                            tf.sort.clone(),
                            vtable_val,
                        ) {
                            field_exprs.push(fat);
                            continue;
                        }
                    }
                }
                return None;
            } else {
                return None;
            }
        }
        Some(Expr::datatype_constructor(
            &tgt_dt.name,
            &tgt_ctor.name,
            field_exprs,
            tgt_sort.clone(),
        ))
    }

    /// Map each TARGET field from the SAME-NAMED source field (a structural
    /// projection), dropping unmatched source fields. Used for the `Vec<T> -> [T]`
    /// unsize where the slice's `{fld_ptr,fld_len,fld_data}` is a subset of the
    /// Vec's `{fld_ptr,fld_len,fld_cap,fld_data}`. Crucially copies the source's
    /// CONCRETE `fld_len` rather than a fresh symbol. Fails closed on any missing
    /// or sort-incompatible field.
    fn coerce_fields_by_name(
        &mut self,
        expr: &Expr,
        src_dt: &ay_bindings::DatatypeSort,
        src_ctor: &ay_bindings::DatatypeConstructor,
        tgt_dt: &ay_bindings::DatatypeSort,
        tgt_ctor: &ay_bindings::DatatypeConstructor,
        tgt_sort: &Sort,
    ) -> Option<Expr> {
        let mut field_exprs = Vec::with_capacity(tgt_ctor.fields.len());
        for tf in &tgt_ctor.fields {
            let sf = src_ctor.fields.iter().find(|f| f.name == tf.name)?;
            let extracted = expr.clone().field_select(&*src_dt.name, &*sf.name, sf.sort.clone());
            if sf.sort == tf.sort {
                field_exprs.push(extracted);
            } else if let (SortInner::BitVec(_), SortInner::BitVec(tb)) =
                (sf.sort.inner(), tf.sort.inner())
            {
                field_exprs.push(coerce_bitvec_width_safe(
                    extracted,
                    tb.width,
                    SignExtension::ZeroExtend,
                ));
            } else {
                return None;
            }
        }
        Some(Expr::datatype_constructor(
            &tgt_dt.name,
            &tgt_ctor.name,
            field_exprs,
            tgt_sort.clone(),
        ))
    }

    /// Extract a thin pointer (BV) from a datatype expression.
    /// Unwraps single-field wrappers recursively until a BV is found.
    fn extract_thin_pointer(&self, expr: &Expr, dt: &ay_bindings::DatatypeSort) -> Option<Expr> {
        if dt.constructors.len() != 1 {
            return None;
        }
        let ctor = dt.constructors.first()?;
        let field = ctor.fields.first()?;
        let extracted = expr.clone().field_select(&*dt.name, &*field.name, field.sort.clone());

        match extracted.sort().inner() {
            SortInner::BitVec(_) => Some(extracted),
            SortInner::Datatype(inner_dt) => self.extract_thin_pointer(&extracted, inner_dt),
            _ => None,
        }
    }

    /// Wrap a thin BV pointer in a target wrapper DT chain, placing a fat pointer
    /// at the innermost `Dyn_*` leaf.
    ///
    /// Handles `BV → Box<dyn Trait>` where Box/Unique/NonNull are single-field
    /// wrappers and the innermost field is a `Dyn_*` fat pointer sort.
    fn wrap_thin_ptr_in_target(
        &self,
        thin_ptr: Expr,
        tgt_dt: &ay_bindings::DatatypeSort,
        tgt_sort: &Sort,
        vtable_val: Expr,
    ) -> Option<Expr> {
        if tgt_dt.constructors.len() != 1 {
            return None;
        }
        let ctor = tgt_dt.constructors.first()?;

        let mut field_exprs = Vec::with_capacity(ctor.fields.len());
        for field in &ctor.fields {
            match field.sort.inner() {
                SortInner::Datatype(inner_dt) if inner_dt.name.starts_with("Dyn_") => {
                    // Leaf: construct fat pointer.
                    let fat = construct_dyn_fat_pointer(
                        thin_ptr.clone(),
                        inner_dt,
                        field.sort.clone(),
                        vtable_val.clone(),
                    )?;
                    field_exprs.push(fat);
                }
                SortInner::Datatype(inner_dt) => {
                    // Nested wrapper: recurse.
                    let wrapped = self.wrap_thin_ptr_in_target(
                        thin_ptr.clone(),
                        inner_dt,
                        &field.sort,
                        vtable_val.clone(),
                    )?;
                    field_exprs.push(wrapped);
                }
                SortInner::BitVec(bv) => {
                    // BV field in wrapper (e.g., allocator marker): fill with thin ptr
                    // coerced to the target width.
                    field_exprs.push(coerce_bitvec_width_safe(
                        thin_ptr.clone(),
                        bv.width,
                        SignExtension::ZeroExtend,
                    ));
                }
                _ => return None,
            }
        }

        Some(Expr::datatype_constructor(&tgt_dt.name, &ctor.name, field_exprs, tgt_sort.clone()))
    }

    /// Resolve the vtable discriminant value for an unsize coercion source type.
    ///
    /// For the BMC statement path, uses a dummy vtable value of 0.
    /// The CHC path has real vtable discriminant tracking; the BMC path relies on
    /// unique-candidate dyn dispatch which doesn't need multi-impl discrimination.
    fn resolve_vtable_value_for_unsize(&self, _src_ty: Option<rustc_public::ty::Ty>) -> Expr {
        Expr::bitvec_const(0u64, POINTER_WIDTH)
    }
}
