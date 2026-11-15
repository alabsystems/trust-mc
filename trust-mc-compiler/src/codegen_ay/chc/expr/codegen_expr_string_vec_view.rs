// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `String.vec` through the `String` model, both ways (C5b, design
//! trust-mc-reds-final §4.2).
//!
//! `translate_ty` models `String` as `RustString(fld_ptr, fld_len, fld_cap)`,
//! not as its one MIR field `vec: Vec<u8>`, so the sort walk has no level for
//! `s.vec`: its field 0 is the model's pointer. The raw walk read that pointer
//! as the whole `Vec<u8>` (every `String` drop does `s.vec`), and C5b's
//! resolver refuses the step (`field_sort_differs_from_type`). The model still
//! determines the field: a `String`'s vector has the String's pointer, length
//! and capacity, and its bytes live in memory at that pointer, which the
//! `Vec<u8>` model's `fld_data` array does not read. So the view is the
//! `Vec<u8>` model value built from the String's three slots, with `fld_data`
//! a booked havoc (`untracked_collection_state`), the same over-approximation
//! `String::into_bytes` makes for the whole vector.
//!
//! The other way, a `Vec<u8>` value stored into a flattened `String` (`String
//! { vec }`, `from_utf8_unchecked`) used to bind the String's three slots to
//! the first three of the vector's four leaves silently, and the leaf guard of
//! the destination builder now refuses a value that does not tile its
//! destination. Those three leaves are the String's pointer, length and
//! capacity, so they are bound; the data array has no place in the model and
//! is dropped, booked as an unattributed `untracked_collection_state` havoc
//! (the String's bytes are not the vector's array, so no counterexample in the
//! harness is certified Genuine through it).
//!
//! A write to `s.vec` through a place stays refused (fail closed).

use std::collections::HashSet;

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef as _;
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::FieldProjection;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::chc::codegen_ctx::{Havoc, chc_fresh_name, sound_havoc};
use crate::codegen_ay::names::{RUST_STRING_SORT, vec_layout};
use crate::codegen_ay::types::ptr_sort;

/// Is `ty` the standard `String`: the ADT `translate_ty` models as
/// `RustString`, with its one field `vec`?
fn is_string_with_one_vec_field(ty: Ty, vec_ty: Ty) -> bool {
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return false };
    if def.trimmed_name() != "String" {
        return false;
    }
    let variants = def.variants();
    let [variant] = variants.as_slice() else { return false };
    let fields = variant.fields();
    let [vec_field] = fields.as_slice() else { return false };
    crate::codegen_ay::shared::mono_ty::field_ty(vec_field, &args) == Some(vec_ty)
}

/// Is `sort` the `Vec` model (`fld_ptr`, `fld_len`, `fld_cap`, `fld_data`)
/// with pointer-sorted metadata? Returns its data sort.
fn vec_model_data_sort(sort: &Sort) -> Option<Sort> {
    let dt = sort.datatype_sort()?;
    let [ctor] = dt.constructors.as_slice() else { return None };
    let names: Vec<&str> = ctor.fields.iter().map(|f| &*f.name).collect();
    if names != vec_layout::FIELDS_ORDERED {
        return None;
    }
    let metadata = [vec_layout::IDX_PTR, vec_layout::IDX_LEN, vec_layout::IDX_CAP];
    if metadata.iter().any(|&i| ctor.fields[i].sort != ptr_sort()) {
        return None;
    }
    Some(ctor.fields[vec_layout::IDX_DATA].sort.clone())
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The read of `<path>.vec`, where `<path>` names a `String` held in the
    /// flattened `local_idx`, as the `Vec<u8>` model value (see the module
    /// docs). `None` unless the path's last step is `String.vec`, the rest of
    /// the path is faithful (`flat_span_for`), the String's slots are the
    /// model's three pointer-sorted leaves, and the field's sort is the `Vec`
    /// model.
    pub(in crate::codegen_ay::chc) fn string_vec_field_view(
        &self,
        local_idx: usize,
        projs: &[FieldProjection],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let (last, prefix) = projs.split_last()?;
        if last.cons_idx.is_some() || last.field_idx != 0 {
            return None;
        }
        let vec_ty = last.field_ty?;
        let local_ty = self.body.locals().get(local_idx)?.ty;
        let string_ty = match prefix.last() {
            Some(fp) => fp.field_ty?,
            None => local_ty,
        };
        if !is_string_with_one_vec_field(string_ty, vec_ty) {
            return None;
        }
        let string_sort = Self::translate_ty(string_ty)?;
        let string_dt = string_sort.datatype_sort()?;
        let [string_ctor] = string_dt.constructors.as_slice() else { return None };
        let string_fields: Vec<&str> = string_ctor.fields.iter().map(|f| &*f.name).collect();
        if &*string_dt.name != RUST_STRING_SORT
            || string_fields != vec_layout::FIELDS_ORDERED[..vec_layout::IDX_DATA]
        {
            return None;
        }
        let vec_sort = Self::translate_ty(vec_ty)?;
        let data_sort = vec_model_data_sort(&vec_sort)?;

        let (offset, count) = if prefix.is_empty() {
            (0, self.flattened_field_count(local_idx))
        } else {
            self.flat_span_for(local_idx, prefix).ok()?
        };
        if count != 3 {
            return None;
        }
        let mut metadata = Vec::with_capacity(4);
        for slot in offset..offset + 3 {
            let leaf = self.flattened_local_field_expr(local_idx, slot, modified_locals)?;
            if *leaf.sort() != ptr_sort() {
                return None;
            }
            metadata.push(leaf);
        }
        let data = Havoc::mint_deferred(
            self,
            sound_havoc::UNTRACKED_COLLECTION_STATE,
            chc_fresh_name("string_vec_data"),
            data_sort,
        );
        metadata.push(data);
        let vec_dt = vec_sort.datatype_sort()?;
        let ctor = &vec_dt.constructors[0];
        Some(Expr::datatype_constructor(&*vec_dt.name, &*ctor.name, metadata, vec_sort.clone()))
    }

    /// The String's three slot values for a `Vec<u8>` model value stored into
    /// the flattened `String` local `dest_local` (see the module docs), or
    /// `None` when `dest_local` is not a `String` model local or `value` is not
    /// the `Vec` model. Books the dropped data array.
    pub(in crate::codegen_ay::chc) fn string_slots_from_vec_value(
        &self,
        dest_local: usize,
        value: &Expr,
    ) -> Option<Vec<Option<Expr>>> {
        vec_model_data_sort(value.sort())?;
        let dest_ty = self.body.locals().get(dest_local)?.ty;
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = dest_ty.kind() else { return None };
        let variants = def.variants();
        let [variant] = variants.as_slice() else { return None };
        let vec_ty =
            crate::codegen_ay::shared::mono_ty::field_ty(variant.fields().first()?, &args)?;
        if !is_string_with_one_vec_field(dest_ty, vec_ty)
            || Self::translate_ty(vec_ty).as_ref() != Some(value.sort())
        {
            return None;
        }
        let string_dt = Self::translate_ty(dest_ty)?.datatype_sort()?.clone();
        let [string_ctor] = string_dt.constructors.as_slice() else { return None };
        let string_fields: Vec<&str> = string_ctor.fields.iter().map(|f| &*f.name).collect();
        if &*string_dt.name != RUST_STRING_SORT
            || string_fields != vec_layout::FIELDS_ORDERED[..vec_layout::IDX_DATA]
            || self.flattened_field_count(dest_local) != vec_layout::IDX_DATA
        {
            return None;
        }
        let mut leaves = Vec::with_capacity(vec_layout::FIELD_COUNT);
        crate::codegen_ay::chc::codegen_stmt_flatten::collect_leaf_exprs(value, &mut leaves);
        if leaves.len() != vec_layout::FIELD_COUNT {
            return None;
        }
        leaves.truncate(vec_layout::IDX_DATA);
        debug!(
            fn_name = %self.fn_name,
            dest_local,
            "String {{ vec }}: the String's slots are the vector's ptr, len and cap; its data array is dropped"
        );
        let _ = self.record_sound_fallback_reason(sound_havoc::UNTRACKED_COLLECTION_STATE.as_str());
        Some(leaves)
    }
}
