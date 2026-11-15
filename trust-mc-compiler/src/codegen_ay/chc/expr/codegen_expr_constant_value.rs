// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exact initialized values whose Rust layout and CHC schema are both known.
//! Padding and inactive payload bytes do not participate in value decoding.

use super::*;
use crate::codegen_ay::chc::call::inline_shared::checked_inline_variant_constructor;
use crate::codegen_ay::chc::decl::global_objects::InitSite;
use crate::kani_middle::abi::LayoutOf;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::rustc_internal;
use rustc_public::ty::Ty;
use std::sync::Arc;

const MAX_VALUE_DEPTH: usize = 12;

impl ChcCtx<'_, '_> {
    /// A bounded value family whose leaves need no address interpretation or
    /// special representation: primitive scalars, tuples, and real core Option.
    pub(in crate::codegen_ay::chc) fn const_safe_value_supported(
        &self,
        ty: Ty,
        depth: usize,
    ) -> bool {
        if depth > MAX_VALUE_DEPTH {
            return false;
        }
        match ty.kind() {
            TyKind::RigidTy(
                RigidTy::Bool
                | RigidTy::Char
                | RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_),
            ) => true,
            TyKind::RigidTy(RigidTy::Tuple(fields)) => {
                fields.iter().all(|ty| self.const_safe_value_supported(*ty, depth + 1))
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) if self.is_core_option_value(def) => {
                let variants = def.variants();
                variants.iter().all(|variant| {
                    variant.fields().iter().all(|field| {
                        mono_ty::field_ty(field, &args)
                            .is_some_and(|ty| self.const_safe_value_supported(ty, depth + 1))
                    })
                })
            }
            _ => false,
        }
    }

    fn is_core_option_value(&self, def: rustc_public::ty::AdtDef) -> bool {
        crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
            self.tcx,
            rustc_internal::internal(self.tcx, def.def_id()),
            &["option", "Option"],
        )
    }

    /// Decode a value only when its whole typed cell and every active field
    /// view can also be seeded with the canonical CHC memory representation.
    /// Build seeds transactionally: a failed nested field keeps all cells free
    /// and the caller retains its existing constant-contents refusal.
    pub(in crate::codegen_ay::chc) fn decode_const_safe_window(
        &self,
        bytes: &dyn ConstRead,
        ty: Ty,
        memory_inits: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
    ) -> Option<Expr> {
        let sort = Self::translate_ty(ty)?;
        let value = self.read_const_safe_value(bytes, 0, ty, &sort, 0)?;
        let mut seeds = Vec::new();
        self.seed_const_safe_value(ty, &value, &mut seeds, site, 0)?;
        memory_inits.extend(seeds);
        Some(value)
    }

    fn seed_const_safe_value(
        &self,
        ty: Ty,
        value: &Expr,
        seeds: &mut Vec<(Arc<str>, Sort, Expr, u32, u64)>,
        site: InitSite,
        depth: usize,
    ) -> Option<()> {
        if !self.const_safe_value_supported(ty, depth)
            || Self::translate_ty(ty).as_ref() != Some(value.sort())
        {
            return None;
        }
        let layout = LayoutOf::new(ty);
        let size = layout.size_of()?;
        if size > 0 {
            let memory_sort = self.elem_sort_for_memory_array(ty);
            let memory_value = if value.sort() == &memory_sort {
                value.clone()
            } else if value.sort().is_datatype() {
                let width = memory_sort.bitvec_width()?;
                // This is the existing typed-memory encoding, not native bytes.
                // Require enough bits for the constructor tag and all payloads:
                // its tag-free fallback can alias None with a zero payload.
                if width > 4096
                    || crate::codegen_ay::types::flattenable_datatype_sort_width(value.sort())?
                        > width
                {
                    return None;
                }
                crate::codegen_ay::chc::push_pending_datatype_sort(value.sort().clone());
                crate::codegen_ay::types::flatten_datatype_to_bitvec(value, width)?
            } else {
                return None;
            };
            if memory_value.sort() != &memory_sort {
                return None;
            }
            seeds.push((
                Arc::from(Self::type_key_for_ty(ty).as_ref()),
                memory_sort,
                memory_value,
                site.obj_id,
                site.base,
            ));
        }
        let recurse_site = |offset: usize| {
            Some(InitSite {
                obj_id: site.obj_id,
                base: site.base.checked_add(u64::try_from(offset).ok()?)?,
            })
        };
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Tuple(fields)) if !fields.is_empty() => {
                let values = if fields.len() == 1 {
                    vec![value.clone()]
                } else {
                    let ay_bindings::ExprValue::DatatypeConstructor { args, .. } = value.value()
                    else {
                        return None;
                    };
                    args.clone()
                };
                for (index, (field_ty, value)) in fields.iter().zip(&values).enumerate() {
                    self.seed_const_safe_value(
                        *field_ty,
                        value,
                        seeds,
                        recurse_site(layout.field_offset(index)?)?,
                        depth + 1,
                    )?;
                }
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) if self.is_core_option_value(def) => {
                let ay_bindings::ExprValue::DatatypeConstructor {
                    constructor_name,
                    args: values,
                    ..
                } = value.value()
                else {
                    return None;
                };
                let dt = value.sort().datatype_sort()?;
                let active =
                    dt.constructors.iter().position(|ctor| ctor.name == *constructor_name)?;
                let variants = def.variants();
                for (index, (field, value)) in
                    variants.get(active)?.fields().iter().zip(values).enumerate()
                {
                    let field_ty = mono_ty::field_ty(field, &args)?;
                    self.seed_const_safe_value(
                        field_ty,
                        value,
                        seeds,
                        recurse_site(layout.variant_field_offset(active, index)?)?,
                        depth + 1,
                    )?;
                }
            }
            _ => {}
        }
        Some(())
    }

    /// Read exactly the typed initialized fields at `offset`. Every data leaf
    /// follows ConstRead's relocation clause; no relocation becomes integer
    /// data, no uninitialized active byte is zero-filled, and no tag/payload
    /// offset is inferred from an SMT sort's width.
    pub(in crate::codegen_ay::chc) fn read_const_safe_value(
        &self,
        bytes: &dyn ConstRead,
        offset: usize,
        ty: Ty,
        sort: &Sort,
        depth: usize,
    ) -> Option<Expr> {
        if !self.const_safe_value_supported(ty, depth)
            || Self::translate_ty(ty).as_ref() != Some(sort)
        {
            return None;
        }
        let layout = LayoutOf::new(ty);
        let size = layout.size_of()?;
        let window = bytes.sub_window(offset, size)?;
        let scalar = |width| {
            if size.checked_mul(8)? != usize::try_from(width).ok()? {
                return None;
            }
            Some(Expr::bitvec_const(window.read_uint_at(0, size)?, width))
        };
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => Some(Expr::bool_const(window.read_bool_at(0)?)),
            TyKind::RigidTy(RigidTy::Char) => {
                let value = window.read_uint_at(0, 4)?;
                char::from_u32(u32::try_from(value).ok()?)?;
                Some(Expr::bitvec_const(value, 32))
            }
            TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)) => {
                scalar(sort.bitvec_width()?)
            }
            TyKind::RigidTy(RigidTy::Tuple(fields)) => {
                if fields.is_empty() {
                    return canonical_zst_expr(ty).filter(|value| value.sort() == sort);
                }
                let mut values = Vec::with_capacity(fields.len());
                for (index, field_ty) in fields.iter().enumerate() {
                    let field_sort = Self::translate_ty(*field_ty)?;
                    values.push(self.read_const_safe_value(
                        &window,
                        layout.field_offset(index)?,
                        *field_ty,
                        &field_sort,
                        depth + 1,
                    )?);
                }
                // The CHC type translator erases singleton tuples.
                if fields.len() == 1 {
                    return values.pop().filter(|value| value.sort() == sort);
                }
                let dt = sort.datatype_sort()?;
                let [ctor] = dt.constructors.as_slice() else { return None };
                if ctor.fields.len() != fields.len()
                    || ctor.fields.iter().enumerate().any(|(index, field)| {
                        *field.name != *names::tuple_field_name(index)
                            || &field.sort != values[index].sort()
                    })
                {
                    return None;
                }
                checked_inline_variant_constructor(&dt.name, &ctor.name, values, sort.clone())
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) if self.is_core_option_value(def) => {
                let variants = def.variants();
                let dt = sort.datatype_sort()?;
                if dt.constructors.len() != variants.len() {
                    return None;
                }
                let active = decode_non_unit_enum_variant_index(&window, ty, variants.len())?;
                let variant = variants.get(active)?;
                let ctor = dt.constructors.get(active)?;
                if variant.fields().len() != ctor.fields.len() {
                    return None;
                }
                let mut values = Vec::with_capacity(ctor.fields.len());
                for (index, (field, sort_field)) in
                    variant.fields().iter().zip(&ctor.fields).enumerate()
                {
                    let field_ty = mono_ty::field_ty(field, &args)?;
                    values.push(self.read_const_safe_value(
                        &window,
                        layout.variant_field_offset(active, index)?,
                        field_ty,
                        &sort_field.sort,
                        depth + 1,
                    )?);
                }
                checked_inline_variant_constructor(&dt.name, &ctor.name, values, sort.clone())
            }
            _ => None,
        }
    }
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
#[path = "codegen_expr_constant_value/tests.rs"]
mod tests;
