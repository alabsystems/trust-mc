// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `Box::new(value)` payload (the BMC `BoxNew` stub).
//!
//! The stub allocated the heap object and returned its address but never
//! stored `value` anywhere, so every read through the box saw unconstrained
//! memory and a counterexample resting on those free bytes was certified
//! Genuine: `Box::new(7u8)` then `assert!(*b == 7)` FAILED with
//! `[AY:CTREX_CAT:Genuine]`, and so did `alloc_id_offset_dual_safe.rs::
//! safe_distinct_fields_differ` (`assert!(s.a != s.b)` through `&s.a` and
//! `&s.b`). Reads through a raw pointer derived from the box load byte memory
//! at `base + field offset`, so the payload is stored there, field by field,
//! with rustc's own layout.
//!
//! A payload with no exact byte image here (an enum, a union, a fat pointer, a
//! value whose sort does not mirror its type) leaves the object unconstrained,
//! which over-approximates every read: a proof over it stands, and the
//! counterexample is tainted (`bmc_sound_havoc`) instead of certified.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, SortInner};
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{AdtDef, AdtKind, GenericArgKind, GenericArgs, RigidTy, Ty, TyKind};
use tracing::debug;

use super::super::IntoOption;
use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::abi::LayoutOf;

/// Nesting bound for aggregate payloads.
const MAX_PAYLOAD_DEPTH: usize = 8;
/// Largest array serialized element by element.
const MAX_PAYLOAD_ARRAY_LEN: u64 = 64;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Store the value `Box::new` boxes at the freshly allocated `addr`.
    pub(in crate::codegen_ay::statement) fn store_box_new_payload(
        &mut self,
        func: &Operand,
        args: &[Operand],
        addr: &Expr,
    ) {
        let payload_ty = func.ty(self.body.locals()).into_option().and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(_, generic_args)) => match generic_args.0.first() {
                Some(GenericArgKind::Type(payload)) => Some(*payload),
                _ => None,
            },
            _ => None,
        });
        let stored = match (payload_ty, args.first()) {
            (Some(ty), Some(operand)) => {
                if self.ctx.has_native_box_allocations() && Self::ty_carries_a_pointer_value(ty) {
                    self.ctx.unsupported_with_fallback(
                        "BoxPointerPayload",
                        "boxed pointer bytes need actual physical-address/provenance transport",
                    );
                }
                match self.codegen_operand(operand) {
                    Some(value) => self.store_payload_bytes(ty, &value, addr, 0),
                    None => false,
                }
            }
            _ => false,
        };
        if stored {
            debug!("BoxNew: payload stored at the allocation by layout");
        } else {
            debug!("BoxNew: payload has no exact byte image; allocation left unconstrained");
            self.ctx.bmc_sound_havoc("box_new_payload_unmodeled");
        }
    }

    /// Store `value` of type `ty` into byte memory at `addr`. `false` when some
    /// part of it has no exact byte image; bytes already stored by then are
    /// exact, and the rest of the object stays unconstrained.
    pub(in crate::codegen_ay::statement) fn store_payload_bytes(
        &mut self,
        ty: Ty,
        value: &Expr,
        addr: &Expr,
        depth: usize,
    ) -> bool {
        if depth > MAX_PAYLOAD_DEPTH {
            return false;
        }
        let Ok(layout) = ty.layout() else {
            return false;
        };
        let shape = layout.shape();
        if !shape.is_sized() {
            return false;
        }
        let size = shape.size.bytes();
        if size == 0 {
            return true;
        }
        let bit_width = u32::try_from(size).ok().and_then(|bytes| bytes.checked_mul(8));
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => {
                if size != 1 || !value.sort().is_bool() {
                    return false;
                }
                self.ctx.store_memory_bytes(addr.clone(), value.clone());
                true
            }
            TyKind::RigidTy(
                RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_) | RigidTy::Char,
            ) => {
                if value.sort().bitvec_width() != bit_width {
                    return false;
                }
                self.ctx.store_memory_bytes(addr.clone(), value.clone());
                true
            }
            TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..))
                if bit_width == Some(2 * POINTER_WIDTH) =>
            {
                self.store_fat_pointer_bytes(value, addr)
            }
            TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..)) => {
                if bit_width != Some(POINTER_WIDTH)
                    || value.sort().bitvec_width() != Some(POINTER_WIDTH)
                {
                    return false;
                }
                self.ctx.store_memory_bytes(addr.clone(), value.clone());
                true
            }
            TyKind::RigidTy(RigidTy::Tuple(fields)) => {
                self.store_payload_field_bytes(ty, &fields, value, addr, depth)
            }
            TyKind::RigidTy(RigidTy::Adt(def, adt_args)) if def.kind() == AdtKind::Struct => {
                if self.store_vec_or_rawvec_bytes(ty, &def, &adt_args, value, addr) {
                    return true;
                }
                let variants = def.variants();
                let [variant] = variants.as_slice() else {
                    return false;
                };
                let Some(fields) = variant
                    .fields()
                    .iter()
                    .map(|field| mono_ty::field_ty(field, &adt_args))
                    .collect::<Option<Vec<Ty>>>()
                else {
                    return false;
                };
                self.store_payload_field_bytes(ty, &fields, value, addr, depth)
            }
            TyKind::RigidTy(RigidTy::Array(element_ty, len)) => {
                let Some(count) = len.eval_target_usize().into_option() else {
                    return false;
                };
                if count > MAX_PAYLOAD_ARRAY_LEN
                    || !matches!(value.sort().inner(), SortInner::Array(_))
                {
                    return false;
                }
                let Some(element_size) = element_ty.layout().ok().map(|l| l.shape().size.bytes())
                else {
                    return false;
                };
                for index in 0..count {
                    let element =
                        value.clone().select(Expr::bitvec_const(u128::from(index), POINTER_WIDTH));
                    let offset = u128::from(index) * element_size as u128;
                    let element_addr =
                        addr.clone().bvadd(Expr::bitvec_const(offset, POINTER_WIDTH));
                    if !self.store_payload_bytes(element_ty, &element, &element_addr, depth + 1) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }

    /// A fat pointer (`&str`, `&[T]`, `&dyn Trait`) is `(data, metadata)` at
    /// offsets 0 and one pointer width; its encoding is a one-constructor
    /// datatype with a `fld_ptr` word and a `fld_len` / `fld_vtable` /
    /// `fld_meta` word. Any other encoding has no byte image here.
    fn store_fat_pointer_bytes(&mut self, value: &Expr, addr: &Expr) -> bool {
        let SortInner::Datatype(datatype) = value.sort().inner() else {
            return false;
        };
        let [constructor] = datatype.constructors.as_slice() else {
            return false;
        };
        let find = |names: &[&str]| {
            constructor.fields.iter().find(|field| names.iter().any(|name| field.name == *name))
        };
        let (Some(data), Some(meta)) =
            (find(&["fld_ptr"]), find(&["fld_len", "fld_vtable", "fld_meta"]))
        else {
            return false;
        };
        let word = u128::from(POINTER_WIDTH / 8);
        for (selector, offset) in [(data, 0u128), (meta, word)] {
            if selector.sort.bitvec_width() != Some(POINTER_WIDTH) {
                return false;
            }
            let field_value = value.clone().field_select(
                datatype.name.clone(),
                selector.name.clone(),
                selector.sort.clone(),
            );
            let at = if offset == 0 {
                addr.clone()
            } else {
                addr.clone().bvadd(Expr::bitvec_const(offset, POINTER_WIDTH))
            };
            self.ctx.store_memory_bytes(at, field_value);
        }
        true
    }

    /// Store the stack/heap header words of `RawVec<T, A>`, `Vec<T, A>`, or
    /// `String`, whose BMC encoding is a flat datatype (`RawVec { fld_ptr,
    /// fld_cap }` or `Vec_<T> / RustString { fld_ptr, fld_len, fld_cap,
    /// fld_data }`) rather than the nested `{ buf: RawVec { inner: RawVecInner
    /// { ptr, cap, alloc } }, len }` MIR struct fields.
    ///
    /// Every word offset is read from `rustc`'s `LayoutOf`, and the total
    /// struct size must equal the written words (`2 * word` for `RawVec`,
    /// `3 * word` for `Vec` and `String`), so any non-ZST allocator field fails
    /// closed (`false`).
    fn store_vec_or_rawvec_bytes(
        &mut self,
        ty: Ty,
        def: &AdtDef,
        adt_args: &GenericArgs,
        value: &Expr,
        addr: &Expr,
    ) -> bool {
        let SortInner::Datatype(datatype) = value.sort().inner() else {
            return false;
        };
        let [constructor] = datatype.constructors.as_slice() else {
            return false;
        };
        let word_bytes = (POINTER_WIDTH / 8) as usize;
        let words: Vec<(&str, usize)> = match def.trimmed_name().as_str() {
            "RawVec" => {
                if LayoutOf::new(ty).size_of() != Some(2 * word_bytes) {
                    return false;
                }
                let Some((ptr_off, cap_off)) = Self::rawvec_ptr_and_cap_offsets(ty, def, adt_args)
                else {
                    return false;
                };
                vec![("fld_ptr", ptr_off), ("fld_cap", cap_off)]
            }
            "Vec" => {
                let Some((ptr_off, cap_off, len_off)) =
                    Self::vec_ptr_cap_len_offsets(ty, def, adt_args)
                else {
                    return false;
                };
                vec![("fld_ptr", ptr_off), ("fld_cap", cap_off), ("fld_len", len_off)]
            }
            "String" => {
                if LayoutOf::new(ty).size_of() != Some(3 * word_bytes) {
                    return false;
                }
                let Some((vec_off, vec_ty)) =
                    Self::named_field_offset_and_ty(ty, def, adt_args, "vec")
                else {
                    return false;
                };
                let TyKind::RigidTy(RigidTy::Adt(vec_def, vec_args)) = vec_ty.kind() else {
                    return false;
                };
                let Some((ptr_off, cap_off, len_off)) =
                    Self::vec_ptr_cap_len_offsets(vec_ty, &vec_def, &vec_args)
                else {
                    return false;
                };
                vec![
                    ("fld_ptr", vec_off + ptr_off),
                    ("fld_cap", vec_off + cap_off),
                    ("fld_len", vec_off + len_off),
                ]
            }
            _ => return false,
        };
        for (selector_name, offset) in words {
            let Some(selector) =
                constructor.fields.iter().find(|field| field.name == selector_name)
            else {
                return false;
            };
            if selector.sort.bitvec_width() != Some(POINTER_WIDTH) {
                return false;
            }
            let field_value = value.clone().field_select(
                datatype.name.clone(),
                selector.name.clone(),
                selector.sort.clone(),
            );
            let at = if offset == 0 {
                addr.clone()
            } else {
                addr.clone().bvadd(Expr::bitvec_const(offset as u128, POINTER_WIDTH))
            };
            self.ctx.store_memory_bytes(at, field_value);
        }
        true
    }

    fn named_field_offset_and_ty(
        ty: Ty,
        def: &AdtDef,
        adt_args: &GenericArgs,
        name: &str,
    ) -> Option<(usize, Ty)> {
        let variants = def.variants();
        let [variant] = variants.as_slice() else {
            return None;
        };
        let fields = variant.fields();
        let idx = fields.iter().position(|f| f.name == name)?;
        let offset = LayoutOf::new(ty).field_offset(idx)?;
        let field_ty = mono_ty::field_ty(&fields[idx], adt_args)?;
        Some((offset, field_ty))
    }

    fn rawvec_ptr_and_cap_offsets(
        ty: Ty,
        def: &AdtDef,
        adt_args: &GenericArgs,
    ) -> Option<(usize, usize)> {
        let word_bytes = (POINTER_WIDTH / 8) as usize;
        if LayoutOf::new(ty).size_of() != Some(2 * word_bytes) {
            return None;
        }
        if let Some((inner_off, inner_ty)) =
            Self::named_field_offset_and_ty(ty, def, adt_args, "inner")
            && let TyKind::RigidTy(RigidTy::Adt(inner_def, inner_args)) = inner_ty.kind()
            && inner_def.kind() == AdtKind::Struct
        {
            let (ptr_off, _) =
                Self::named_field_offset_and_ty(inner_ty, &inner_def, &inner_args, "ptr")?;
            let (cap_off, _) =
                Self::named_field_offset_and_ty(inner_ty, &inner_def, &inner_args, "cap")?;
            return Some((inner_off + ptr_off, inner_off + cap_off));
        }
        let (ptr_off, _) = Self::named_field_offset_and_ty(ty, def, adt_args, "ptr")?;
        let (cap_off, _) = Self::named_field_offset_and_ty(ty, def, adt_args, "cap")?;
        Some((ptr_off, cap_off))
    }

    fn vec_ptr_cap_len_offsets(
        ty: Ty,
        def: &AdtDef,
        adt_args: &GenericArgs,
    ) -> Option<(usize, usize, usize)> {
        let word_bytes = (POINTER_WIDTH / 8) as usize;
        if LayoutOf::new(ty).size_of() != Some(3 * word_bytes) {
            return None;
        }
        let (buf_off, buf_ty) = Self::named_field_offset_and_ty(ty, def, adt_args, "buf")?;
        let (len_off, _) = Self::named_field_offset_and_ty(ty, def, adt_args, "len")?;
        let TyKind::RigidTy(RigidTy::Adt(buf_def, buf_args)) = buf_ty.kind() else {
            return None;
        };
        let (ptr_off, cap_off) = Self::rawvec_ptr_and_cap_offsets(buf_ty, &buf_def, &buf_args)?;
        Some((buf_off + ptr_off, buf_off + cap_off, len_off))
    }

    /// Store a struct or tuple whose datatype value has exactly one constructor
    /// with one selector per declared field, in declaration order.
    fn store_payload_field_bytes(
        &mut self,
        ty: Ty,
        fields: &[Ty],
        value: &Expr,
        addr: &Expr,
        depth: usize,
    ) -> bool {
        let SortInner::Datatype(datatype) = value.sort().inner() else {
            return false;
        };
        let [constructor] = datatype.constructors.as_slice() else {
            return false;
        };
        // The flattened Option-like struct (`is_some`, payload) is not a plain
        // record of the declared fields.
        if constructor.fields.len() != fields.len()
            || constructor.fields.first().is_some_and(|field| field.name == "is_some")
        {
            return false;
        }
        let layout = LayoutOf::new(ty);
        for (index, field_ty) in fields.iter().enumerate() {
            let Some(offset) = layout.field_offset(index) else {
                return false;
            };
            let selector = &constructor.fields[index];
            let field_value = value.clone().field_select(
                datatype.name.clone(),
                selector.name.clone(),
                selector.sort.clone(),
            );
            let field_addr = if offset == 0 {
                addr.clone()
            } else {
                addr.clone().bvadd(Expr::bitvec_const(offset as u128, POINTER_WIDTH))
            };
            if !self.store_payload_bytes(*field_ty, &field_value, &field_addr, depth + 1) {
                return false;
            }
        }
        true
    }
}
