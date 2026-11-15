// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integer reads assembled from initialized bytes of an authoritative array.
//! Typed mirrors need not seed every view. A raw read must not turn a missing
//! cell into evidence, nor treat a compact datatype as physical bits.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Place, ProjectionElem, StatementKind, TerminatorKind};
use rustc_public::ty::{AdtKind, FloatTy, RigidTy, Ty, TyKind, UintTy};

use crate::codegen_ay::chc::stmt::codegen_stmt_mirror::ARRAY_ELEMENT_MEMORY_MIRROR_LIMIT;
use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::types::datatype_field_select;
use crate::kani_middle::abi::LayoutOf;

use super::ChcCtx;
use super::codegen_expr_deref_resolve::DerefCascadeResult;
use super::codegen_types::CodegenTypes;

impl ChcCtx<'_, '_> {
    pub(super) fn try_resolve_owned_array_byte(
        &mut self,
        place: &Place,
        modified: &HashSet<usize>,
    ) -> Option<DerefCascadeResult> {
        if !matches!(place.projection.as_slice(), [ProjectionElem::Deref]) {
            return None;
        }
        let TyKind::RigidTy(RigidTy::RawPtr(read_ty, _)) =
            self.body.locals().get(place.local)?.ty.kind()
        else {
            return None;
        };
        // Prove the owner from definitions even when an inlined as_ptr lost
        // its allocation metadata. A matching pointer sort supplies no proof.
        let (owner, ty, offset) =
            self.body.locals().iter().enumerate().find_map(|(owner, decl)| {
                let ty = self.resolve_body_ty(decl.ty);
                if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Array(..))) {
                    return None;
                }
                let referent =
                    crate::codegen_ay::chc::RefTarget { local: owner, projections: vec![] };
                let offset =
                    u64::try_from(self.store_pointer_referent_byte_offset(place.local, &referent)?)
                        .ok()?;
                Some((owner, ty, offset))
            })?;
        let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = ty.kind() else {
            return None;
        };
        // Same-type aggregate reads remain on the typed-value/memory routes.
        if read_ty == ty
            || (read_ty == elem_ty
                && !matches!(read_ty.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_))))
        {
            return None;
        }
        let size = read_ty.layout().ok()?.shape().size.bytes() as u64;
        if size == 0
            || offset.checked_add(size)? > ty.layout().ok()?.shape().size.bytes() as u64
            || self.liveness.dead_locals.contains(&owner)
        {
            // The ordinary pointer-bound and lifetime paths report these.
            return None;
        }
        let read_align = u64::try_from(read_ty.layout().ok()?.shape().abi_align).ok()?;
        let owner_align = u64::try_from(ty.layout().ok()?.shape().abi_align).ok()?;
        let register_is_authoritative = self.array_byte_register_is_authoritative(owner);
        // Keep exact register reads when available: the element-memory
        // expansion is bounded and may not have seeded this array. When a
        // writer makes the register unsuitable, preserve the established
        // element-typed memory route. Its cells represent complete elements
        // at the physical stride, not views starting inside an element.
        if read_ty == elem_ty
            && offset % size == 0
            && read_align != 0
            && owner_align % read_align == 0
            && offset % read_align == 0
            && !register_is_authoritative
            && self.get_array_length(ty).is_some_and(|len| len <= ARRAY_ELEMENT_MEMORY_MIRROR_LIMIT)
        {
            return None;
        }
        // The usual null/constant checks ran before this resolver. Retain the
        // stack object's validity check even when its value answers the read.
        self.emit_ptr_obj_valid_check(place.local, modified);
        if register_is_authoritative
            && !self.ty_has_interior_mut(ty)
            && let Some(value) =
                self.owned_u32_char_array_view(owner, ty, read_ty, offset, modified)
        {
            return Some(DerefCascadeResult::Resolved(value));
        }
        let value = if matches!(read_ty.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_)))
            && size <= 16
            && read_align != 0
            && owner_align % read_align == 0
            && offset % read_align == 0
            && register_is_authoritative
            && !self.ty_has_interior_mut(ty)
        {
            self.translate_place_with_modified(
                &Place { local: owner, projection: vec![] },
                modified,
            )
            .and_then(|value| {
                let mut result = None;
                for i in 0..size {
                    let byte = self.initialized_value_byte(&value, ty, offset + i, 8)?;
                    result = Some(match (result, self.tcx.data_layout.endian) {
                        (None, _) => byte,
                        (Some(lower), rustc_abi::Endian::Little) => byte.concat(lower),
                        (Some(higher), rustc_abi::Endian::Big) => higher.concat(byte),
                    });
                }
                result
            })
        } else {
            None
        };
        if let Some(value) = value {
            return Some(DerefCascadeResult::Resolved(value));
        }
        self.record_sound_fallback_reason("array_byte_view_unmodeled");
        Some(DerefCascadeResult::Bail)
    }

    /// A whole char array has the same physical bits as an equally sized
    /// u32 array. This is a value view, not a claim that those bits are valid
    /// Unicode scalars: the existing validity obligations must still check
    /// every element, including invalid and symbolic bit patterns.
    fn owned_u32_char_array_view(
        &mut self,
        owner: usize,
        owner_ty: Ty,
        read_ty: Ty,
        offset: u64,
        modified: &HashSet<usize>,
    ) -> Option<Expr> {
        let TyKind::RigidTy(RigidTy::Array(owner_elem, owner_len)) = owner_ty.kind() else {
            return None;
        };
        let TyKind::RigidTy(RigidTy::Array(read_elem, read_len)) = read_ty.kind() else {
            return None;
        };
        if offset != 0
            || !matches!(owner_elem.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U32)))
            || !matches!(read_elem.kind(), TyKind::RigidTy(RigidTy::Char))
            || owner_len.eval_target_usize().ok()? != read_len.eval_target_usize().ok()?
        {
            return None;
        }
        let owner_word = owner_elem.layout().ok()?;
        let read_word = read_elem.layout().ok()?;
        let owner_layout = owner_ty.layout().ok()?;
        let read_layout = read_ty.layout().ok()?;
        if owner_word.shape().size.bytes() != 4
            || read_word.shape().size.bytes() != 4
            || owner_word.shape().abi_align != read_word.shape().abi_align
            || owner_layout.shape().size != read_layout.shape().size
            || owner_layout.shape().abi_align != read_layout.shape().abi_align
        {
            return None;
        }
        let value = self
            .translate_place_with_modified(&Place { local: owner, projection: vec![] }, modified)?;
        let expected = Self::translate_ty(read_ty)?;
        (value.sort() == &expected).then_some(value)
    }

    fn array_byte_register_is_authoritative(&self, owner: usize) -> bool {
        if self.local_is_mutably_borrowed(owner)
            || !self.local_register_is_authoritative(owner)
            || self.body_stores_through_deref()
        {
            return false;
        }
        for block in &self.body.blocks {
            // Intrinsic copies can write without an Assign-through-Deref.
            if block.statements.iter().any(|statement| {
                matches!(&statement.kind, StatementKind::Intrinsic(kind)
                    if !matches!(kind, rustc_public::mir::NonDivergingIntrinsic::Assume(_)))
            }) {
                return false;
            }
            if let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind {
                let Ok(ty) = func.ty(self.body.locals()) else {
                    return false;
                };
                if let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() {
                    let Ok(instance) = Instance::resolve(def, &args) else {
                        return false;
                    };
                    if crate::kani_middle::transform::instance_has_unit_stub(&instance) {
                        return false;
                    }
                    let Ok(result_ty) = destination.ty(self.body.locals()) else {
                        return false;
                    };
                    if matches!(
                        result_ty.kind(),
                        TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
                    ) && !crate::kani_middle::std_abstraction::is_sysroot_core_definition(
                        self.tcx,
                        rustc_public::rustc_internal::internal(self.tcx, instance.def.def_id()),
                    ) && !matches!(
                        self.detect_kani_model(func),
                        Some(crate::kani_middle::kani_functions::KaniModel::Offset)
                    ) {
                        return false;
                    }
                } else if destination.ty(self.body.locals()).ok().is_none_or(|ty| {
                    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)))
                }) {
                    return false;
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, .. }
                    if crate::codegen_ay::chc::modifies_frame_net::call_args_may_write(
                        self,
                        args,
                        self.body.locals(),
                    ) =>
                {
                    // The registered offset model only computes/checks a
                    // pointer. No other pointer-capable call is an authority
                    // for reading the owner's register after it returns.
                    if !matches!(
                        self.detect_kani_model(func),
                        Some(crate::kani_middle::kani_functions::KaniModel::Offset)
                    ) {
                        return false;
                    }
                    let Ok(ty) = func.ty(self.body.locals()) else {
                        return false;
                    };
                    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else {
                        return false;
                    };
                    let Ok(instance) = Instance::resolve(def, &args) else {
                        return false;
                    };
                    if crate::kani_middle::transform::instance_has_unit_stub(&instance) {
                        return false;
                    }
                }
                TerminatorKind::Goto { .. }
                | TerminatorKind::SwitchInt { .. }
                | TerminatorKind::Return
                | TerminatorKind::Resume
                | TerminatorKind::Abort
                | TerminatorKind::Unreachable
                | TerminatorKind::Assert { .. }
                | TerminatorKind::Call { .. } => {}
                _ => return false,
            }
        }
        true
    }

    /// Exactly one initialized scalar byte. Padding, pointer representations,
    /// enum layouts and unsupported values decline without fabricating bits.
    fn initialized_value_byte(
        &mut self,
        value: &Expr,
        ty: Ty,
        offset: u64,
        depth: usize,
    ) -> Option<Expr> {
        if depth == 0 {
            return None;
        }
        let ty = self.resolve_body_ty(ty);
        let size = u64::try_from(ty.layout().ok()?.shape().size.bytes()).ok()?;
        if offset >= size {
            return None;
        }
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) if size == 1 && value.sort().is_bool() => Some(
                Expr::ite(value.clone(), Expr::bitvec_const(1u8, 8), Expr::bitvec_const(0u8, 8)),
            ),
            TyKind::RigidTy(
                RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Char
                | RigidTy::Float(FloatTy::F32 | FloatTy::F64),
            ) => {
                if u64::from(value.sort().bitvec_width()?) != size.checked_mul(8)? {
                    return None;
                }
                let byte = match self.tcx.data_layout.endian {
                    rustc_abi::Endian::Little => offset,
                    rustc_abi::Endian::Big => size - 1 - offset,
                };
                let low = u32::try_from(byte.checked_mul(8)?).ok()?;
                Some(value.clone().extract(low + 7, low))
            }
            TyKind::RigidTy(RigidTy::Array(elem, count)) => {
                let elem_size = u64::try_from(elem.layout().ok()?.shape().size.bytes()).ok()?;
                if elem_size == 0 {
                    return None;
                }
                let index = offset / elem_size;
                if index >= count.eval_target_usize().ok()? {
                    return None;
                }
                let width = value.sort().array_sort()?.index_sort.bitvec_width()?;
                let elem_value = value.clone().select(Expr::bitvec_const(index, width));
                let elem_value = self.try_unflatten_bv_to_datatype(elem_value, elem);
                self.initialized_value_byte(&elem_value, elem, offset % elem_size, depth - 1)
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) if def.kind() == AdtKind::Struct => {
                let variants = def.variants();
                let [variant] = variants.as_slice() else {
                    return None;
                };
                let fields = variant
                    .fields()
                    .iter()
                    .map(|field| mono_ty::field_ty(field, &args))
                    .collect::<Option<Vec<_>>>()?;
                self.initialized_field_byte(value, ty, &fields, offset, depth)
            }
            TyKind::RigidTy(RigidTy::Tuple(fields)) => {
                self.initialized_field_byte(value, ty, &fields, offset, depth)
            }
            _ => None,
        }
    }

    fn initialized_field_byte(
        &mut self,
        value: &Expr,
        ty: Ty,
        fields: &[Ty],
        offset: u64,
        depth: usize,
    ) -> Option<Expr> {
        for (index, field) in fields.iter().enumerate() {
            let start = u64::try_from(LayoutOf::new(ty).field_offset(index)?).ok()?;
            let size = u64::try_from(field.layout().ok()?.shape().size.bytes()).ok()?;
            if offset >= start && offset < start.checked_add(size)? {
                let field_value = datatype_field_select(value.clone(), 0, index)?;
                return self.initialized_value_byte(
                    &field_value,
                    *field,
                    offset - start,
                    depth - 1,
                );
            }
        }
        None
    }
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod tests {
    use super::*;
    use crate::callee_body::CalleeBody;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

    #[test]
    fn test_fixed_array_byte_refuses_stubbed_pointer_producer() {
        const SOURCE: &str = r#"
            #![allow(dead_code)]
            pub fn pointer(values: &[u8; 2]) -> *const u8 { values.as_ptr() }
            pub fn shifted(values: &[u8]) -> *const u8 { unsafe { values.as_ptr().add(1) } }
        "#;
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "pointer");
            let body = instance.callee_body().unwrap();
            let producer = body
                .blocks
                .iter()
                .find_map(|block| {
                    let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                        return None;
                    };
                    let TyKind::RigidTy(RigidTy::FnDef(def, args)) =
                        func.ty(body.locals()).ok()?.kind()
                    else {
                        return None;
                    };
                    let instance = Instance::resolve(def, &args).ok()?;
                    instance.def.name().ends_with("as_ptr").then_some(def)
                })
                .expect("real slice as_ptr producer");
            let replacement = find_instance_by_suffix(ctx.tcx, "shifted");
            let TyKind::RigidTy(RigidTy::FnDef(replacement, _)) = replacement.ty().kind() else {
                panic!("replacement FnDef");
            };
            let chc = ChcCtx::new(ctx.tcx, &body, "pointer", ChcConfig::default());
            assert!(chc.array_byte_register_is_authoritative(1));
            let _scope = crate::kani_middle::transform::UnitStubsTestScope::install(
                [(producer, replacement)].into_iter().collect(),
            );
            assert!(
                !chc.array_byte_register_is_authoritative(1),
                "a shifted pointer replacement cannot inherit the original read authority"
            );
        });
    }

    #[test]
    fn test_fixed_array_byte_refuses_user_named_pointer_producer() {
        const SOURCE: &str = r#"
            #![allow(dead_code)]
            mod not_slice {
                #[inline(never)]
                pub fn as_ptr(values: &[u8; 2]) -> *const u8 {
                    unsafe { values.as_ptr().add(1) }
                }
            }
            pub fn pointer(values: &[u8; 2]) -> *const u8 { not_slice::as_ptr(values) }
        "#;
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let body = find_instance_by_suffix(ctx.tcx, "pointer").callee_body().unwrap();
            assert!(body.blocks.iter().any(|block| {
                let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                    return false;
                };
                let Ok(ty) = func.ty(body.locals()) else {
                    return false;
                };
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) = ty.kind() else {
                    return false;
                };
                def.name().contains("not_slice")
            }));
            let chc = ChcCtx::new(ctx.tcx, &body, "pointer", ChcConfig::default());
            assert!(
                !chc.array_byte_register_is_authoritative(1),
                "a user function name is not an authenticated pointer-identity model"
            );
        });
    }
}
