// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Can a shared owner handle reach mutable element storage?
//!
//! Actual Vec storage erases its element type: the held RawVecInner carries
//! NonNull<u8>, with T retained only by PhantomData<T>. The ordinary declared-
//! field staleness walk cannot recover that allocation's T from its fields.
//! Authenticate the Vec definition before inspecting its declared element and
//! allocator arguments. Other ADTs retain their actual declared fields.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::HashMap;

use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};

use super::ChcCtx;

/// One prescan's resolved-type answers. Remaining depth is part of the key:
/// an answer with more traversal room cannot excuse an exhausted query.
pub(in crate::codegen_ay::chc) type VecBufferTypeMemo = HashMap<(Ty, u8), bool>;

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn vec_shared_type_can_change_buffer(
        &self,
        ty: Ty,
        memo: &mut VecBufferTypeMemo,
    ) -> bool {
        self.vec_shared_type_can_change_buffer_at(ty, 12, memo)
    }

    fn vec_shared_type_can_change_buffer_at(
        &self,
        ty: Ty,
        depth: u8,
        memo: &mut VecBufferTypeMemo,
    ) -> bool {
        let ty = self.resolve_body_ty(ty);
        if let Some(&answer) = memo.get(&(ty, depth)) {
            return answer;
        }
        if depth == 0 {
            memo.insert((ty, depth), true);
            return true;
        }
        // Preserve the existing actual-type predicate for ordinary Cell,
        // RefCell, Mutex and pointers to their storage, including unresolved
        // parameters and opaque/deep types, which already fail toward true.
        if crate::codegen_ay::foreign_defs::ty_copy_can_go_stale(self.tcx, ty) {
            memo.insert((ty, depth), true);
            return true;
        }
        let answer = match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let actual_vec =
                    crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
                        self.tcx,
                        rustc_internal::internal(self.tcx, def.def_id()),
                        &["vec", "Vec"],
                    );
                if actual_vec && !matches!(args.0.first(), Some(GenericArgKind::Type(_))) {
                    true
                } else {
                    // Only authenticated Vec gets this ownership edge. A
                    // same-named user ADT with PhantomData<Cell<T>> has no
                    // such allocation ownership merely because of its name.
                    (actual_vec
                        && args.0.iter().any(|arg| {
                            matches!(arg, GenericArgKind::Type(inner)
                            if self.vec_shared_type_can_change_buffer_at(*inner, depth - 1, memo))
                        }))
                        || def.variants().into_iter().any(|variant| {
                            variant.fields().into_iter().any(|field| {
                                crate::codegen_ay::shared::mono_ty::field_ty(&field, &args)
                                    .is_none_or(|field_ty| {
                                        self.vec_shared_type_can_change_buffer_at(
                                            field_ty,
                                            depth - 1,
                                            memo,
                                        )
                                    })
                            })
                        })
                }
            }
            TyKind::RigidTy(
                RigidTy::Ref(_, inner, _)
                | RigidTy::RawPtr(inner, _)
                | RigidTy::Slice(inner)
                | RigidTy::Array(inner, _)
                | RigidTy::Pat(inner, _),
            ) => self.vec_shared_type_can_change_buffer_at(inner, depth - 1, memo),
            TyKind::RigidTy(RigidTy::Tuple(fields)) => fields
                .into_iter()
                .any(|field| self.vec_shared_type_can_change_buffer_at(field, depth - 1, memo)),
            TyKind::RigidTy(
                RigidTy::Bool
                | RigidTy::Char
                | RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_)
                | RigidTy::Never
                | RigidTy::Str
                | RigidTy::Foreign(_)
                | RigidTy::FnDef(..)
                | RigidTy::FnPtr(_),
            ) => false,
            _ => true,
        };
        memo.insert((ty, depth), answer);
        answer
    }
}
