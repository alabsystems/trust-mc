// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Metadata transport through actual native Box casts and dyn reborrows.

use super::{ChcCtx, NativeDynOrigin, plain};
use rustc_public::mir::{BorrowKind, Operand, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, Ty, TyKind};

fn direct_dynamic(ty: Ty) -> Option<Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _))
            if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) =>
        {
            Some(inner)
        }
        _ => None,
    }
}

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn host_native_dyn_receiver_origin(
        &self,
        operand: &Operand,
    ) -> Option<NativeDynOrigin> {
        if !self.inline_walk_frames.is_empty() {
            return None;
        }
        let place = plain(operand)?;
        if !place.projection.is_empty() {
            return None;
        }
        self.native_receiver_local(place.local, &mut Vec::new(), &mut 16_384)
    }

    fn native_receiver_local(
        &self,
        local: usize,
        seen: &mut Vec<usize>,
        budget: &mut usize,
    ) -> Option<NativeDynOrigin> {
        *budget = budget.checked_sub(1)?;
        if local <= self.body.arg_locals().len() || seen.len() >= 32 || seen.contains(&local) {
            return None;
        }
        seen.push(local);
        let ty = self.normalized_box_ty(self.resolve_body_ty(self.body.locals().get(local)?.ty))?;
        let dynamic = direct_dynamic(ty)?;
        // A borrow/address of carrier storage can mutate the metadata behind
        // this local. A borrow of the pointed-to payload is a different event.
        for statement in self.body.blocks.iter().flat_map(|block| &block.statements) {
            *budget = budget.checked_sub(1)?;
            if matches!(&statement.kind,
                StatementKind::Assign(_, Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p))
                if p.local == local && p.projection.is_empty())
            {
                return None;
            }
        }
        let rhs = super::birth::definition(self.body, local)?;
        let origin = match rhs {
            Rvalue::Use(operand, ..) => {
                let source = plain(operand)?;
                if !source.projection.is_empty()
                    || self.normalized_box_ty(
                        self.resolve_body_ty(source.ty(self.body.locals()).ok()?),
                    )? != ty
                {
                    return None;
                }
                self.native_receiver_local(source.local, seen, budget)?
            }
            Rvalue::Ref(_, kind, source)
                if source.projection.as_slice() == [ProjectionElem::Deref]
                    && !matches!(kind, BorrowKind::Fake(_))
                    && matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(..))) =>
            {
                let source_ty = self.normalized_box_ty(
                    self.resolve_body_ty(self.body.locals().get(source.local)?.ty),
                )?;
                if direct_dynamic(source_ty)? != dynamic {
                    return None;
                }
                self.native_receiver_local(source.local, seen, budget)?
            }
            #[cfg(all(trust_toolchain, version("1.101")))]
            Rvalue::Cast(rustc_public::mir::CastKind::BoxDerefTransmute, operand, target)
                if self.normalized_box_ty(self.resolve_body_ty(*target))? == ty =>
            {
                self.host_native_dyn_box_deref_origin(operand, *target)?.2
            }
            _ => return None,
        };
        (origin.dynamic == dynamic).then_some(origin)
    }
}
