// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native dyn pointer metadata is a typed coercion result, not a numeric
//! vtable guess. These facts describe the exact Box value bound in a frame.

use super::ChcCtx;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::shared::native_box_raw::{
    native_box_raw_pointer_field, native_dyn_pointer_pointee,
};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::mir::{Body, LocalDecl, Operand, Place, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, Ty, TyKind};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct NativeDynOrigin {
    pub dynamic: Ty,
    pub concrete: Ty,
    pub carrier: Ty,
    pub vtable: u64,
    pub allocation: u32,
    pub constant_callable: bool,
    pub origin: (u64, usize),
}

impl NativeDynOrigin {
    pub(in crate::codegen_ay::chc) fn vtable_expr(&self) -> Expr {
        Expr::bitvec_const(self.vtable, 64)
    }
}

fn plain(operand: &Operand) -> Option<&Place> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        _ => None,
    }
}

mod birth;
mod borrow;
mod receiver;

impl ChcCtx<'_, '_> {
    /// A dyn pointer's logical vtable ID is not its native vtable address.
    /// Cross-type transmute needs a physical byte image; neither a widened
    /// data word nor a logical datatype supplies one. The checked native Box
    /// cast has a separate operation and is not a raw-byte transmute.
    pub(in crate::codegen_ay::chc) fn native_dyn_transmute_needs_bytes(
        &self,
        source: Ty,
        target: Ty,
    ) -> bool {
        let Some(source) = self.normalized_box_ty(self.resolve_body_ty(source)) else {
            return true;
        };
        let Some(target) = self.normalized_box_ty(self.resolve_body_ty(target)) else {
            return true;
        };
        if source == target {
            return false;
        }
        [source, target].into_iter().any(|ty| {
            native_dyn_pointer_pointee(self.tcx, ty).is_some()
                && ty.layout().ok().is_none_or(|layout| layout.shape().size.bytes() != 8)
        })
    }

    pub(in crate::codegen_ay::chc) fn inline_native_dyn_origin(
        &self,
        operand: &Operand,
        locals: &[LocalDecl],
    ) -> Option<NativeDynOrigin> {
        let place = plain(operand)?;
        let origin =
            self.inline_walk_frames.last()?.native_dyn_origins.get(&place.local)?.clone()?;
        self.native_dyn_projection(&origin, locals, place)?;
        Some(origin)
    }

    /// A projection may only peel native pointer carrier fields at offset zero.
    /// A dereference of a dyn data pointer is not such a projection.
    fn native_dyn_projection(
        &self,
        origin: &NativeDynOrigin,
        locals: &[LocalDecl],
        place: &Place,
    ) -> Option<()> {
        if place.projection.len() > 32 {
            return None;
        }
        let mut ty = self.normalized_box_ty(self.resolve_body_ty(locals.get(place.local)?.ty))?;
        self.native_dyn_origin_matches(origin, ty).then_some(())?;
        for projection in &place.projection {
            match projection {
                ProjectionElem::Deref => {
                    let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = ty.kind() else {
                        return None;
                    };
                    if matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
                        return None;
                    }
                    ty = pointee;
                }
                ProjectionElem::Field(index, field) => {
                    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
                    let allowed = if def.is_box() {
                        *index == 0
                    } else {
                        native_box_raw_pointer_field(self.tcx, def, &args)
                            .is_some_and(|(pointer, _)| pointer == *index)
                    };
                    if !allowed {
                        return None;
                    }
                    ty = self.normalized_box_ty(*field)?;
                    self.native_dyn_origin_matches(origin, ty).then_some(())?;
                }
                _ => return None,
            }
        }
        Some(())
    }

    pub(in crate::codegen_ay::chc) fn native_dyn_field_value(
        &self,
        locals: &[LocalDecl],
        place: &Place,
        local_exprs: &std::collections::HashMap<usize, Expr>,
    ) -> Option<Expr> {
        let origin = self.inline_native_dyn_origin(&Operand::Copy(place.clone()), locals)?;
        if place.projection.is_empty() {
            return None;
        }
        let value = local_exprs.get(&place.local)?;
        // The data word is licensed by the native coercion and pointer view.
        // It is never constructed by extending a pointee's logical value.
        (value.sort() == &Self::translate_ty(locals.get(place.local)?.ty)?
            && value.sort().bitvec_width() == Some(64)
            && self.native_dyn_origin_matches(&origin, place.ty(locals).ok()?))
        .then(|| value.clone())
    }

    pub(in crate::codegen_ay::chc) fn invalidate_native_dyn_origin(
        &mut self,
        origin: (u64, usize),
    ) {
        let mut revoked = false;
        for frame in &mut self.inline_walk_frames {
            for binding in frame.native_dyn_origins.values_mut() {
                if binding.as_ref().is_some_and(|binding| binding.origin == origin) {
                    *binding = None;
                    revoked = true;
                }
            }
        }
        if revoked {
            self.record_sound_fallback_reason("native_dyn_metadata_revoked");
        }
    }

    /// A write that might reach the payload revokes both its metadata binding
    /// and the immutable constant-callable shortcut. A proven different object
    /// preserves them. Unknown addresses never establish disjointness.
    pub(in crate::codegen_ay::chc) fn note_native_dyn_memory_write(&mut self, address: &Expr) {
        if !self
            .inline_walk_frames
            .iter()
            .any(|frame| frame.native_dyn_origins.values().any(Option::is_some))
        {
            return;
        }
        let allocation =
            crate::codegen_ay::chc::expr::codegen_expr_box_deref::legacy_pointer_tree_is_bounded(
                address,
            )
            .then(|| Self::try_extract_constant_addr(address))
            .flatten()
            .map(|(id, _)| id);
        let mut revoked = false;
        for frame in &mut self.inline_walk_frames {
            for binding in frame.native_dyn_origins.values_mut() {
                if binding.as_ref().is_some_and(|origin| allocation != Some(origin.allocation))
                    && allocation.is_some()
                {
                    continue;
                }
                revoked |= binding.is_some();
                *binding = None;
            }
        }
        if revoked {
            self.record_sound_fallback_reason("native_dyn_payload_write_unresolved");
        }
    }

    pub(in crate::codegen_ay::chc) fn set_native_dyn_binding(
        &mut self,
        locals: &[LocalDecl],
        local: usize,
        binding: Option<NativeDynOrigin>,
    ) -> Option<NativeDynOrigin> {
        let binding = binding.filter(|binding| {
            locals.get(local).is_some_and(|decl| self.native_dyn_origin_matches(binding, decl.ty))
        });
        let old = self
            .inline_walk_frames
            .last()
            .and_then(|frame| frame.native_dyn_origins.get(&local))
            .cloned()
            .flatten();
        if let Some(old) = old
            && Some(&old) != binding.as_ref()
        {
            self.invalidate_native_dyn_origin(old.origin);
        }
        if let Some(frame) = self.inline_walk_frames.last_mut() {
            let previous = frame.native_dyn_origins.entry(local).or_insert_with(|| binding.clone());
            if *previous != binding {
                *previous = None;
            }
            return previous.clone();
        }
        None
    }

    pub(in crate::codegen_ay::chc) fn forget_native_dyn_binding(&mut self, local: usize) {
        if let Some(binding) = self
            .inline_walk_frames
            .last_mut()
            .and_then(|frame| frame.native_dyn_origins.get_mut(&local))
        {
            *binding = None;
        }
    }

    /// The call first invalidates the old carrier and reserves an unknown
    /// result. A previously unknown destination never gains authority from a
    /// later speculative branch. Only this call's fresh exact return may seed it.
    pub(in crate::codegen_ay::chc) fn begin_native_dyn_return(
        &mut self,
        locals: &[LocalDecl],
        local: usize,
    ) -> bool {
        self.forget_native_drop_address(local);
        let native = locals.get(local).is_some_and(|decl| {
            self.normalized_box_ty(self.resolve_body_ty(decl.ty))
                .and_then(|ty| native_dyn_pointer_pointee(self.tcx, ty))
                .is_some()
        });
        if !native {
            return false;
        }
        let fresh = self
            .inline_walk_frames
            .last()
            .is_some_and(|frame| !frame.native_dyn_origins.contains_key(&local));
        self.set_native_dyn_binding(locals, local, None);
        fresh
    }

    pub(in crate::codegen_ay::chc) fn finish_native_dyn_return(
        &mut self,
        body: &Body,
        local: usize,
        fresh: bool,
        binding: Option<NativeDynOrigin>,
    ) -> Option<NativeDynOrigin> {
        // A raw address of this carrier can outlive its prior binding. The
        // model does not track writes through such independently stored aliases.
        let raw_exposed = body.blocks.iter().flat_map(|block| &block.statements).any(|statement| {
            matches!(&statement.kind, StatementKind::Assign(_, Rvalue::AddressOf(_, place))
                if place.local == local && !matches!(place.projection.first(), Some(ProjectionElem::Deref)))
        });
        let binding = binding.filter(|binding| {
            fresh
                && !raw_exposed
                && body
                    .locals()
                    .get(local)
                    .is_some_and(|decl| self.native_dyn_origin_matches(binding, decl.ty))
        });
        if let Some(binding) = binding {
            self.inline_walk_frames
                .last_mut()?
                .native_dyn_origins
                .insert(local, Some(binding.clone()));
            Some(binding)
        } else {
            None
        }
    }

    pub(in crate::codegen_ay::chc) fn native_dyn_carrier_write(
        &mut self,
        locals: &[LocalDecl],
        place: &Place,
    ) {
        let Some(origin) = self.inline_native_dyn_origin(
            &Operand::Copy(Place { local: place.local, projection: vec![] }),
            locals,
        ) else {
            return;
        };
        let ty = self.resolve_body_ty(locals[place.local].ty);
        let carrier = match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(..)) => true,
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
                !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)))
            }
            _ => false,
        };
        if carrier {
            self.invalidate_native_dyn_origin(origin.origin);
        }
    }

    pub(in crate::codegen_ay::chc) fn note_native_dyn_assignment(
        &mut self,
        body: &Body,
        local: usize,
        rhs: Option<&Rvalue>,
    ) -> Option<NativeDynOrigin> {
        self.note_native_drop_assignment(body, local, rhs);
        if let Some(rhs) = rhs {
            let escaping = match rhs {
                Rvalue::AddressOf(_, place) => Some(place),
                Rvalue::Ref(_, _, place) if self.last_inline_ref_was_address => Some(place),
                _ => None,
            };
            if let Some(place) = escaping
                && place.ty(body.locals()).ok().is_some_and(|ty| {
                    native_dyn_pointer_pointee(self.tcx, self.resolve_body_ty(ty)).is_some()
                })
                && let Some(origin) = self.inline_native_dyn_origin(
                    &Operand::Copy(Place { local: place.local, projection: vec![] }),
                    body.locals(),
                )
            {
                self.invalidate_native_dyn_origin(origin.origin);
            }
            if let Rvalue::Cast(_, operand, target) = rhs
                && let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) =
                    self.resolve_body_ty(*target).kind()
                && !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)))
                && native_dyn_pointer_pointee(self.tcx, pointee).is_some()
                && let Some(origin) = self.inline_native_dyn_origin(operand, body.locals())
            {
                self.invalidate_native_dyn_origin(origin.origin);
            }
        }
        if !body.locals().get(local).is_some_and(|decl| {
            self.normalized_box_ty(self.resolve_body_ty(decl.ty))
                .and_then(|ty| native_dyn_pointer_pointee(self.tcx, ty))
                .is_some()
        }) {
            return None;
        }
        let binding = rhs.and_then(|rhs| match rhs {
            Rvalue::Cast(rustc_public::mir::CastKind::Transmute, operand, target)
                if operand.ty(body.locals()).ok().is_some_and(|source| self.native_dyn_transmute_needs_bytes(source, *target)) => None,
            Rvalue::Use(operand, ..) | Rvalue::Cast(_, operand, _) => self.inline_native_dyn_origin(operand, body.locals()),
            Rvalue::CopyForDeref(place) => self.inline_native_dyn_origin(&Operand::Copy(place.clone()), body.locals()),
            Rvalue::Ref(_, _, place) if matches!(place.projection.as_slice(), [ProjectionElem::Deref])
                && matches!(self.resolve_body_ty(body.locals().get(place.local)?.ty).kind(), TyKind::RigidTy(RigidTy::RawPtr(pointee, _) | RigidTy::Ref(_, pointee, _)) if matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)))) =>
                self.inline_native_dyn_origin(&Operand::Copy(Place { local: place.local, projection: vec![] }), body.locals()),
            Rvalue::Ref(_, _, place) if !self.last_inline_ref_was_address => self.inline_native_dyn_origin(&Operand::Copy(place.clone()), body.locals()),
            _ => None,
        }).filter(|binding| body.locals().get(local).is_some_and(|decl| self.native_dyn_origin_matches(binding, decl.ty)));
        self.set_native_dyn_binding(body.locals(), local, binding)
    }
}
