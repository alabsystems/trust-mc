// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A reference selected from a field can still be an address. Identity
//! decoding needs an actual scalar value view before the next dereference.

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::PlaceResolver;
use ay_bindings::Expr;
use rustc_public::mir::{LocalDecl, Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;

pub(in crate::codegen_ay::chc) fn has_value_view(
    ctx: &mut ChcCtx<'_, '_>,
    local_exprs: &HashMap<usize, Expr>,
    place: &Place,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> bool {
    if !place.projection.iter().skip(1).any(|step| matches!(step, ProjectionElem::Deref)) {
        return true;
    }
    if place.projection.len() > 128 {
        return false;
    }
    let mut scalar_deref = None;
    for (index, step) in place.projection.iter().enumerate().skip(1) {
        if !matches!(step, ProjectionElem::Deref) {
            continue;
        }
        let prefix = Place { local: place.local, projection: place.projection[..index].to_vec() };
        let Ok(reference) = prefix.ty(locals) else { return false };
        let reference = ctx.resolve_body_ty(reference);
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = reference.kind() else { continue };
        let pointee = ctx.resolve_body_ty(pointee);
        if !matches!(
            pointee.kind(),
            TyKind::RigidTy(
                RigidTy::Bool
                    | RigidTy::Char
                    | RigidTy::Int(_)
                    | RigidTy::Uint(_)
                    | RigidTy::Float(_)
            )
        ) {
            continue;
        }
        // The prefix resolver below must contain no scalar dereference of
        // its own: this also bounds recursion for malformed projection paths.
        if scalar_deref.is_some() {
            return false;
        }
        scalar_deref = Some((prefix, reference, pointee));
    }
    let Some((prefix, reference, pointee)) = scalar_deref else { return true };
    if matches!(prefix.projection.as_slice(), [ProjectionElem::Field(0, _)])
        && locals.get(place.local).is_some_and(|decl| {
            ctx.readonly_singleton_field_is_current_value(place.local, decl.ty, reference)
        })
    {
        return true;
    }
    let Some(value) = super::place::resolve_place(ctx, local_exprs, &prefix, resolver, locals)
    else {
        return false;
    };
    // The actual native reference type supplies its canonical address sort.
    // Distinct pointee and reference representations distinguish a scalar
    // value; equal representations need the positive tuple fact above.
    let (Some(pointee_sort), Some(reference_sort)) =
        (ChcCtx::translate_ty(pointee), ChcCtx::translate_ty(reference))
    else {
        return false;
    };
    value.sort() == &pointee_sort && pointee_sort != reference_sort
}
