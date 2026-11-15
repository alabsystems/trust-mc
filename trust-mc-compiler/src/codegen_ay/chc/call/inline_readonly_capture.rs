// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Current scalar reads captured by a native closure. Keep the original
//! closure carrier (including address fields) intact and return a separate
//! typed value only at an authenticated reference-field read.

use super::ChcCtx;
use super::codegen_types::CodegenTypes;
use super::inline_readonly_ref::ReadonlyRefValue;
use super::inline_ref_arg_binding::InlineArgBinding;
use ay_bindings::Expr;
use rustc_public::mir::{Body, LocalDecl, Operand, Place, ProjectionElem};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use std::collections::HashSet;

impl ChcCtx<'_, '_> {
    pub(super) fn readonly_capture_aggregate(
        &self,
        body: &Body,
        ty: Ty,
        operands: &[Operand],
    ) -> Option<ReadonlyRefValue> {
        if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Closure(..))) || operands.len() > 128 {
            return None;
        }
        let captures = operands
            .iter()
            .enumerate()
            .filter_map(|(index, operand)| {
                let reference = self.resolve_body_ty(operand.ty(body.locals()).ok()?);
                let read = self.readonly_value(operand)?;
                self.readonly_scalar_pointee(reference)?;
                (read.ty == reference).then_some((index, reference, read.value?))
            })
            .collect::<Vec<_>>();
        (!captures.is_empty()).then(|| ReadonlyRefValue {
            ty,
            mark: self.heap_state.write_mark(),
            value: None,
            captures,
        })
    }

    pub(super) fn note_readonly_resolved_value(&mut self, local: usize, expression: &Expr) {
        let Some(mut read) = self
            .inline_walk_frames
            .last()
            .and_then(|frame| frame.readonly_ref_values.get(&local))
            .cloned()
            .flatten()
        else {
            return;
        };
        let Some(pointee) = self.readonly_scalar_pointee(read.ty) else { return };
        if read.mark != self.heap_state.write_mark()
            || Self::translate_ty(pointee).as_ref() != Some(expression.sort())
        {
            return;
        }
        if read.value.as_ref().is_some_and(|old| old != expression) {
            return;
        }
        read.value = Some(expression.clone());
        if let Some(frame) = self.inline_walk_frames.last_mut() {
            frame.readonly_ref_values.insert(local, Some(read));
        }
    }

    pub(super) fn host_readonly_capture_seed(
        &mut self,
        operand: &Operand,
        modified: &HashSet<usize>,
    ) -> Option<ReadonlyRefValue> {
        let (ty, fields) = self.host_closure_capture_operands(operand)?;
        let mut captures = Vec::new();
        let mut remaining = 16_384usize;
        if fields.len() > 128 {
            return None;
        }
        for (index, operand) in fields.iter().enumerate() {
            let reference = self.resolve_body_ty(operand.ty(self.body.locals()).ok()?);
            if self.readonly_scalar_pointee(reference).is_none()
                || !self.closure_reference_producer_is_tracked(
                    operand,
                    &mut HashSet::new(),
                    &mut remaining,
                )
            {
                continue;
            }
            // A capture is read through the same host binder as a shared
            // comparison argument. Unreported/address lanes grant no fact.
            let value = match self.bind_call_arg_for_inline(operand, modified, true) {
                InlineArgBinding::BoundReferent(value) | InlineArgBinding::ReadThrough(value) => {
                    value
                }
                _ => continue,
            };
            let read = self.readonly_ref_seed_for_value(reference, &value)?;
            captures.push((index, reference, read.value?));
        }
        (!captures.is_empty()).then(|| ReadonlyRefValue {
            ty,
            mark: self.heap_state.write_mark(),
            value: None,
            captures,
        })
    }

    pub(in crate::codegen_ay::chc) fn readonly_capture_field_value(
        &self,
        place: &Place,
        locals: &[LocalDecl],
    ) -> Option<Expr> {
        if place.projection.is_empty() || self.inline_walk_written_since_mark() {
            return None;
        }
        let root = Operand::Copy(Place { local: place.local, projection: vec![] });
        let aggregate = self.readonly_value(&root)?;
        if aggregate.captures.is_empty()
            && !matches!(aggregate.ty.kind(), TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.len() == 1)
        {
            return None;
        }
        let mut field_place = place.clone();
        let dereferenced = matches!(field_place.projection.last(), Some(ProjectionElem::Deref));
        if dereferenced {
            field_place.projection.pop();
        }
        let reference = self.resolve_body_ty(field_place.ty(locals).ok()?);
        let pointee = self.readonly_scalar_pointee(reference)?;
        if dereferenced && self.resolve_body_ty(place.ty(locals).ok()?) != pointee {
            return None;
        }
        let field = Operand::Copy(field_place);
        let read = self.readonly_value(&field)?;
        (read.ty == reference)
            .then_some(read.value?)
            .filter(|value| Self::translate_ty(pointee).as_ref() == Some(value.sort()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::callee_body::CalleeBody;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
    use rustc_public::mir::{AggregateKind, ProjectionElem, Rvalue, StatementKind};

    #[test]
    fn readonly_logical_value_cannot_supply_an_aggregate_or_dyn_pointer_image() {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // Compiler-only representation refusals: neither body is executed as
        // a native oracle. The native types supply the actual target layouts.
        with_test_ay_ctx_for_source(
            "pub trait Read {} impl Read for u64 {}\n\
             #[repr(transparent)] pub struct Word(pub u64);\n\
             pub unsafe fn image(value: &u64) -> (u32,u32) { unsafe { core::mem::transmute(value) } }\n\
             pub unsafe fn word(value: &u64) -> Word { unsafe { core::mem::transmute(value) } }\n\
             pub unsafe fn tuple_image(value: (&u64,)) -> u64 { unsafe { core::mem::transmute(value) } }\n\
             pub fn dynamic(value: &u64) -> &dyn Read { value }",
            |ctx| {
                for name in ["image", "word", "tuple_image", "dynamic"] {
                    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
                    let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
                    let cast = body
                        .blocks
                        .iter()
                        .flat_map(|b| &b.statements)
                        .find_map(|s| match &s.kind {
                            StatementKind::Assign(_, rvalue @ Rvalue::Cast(..)) => Some(rvalue),
                            _ => None,
                        })
                        .expect("native reference representation conversion");
                    let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
                    let datum = Expr::bitvec_const(19u64, 64);
                    let carrier_ty = body.locals()[1].ty;
                    let reference_ty = match carrier_ty.kind() {
                        TyKind::RigidTy(RigidTy::Tuple(fields)) => fields[0],
                        _ => carrier_ty,
                    };
                    let mut read = chc.readonly_ref_seed_for_value(reference_ty, &datum).unwrap();
                    read.ty = carrier_ty;
                    chc.inline_walk_param_readonly_ref_seeds = Some(vec![(1, read)]);
                    chc.with_inline_walk_frame(&body, |chc| {
                        let values = std::collections::HashMap::from([(1, datum)]);
                        let fields = std::collections::HashMap::new();
                        let result = super::super::inline_shared::inline_rvalue_to_expr(
                            chc, cast, &values,
                            &super::super::inline_shared::PlaceResolver::FieldMap(&fields),
                            body.locals(), Some(0));
                        let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                            .remove(name).unwrap_or_default();
                        assert!(result.is_none() && reasons.contains_key("readonly_ref_address_cast_unmodeled"),
                            "{name}: logical datum received a physical pointer view: {result:?}, {reasons:?}");
                    });
                }
            },
        );
    }

    #[test]
    fn readonly_capture_reads_expire_and_unknown_writes_dominate() {
        with_test_ay_ctx_for_source(
            "pub fn capture(value: &u64) -> bool { let f=move|| *value==19; f() }",
            |ctx| {
                let body = find_instance_by_suffix(ctx.tcx, "capture").callee_body().unwrap();
                let (destination, rhs) = body
                    .blocks
                    .iter()
                    .flat_map(|block| &block.statements)
                    .find_map(|statement| match &statement.kind {
                        StatementKind::Assign(
                            place,
                            rhs @ Rvalue::Aggregate(AggregateKind::Closure(..), _),
                        ) => Some((place.local, rhs)),
                        _ => None,
                    })
                    .unwrap();
                for unknown in [false, true] {
                    let mut chc = ChcCtx::new(ctx.tcx, &body, "capture", ChcConfig::default());
                    chc.inline_walk_param_readonly_ref_seeds = Some(vec![(
                        1,
                        chc.readonly_ref_seed_for_value(
                            body.locals()[1].ty,
                            &Expr::bitvec_const(19u64, 64),
                        )
                        .unwrap(),
                    )]);
                    chc.with_inline_walk_frame(&body, |chc| {
                        chc.note_inline_readonly_ref_assignment(&body, destination, Some(rhs));
                        let field = Place {
                            local: destination,
                            projection: vec![ProjectionElem::Field(0, body.locals()[1].ty)],
                        };
                        assert_eq!(
                            chc.readonly_capture_field_value(&field, body.locals()),
                            Some(Expr::bitvec_const(19u64, 64))
                        );
                        let mut deref = field.clone();
                        deref.projection.push(ProjectionElem::Deref);
                        assert_eq!(
                            chc.readonly_capture_field_value(&deref, body.locals()),
                            Some(Expr::bitvec_const(19u64, 64))
                        );
                        if unknown {
                            chc.note_inline_readonly_ref_assignment(&body, destination, None);
                            chc.note_inline_readonly_ref_assignment(&body, destination, Some(rhs));
                        } else {
                            chc.heap_state.note_write();
                        }
                        assert!(chc.readonly_capture_field_value(&field, body.locals()).is_none());
                        assert!(chc.readonly_capture_field_value(&deref, body.locals()).is_none());
                    });
                }
            },
        );
    }
}
