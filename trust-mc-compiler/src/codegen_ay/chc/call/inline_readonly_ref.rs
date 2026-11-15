// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Typed value authority for a shared scalar reference and its RustCall
//! singleton. A pointer-width scalar needs a real binder/borrow certificate.

use super::ChcCtx;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::chc::heap_state::HeapWriteMark;
use ay_bindings::Expr;
use rustc_public::mir::{AggregateKind, Body, Mutability, Operand, ProjectionElem, Rvalue};
use rustc_public::ty::{RigidTy, Ty, TyKind};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct ReadonlyRefValue {
    pub ty: Ty,
    pub mark: HeapWriteMark,
    pub value: Option<Expr>,
    pub captures: Vec<(usize, Ty, Expr)>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::callee_body::CalleeBody;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
    use rustc_public::mir::{Place, StatementKind};

    #[test]
    fn readonly_tuple_certificates_expire_after_writes_and_unknown_assignments() {
        with_test_ay_ctx_for_source("pub fn pair(value: &u64) -> (&u64,) { (value,) }", |ctx| {
            let body = find_instance_by_suffix(ctx.tcx, "pair").callee_body().unwrap();
            let (destination, rhs) = body
                .blocks
                .iter()
                .flat_map(|block| &block.statements)
                .find_map(|statement| match &statement.kind {
                    StatementKind::Assign(
                        place,
                        rhs @ Rvalue::Aggregate(AggregateKind::Tuple, _),
                    ) => Some((place.local, rhs)),
                    _ => None,
                })
                .unwrap();
            for stale in [false, true] {
                let mut chc = ChcCtx::new(ctx.tcx, &body, "pair", ChcConfig::default());
                chc.inline_walk_param_referent_seeds = Some(vec![1]);
                let seed = chc
                    .readonly_ref_seed_for_value(body.locals()[1].ty, &Expr::bitvec_const(7u64, 64))
                    .unwrap();
                chc.inline_walk_param_readonly_ref_seeds = Some(vec![(1, seed)]);
                chc.with_inline_walk_frame(&body, |chc| {
                    let argument = Operand::Copy(Place { local: 1, projection: vec![] });
                    assert!(chc.readonly_ref_value_matches(&argument, body.locals()[1].ty));
                    chc.note_inline_readonly_ref_assignment(&body, destination, Some(rhs));
                    let tuple = Operand::Copy(Place { local: destination, projection: vec![] });
                    assert_eq!(chc.readonly_ref_call_seeds(&[tuple.clone()], &body).len(), 1);
                    if stale {
                        chc.heap_state.note_write();
                    } else {
                        chc.note_inline_readonly_ref_assignment(&body, destination, None);
                        chc.note_inline_readonly_ref_assignment(&body, destination, Some(rhs));
                    }
                    assert!(chc.readonly_ref_call_seeds(&[tuple], &body).is_empty());
                });
            }
        });
    }

    #[test]
    fn legacy_referent_tags_cannot_refresh_an_expired_readonly_value() {
        with_test_ay_ctx_for_source("pub fn pair(value: &u64) -> (&u64,) { (value,) }", |ctx| {
            let body = find_instance_by_suffix(ctx.tcx, "pair").callee_body().unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, "pair", ChcConfig::default());
            let operand = Operand::Copy(Place { local: 1, projection: vec![] });
            let seed = chc
                .readonly_ref_seed_for_value(body.locals()[1].ty, &Expr::bitvec_const(7u64, 64))
                .unwrap();
            chc.inline_walk_param_readonly_ref_seeds = Some(vec![(1, seed)]);
            chc.with_inline_walk_frame(&body, |chc| {
                assert!(chc.readonly_ref_value_matches(&operand, body.locals()[1].ty));
                chc.heap_state.note_write();
                assert!(chc.inline_walk_operand_is_referent(&operand));
                assert!(chc.readonly_ref_call_seeds(&[operand.clone()], &body).is_empty());
                chc.inline_walk_param_referent_seeds = Some(vec![1]);
                chc.with_inline_walk_frame(&body, |chc| {
                    assert!(chc.inline_walk_operand_is_referent(&operand));
                    assert!(!chc.readonly_ref_value_matches(&operand, body.locals()[1].ty));
                });
            });
        });
    }

    #[test]
    fn readonly_rustcall_field_and_copy_keep_only_the_current_read() {
        with_test_ay_ctx_for_source("pub fn pair(value: &u64) -> (&u64,) { (value,) }", |ctx| {
            let original = find_instance_by_suffix(ctx.tcx, "pair").callee_body().unwrap();
            let mut locals = original.locals().to_vec();
            locals.push(locals[1].clone());
            let body = Body::new(
                original.blocks.clone(),
                locals,
                original.arg_locals().len(),
                original.var_debug_info.clone(),
                None,
                original.span,
            );
            let copy = body.locals().len();
            let copy = copy - 1;
            let rhs = body
                .blocks
                .iter()
                .flat_map(|block| &block.statements)
                .find_map(|statement| match &statement.kind {
                    StatementKind::Assign(_, rhs @ Rvalue::Aggregate(AggregateKind::Tuple, _)) => {
                        Some(rhs.clone())
                    }
                    _ => None,
                })
                .unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, "pair", ChcConfig::default());
            let reference = body.locals()[1].ty;
            chc.inline_walk_param_readonly_ref_seeds = Some(vec![(
                1,
                chc.readonly_ref_seed_for_value(reference, &Expr::bitvec_const(19u64, 64)).unwrap(),
            )]);
            chc.with_inline_walk_frame(&body, |chc| {
                chc.note_inline_readonly_ref_assignment(&body, 0, Some(&rhs));
                let field = Operand::Copy(Place {
                    local: 0,
                    projection: vec![ProjectionElem::Field(0, reference)],
                });
                assert!(chc.readonly_ref_value_matches(&field, reference));
                let use_field = crate::rustc_compat::rvalue_use!(Rvalue::Use(field.clone()));
                chc.note_inline_readonly_ref_assignment(&body, copy, Some(&use_field));
                chc.tag_inline_walk_referent_local(copy);
                let copied = Operand::Copy(Place { local: copy, projection: vec![] });
                assert!(chc.readonly_ref_value_matches(&copied, reference));
                assert_eq!(chc.readonly_ref_call_seeds(&[field.clone()], &body).len(), 1);
                chc.heap_state.note_write();
                assert!(!chc.readonly_ref_value_matches(&field, reference));
                assert!(!chc.readonly_ref_value_matches(&copied, reference));
                assert!(chc.readonly_ref_call_seeds(&[field], &body).is_empty());
            });
        });
    }
}

impl ChcCtx<'_, '_> {
    pub(super) fn readonly_scalar_pointee(&self, ty: Ty) -> Option<Ty> {
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, Mutability::Not)) =
            self.resolve_body_ty(ty).kind()
        else {
            return None;
        };
        let pointee = self.resolve_body_ty(pointee);
        matches!(
            pointee.kind(),
            TyKind::RigidTy(
                RigidTy::Bool
                    | RigidTy::Char
                    | RigidTy::Int(_)
                    | RigidTy::Uint(_)
                    | RigidTy::Float(_)
            )
        )
        .then_some(pointee)
    }

    pub(super) fn readonly_ref_seed(&self, ty: Ty) -> Option<ReadonlyRefValue> {
        self.readonly_scalar_pointee(ty)?;
        Some(ReadonlyRefValue {
            ty: self.resolve_body_ty(ty),
            mark: self.heap_state.write_mark(),
            value: None,
            captures: vec![],
        })
    }

    pub(super) fn readonly_ref_seed_for_value(
        &self,
        ty: Ty,
        value: &Expr,
    ) -> Option<ReadonlyRefValue> {
        let pointee = self.readonly_scalar_pointee(ty)?;
        if Self::translate_ty(pointee).as_ref() != Some(value.sort()) {
            return None;
        }
        let mut seed = self.readonly_ref_seed(ty)?;
        seed.value = Some(value.clone());
        Some(seed)
    }

    pub(super) fn readonly_value(&self, operand: &Operand) -> Option<ReadonlyRefValue> {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else { return None };
        let mut value =
            self.inline_walk_frames.last()?.readonly_ref_values.get(&place.local)?.clone()?;
        if value.mark != self.heap_state.write_mark() {
            return None;
        }
        if let Some((field, field_ty)) = match place.projection.as_slice() {
            [ProjectionElem::Field(field, ty)]
            | [ProjectionElem::Deref, ProjectionElem::Field(field, ty)] => {
                Some((*field, self.resolve_body_ty(*ty)))
            }
            _ => None,
        } && let Some((_, _, datum)) =
            value.captures.iter().find(|(index, ty, _)| *index == field && *ty == field_ty)
        {
            let mut read = self.readonly_ref_seed_for_value(field_ty, datum)?;
            read.mark = value.mark;
            return Some(read);
        }
        if let [ProjectionElem::Field(0, field_ty)] = place.projection.as_slice() {
            let TyKind::RigidTy(RigidTy::Tuple(fields)) = value.ty.kind() else { return None };
            let field_ty = self.resolve_body_ty(*field_ty);
            if fields.as_slice() != [field_ty] || self.readonly_scalar_pointee(field_ty).is_none() {
                return None;
            }
            value.ty = field_ty;
            return Some(value);
        }
        if !place.projection.is_empty() {
            return None;
        }
        (value.mark == self.heap_state.write_mark()
            && (self.readonly_scalar_pointee(value.ty).is_none()
                || self.inline_walk_operand_is_referent(operand)))
        .then_some(value)
    }

    pub(in crate::codegen_ay::chc) fn readonly_ref_value_matches(
        &self,
        operand: &Operand,
        reference: Ty,
    ) -> bool {
        self.readonly_value(operand).is_some_and(|value| {
            value.ty == self.resolve_body_ty(reference)
                && self.readonly_scalar_pointee(value.ty).is_some()
        })
    }

    pub(super) fn readonly_ref_call_seeds(
        &self,
        args: &[Operand],
        callee: &Body,
    ) -> Vec<(usize, ReadonlyRefValue)> {
        args.iter()
            .enumerate()
            .filter_map(|(i, operand)| {
                let mut value = self.readonly_value(operand)?;
                let param = self.resolve_body_ty(callee.locals().get(i + 1)?.ty);
                if value.ty != param {
                    if !value.captures.is_empty()
                        && matches!(param.kind(), TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) if self.resolve_body_ty(pointee) == value.ty) {
                        value.ty = param;
                        return Some((i + 1, value));
                    }
                    // Native RustCall can flatten the actual one-field tuple
                    // into its exact element parameter. An ordinary tuple
                    // parameter keeps its own type and certificate.
                    let TyKind::RigidTy(RigidTy::Tuple(fields)) = value.ty.kind() else {
                        return None;
                    };
                    if fields.as_slice() != [param] || self.readonly_scalar_pointee(param).is_none()
                    {
                        return None;
                    }
                    value.ty = param;
                }
                Some((i + 1, value))
            })
            .collect()
    }

    pub(super) fn readonly_singleton_field_is_current_value(
        &self,
        local: usize,
        root_ty: Ty,
        field_ty: Ty,
    ) -> bool {
        let operand = Operand::Copy(rustc_public::mir::Place { local, projection: vec![] });
        self.readonly_value(&operand).is_some_and(|value| {
            value.ty == self.resolve_body_ty(root_ty)
                && matches!(value.ty.kind(), TyKind::RigidTy(RigidTy::Tuple(fields))
                    if fields.as_slice() == [self.resolve_body_ty(field_ty)])
                && self.readonly_scalar_pointee(field_ty).is_some()
        })
    }

    pub(super) fn note_inline_readonly_ref_assignment(
        &mut self,
        body: &Body,
        destination: usize,
        rhs: Option<&Rvalue>,
    ) {
        if let Some(Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)) = rhs
            && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
            && let Some(frame) = self.inline_walk_frames.last_mut()
            && frame.readonly_ref_values.contains_key(&place.local)
        {
            frame.readonly_ref_values.insert(place.local, None);
        }
        let Some(decl) = body.locals().get(destination) else { return };
        let ty = self.resolve_body_ty(decl.ty);
        let value = rhs.and_then(|rhs| match rhs {
            Rvalue::Ref(_, _, place) if !self.last_inline_ref_was_address => {
                if place.projection.is_empty()
                    && let Some(mut aggregate) = self.readonly_value(&Operand::Copy(place.clone()))
                    && !aggregate.captures.is_empty()
                    && matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) if self.resolve_body_ty(pointee) == aggregate.ty) {
                    aggregate.ty = ty;
                    return Some(aggregate);
                }
                let pointee = self.readonly_scalar_pointee(ty)?;
                let source_ty = self.resolve_body_ty(place.ty(body.locals()).ok()?);
                let complete_value = place.projection.is_empty()
                    || (matches!(place.projection.as_slice(), [ProjectionElem::Deref])
                        && self.readonly_ref_value_matches(
                            &Operand::Copy(rustc_public::mir::Place {
                                local: place.local,
                                projection: vec![],
                            }),
                            ty,
                        ));
                (complete_value && source_ty == pointee)
                    .then(|| self.readonly_ref_seed(ty))
                    .flatten()
            }
            Rvalue::Use(operand, ..) => self.readonly_value(operand).filter(|value| value.ty == ty),
            Rvalue::Aggregate(AggregateKind::Closure(_, _), operands) => {
                self.readonly_capture_aggregate(body, ty, operands)
            }
            Rvalue::Aggregate(AggregateKind::Tuple, operands) => {
                let [operand] = operands.as_slice() else { return None };
                let TyKind::RigidTy(RigidTy::Tuple(fields)) = ty.kind() else { return None };
                let mut value = self.readonly_value(operand)?;
                if fields.as_slice() != [value.ty]
                    || !self.readonly_ref_value_matches(operand, value.ty)
                {
                    return None;
                }
                value.ty = ty;
                Some(value)
            }
            _ => None,
        });
        if let Some(frame) = self.inline_walk_frames.last_mut() {
            // Unknown or conflicting writes dominate across shared arms.
            let entry =
                frame.readonly_ref_values.entry(destination).or_insert_with(|| value.clone());
            if *entry != value {
                *entry = None;
            }
        }
    }
}
