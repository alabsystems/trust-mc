// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bind RustCall's current fields with the ordinary host reference contract.
//! An earlier producer is usable only while its carrier and copied operands
//! are stable. Selected references without a readable value remain incomplete.

use ay_bindings::Expr;
use rustc_public::mir::{
    AggregateKind, Body, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;

use super::super::ChcCtx;
use super::super::inline_readonly_ref::ReadonlyRefValue;
use super::super::inline_ref_arg_binding::InlineArgBinding;

#[derive(Default)]
pub(super) struct ClosureCallArgs {
    pub values: Vec<Expr>,
    // Zero-based argument indices, re-keyed once the native ABI is known.
    address: Vec<usize>,
    referent: Vec<usize>,
    readonly: Vec<(usize, ReadonlyRefValue)>,
}

impl ClosureCallArgs {
    pub(super) fn seed(&self, ctx: &mut ChcCtx<'_, '_>, first: usize) {
        ctx.inline_walk_param_address_seeds =
            Some(self.address.iter().map(|i| i + first).collect());
        ctx.inline_walk_param_referent_seeds =
            Some(self.referent.iter().map(|i| i + first).collect());
        ctx.inline_walk_param_readonly_ref_seeds =
            Some(self.readonly.iter().map(|(i, value)| (i + first, value.clone())).collect());
    }

    pub(super) fn clear(ctx: &mut ChcCtx<'_, '_>) {
        ctx.inline_walk_param_address_seeds = None;
        ctx.inline_walk_param_referent_seeds = None;
        ctx.inline_walk_param_readonly_ref_seeds = None;
    }
}

/// No whole-body first-writer wins. Distinguish absent definitions (native
/// parameters) from invalid/ambiguous/escaped/repeated producers. The common
/// work budget bounds every recursive copy and operand validation together.
fn single_producer<'a>(
    body: &'a Body,
    local: usize,
    remaining: &mut usize,
) -> Result<Option<&'a Rvalue>, ()> {
    single_producer_inner(body, local, remaining, false)
}

fn single_producer_inner<'a>(
    body: &'a Body,
    local: usize,
    remaining: &mut usize,
    allow_shared_borrow: bool,
) -> Result<Option<&'a Rvalue>, ()> {
    // Native pre-inlining appends blocks and can jump back to an earlier
    // block number without a cycle. Check the actual graph, not its numbering.
    if body.blocks.len() > *remaining {
        return Err(());
    }
    let mut incoming = vec![0usize; body.blocks.len()];
    for block in &body.blocks {
        *remaining = remaining.checked_sub(1).ok_or(())?;
        for target in block.terminator.successors() {
            *remaining = remaining.checked_sub(1).ok_or(())?;
            let count = incoming.get_mut(target).ok_or(())?;
            *count = count.checked_add(1).ok_or(())?;
        }
    }
    let mut ready = incoming
        .iter()
        .enumerate()
        .filter_map(|(i, count)| (*count == 0).then_some(i))
        .collect::<Vec<_>>();
    let mut visited = 0usize;
    while let Some(index) = ready.pop() {
        *remaining = remaining.checked_sub(1).ok_or(())?;
        visited += 1;
        for target in body.blocks[index].terminator.successors() {
            *remaining = remaining.checked_sub(1).ok_or(())?;
            incoming[target] = incoming[target].checked_sub(1).ok_or(())?;
            if incoming[target] == 0 {
                ready.push(target);
            }
        }
    }
    if visited != body.blocks.len() {
        return Err(());
    }
    let mut producer = None;
    for block in &body.blocks {
        *remaining = remaining.checked_sub(1).ok_or(())?;
        if matches!(&block.terminator.kind, TerminatorKind::Call { destination, .. } if destination.local == local)
        {
            return Err(());
        }
        for statement in &block.statements {
            *remaining = remaining.checked_sub(1).ok_or(())?;
            match &statement.kind {
                StatementKind::Assign(place, rhs) => {
                    let permitted_shared = allow_shared_borrow
                        && matches!(rhs,
                        Rvalue::Ref(_, rustc_public::mir::BorrowKind::Shared, source)
                            if source.local == local && source.projection.is_empty());
                    if !permitted_shared
                        && matches!(rhs, Rvalue::Ref(_, _, source) | Rvalue::AddressOf(_, source)
                        if source.local == local && !matches!(source.projection.first(), Some(ProjectionElem::Deref)))
                    {
                        return Err(());
                    }
                    if place.local == local {
                        if !place.projection.is_empty() || producer.is_some() {
                            return Err(());
                        }
                        producer = Some(rhs);
                    }
                }
                StatementKind::SetDiscriminant { place, .. } if place.local == local => {
                    return Err(());
                }
                _ => {}
            }
        }
    }
    Ok(producer)
}

fn stable_operand(
    body: &Body,
    operand: &Operand,
    remaining: &mut usize,
    seen: &mut HashSet<usize>,
) -> bool {
    match operand {
        Operand::Constant(_) => true,
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            if seen.len() >= 32 || !seen.insert(place.local) {
                return false;
            }
            match single_producer(body, place.local, remaining) {
                Ok(Some(Rvalue::Use(source, ..))) => stable_operand(body, source, remaining, seen),
                Ok(Some(Rvalue::Ref(_, _, source))) => source.projection.is_empty(),
                Ok(None) => (1..=body.arg_locals().len()).contains(&place.local),
                _ => false,
            }
        }
        _ => false,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc::call) fn host_closure_capture_operands(
        &self,
        operand: &Operand,
    ) -> Option<(rustc_public::ty::Ty, Vec<Operand>)> {
        let seed_ty = self.resolve_body_ty(operand.ty(self.body.locals()).ok()?);
        let closure_ty = match seed_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => self.resolve_body_ty(pointee),
            _ => seed_ty,
        };
        let TyKind::RigidTy(RigidTy::Closure(expected, expected_args)) = closure_ty.kind() else {
            return None;
        };
        let mut current = operand.clone();
        let mut seen = HashSet::new();
        let mut remaining = 16_384usize;
        loop {
            let (Operand::Copy(place) | Operand::Move(place)) = &current else { return None };
            if !place.projection.is_empty() || seen.len() >= 32 || !seen.insert(place.local) {
                return None;
            }
            match single_producer_inner(self.body, place.local, &mut remaining, true).ok()?? {
                Rvalue::Use(source, ..) => current = source.clone(),
                Rvalue::Ref(_, _, source) if source.projection.is_empty() => {
                    current = Operand::Copy(source.clone())
                }
                Rvalue::Aggregate(AggregateKind::Closure(def, args), fields)
                    if *def == expected && *args == expected_args =>
                {
                    if fields.len() > 128 {
                        return None;
                    }
                    return Some((seed_ty, fields.clone()));
                }
                _ => return None,
            }
        }
    }

    pub(in crate::codegen_ay::chc::call) fn bind_rustcall_single_reference(
        &mut self,
        tuple: &Operand,
        modified: &HashSet<usize>,
    ) -> Option<(InlineArgBinding, Option<ReadonlyRefValue>)> {
        let mut arguments = self.extract_closure_call_args(tuple, modified)?;
        if arguments.values.len() != 1 {
            return None;
        }
        let value = arguments.values.pop()?;
        let read = arguments.readonly.pop().map(|(_, value)| value);
        Some((
            if arguments.address.contains(&0) {
                InlineArgBinding::BoundAddress(value)
            } else if arguments.referent.contains(&0) {
                InlineArgBinding::BoundReferent(value)
            } else {
                InlineArgBinding::Bound(value)
            },
            read,
        ))
    }

    fn validated_closure_arg_fields(&self, operand: &Operand) -> Option<Vec<Operand>> {
        let mut operand = operand;
        let mut seen = HashSet::new();
        let mut remaining = 16_384usize;
        loop {
            let (Operand::Copy(place) | Operand::Move(place)) = operand else { return None };
            if !place.projection.is_empty() || seen.len() >= 32 || !seen.insert(place.local) {
                return None;
            }
            match single_producer(self.body, place.local, &mut remaining).ok()?? {
                Rvalue::Use(source, ..) => operand = source,
                Rvalue::Aggregate(AggregateKind::Tuple, fields) => {
                    if fields.iter().all(|field| {
                        stable_operand(self.body, field, &mut remaining, &mut HashSet::new())
                    }) {
                        return Some(fields.clone());
                    }
                    return None;
                }
                _ => return None,
            }
        }
    }

    pub(super) fn extract_closure_call_arg_operands(&self, arg_tuple: &Operand) -> Vec<Operand> {
        if let Some(fields) = self.validated_closure_arg_fields(arg_tuple) {
            return fields;
        }
        let (Operand::Copy(place) | Operand::Move(place)) = arg_tuple else { return Vec::new() };
        let Ok(ty) = arg_tuple.ty(self.body.locals()) else { return Vec::new() };
        let TyKind::RigidTy(RigidTy::Tuple(fields)) = self.resolve_body_ty(ty).kind() else {
            return Vec::new();
        };
        if fields.len() > 128 || place.projection.len() >= 128 {
            return Vec::new();
        }
        fields
            .iter()
            .enumerate()
            .map(|(index, ty)| {
                let mut field = place.clone();
                field.projection.push(ProjectionElem::Field(index, *ty));
                Operand::Copy(field)
            })
            .collect()
    }

    pub(super) fn extract_closure_call_args(
        &mut self,
        arg_tuple: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<ClosureCallArgs> {
        let ty = self.resolve_body_ty(arg_tuple.ty(self.body.locals()).ok()?);
        let TyKind::RigidTy(RigidTy::Tuple(types)) = ty.kind() else { return None };
        let operands = self.extract_closure_call_arg_operands(arg_tuple);
        if operands.len() != types.len() {
            return None;
        }
        let mut result = ClosureCallArgs::default();
        let mut remaining = 16_384usize;
        for (index, operand) in operands.iter().enumerate() {
            let ty = self.resolve_body_ty(operand.ty(self.body.locals()).ok()?);
            if ty != self.resolve_body_ty(types[index]) {
                self.record_sound_fallback_reason("closure_call_arg_type_mismatch");
                return None;
            }
            // A copied reference FIELD is not itself a scalar read. Legacy
            // ref-target resolution can erase that distinction, so do not
            // mint a fresh read certificate from that unsupported producer.
            if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(..)))
                && !self.closure_reference_producer_is_tracked(
                    operand,
                    &mut HashSet::new(),
                    &mut remaining,
                )
            {
                self.record_sound_fallback_reason("closure_ref_value_producer_unproven");
                return None;
            }
            let (value, referent) =
                match self.bind_call_arg_for_inline(operand, modified_locals, false) {
                    InlineArgBinding::Bound(value) => (value, false),
                    InlineArgBinding::BoundAddress(value) => {
                        result.address.push(index);
                        (value, false)
                    }
                    InlineArgBinding::BoundReferent(value)
                    | InlineArgBinding::ReadThrough(value) => {
                        result.referent.push(index);
                        (value, true)
                    }
                    InlineArgBinding::Refused(reason) => {
                        self.record_sound_fallback_reason(reason);
                        return None;
                    }
                    InlineArgBinding::Unresolved => {
                        self.record_sound_fallback_reason("closure_call_arg_unresolved");
                        return None;
                    }
                };
            if referent && let Some(seed) = self.readonly_ref_seed_for_value(ty, &value) {
                result.readonly.push((index, seed));
            }
            result.values.push(value);
        }
        Some(result)
    }

    pub(in crate::codegen_ay::chc::call) fn closure_reference_producer_is_tracked(
        &self,
        operand: &Operand,
        seen: &mut HashSet<usize>,
        remaining: &mut usize,
    ) -> bool {
        match operand {
            Operand::Constant(_) => true,
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                if seen.len() >= 32 || !seen.insert(place.local) {
                    return false;
                }
                match single_producer(self.body, place.local, remaining) {
                    Ok(Some(Rvalue::Ref(_, _, source))) if source.projection.is_empty() => true,
                    Ok(Some(Rvalue::Ref(_, _, source)))
                        if matches!(source.projection.as_slice(), [ProjectionElem::Deref]) =>
                    {
                        self.closure_reference_producer_is_tracked(
                            &Operand::Copy(Place { local: source.local, projection: vec![] }),
                            seen,
                            remaining,
                        )
                    }
                    Ok(Some(Rvalue::Use(source, ..))) => {
                        self.closure_reference_producer_is_tracked(source, seen, remaining)
                    }
                    Ok(Some(Rvalue::CopyForDeref(source))) if source.projection.is_empty() => self
                        .closure_reference_producer_is_tracked(
                            &Operand::Copy(source.clone()),
                            seen,
                            remaining,
                        ),
                    // A native reference parameter's auxiliary pointee is an
                    // actual host read. The structured binder still decides
                    // whether it obtained that value or only an address.
                    Ok(None) => (1..=self.body.arg_locals().len()).contains(&place.local),
                    _ => false,
                }
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests;
