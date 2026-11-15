// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Closed native callable borrows of owner storage. The owner value is read
//! separately; this certificate never identifies its storage with its payload.

use super::{ChcCtx, plain};
use crate::codegen_ay::shared::{
    native_box_call::native_global_dyn_box_call, native_box_drop::native_global_box_pointee,
};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use std::collections::{HashMap, HashSet};

fn reference_box(ctx: &ChcCtx<'_, '_>, body: &Body, local: usize) -> Option<Ty> {
    let ty = ctx.normalized_box_ty(ctx.resolve_body_ty(body.locals().get(local)?.ty))?;
    let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = ty.kind() else {
        return None;
    };
    matches!(
        native_global_box_pointee(ctx.tcx, inner)?.kind(),
        TyKind::RigidTy(RigidTy::Dynamic(..))
    )
    .then_some(inner)
}
fn use_operand(operand: &Operand, aliases: &HashSet<Local>) -> bool {
    plain(operand).is_some_and(|place| aliases.contains(&place.local))
}
fn use_rvalue(rhs: &Rvalue, aliases: &HashSet<Local>) -> bool {
    match rhs {
        Rvalue::AddressOf(_, p)
        | Rvalue::CopyForDeref(p)
        | Rvalue::Discriminant(p)
        | Rvalue::Len(p)
        | Rvalue::Ref(_, _, p) => aliases.contains(&p.local),
        #[cfg(trust_toolchain)]
        Rvalue::Reborrow(_, _, p) => aliases.contains(&p.local),
        Rvalue::Aggregate(_, args) => args.iter().any(|arg| use_operand(arg, aliases)),
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            use_operand(a, aliases) || use_operand(b, aliases)
        }
        Rvalue::Cast(_, arg, _)
        | Rvalue::Repeat(arg, _)
        | Rvalue::UnaryOp(_, arg)
        | Rvalue::Use(arg, ..) => use_operand(arg, aliases),
        #[cfg(not(trust_toolchain))]
        Rvalue::ShallowInitBox(arg, _) => use_operand(arg, aliases),
        Rvalue::ThreadLocalRef(_) => false,
        #[cfg(not(trust_toolchain))]
        Rvalue::NullaryOp(..) => false,
    }
}
fn spend(budget: &mut usize) -> Option<()> {
    *budget = budget.checked_sub(1)?;
    Some(())
}
fn root(
    ctx: &ChcCtx<'_, '_>,
    body: &Body,
    local: usize,
    defs: &HashMap<Local, Option<&Rvalue>>,
    path: &mut Vec<Local>,
    budget: &mut usize,
) -> Option<Local> {
    spend(budget)?;
    if local == 0 || local <= body.arg_locals().len() || path.len() >= 32 || path.contains(&local) {
        return None;
    }
    let box_ty = reference_box(ctx, body, local)?;
    path.push(local);
    let result = match defs.get(&local).copied().flatten()? {
        Rvalue::Ref(_, kind, place)
            if !matches!(kind, rustc_public::mir::BorrowKind::Fake(_))
                && place.projection.is_empty() =>
        {
            (ctx.normalized_box_ty(ctx.resolve_body_ty(body.locals().get(place.local)?.ty))?
                == box_ty)
                .then_some(place.local)
        }
        Rvalue::Ref(_, kind, place)
            if !matches!(kind, rustc_public::mir::BorrowKind::Fake(_))
                && place.projection.as_slice() == [ProjectionElem::Deref] =>
        {
            (reference_box(ctx, body, place.local)? == box_ty).then_some(())?;
            root(ctx, body, place.local, defs, path, budget)
        }
        Rvalue::Use(arg, ..) => {
            let source = plain(arg)?;
            if !source.projection.is_empty() || reference_box(ctx, body, source.local)? != box_ty {
                return None;
            }
            root(ctx, body, source.local, defs, path, budget)
        }
        _ => None,
    };
    path.pop();
    result
}
impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn host_native_dyn_borrow_owner(
        &self,
        borrow: usize,
    ) -> Option<Local> {
        let body = self.body;
        reference_box(self, body, borrow)?;
        let mut budget = 16_384;
        let mut defs = HashMap::new();
        for block in &body.blocks {
            spend(&mut budget)?;
            if let TerminatorKind::Call { destination, .. } = &block.terminator.kind {
                defs.insert(destination.local, None);
            }
            for statement in &block.statements {
                spend(&mut budget)?;
                if let StatementKind::Assign(destination, rhs) = &statement.kind {
                    let entry = defs.entry(destination.local);
                    match entry {
                        std::collections::hash_map::Entry::Vacant(entry)
                            if destination.projection.is_empty() =>
                        {
                            entry.insert(Some(rhs));
                        }
                        _ => {
                            defs.insert(destination.local, None);
                        }
                    }
                }
            }
        }
        let owner = root(self, body, borrow, &defs, &mut Vec::new(), &mut budget)?;
        let mut aliases = HashSet::new();
        for local in 1..body.locals().len() {
            spend(&mut budget)?;
            if reference_box(self, body, local).is_some()
                && root(self, body, local, &defs, &mut Vec::new(), &mut budget) == Some(owner)
            {
                aliases.insert(local);
            }
        }
        for block in &body.blocks {
            spend(&mut budget)?;
            for statement in &block.statements {
                spend(&mut budget)?;
                match &statement.kind {
                    StatementKind::Assign(destination, rhs) => {
                        if aliases.contains(&destination.local)
                            && (!destination.projection.is_empty()
                                || defs.get(&destination.local).copied().flatten().is_none())
                        {
                            return None;
                        }
                        if use_rvalue(rhs, &aliases)
                            && (!aliases.contains(&destination.local)
                                || !destination.projection.is_empty())
                        {
                            return None;
                        }
                    }
                    StatementKind::SetDiscriminant { place, .. }
                        if aliases.contains(&place.local) =>
                    {
                        return None;
                    }
                    StatementKind::Intrinsic(_) => return None,
                    _ => {}
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    if use_operand(func, &aliases) || aliases.contains(&destination.local) {
                        return None;
                    }
                    let used = args
                        .iter()
                        .enumerate()
                        .filter(|(_, arg)| use_operand(arg, &aliases))
                        .collect::<Vec<_>>();
                    if used.is_empty() {
                        continue;
                    }
                    let [(0, receiver)] = used.as_slice() else {
                        return None;
                    };
                    let place = plain(receiver)?;
                    if !place.projection.is_empty() {
                        return None;
                    }
                    let TyKind::RigidTy(RigidTy::FnDef(def, args)) =
                        func.ty(body.locals()).ok()?.kind()
                    else {
                        return None;
                    };
                    let callee = Instance::resolve(def, &args).ok()?;
                    let (box_ty, _) = native_global_dyn_box_call(self.tcx, &callee)?;
                    if reference_box(self, body, place.local)? != box_ty {
                        return None;
                    }
                }
                TerminatorKind::Drop { place, .. } if aliases.contains(&place.local) => {
                    return None;
                }
                TerminatorKind::SwitchInt { discr, .. } if use_operand(discr, &aliases) => {
                    return None;
                }
                // Ref<Box> cannot be a typed MIR arithmetic/assert operand;
                // conversions that expose it were rejected at their rvalue.
                TerminatorKind::Assert { cond, .. } if use_operand(cond, &aliases) => return None,
                TerminatorKind::InlineAsm { .. } => return None,
                _ => {}
            }
        }
        Some(owner)
    }
    pub(super) fn host_native_dyn_unmodeled_exposure(&self, local: usize) -> bool {
        let mut budget = 16_384usize;
        for statement in self.body.blocks.iter().flat_map(|block| &block.statements) {
            if spend(&mut budget).is_none() {
                return true;
            }
            let StatementKind::Assign(destination, rhs) = &statement.kind else {
                continue;
            };
            let place = match rhs {
                Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => place,
                _ => continue,
            };
            if place.local != local {
                continue;
            }
            if !matches!(rhs, Rvalue::Ref(..))
                || !place.projection.is_empty()
                || !destination.projection.is_empty()
                || self.host_native_dyn_borrow_owner(destination.local) != Some(local)
            {
                return true;
            }
        }
        false
    }
    pub(in crate::codegen_ay::chc) fn host_native_dyn_callable_receiver(
        &self,
        operand: &Operand,
    ) -> Option<(Place, super::NativeDynOrigin)> {
        let place = plain(operand)?;
        if !place.projection.is_empty() {
            return None;
        }
        let owner = self.host_native_dyn_borrow_owner(place.local)?;
        let value = Place { local: owner, projection: vec![] };
        let origin = self.host_native_dyn_origin(&Operand::Copy(value.clone()))?;
        Some((value, origin))
    }
}
