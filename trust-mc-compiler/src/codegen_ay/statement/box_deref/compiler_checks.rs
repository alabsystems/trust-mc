// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Numeric temporaries used exclusively by actual compiler pointer assertions.
//! A transitive alias escaping a check chain refuses the whole classification.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::mir::visit::{
    Location, MirVisitor, PlaceContext, statement_location, terminator_location,
};
use rustc_public::mir::{
    AssertMessage, Body, Local, Operand, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, TyKind, UintTy};
use std::collections::{HashMap, HashSet};
#[cfg(all(test, feature = "compiler-corpus-tests", trust_toolchain, version("1.101")))]
mod tests;

fn local(operand: &Operand) -> Option<usize> {
    match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
        _ => None,
    }
}
struct Mentions(Vec<usize>);
impl MirVisitor for Mentions {
    fn visit_local(&mut self, local: &Local, _: PlaceContext, _: Location) {
        self.0.push(*local);
    }
}

pub(in crate::codegen_ay::statement) fn compiler_pointer_check_casts(
    body: &Body,
) -> HashMap<usize, u64> {
    let mut defs = HashMap::<usize, Vec<Option<(usize, usize)>>>::new();
    for (bb, block) in body.blocks.iter().enumerate() {
        for (si, statement) in block.statements.iter().enumerate() {
            if let StatementKind::Assign(place, _) = &statement.kind
                && place.projection.is_empty()
            {
                defs.entry(place.local).or_default().push(Some((bb, si)));
            }
        }
        if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
            && destination.projection.is_empty()
        {
            defs.entry(destination.local).or_default().push(None);
        }
    }
    let mut sites = HashSet::new();
    let mut checks = HashSet::new();
    let mut chain = HashSet::new();
    let mut casts = HashMap::<usize, u64>::new();
    for (bb, block) in body.blocks.iter().enumerate() {
        let TerminatorKind::Assert { cond, msg, .. } = &block.terminator.kind else { continue };
        let (align, found) = match msg {
            AssertMessage::NullPointerDereference => (1, None),
            #[cfg(trust_toolchain)]
            AssertMessage::NullReferenceConstructed => (1, None),
            AssertMessage::MisalignedPointerDereference {
                required: Operand::Constant(c),
                found,
            } => {
                let Ok(align) = c.const_.eval_target_usize() else { return HashMap::new() };
                if !align.is_power_of_two() {
                    return HashMap::new();
                }
                (align, Some(found))
            }
            _ => continue,
        };
        checks.insert(bb);
        let mut work: Vec<_> =
            [Some(cond), found].into_iter().flatten().filter_map(local).collect();
        let mut seen = HashSet::new();
        while let Some(value) = work.pop() {
            if !seen.insert(value) {
                continue;
            }
            if seen.len() > 32 || chain.len() > 512 {
                return HashMap::new();
            }
            chain.insert(value);
            let Some([Some((db, ds))]) = defs.get(&value).map(Vec::as_slice) else { continue };
            let StatementKind::Assign(_, rhs) = &body.blocks[*db].statements[*ds].kind else {
                continue;
            };
            match rhs {
                Rvalue::BinaryOp(_, a, b) => {
                    sites.insert((*db, *ds));
                    work.extend([a, b].into_iter().filter_map(local));
                }
                Rvalue::UnaryOp(_, a) | Rvalue::Use(a, ..) => {
                    sites.insert((*db, *ds));
                    work.extend(local(a));
                }
                Rvalue::Cast(_, source, target)
                    if matches!(target.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::Usize)))
                        && source.ty(body.locals()).is_ok_and(|ty| {
                            matches!(ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
                        }) =>
                {
                    sites.insert((*db, *ds));
                    casts.entry(value).and_modify(|old| *old = (*old).max(align)).or_insert(align);
                }
                _ => {}
            }
        }
    }
    if chain.contains(&0) {
        return HashMap::new();
    } // Return reads _0 implicitly.
    // Inspect ALL chain locals, including copies and arithmetic intermediates.
    // Checking only the cast destination would miss an alias read by user code.
    for (bb, block) in body.blocks.iter().enumerate() {
        for (si, statement) in block.statements.iter().enumerate() {
            if sites.contains(&(bb, si)) {
                continue;
            }
            let mut mentions = Mentions(Vec::new());
            mentions.visit_statement(statement, statement_location(body, &bb, si));
            if mentions.0.iter().any(|v| chain.contains(v)) {
                return HashMap::new();
            }
        }
        if checks.contains(&bb) {
            continue;
        }
        let mut mentions = Mentions(Vec::new());
        mentions.visit_terminator(&block.terminator, terminator_location(body, &bb));
        if mentions.0.iter().any(|v| chain.contains(v)) {
            return HashMap::new();
        }
    }
    casts
}

impl super::StatementCodegen<'_, '_, '_> {
    pub(super) fn checked_compiler_numeric_pointer(
        &mut self,
        source: rustc_public::ty::Ty,
        value: &super::Expr,
    ) -> bool {
        let Some(required) = self.bmc_box_pointer_check_alignment else { return false };
        let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) = source.kind() else { return false };
        let Some(checks) = self.native_box_pointer_checks(value, pointee) else { return false };
        let mut pending = vec![value];
        let mut budget = super::BUDGET;
        while let Some(part) = pending.pop() {
            let Some(left) = budget.checked_sub(1) else { return false };
            budget = left;
            if let Some(super::BoxPointerOrigin::Allocation(index)) =
                self.ctx.box_pointer_origin(part)
                && !self.ctx.native_box_allocation(index).is_some_and(|fact| fact.align >= required)
            {
                return false;
            }
            pending.extend(part.children());
        }
        for check in checks {
            self.record_violation_guarded_with_message(
                check.not(),
                "box_deref_validity",
                Some("native pointer check source validity".into()),
            );
        }
        true
    }
}
