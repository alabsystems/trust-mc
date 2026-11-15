// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Unanimous producer invariants, not may-points-to guesses. The admitted
//! iterator operations mutate only the cursor: all constructors/copies must
//! establish the SAME data address and extent before either can be constant
//! propagated. Otherwise the runtime fields remain authoritative.
use super::ChcCtx;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn static_iterator_invariants(
        &self,
        op: &Operand,
    ) -> Option<(Expr, Expr)> {
        if !self.static_iterator_uses_closed() {
            return None;
        }
        let (idx, offset, len) = self.static_iterator_constant_parts(op, 16)?;
        let mut objects =
            self.ref_resolution.static_state_idx_by_obj.iter().filter(|(_, i)| **i == idx);
        let (&object, _) = objects.next()?;
        if objects.next().is_some() || offset > u32::MAX as u64 {
            return None;
        }
        Some((
            Expr::bitvec_const(object as u128, 32).concat(Expr::bitvec_const(offset as u128, 32)),
            Expr::bitvec_const(len as u128, POINTER_WIDTH),
        ))
    }

    fn static_iterator_constant_parts(
        &self,
        op: &Operand,
        depth: usize,
    ) -> Option<(usize, u64, u64)> {
        let depth = depth.checked_sub(1)?;
        let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
        if !p.projection.is_empty() || p.local <= self.body.arg_locals().len() {
            return None;
        }
        self.borrowed_slice_item_ty(self.body.locals().get(p.local)?.ty)?;
        let mut invariant = None;
        let mut agree = |parts| {
            if invariant.is_some_and(|old| old != parts) {
                return None;
            }
            invariant = Some(parts);
            Some(())
        };
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && lhs.local == p.local
                {
                    if !lhs.projection.is_empty() {
                        return None;
                    }
                    let parts = match rhs {
                        Rvalue::Use(op, ..) => self.static_iterator_constant_parts(op, depth)?,
                        Rvalue::Ref(_, _, place) if place.projection.is_empty() => self
                            .static_iterator_constant_parts(&Operand::Copy(place.clone()), depth)?,
                        _ => return None,
                    };
                    agree(parts)?;
                }
            }
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                && destination.local == p.local
            {
                if !destination.projection.is_empty() || args.len() != 1 {
                    return None;
                }
                let parts = if self.core_method(func, "iter") {
                    let (idx, Some(offset)) = self.static_of_pointer_operand(&args[0])? else {
                        return None;
                    };
                    let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) =
                        args[0].ty(self.body.locals()).ok()?.kind()
                    else {
                        return None;
                    };
                    let len = match pointee.kind() {
                        TyKind::RigidTy(RigidTy::Array(_, n)) => n.eval_target_usize().ok()?,
                        TyKind::RigidTy(RigidTy::Slice(_)) => {
                            let (Operand::Copy(p) | Operand::Move(p)) = &args[0] else {
                                return None;
                            };
                            if !p.projection.is_empty() {
                                return None;
                            }
                            self.try_resolve_slice_len_for_local(p.local)?
                        }
                        _ => return None,
                    };
                    (idx, offset, len)
                } else if self.core_method(func, "into_iter") {
                    self.static_iterator_constant_parts(&args[0], depth)?
                } else {
                    return None;
                };
                agree(parts)?;
            }
        }
        invariant
    }
}
