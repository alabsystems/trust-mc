// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Concrete BV expression evaluation and MIR string extraction utilities.
//!
//! Extracted from `helpers.rs` per #4129 (500 LOC threshold).
//!
//! Contains:
//! - `try_eval_concrete_bv_usize`: evaluate BV expressions with all-concrete operands
//! - `concrete_strs_of_iter_source`: the `[&str; N]` literal an iterator reads, traced exactly
//!
//! Part of #3189: concrete replay count extraction for filter_map chains.

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Rvalue, StatementKind};

use super::super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Try to evaluate a BV expression with all-concrete operands to a usize.
    ///
    /// Handles patterns like `ite(bvuge(2, 0), bvsub(2, 0), 0)` that arise from
    /// `bv_saturating_sub` on concrete VecIntoIter pos/len values. AY doesn't
    /// simplify these at construction time, so we evaluate them here.
    ///
    /// Part of #3189: concrete replay count extraction for filter_map chains.
    pub(in crate::codegen_ay::chc) fn try_eval_concrete_bv_usize(expr: &Expr) -> Option<usize> {
        use ay_bindings::ExprValue;
        match expr.value() {
            ExprValue::BitVecConst { value, .. } => usize::try_from(value.clone()).ok(),
            ExprValue::BvSub(lhs, rhs) => {
                let l = Self::try_eval_concrete_bv_usize(lhs)?;
                let r = Self::try_eval_concrete_bv_usize(rhs)?;
                l.checked_sub(r)
            }
            ExprValue::BvAdd(lhs, rhs) => {
                let l = Self::try_eval_concrete_bv_usize(lhs)?;
                let r = Self::try_eval_concrete_bv_usize(rhs)?;
                l.checked_add(r)
            }
            ExprValue::Ite { cond, then_expr, else_expr } => {
                let c = Self::try_eval_concrete_bv_bool(cond)?;
                if c {
                    Self::try_eval_concrete_bv_usize(then_expr)
                } else {
                    Self::try_eval_concrete_bv_usize(else_expr)
                }
            }
            _ => None,
        }
    }

    /// Try to evaluate a Bool expression with all-concrete operands.
    ///
    /// Part of #3189: helper for try_eval_concrete_bv_usize.
    fn try_eval_concrete_bv_bool(expr: &Expr) -> Option<bool> {
        use ay_bindings::ExprValue;
        match expr.value() {
            ExprValue::BoolConst(b) => Some(*b),
            ExprValue::BvUGe(lhs, rhs) => {
                let l = Self::try_eval_concrete_bv_usize(lhs)?;
                let r = Self::try_eval_concrete_bv_usize(rhs)?;
                Some(l >= r)
            }
            ExprValue::BvULe(lhs, rhs) => {
                let l = Self::try_eval_concrete_bv_usize(lhs)?;
                let r = Self::try_eval_concrete_bv_usize(rhs)?;
                Some(l <= r)
            }
            _ => None,
        }
    }

    /// The `&str` literals the iterator held by `start` (an adapter's
    /// receiver local) iterates, when the MIR establishes its source exactly:
    /// a `[&str; N]` literal reached through `<[T]>::iter` / `into_iter`,
    /// `&` / unsizing / copies, or through `vec![..]` (`into_vec` of a box
    /// whose one write is the literal), every local on the way written once
    /// and never borrowed mutably.
    ///
    /// The scan this replaces returned the FIRST `[&str; N]` aggregate of
    /// the body whatever the iterator read: with another string array
    /// before it, `hi.iter().flat_map(|s| s.chars()).next() == Some('a')`
    /// verified clean where Kani fails and the true `Some('H')` was
    /// certified a Genuine failure (walker fail-closed repair round 5,
    /// `iter_concrete_source_dual.rs`).
    pub(in crate::codegen_ay::chc) fn concrete_strs_of_iter_source(
        &self,
        start: usize,
        max_count: usize,
    ) -> Option<Vec<String>> {
        use rustc_public::mir::{AggregateKind, ProjectionElem, TerminatorKind};
        use rustc_public::ty::{RigidTy, TyKind};
        let mut local = start;
        for _ in 0..12 {
            // The one whole-local definition: a statement or a call.
            let mut stmt_def: Option<&Rvalue> = None;
            let mut call_def: Option<(&Operand, &[Operand])> = None;
            let mut defs = 0usize;
            let mut deref_writes: Vec<&Rvalue> = Vec::new();
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                    if lhs.local != local {
                        continue;
                    }
                    match lhs.projection.as_slice() {
                        [] => {
                            defs += 1;
                            stmt_def = Some(rhs);
                        }
                        [ProjectionElem::Deref] => deref_writes.push(rhs),
                        _ => return None,
                    }
                }
                if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                    && destination.local == local
                {
                    if !destination.projection.is_empty() {
                        return None;
                    }
                    defs += 1;
                    call_def = Some((func, args.as_slice()));
                }
            }
            if defs != 1 || self.local_mutably_borrowed(local) {
                return None;
            }
            let next = if let Some((func, args)) = call_def {
                // An element-preserving std conversion: `into_iter`, a slice's
                // `iter` / `into_vec`, `Vec`'s `deref`, as the instance the call
                // resolves to names it (never the crate's own impl).
                let TyKind::RigidTy(RigidTy::FnDef(def, fn_args)) =
                    func.ty(self.body.locals()).ok()?.kind()
                else {
                    return None;
                };
                let instance = rustc_public::mir::mono::Instance::resolve(def, &fn_args).ok()?;
                let krate = rustc_public::CrateDef::krate(&instance.def);
                let name = rustc_public::CrateDef::name(&instance.def);
                let through = !krate.is_local
                    && matches!(krate.name.as_str(), "core" | "alloc" | "std")
                    && (name.ends_with("::into_iter")
                        || (name.contains("slice::<impl")
                            && (name.ends_with("::iter") || name.ends_with("::into_vec")))
                        || name.ends_with("Deref>::deref"));
                if !through {
                    return None;
                }
                let (Operand::Copy(place) | Operand::Move(place)) = args.first()? else {
                    return None;
                };
                if !place.projection.is_empty() {
                    return None;
                }
                place.local
            } else {
                // A box filled by one deref write (`vec![..]`'s `Box::new([..])`).
                let rhs = match deref_writes.as_slice() {
                    [] => stmt_def?,
                    [write] => *write,
                    _ => return None,
                };
                match rhs {
                    Rvalue::Aggregate(AggregateKind::Array(elem_ty), operands) => {
                        if operands.is_empty() || operands.len() > max_count {
                            return None;
                        }
                        let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = elem_ty.kind() else {
                            return None;
                        };
                        if !matches!(inner.kind(), TyKind::RigidTy(RigidTy::Str)) {
                            return None;
                        }
                        return operands
                            .iter()
                            .map(|op| match op {
                                Operand::Constant(c) => {
                                    self.try_read_str_from_mir_const_ref(&c.const_)
                                }
                                Operand::Copy(place) | Operand::Move(place)
                                    if place.projection.is_empty()
                                        && self.local_written_once_unborrowed(place.local) =>
                                {
                                    self.trace_local_to_str_const(place.local)
                                }
                                _ => None,
                            })
                            .collect();
                    }
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                    | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                        if place.projection.is_empty() =>
                    {
                        place.local
                    }
                    Rvalue::Ref(_, _, place)
                        if place.projection.is_empty()
                            || matches!(place.projection.as_slice(), [ProjectionElem::Deref]) =>
                    {
                        place.local
                    }
                    _ if !deref_writes.is_empty() => return None,
                    _ => return None,
                }
            };
            local = next;
        }
        None
    }

    /// Is `local`, or any of its fields, borrowed mutably or by a raw
    /// pointer anywhere in the body?
    fn local_mutably_borrowed(&self, local: usize) -> bool {
        use rustc_public::mir::Mutability;
        use rustc_public::ty::{RigidTy, TyKind};
        self.body.blocks.iter().flat_map(|block| &block.statements).any(|stmt| {
            let StatementKind::Assign(_, rhs) = &stmt.kind else { return false };
            let (Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)) = rhs else {
                return false;
            };
            place.local == local
                && !(matches!(rhs, Rvalue::Ref(..))
                    && matches!(
                        rhs.ty(self.body.locals()).map(|ty| ty.kind()),
                        Ok(TyKind::RigidTy(RigidTy::Ref(_, _, Mutability::Not)))
                    ))
        })
    }

    /// Trace a MIR local back to its `&str` constant assignment.
    /// Part of #3189.
    fn trace_local_to_str_const(&self, target_local: usize) -> Option<String> {
        if !self.local_written_once_unborrowed(target_local) {
            return None;
        }
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if lhs.local != target_local || !lhs.projection.is_empty() {
                    continue;
                }
                if let Rvalue::Use(Operand::Constant(c), ..) = rhs {
                    return self.try_read_str_from_mir_const_ref(&c.const_);
                }
            }
        }
        None
    }

    /// Constrain a FlattenNext payload to the chars the `flat_map(|s|
    /// s.chars())` receiver `iter_local` was built over (its recorded
    /// concrete elements, `codegen_iter_constructor`): the payload is one of
    /// them. It read the first string array of the body instead (walker
    /// fail-closed repair round 5, `iter_concrete_source_dual.rs`).
    ///
    /// Part of #4112: flat_map(|s| s.chars()) over concrete string literals.
    pub(in crate::codegen_ay::chc) fn try_constrain_flatten_next_payload(
        &self,
        payload: &Expr,
        iter_local: Option<usize>,
    ) -> Option<Expr> {
        let chars = self
            .collections
            .adapter_source_data
            .get(&iter_local?)
            .and_then(|data| data.concrete_elems.clone())?;
        let payload_width = payload.sort().bitvec_width()?;
        let mut disjuncts: Vec<Expr> = Vec::new();
        for c in &chars {
            let ay_bindings::ExprValue::BitVecConst { value, .. } = c.value() else {
                return None;
            };
            disjuncts.push(payload.clone().eq(Expr::bitvec_const(value.clone(), payload_width)));
        }
        if disjuncts.is_empty() {
            return None;
        }
        let mut result = disjuncts.remove(0);
        for d in disjuncts {
            result = result.or(d);
        }
        Some(result)
    }

    /// Read string bytes from a MIR `&str` constant: the pointee WINDOW its
    /// pointer names (`const_pointer::fixed_pointee`), at the pointer's offset,
    /// for the length its metadata word carries — not the target from byte 0.
    /// Part of #3189: MIR fallback for BV64 pointer elements.
    fn try_read_str_from_mir_const_ref(
        &self,
        mir_const: &rustc_public::ty::MirConst,
    ) -> Option<String> {
        use crate::codegen_ay::shared::const_pointer::{self, ConstRead};
        use rustc_public::ty::{RigidTy, TyKind};
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = mir_const.ty().kind() else {
            return None;
        };
        if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Str)) {
            return None;
        }
        let bytes = const_pointer::const_bytes(mir_const)?;
        let (r, window) = const_pointer::fixed_pointee(self.tcx, &bytes, 0, pointee)?;
        let len = usize::try_from(r.metadata?).ok()?;
        if len == 0 || len > 256 || window.len() != len {
            return None;
        }
        String::from_utf8(window.read_data_bytes(0, len)?).ok()
    }
}
