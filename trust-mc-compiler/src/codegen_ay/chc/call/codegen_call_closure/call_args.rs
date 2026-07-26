// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Closure call argument extraction and translation.
//!
//! For `Fn::call(&self, (arg1, arg2, ...))`, the second argument is a tuple
//! local. These helpers search for the `Aggregate(Tuple, fields)` statement
//! that built this tuple and extract the individual field expressions.
//!
//! Extracted from `mod.rs` — Part of #4206.

use ay_bindings::Expr;
use rustc_public::mir::{AggregateKind, Operand, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;

use super::super::ChcCtx;
use super::super::codegen_call_misc::CallMisc;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(super) fn extract_closure_call_arg_operands(&self, arg_tuple: &Operand) -> Vec<Operand> {
        let tuple_local = match arg_tuple {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return Vec::new(),
        };

        self.find_closure_call_arg_operand_fields(tuple_local, &mut HashSet::new())
            .unwrap_or_default()
    }

    fn find_closure_call_arg_operand_fields(
        &self,
        tuple_local: usize,
        visited: &mut HashSet<usize>,
    ) -> Option<Vec<Operand>> {
        if !visited.insert(tuple_local) {
            return None;
        }

        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind
                    && place.local == tuple_local
                {
                    match rvalue {
                        Rvalue::Aggregate(AggregateKind::Tuple, fields) => {
                            return Some(fields.clone());
                        }
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                            if src.projection.is_empty() =>
                        {
                            return self.find_closure_call_arg_operand_fields(src.local, visited);
                        }
                        _ => {}
                    }
                }
            }
        }

        None
    }

    /// Extract individual arguments from the call argument tuple.
    ///
    /// For `Fn::call(&self, (arg1, arg2, ...))`, the second argument is a tuple
    /// local. We search for the `Aggregate(Tuple, fields)` statement that built
    /// this tuple and extract the individual field expressions.
    pub(super) fn extract_closure_call_args(
        &mut self,
        arg_tuple: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Vec<Expr> {
        let field_operands = self.extract_closure_call_arg_operands(arg_tuple);
        if !field_operands.is_empty() {
            return field_operands
                .iter()
                .filter_map(|op| self.translate_closure_call_arg(op, modified_locals))
                .collect();
        }

        let tuple_local = match arg_tuple {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => {
                // external enum: Operand
                // Constant or projected operand — try direct translation
                return self
                    .translate_operand_with_modified(arg_tuple, modified_locals)
                    .into_iter()
                    .collect();
            }
        };

        // Search all blocks for the Aggregate(Tuple, ...) that built this local.
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind
                    && place.local == tuple_local
                    && let Rvalue::Aggregate(AggregateKind::Tuple, fields) = rvalue
                {
                    return fields
                        .iter()
                        .filter_map(|op| self.translate_closure_call_arg(op, modified_locals))
                        .collect();
                }
            }
        }

        // Fallback: translate the tuple operand directly as a single argument.
        // For rust-call shims, the operand can already be a tuple-typed value
        // instead of a local built by `Aggregate(Tuple, ...)` in the current
        // body (for example `<Box<F> as FnOnce>::call_once`). In that case we
        // still need to split the tuple into per-argument field expressions.
        let Some(tuple_expr) = self.translate_operand_with_modified(arg_tuple, modified_locals)
        else {
            return Vec::new();
        };
        let Ok(tuple_ty) = arg_tuple.ty(self.body.locals()) else {
            return vec![tuple_expr];
        };
        let TyKind::RigidTy(RigidTy::Tuple(field_tys)) = tuple_ty.kind() else {
            return vec![tuple_expr];
        };
        if field_tys.is_empty() {
            return Vec::new();
        }

        let Some(dt) = tuple_expr.sort().datatype_sort() else {
            return vec![tuple_expr];
        };
        let Some(cons) = dt.constructors.first() else {
            return vec![tuple_expr];
        };
        if cons.fields.len() != field_tys.len() {
            return vec![tuple_expr];
        }

        cons.fields
            .iter()
            .map(|field| tuple_expr.clone().field_select(&dt.name, &field.name, field.sort.clone()))
            .collect()
    }

    fn translate_closure_call_arg(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let mut current = arg.clone();
        let mut visited = HashSet::new();
        for _ in 0..6 {
            let local = match &current {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    Some(place.local)
                }
                _ => None,
            };
            let Some(local) = local else { break };
            if !visited.insert(local) {
                break;
            }
            let Some(next_local) = self.find_closure_capture_source_local(local) else {
                break;
            };
            current = Operand::Copy(rustc_public::mir::Place {
                local: next_local,
                projection: Vec::new(),
            });
        }

        // Mirror fn-inline argument seeding: shared-reference closure params
        // are transparent under the inline walker's Deref-as-identity model,
        // so `&T` / `&Vec<T>` args must be seeded with the pointee value.
        if matches!(
            current.ty(self.body.locals()).ok().map(|ty| ty.kind()),
            Some(TyKind::RigidTy(RigidTy::RawPtr(..)))
        ) {
            return self
                .translate_operand_with_modified(&current, modified_locals)
                .or_else(|| self.resolve_ref_or_const_referent(&current, modified_locals));
        }

        self.resolve_ref_or_const_referent(&current, modified_locals)
            .or_else(|| self.translate_operand_with_modified(&current, modified_locals))
    }
}
