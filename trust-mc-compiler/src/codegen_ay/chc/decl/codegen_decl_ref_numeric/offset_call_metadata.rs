// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_public::mir::{BinOp, Operand, Rvalue, StatementKind, TerminatorKind};
use std::collections::{HashMap, HashSet};
use tracing::debug;

use super::ChcCtx;
use crate::codegen_ay::chc::expr::codegen_expr_constant::ExprConstant;
use crate::codegen_ay::stubs::StubKind;
use crate::kani_middle::kani_functions::KaniModel;

enum PointerOffsetMetadataKind {
    Signed,
    Add,
    Sub,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Pass 5e: Pre-collect metadata for pointer-offset call destinations.
    ///
    /// `ptr.add()`/`ptr.sub()` can be lowered to calls in predecessor blocks.
    /// Later blocks can cast/use that call result before the terminator dispatcher
    /// runs, so seed the destination local up front with the same referent and
    /// constant offset metadata when the count is statically known.
    pub(super) fn collect_pointer_offset_call_metadata(&mut self) {
        let const_isize_locals = self.collect_simple_isize_locals();
        for bb in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &bb.terminator.kind else {
                continue;
            };
            let Some(kind) = self.pointer_offset_metadata_kind(func) else { continue };
            if !destination.projection.is_empty() {
                continue;
            }
            let Some(src_local) = (match args.first() {
                Some(Operand::Copy(place) | Operand::Move(place))
                    if place.projection.is_empty() =>
                {
                    Some(place.local)
                }
                _ => None,
            }) else {
                continue;
            };
            let Some(ref_target) = self.ref_resolution.ref_targets.get(&src_local).cloned() else {
                continue;
            };

            let dest_local = destination.local;
            if !self.path_insensitive_metadata_copy_is_unique(src_local, dest_local) {
                self.ref_resolution.clear_path_insensitive_ref_metadata(dest_local);
                continue;
            }
            let delta = args
                .get(1)
                .and_then(|arg| self.resolve_decl_const_isize_operand(arg, &const_isize_locals))
                .and_then(|count| match kind {
                    PointerOffsetMetadataKind::Signed | PointerOffsetMetadataKind::Add => {
                        Some(count)
                    }
                    PointerOffsetMetadataKind::Sub => count.checked_neg(),
                });
            self.ref_resolution.ref_targets.insert(dest_local, ref_target);
            self.propagate_ptr_offset_result_metadata_from_parts(dest_local, src_local, delta);

            debug!(
                src_local,
                dest_local,
                "collect_pointer_offset_call_metadata: seeded pointer-offset destination"
            );
        }
    }

    fn pointer_offset_metadata_kind(&self, func: &Operand) -> Option<PointerOffsetMetadataKind> {
        if matches!(self.detect_kani_model(func), Some(KaniModel::Offset)) {
            return Some(PointerOffsetMetadataKind::Signed);
        }
        match self.detect_stub(func).filter(|stub| StubKind::is_ptr_memory(*stub)) {
            Some(StubKind::PtrAdd) => Some(PointerOffsetMetadataKind::Add),
            Some(StubKind::PtrSub) => Some(PointerOffsetMetadataKind::Sub),
            _ => None,
        }
    }

    fn collect_simple_isize_locals(&self) -> HashMap<usize, i128> {
        let mut values = HashMap::new();
        // Locals assigned different values in different blocks must be excluded
        // from constant propagation because they are path-dependent. Without this,
        // the fixed-point loop oscillates infinitely. Part of #3922.
        let mut conflicting: HashSet<usize> = HashSet::new();
        let mut changed = true;
        while changed {
            changed = false;
            for bb in &self.body.blocks {
                for stmt in &bb.statements {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                        continue;
                    };
                    if !lhs.projection.is_empty() {
                        continue;
                    }
                    let local_idx: usize = lhs.local;
                    if conflicting.contains(&local_idx) {
                        continue;
                    }
                    let value = self.eval_simple_isize_rvalue(rhs, &values);
                    if let Some(value) = value {
                        match values.get(&local_idx) {
                            Some(&existing) if existing == value => {}
                            Some(_) => {
                                values.remove(&local_idx);
                                conflicting.insert(local_idx);
                                changed = true;
                            }
                            None => {
                                values.insert(local_idx, value);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
        values
    }

    fn eval_simple_isize_rvalue(
        &self,
        rhs: &Rvalue,
        values: &HashMap<usize, i128>,
    ) -> Option<i128> {
        match rhs {
            Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                self.resolve_decl_const_isize_operand(operand, values)
            }
            Rvalue::BinaryOp(op, lhs, rhs) => {
                let lhs = self.resolve_decl_const_isize_operand(lhs, values)?;
                let rhs = self.resolve_decl_const_isize_operand(rhs, values)?;
                match op {
                    BinOp::Add | BinOp::AddUnchecked => lhs.checked_add(rhs),
                    BinOp::Sub | BinOp::SubUnchecked => lhs.checked_sub(rhs),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn resolve_decl_const_isize_operand(
        &self,
        operand: &Operand,
        values: &HashMap<usize, i128>,
    ) -> Option<i128> {
        match operand {
            Operand::Constant(c) => self.extract_decl_const_isize(c),
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                values.get(&place.local).copied()
            }
            _ => None,
        }
    }

    fn extract_decl_const_isize(&self, const_op: &rustc_public::mir::ConstOperand) -> Option<i128> {
        self.translate_constant(const_op).and_then(|expr| Self::const_isize_from_expr(&expr))
    }
}
