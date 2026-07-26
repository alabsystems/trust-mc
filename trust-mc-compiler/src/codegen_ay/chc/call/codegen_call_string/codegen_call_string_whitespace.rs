// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `SplitWhitespace::next` string-core summary helpers.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};
use tracing::debug;

use crate::codegen_ay::chc::stub_codegen::stubs_option_helpers::option_value_sort;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_types::CodegenTypes;
use super::super::stubs_option_helpers::OptionHelpers;
use super::super::{ChcCtx, chc_fresh_name, declare_pending_var};
use super::codegen_call_string_utf8::ConcreteByteSlice;

pub(in crate::codegen_ay::chc) trait CallStringWhitespace {
    fn codegen_split_whitespace(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        extra_dests: &mut Vec<usize>,
    );

    fn codegen_split_whitespace_next(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    );
}

impl<'tcx, 'body> CallStringWhitespace for ChcCtx<'tcx, 'body> {
    fn codegen_split_whitespace(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        extra_dests: &mut Vec<usize>,
    ) {
        if let Some(source_slice) = self.try_resolve_concrete_str_slice_arg(args, modified_locals) {
            self.record_slice_backing_local(dest_local, &source_slice);
            debug!(dest_local, "split_whitespace: recorded source backing on iterator local");
        } else {
            self.record_sound_fallback_reason("split_whitespace_constructor_symbolic");
        }
        extra_dests.push(dest_local);
    }

    fn codegen_split_whitespace_next(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        let Some(result_sort) =
            self.body.locals().get(dest_local).and_then(|decl| Self::translate_ty(decl.ty))
        else {
            self.record_sound_fallback_reason("split_whitespace_next_missing_sort");
            return;
        };

        let precise_result = self.resolve_collection_local(args).and_then(|receiver_local| {
            let source =
                self.try_resolve_concrete_split_whitespace_source(receiver_local, modified_locals)?;
            let source_text = String::from_utf8(source.bytes.clone()).ok()?;
            let token_index =
                self.split_whitespace_next_token_index(receiver_local, self.current_encode_bb)?;
            let token_bounds = split_whitespace_bounds(&source_text);
            if let Some((start, len)) = token_bounds.get(token_index).copied() {
                let payload_sort = option_value_sort(&result_sort)?;
                let ptr_width = source.ptr.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
                let offset_width = source.offset.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
                let len_width = source.len.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
                let ptr_start_expr = Expr::bitvec_const(start as u64, ptr_width);
                let offset_start_expr = Expr::bitvec_const(start as u64, offset_width);
                let token_slice = ConcreteByteSlice {
                    ptr: source.ptr.clone().bvadd(ptr_start_expr),
                    data: source.data.clone(),
                    len: Expr::bitvec_const(len as u64, len_width),
                    offset: source.offset.clone().bvadd(offset_start_expr),
                    bytes: source.bytes[start..start + len].to_vec(),
                };
                let payload = self.build_slice_value_for_sort(&token_slice, &payload_sort)?;
                let some_expr = self.make_some_expr_for_option(payload, &result_sort)?;
                self.record_slice_backing_local(dest_local, &token_slice);
                debug!(
                    dest_local,
                    receiver_local,
                    token_index,
                    token = ?String::from_utf8_lossy(&token_slice.bytes),
                    "SplitWhitespace::next: concrete token"
                );
                Some(some_expr)
            } else {
                let none_expr = self.make_none_expr_for_option(&result_sort)?;
                debug!(
                    dest_local,
                    receiver_local, token_index, "SplitWhitespace::next: concrete None"
                );
                Some(none_expr)
            }
        });

        let result_expr = precise_result.unwrap_or_else(|| {
            self.record_sound_fallback_reason("split_whitespace_next_symbolic");
            declare_pending_var(chc_fresh_name("__split_whitespace_next"), result_sort.clone())
        });

        if let Some(flat_constraints) =
            self.build_flattened_destination_constraints(dest_local, result_expr.clone())
        {
            extra_constraints.extend(flat_constraints);
            extra_dests.push(dest_local);
            return;
        }

        if let Some((_, dest_var)) = self.resolve_destination(dest_local)
            && let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                result_expr,
                dest_var.sort(),
                dest_local,
                "codegen_split_whitespace_next",
            )
        {
            extra_constraints.push(eq);
            extra_dests.push(dest_local);
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve the concrete source slice for a `SplitWhitespace::next` receiver.
    pub(in crate::codegen_ay::chc) fn try_resolve_concrete_split_whitespace_source(
        &mut self,
        receiver_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<ConcreteByteSlice> {
        let mut worklist = vec![self.resolve_provenance_local(receiver_local)];
        let mut visited = HashSet::new();

        while let Some(local) = worklist.pop() {
            if !visited.insert(local) {
                continue;
            }

            if let Some(slice) = self.try_resolve_recorded_concrete_slice_local(local) {
                return Some(slice);
            }

            for bb_data in &self.body.blocks {
                let TerminatorKind::Call { func, args, destination, .. } = &bb_data.terminator.kind
                else {
                    continue;
                };
                if destination.local != local {
                    continue;
                }
                let Some(callee_path) = self.resolve_callee_path(func) else {
                    continue;
                };
                if callee_path.ends_with("::split_whitespace") {
                    return self.try_resolve_concrete_str_slice_arg(args, modified_locals);
                }
            }

            for bb_data in &self.body.blocks {
                for stmt in &bb_data.statements {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                    if lhs.local != local || !lhs.projection.is_empty() {
                        continue;
                    }
                    match rhs {
                        Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                        | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                            if place.projection.is_empty() =>
                        {
                            worklist.push(self.resolve_provenance_local(place.local));
                        }
                        Rvalue::Aggregate(_, operands) => {
                            for operand in operands {
                                let (Operand::Copy(place) | Operand::Move(place)) = operand else {
                                    continue;
                                };
                                if place.projection.is_empty() {
                                    worklist.push(self.resolve_provenance_local(place.local));
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        None
    }

    /// Determine the zero-based token index for the current `SplitWhitespace::next`
    /// call by requiring a unique predecessor chain back to the entry block.
    pub(in crate::codegen_ay::chc) fn split_whitespace_next_token_index(
        &self,
        receiver_local: usize,
        current_bb: usize,
    ) -> Option<usize> {
        let chain = self.strict_linear_predecessor_chain_to_entry(current_bb)?;
        if !self.block_calls_split_whitespace_next(current_bb, receiver_local) {
            return None;
        }

        Some(
            chain
                .into_iter()
                .take_while(|&bb_idx| bb_idx != current_bb)
                .filter(|&bb_idx| self.block_calls_split_whitespace_next(bb_idx, receiver_local))
                .count(),
        )
    }

    fn strict_linear_predecessor_chain_to_entry(&self, bb_idx: usize) -> Option<Vec<usize>> {
        let block_count = self.body.blocks.len();
        let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); block_count];
        for (idx, block) in self.body.blocks.iter().enumerate() {
            for succ in Self::block_successors(&block.terminator.kind) {
                if succ < block_count {
                    predecessors[succ].push(idx);
                }
            }
        }

        let mut chain = Vec::new();
        let mut visited = HashSet::new();
        let mut current = bb_idx;
        loop {
            if !visited.insert(current) {
                return None;
            }
            chain.push(current);
            let preds = predecessors.get(current)?;
            match preds.as_slice() {
                [] => break,
                [pred] => current = *pred,
                _ => return None,
            }
        }
        chain.reverse();
        Some(chain)
    }

    fn block_calls_split_whitespace_next(&self, bb_idx: usize, receiver_local: usize) -> bool {
        let Some(block) = self.body.blocks.get(bb_idx) else { return false };
        let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
            return false;
        };
        let Some(callee_path) = self.resolve_callee_path(func) else {
            return false;
        };
        callee_path.contains("SplitWhitespace")
            && callee_path.ends_with("::next")
            && self.resolve_collection_local(args) == Some(receiver_local)
    }
}

fn split_whitespace_bounds(input: &str) -> Vec<(usize, usize)> {
    let mut bounds = Vec::new();
    let mut token_start = None;

    for (idx, ch) in input.char_indices() {
        if ch.is_whitespace() {
            if let Some(start) = token_start.take() {
                bounds.push((start, idx - start));
            }
        } else if token_start.is_none() {
            token_start = Some(idx);
        }
    }

    if let Some(start) = token_start {
        bounds.push((start, input.len() - start));
    }

    bounds
}
