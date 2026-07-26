// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Pattern replacement, storage movement, and block manipulation utilities for loop contracts.
//!
//! This module contains the helper functions used by the core transform pass:
//! - `replace_first_pat_by_nth_pat`: replaces "firstpat" variables with "nthpat" equivalents
//! - `move_storagelive_assign_to_loophead` / `move_storagelive_call_to_loophead`: hoists variable
//!   initialization to loop heads
//! - Block/terminator manipulation utilities (`terminator_of_new_destination`, `block_of_new_target`, etc.)

use super::LoopContractPass;
use crate::kani_middle::transform::body::{InsertPosition, MutableBody, SourceInstruction};
use rustc_public::mir::{
    BasicBlock, Operand, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
};
use std::collections::{HashMap, HashSet, VecDeque};
use std::mem;

impl LoopContractPass {
    // Return the same Terminator with new destination
    pub(super) fn terminator_of_new_destination(
        old: Terminator,
        new_destination_local: usize,
    ) -> Terminator {
        let mut terminator = old;
        if let TerminatorKind::Call { destination, .. } = &mut terminator.kind {
            destination.local = new_destination_local;
        }
        terminator
    }

    // Replace the "firstpat" vars with its corresponding "nthpat" vars
    // See the comments in kani/library/kani_macros/src/sysroot/loop_contracts/mod.rs
    pub(super) fn replace_first_pat_by_nth_pat(&self, body: &mut MutableBody) {
        let first_nth_list = self.get_first_pats_and_nth_pats(body);
        for (firstvar, nthvar, first_blockid, nth_blockid) in first_nth_list {
            // Replace firstpat by nthpat in the destination of "kani::KaniIter::first" function call
            let old_terminator = body.blocks()[first_blockid].terminator.clone();
            let new_terminator = Self::terminator_of_new_destination(old_terminator, nthvar);
            body.replace_terminator(
                &SourceInstruction::Terminator { bb: first_blockid },
                new_terminator,
            );
            let span = body.blocks()[first_blockid]
                .statements
                .first()
                .expect("block should have statements")
                .span;
            // Add the StorageLive(nthpat) statement at the begining of the same block
            let storagelive_stmt = Statement { kind: StatementKind::StorageLive(nthvar), span };
            body.insert_stmt(
                storagelive_stmt,
                &mut SourceInstruction::Statement { idx: 0, bb: first_blockid },
                InsertPosition::Before,
            );

            // Remove the StorageLive(firstpat) statement in the same block if any
            let mut storageliveid = None;
            for (id, stmt) in body.blocks()[first_blockid].statements.iter().enumerate() {
                if let StatementKind::StorageLive(local) = &stmt.kind
                    && *local == firstvar
                {
                    storageliveid = Some(id);
                }
            }
            if let Some(id) = storageliveid {
                body.remove_stmt(first_blockid, id);
            }

            // Construct the HashMap of the firstpat projections with nthpat projections.
            // Part of #1962: Pre-index nth block projections to avoid O(f*n) nested loop.
            let mut firstprj_nthprj: HashMap<usize, usize> = HashMap::new();
            firstprj_nthprj.insert(firstvar, nthvar);

            // Pre-extract nth block projection info: (projection, target_local)
            let nth_projections: Vec<_> = body.blocks()[nth_blockid + 1]
                .statements
                .iter()
                .filter_map(|istmt| {
                    if let StatementKind::Assign(iprjplace, irval) = &istmt.kind
                        && let Rvalue::Use(Operand::Copy(nthpatplace)) = irval
                        && nthpatplace.local == nthvar
                    {
                        Some((&nthpatplace.projection, iprjplace.local))
                    } else {
                        None
                    }
                })
                .collect();

            for fstmt in &body.blocks()[first_blockid + 1].statements {
                if let StatementKind::Assign(fprjplace, frval) = &fstmt.kind
                    && let Rvalue::Use(Operand::Copy(firstpatplace)) = frval
                    && firstpatplace.local == firstvar
                {
                    let firstprj = fprjplace.local;
                    // O(nth_projections) linear scan for projection match
                    if let Some(&(_, nthprj)) =
                        nth_projections.iter().find(|(proj, _)| *proj == &firstpatplace.projection)
                    {
                        firstprj_nthprj.insert(firstprj, nthprj);
                    }
                }
            }

            // Replace the firstpat (and its projections) with nthpat (and its projections)
            // in the places where they may get involved, which includes, the comments in code.
            // First, in the block that  "kani::KaniIter::first" is called
            let new_stmts = {
                let firstprj_stmts = &body.blocks()[first_blockid + 1].statements;
                let mut new_stmts: Vec<Statement> = Vec::with_capacity(firstprj_stmts.len());
                for stmt in firstprj_stmts {
                    match &stmt.kind {
                        // The StorageLive statements of the projections
                        // There might be some without StorageLive statements
                        // So we just remove them and add a new one for each nthpat projection later
                        StatementKind::StorageLive(local) => {
                            if !firstprj_nthprj.contains_key(local) {
                                new_stmts.push(stmt.clone());
                            }
                        }
                        // The assign statements of the projections
                        StatementKind::Assign(fprjplace, frval) => {
                            let new_stmt = match frval {
                                Rvalue::Use(Operand::Copy(firstpatplace))
                                    if firstpatplace.local == firstvar =>
                                {
                                    let nthprj = firstprj_nthprj
                                        .get(&fprjplace.local)
                                        .expect("nthprj mapping should exist");
                                    Statement {
                                        kind: StatementKind::Assign(
                                            Place {
                                                local: *nthprj,
                                                projection: fprjplace.projection.clone(),
                                            },
                                            Rvalue::Use(Operand::Copy(Place {
                                                local: nthvar,
                                                projection: firstpatplace.projection.clone(),
                                            })),
                                        ),
                                        span: stmt.span,
                                    }
                                }
                                Rvalue::CopyForDeref(firstpatplace)
                                    if firstpatplace.local == firstvar =>
                                {
                                    Statement {
                                        kind: StatementKind::Assign(
                                            fprjplace.clone(),
                                            Rvalue::CopyForDeref(Place {
                                                local: nthvar,
                                                projection: firstpatplace.projection.clone(),
                                            }),
                                        ),
                                        span: stmt.span,
                                    }
                                }
                                // When Use(Copy) or CopyForDeref matched the pattern but
                                // the guard failed (firstpatplace.local != firstvar), the
                                // statement must pass through unchanged — do NOT fall into
                                // the catch-all which would apply the nthprj remapping.
                                Rvalue::Use(Operand::Copy(_)) | Rvalue::CopyForDeref(_) => {
                                    stmt.clone()
                                }
                                _ => {
                                    // external enum: Rvalue
                                    if let Some(nthprj) = firstprj_nthprj.get(&fprjplace.local) {
                                        Statement {
                                            kind: StatementKind::Assign(
                                                Place {
                                                    local: *nthprj,
                                                    projection: fprjplace.projection.clone(),
                                                },
                                                frval.clone(),
                                            ),
                                            span: stmt.span,
                                        }
                                    } else {
                                        stmt.clone()
                                    }
                                }
                            };
                            new_stmts.push(new_stmt);
                        }
                        _ => new_stmts.push(stmt.clone()), // external enum: StatementKind
                    }
                }
                new_stmts
            };

            body.replace_statements(
                &SourceInstruction::Statement { idx: 0, bb: first_blockid + 1 },
                new_stmts,
            );

            // Second, in the loophead block right after that
            let new_loophead_stmts = {
                let loophead_stmts = &body.blocks()[first_blockid + 2].statements;
                let mut new_loophead_stmts = Vec::new();
                if let StatementKind::Assign(
                    _,
                    Rvalue::Ref(_, _, Place { local: closurelocal, .. }),
                ) = &loophead_stmts.last().expect("loophead block should have statements").kind
                {
                    for stmt in loophead_stmts {
                        // In the Operands of the loop invariant closure
                        if let StatementKind::Assign(lhs, Rvalue::Aggregate(aggrkind, operands)) =
                            &stmt.kind
                            && lhs.local == *closurelocal
                        {
                            let mut new_operands = Vec::new();
                            for operand in operands {
                                if let Operand::Move(Place {
                                    local: operandlocal,
                                    projection: proj,
                                }) = operand
                                    && let Some(nthprj) = firstprj_nthprj.get(operandlocal)
                                {
                                    let new_operand = Operand::Move(Place {
                                        local: *nthprj,
                                        projection: proj.clone(),
                                    });
                                    new_operands.push(new_operand);
                                } else if let Operand::Copy(Place {
                                    local: operandlocal,
                                    projection: proj,
                                }) = operand
                                    && let Some(nthprj) = firstprj_nthprj.get(operandlocal)
                                {
                                    let new_operand = Operand::Copy(Place {
                                        local: *nthprj,
                                        projection: proj.clone(),
                                    });
                                    new_operands.push(new_operand);
                                } else {
                                    new_operands.push(operand.clone());
                                }
                            }
                            let new_rval = Rvalue::Aggregate(aggrkind.clone(), new_operands);
                            new_loophead_stmts.push(Statement {
                                kind: StatementKind::Assign(lhs.clone(), new_rval),
                                span: stmt.span,
                            });
                        } else if let StatementKind::Assign(
                            lhs,
                            Rvalue::Ref(
                                region,
                                borrowkind,
                                Place { local: firstlocal, projection },
                            ),
                        ) = &stmt.kind
                             // In the borrow statements
                            && let Some(nthlocal) = firstprj_nthprj.get(firstlocal)
                        {
                            let new_rval = Rvalue::Ref(
                                region.clone(),
                                *borrowkind,
                                Place { local: *nthlocal, projection: projection.clone() },
                            );
                            new_loophead_stmts.push(Statement {
                                kind: StatementKind::Assign(lhs.clone(), new_rval),
                                span: stmt.span,
                            });
                        } else {
                            new_loophead_stmts.push(stmt.clone());
                        }
                    }
                } else {
                    unreachable!("expected loop head block but condition not met")
                }
                new_loophead_stmts
            };

            body.replace_statements(
                &SourceInstruction::Statement { idx: 0, bb: first_blockid + 2 },
                new_loophead_stmts,
            );

            // Remove the StorageDead statements of nthpat and its projections.
            // Pre-compute HashSet of removal locals to avoid O(V) linear scan
            // per statement. Part of #2372.
            let removal_locals: HashSet<usize> = firstprj_nthprj.values().copied().collect();
            let mut blocks_with_removed_stmts = Vec::new();
            for (block_id, block) in body.blocks().iter().enumerate() {
                // Check if any statement needs removal before cloning
                let has_removal = block.statements.iter().any(|stmt| match &stmt.kind {
                    StatementKind::StorageDead(local) => removal_locals.contains(local),
                    StatementKind::StorageLive(local) => {
                        removal_locals.contains(local) && block_id == nth_blockid + 1
                    }
                    _ => false, // external enum: StatementKind
                });
                if has_removal {
                    let new_stmts = block
                        .statements
                        .iter()
                        .filter(|stmt| match &stmt.kind {
                            StatementKind::StorageDead(local) => !removal_locals.contains(local),
                            StatementKind::StorageLive(local) => {
                                !(removal_locals.contains(local) && block_id == nth_blockid + 1)
                            }
                            _ => true, // external enum: StatementKind
                        })
                        .cloned()
                        .collect();
                    blocks_with_removed_stmts.push((block_id, new_stmts));
                }
            }

            for (block_id, stmts) in blocks_with_removed_stmts {
                body.replace_statements(
                    &SourceInstruction::Statement { idx: 0, bb: block_id },
                    stmts,
                );
            }
        }
    }

    pub(super) fn move_storagelive_assign_to_loophead(
        &self,
        body: &mut MutableBody,
        loop_head_map: &HashMap<usize, usize>,
    ) -> HashSet<usize> {
        let mut add_assign_list: Vec<(usize, Statement)> = Vec::new();
        let mut found_local_list: HashSet<usize> = HashSet::new();
        let localvars = self.get_user_defined_variables(body);
        for block_idx in 0..body.num_blocks() {
            let Some(&closest_loop_head) = loop_head_map.get(&block_idx) else {
                continue;
            };

            let block_stmts = {
                let block = body.block_mut(block_idx);
                mem::take(&mut block.statements)
            };
            let mut remaining_stmts: VecDeque<Statement> = block_stmts.into();
            let mut new_stmts: Vec<Statement> = Vec::with_capacity(remaining_stmts.len());

            while let Some(stmt) = remaining_stmts.pop_front() {
                if let StatementKind::StorageLive(local) = &stmt.kind
                    && localvars.contains(local)
                    && !found_local_list.contains(local)
                {
                    let local = *local;

                    // Case 1: StorageLive followed by an assign.
                    if let Some(next_stmt) = remaining_stmts.front()
                        && matches!(&next_stmt.kind, StatementKind::Assign(lhs, _) if lhs.local == local)
                    {
                        found_local_list.insert(local);
                        let next_stmt = remaining_stmts
                            .pop_front()
                            .expect("front statement should exist after guard");
                        add_assign_list.push((closest_loop_head, stmt));
                        add_assign_list.push((closest_loop_head, next_stmt.clone()));
                        new_stmts.push(next_stmt);
                        continue;
                    }

                    // Case 2: for Clone():
                    // StorageLive followed by a StorageLive of a temp var, an assign ref of the
                    // temp var, an assign of the current local, then a StorageDead of temp var.
                    if let Some(next_stmt) = remaining_stmts.front()
                        && let StatementKind::StorageLive(temp_local) = &next_stmt.kind
                        && let Some(third_stmt) = remaining_stmts.get(1)
                        && let Some(fourth_stmt) = remaining_stmts.get(2)
                        && let Some(fifth_stmt) = remaining_stmts.get(3)
                        && matches!(&third_stmt.kind, StatementKind::Assign(lhs, _) if lhs.local == *temp_local)
                        && matches!(&fourth_stmt.kind, StatementKind::Assign(lhs, _) if lhs.local == local)
                        && matches!(&fifth_stmt.kind, StatementKind::StorageDead(dead_local) if dead_local == temp_local)
                    {
                        found_local_list.insert(local);
                        let next_stmt = remaining_stmts
                            .pop_front()
                            .expect("statement should exist after lookahead");
                        let third_stmt = remaining_stmts
                            .pop_front()
                            .expect("statement should exist after lookahead");
                        let fourth_stmt = remaining_stmts
                            .pop_front()
                            .expect("statement should exist after lookahead");
                        let fifth_stmt = remaining_stmts
                            .pop_front()
                            .expect("statement should exist after lookahead");
                        add_assign_list.push((closest_loop_head, stmt));
                        add_assign_list.push((closest_loop_head, next_stmt.clone()));
                        add_assign_list.push((closest_loop_head, third_stmt.clone()));
                        add_assign_list.push((closest_loop_head, fourth_stmt.clone()));
                        add_assign_list.push((closest_loop_head, fifth_stmt.clone()));
                        new_stmts.push(next_stmt);
                        new_stmts.push(third_stmt);
                        new_stmts.push(fourth_stmt);
                        new_stmts.push(fifth_stmt);
                        continue;
                    }
                }

                new_stmts.push(stmt);
            }

            body.replace_statements(&SourceInstruction::Terminator { bb: block_idx }, new_stmts);
        }

        for (block_idx, stmt) in add_assign_list {
            body.insert_stmt(
                stmt,
                &mut SourceInstruction::Terminator { bb: block_idx },
                InsertPosition::Before,
            );
        }
        found_local_list
    }

    pub(super) fn block_of_new_target(old: &BasicBlock, new_target: usize) -> BasicBlock {
        let mut new_block = old.clone();
        if let TerminatorKind::Call { target, .. } = &mut new_block.terminator.kind {
            *target = Some(new_target);
        }
        new_block
    }

    // Insert a list of blocks consecutively between the loop head and its next block
    pub(super) fn insert_blocks_from_loophead(
        body: &mut MutableBody,
        blocks: &[BasicBlock],
        loophead: usize,
    ) {
        for (i, block) in blocks.iter().enumerate() {
            if i == 0 {
                let modified_block = Self::block_of_new_target(block, loophead);
                body.insert_bb(
                    modified_block,
                    &mut SourceInstruction::Terminator { bb: loophead },
                    InsertPosition::Before,
                );
            } else {
                let modified_block = if i == blocks.len() - 1 {
                    Self::block_of_new_target(block, loophead)
                } else {
                    Self::block_of_new_target(block, body.blocks().len() + 1)
                };
                body.insert_bb(
                    modified_block,
                    &mut SourceInstruction::Terminator { bb: body.blocks().len() - 1 },
                    InsertPosition::After,
                );
            }
        }
    }

    // Insert a list of blocks consecutively at the end of the body then let the final one connect to the loop-head
    pub(super) fn insert_blocks_from_at_bottom_connect_to_loophead(
        body: &mut MutableBody,
        blocks: &[BasicBlock],
        loophead: usize,
    ) {
        for (i, block) in blocks.iter().enumerate() {
            let modified_block = if i == blocks.len() - 1 {
                Self::block_of_new_target(block, loophead)
            } else {
                Self::block_of_new_target(block, body.blocks().len() + 1)
            };
            body.insert_bb(
                modified_block,
                &mut SourceInstruction::Terminator { bb: body.blocks().len() - 1 },
                InsertPosition::After,
            );
        }
    }

    //Move all variables initiation using function-call inside the loop body to the loop-head
    pub(super) fn move_storagelive_call_to_loophead(
        &self,
        body: &mut MutableBody,
        loop_head_map: &HashMap<usize, usize>,
        found_local_list: HashSet<usize>,
    ) {
        let mut found_local_list = found_local_list;
        let localvars = self.get_storage_moving_variables(body);
        let forloopvars = self.get_kaniiter_variables(body);
        let mut current_user_local = 0;
        let mut current_local_decl_blocks: Vec<BasicBlock> = Vec::new();
        let mut move_call_list: Vec<(usize, Vec<BasicBlock>)> = Vec::new();
        let mut kaniiter_blocks: Vec<usize> = Vec::new();
        for (block_idx, block) in body.blocks().iter().enumerate() {
            let mut decl_current_user_local = false;
            let mut storage_live_block_stmt: Vec<Statement> = Vec::new();
            if loop_head_map.get(&block_idx).is_none() {
                continue;
            }
            let closest_loop_head =
                *loop_head_map.get(&block_idx).expect("block should have associated loop head");
            for stmt in &block.statements {
                if let StatementKind::StorageLive(local) = &stmt.kind
                    && (localvars.contains(local) && !found_local_list.contains(local))
                    && current_user_local == 0
                {
                    current_user_local = *local;
                    found_local_list.insert(*local);
                    decl_current_user_local = true;
                }
                if decl_current_user_local {
                    storage_live_block_stmt.push(stmt.clone());
                }
            }

            if decl_current_user_local {
                let first_block = BasicBlock {
                    statements: storage_live_block_stmt,
                    terminator: block.terminator.clone(),
                };
                current_local_decl_blocks.push(first_block);
            } else if current_user_local != 0 {
                current_local_decl_blocks.push(block.clone());
            }

            if let TerminatorKind::Call { destination: dest, .. } = &block.terminator.kind
                && dest.local == current_user_local
                && current_user_local != 0
            {
                move_call_list.push((closest_loop_head, mem::take(&mut current_local_decl_blocks)));
                current_user_local = 0;
            }

            if let TerminatorKind::Call { destination: dest, .. } = &block.terminator.kind
                && forloopvars.contains(&dest.local)
            {
                kaniiter_blocks.push(block_idx);
            }
        }

        let mut current_loop_head = 0;
        move_call_list.sort_by_key(|(closest_loop_head, _)| *closest_loop_head);
        for (loophead, blocks) in &move_call_list {
            if current_loop_head != *loophead {
                Self::insert_blocks_from_loophead(body, blocks, *loophead);
                current_loop_head = *loophead;
            } else {
                Self::insert_blocks_from_at_bottom_connect_to_loophead(body, blocks, *loophead);
            }
        }

        // For the performance benefits remove the re-assign statements of kaniiter variables
        // after adding the same one at loop head
        for block_idx in kaniiter_blocks {
            let span = body.blocks()[block_idx].terminator.span;
            body.replace_terminator(
                &SourceInstruction::Terminator { bb: block_idx },
                Terminator { kind: TerminatorKind::Goto { target: block_idx + 1 }, span },
            );
        }
    }
}
