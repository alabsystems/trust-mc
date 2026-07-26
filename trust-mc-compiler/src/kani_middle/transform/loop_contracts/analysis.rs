// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Loop structure and variable analysis for loop contract transformation.

use super::LoopContractPass;
use crate::kani_middle::KaniAttributes;
use crate::kani_middle::transform::body::MutableBody;
use crate::rustc_public::CrateDef;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::{Operand, Rvalue, TerminatorKind, VarDebugInfoContents};
use rustc_public::ty::RigidTy;
use rustc_span::Symbol;
use std::collections::{HashMap, HashSet};

impl LoopContractPass {
    pub(super) fn get_user_defined_variables(&self, body: &MutableBody) -> HashSet<usize> {
        body.var_debug_info()
            .iter()
            .filter_map(|info| match &info.value {
                VarDebugInfoContents::Place(place) if place.local != 0 => Some(place.local),
                _ => None, // external enum: VarDebugInfoContents
            })
            .collect()
    }

    pub(super) fn get_first_pats_and_nth_pats(
        &self,
        body: &MutableBody,
    ) -> Vec<(usize, usize, usize, usize)> {
        let mut first_pats_and_nth_pats: Vec<(usize, usize, usize, usize)> = Vec::new();
        let mut current_firstpat = 0;
        let mut current_firstpat_pos = 0;
        for (blockid, block) in body.blocks().iter().enumerate() {
            if let TerminatorKind::Call {
                func: terminator_func,
                args: _,
                destination: dest,
                target: _,
                unwind: _,
            } = &block.terminator.kind
            {
                let Some(RigidTy::FnDef(fn_def, _)) = terminator_func
                    .ty(body.locals())
                    .ok()
                    .and_then(|fn_ty| fn_ty.kind().rigid().cloned())
                else {
                    continue;
                };
                if fn_def.name() == "kani::KaniIter::first" {
                    current_firstpat = dest.local;
                    current_firstpat_pos = blockid;
                }
                if fn_def.name() == "kani::KaniIter::nth" && current_firstpat != 0 {
                    first_pats_and_nth_pats.push((
                        current_firstpat,
                        dest.local,
                        current_firstpat_pos,
                        blockid,
                    ));
                    current_firstpat = 0;
                }
            }
        }
        first_pats_and_nth_pats
    }

    pub(super) fn get_storage_moving_variables(&self, body: &MutableBody) -> HashSet<usize> {
        let first_nth_list = self.get_first_pats_and_nth_pats(body);
        let mut moving_vars = self.get_user_defined_variables(body);
        for (firstvar, _, _, _) in first_nth_list {
            moving_vars.insert(firstvar);
        }
        moving_vars
    }

    pub(super) fn get_kaniiter_variables(&self, body: &MutableBody) -> HashSet<usize> {
        body.var_debug_info()
            .iter()
            .filter_map(|info| {
                if info.name.contains("kaniiter") && !info.name.contains("kani_iter_len") {
                    match &info.value {
                        VarDebugInfoContents::Place(place) if place.local != 0 => Some(place.local),
                        _ => None, // external enum: VarDebugInfoContents
                    }
                } else {
                    None
                }
            })
            .collect()
    }

    pub(super) fn is_loop_head(&self, body: &MutableBody, tcx: TyCtxt, block_idx: usize) -> bool {
        let terminator = body.blocks()[block_idx].terminator.clone();
        if let TerminatorKind::Call {
            func: terminator_func,
            args: terminator_args,
            destination: _,
            target: _,
            unwind: _,
        } = &terminator.kind
        {
            let Some(RigidTy::FnDef(fn_def, _)) = terminator_func
                .ty(body.locals())
                .ok()
                .and_then(|fn_ty| fn_ty.kind().rigid().cloned())
            else {
                return false;
            };
            KaniAttributes::for_def_id(tcx, fn_def.def_id()).fn_marker()
                == Some(Symbol::intern("kani_register_loop_contract"))
                && matches!(
                    &terminator_args[1],
                    Operand::Constant(op)
                        if op.const_.eval_target_usize().map(|value| value == 0).unwrap_or(false)
                )
        } else {
            false
        }
    }

    pub(super) fn get_loop_positions(
        &self,
        body: &MutableBody,
        tcx: TyCtxt,
    ) -> Vec<(usize, usize)> {
        let mut loop_pos: Vec<(usize, usize)> = Vec::new();
        for (block_idx, _) in body.blocks().iter().enumerate() {
            if self.is_loop_head(body, tcx, block_idx) {
                let loop_latch_id = self.get_last_loop_latch_id(body, block_idx);
                loop_pos.push((block_idx, loop_latch_id));
            }
        }
        loop_pos
    }

    pub(super) fn get_associated_loop_head(
        &self,
        block_idx: usize,
        loop_positions: &Vec<(usize, usize)>,
    ) -> Option<usize> {
        let mut current_loop_head: Option<usize> = None;
        for (loop_head_idx, loop_latch_idx) in loop_positions {
            if block_idx > *loop_head_idx && block_idx <= *loop_latch_idx {
                current_loop_head = Some(*loop_head_idx);
            }
        }
        current_loop_head
    }

    pub(super) fn get_associated_loop_head_hashmap(
        &self,
        body: &MutableBody,
        tcx: TyCtxt,
    ) -> HashMap<usize, usize> {
        let loop_positions = self.get_loop_positions(body, tcx);
        let mut loop_head_map: HashMap<usize, usize> = HashMap::new();
        for (block_idx, _) in body.blocks().iter().enumerate() {
            let loop_head = self.get_associated_loop_head(block_idx, &loop_positions);
            if let Some(loop_head) = loop_head {
                loop_head_map.insert(block_idx, loop_head);
            }
        }
        loop_head_map
    }

    pub(super) fn get_last_loop_latch_id(&self, body: &MutableBody, loop_head_id: usize) -> usize {
        let mut loop_latch_id = loop_head_id;
        for (bb_idx, block) in body.blocks().iter().enumerate() {
            match block.terminator.kind {
                TerminatorKind::Goto { target }
                    if (target == loop_head_id && bb_idx > loop_head_id) =>
                {
                    loop_latch_id = bb_idx;
                }
                _ => (), // external enum: TerminatorKind
            }
        }
        loop_latch_id
    }

    pub(super) fn get_all_loop_latch_ids(
        &self,
        body: &MutableBody,
        loop_head_id: usize,
    ) -> Vec<usize> {
        let mut loop_latch_ids = Vec::new();
        for (bb_idx, block) in body.blocks().iter().enumerate() {
            match block.terminator.kind {
                TerminatorKind::Goto { target }
                    if (target == loop_head_id && bb_idx > loop_head_id) =>
                {
                    loop_latch_ids.push(bb_idx);
                }
                _ => (), // external enum: TerminatorKind
            }
        }
        loop_latch_ids
    }

    pub(super) fn is_supported_argument_of_closure(&self, rv: &Rvalue, body: &MutableBody) -> bool {
        let var_debug_info = &body.var_debug_info();
        matches!(rv, Rvalue::Ref(_, _, place) if
        var_debug_info.iter().any(|info|
            matches!(&info.value, VarDebugInfoContents::Place(debug_place) if *place == *debug_place)
        ))
    }
}
