// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! MIR transformation pass for range iteration unrolling.
//!
//! This pass transforms `for i in start..end` loops from iterator-based to
//! explicit indexed loops. The transformation avoids unconstrained Option
//! discriminants from Range::next() by encoding the range bounds directly.
//!
//! Supports both signed (i8..isize) and unsigned (u8..usize) integer ranges.
//!
//! Loop detection is in this file; block-level MIR rewriting is in
//! `range_iter_transform.rs`.

use super::TransformPass;
use super::range_iter_transform::transform_range_loop;
use crate::kani_middle::transform::TransformationType;
use crate::kani_middle::transform::body::MutableBody;
use crate::kani_queries::QueryDb;
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    BasicBlockIdx, Body, Local, LocalDecl, Operand, Place, Terminator, TerminatorKind,
};
use rustc_public::ty::{AdtKind, IntTy, RigidTy, Span, Ty, TyKind, UintTy};
use std::fmt::Debug;
use tracing::{debug, trace};

/// Range iteration unrolling transformation pass.
#[derive(Debug, Default, Clone)]
pub(crate) struct RangeIterUnrollPass;

impl RangeIterUnrollPass {
    /// Create a new range iteration unroll pass.
    pub(crate) fn new() -> Self {
        RangeIterUnrollPass
    }
}

impl TransformPass for RangeIterUnrollPass {
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        TransformationType::Stubbing
    }

    fn is_enabled(&self, query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        // Gate behind --unstable=range-iter-unroll flag (#1534)
        // Transform is untested; requires explicit opt-in like array-iter-unroll
        query_db.args().unstable_features.iter().any(|f| f == "range-iter-unroll")
    }

    fn transform(&mut self, tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        debug!("RangeIterUnrollPass::transform for {:?}", instance.name());

        let range_loops = find_range_for_loops(&body);
        if range_loops.is_empty() {
            return (false, body);
        }

        let mut mutable_body = MutableBody::from(body);
        let mut transformed = false;

        for loop_info in range_loops {
            if transform_range_loop(tcx, &mut mutable_body, &loop_info) {
                transformed = true;
                debug!(
                    "Transformed range loop: range={:?}, into_iter_bb={}",
                    loop_info.range_place, loop_info.into_iter_bb
                );
            }
        }

        let new_body = mutable_body.into();
        (transformed, new_body)
    }
}

/// The integer type for range elements (signed or unsigned).
#[derive(Debug, Clone, Copy)]
pub(super) enum ElemIntType {
    /// Unsigned integer type (u8, u16, u32, u64, u128, usize).
    Unsigned(UintTy),
    /// Signed integer type (i8, i16, i32, i64, i128, isize).
    Signed(IntTy),
}

/// Information about a detected range for-loop.
#[derive(Debug)]
pub(super) struct RangeForLoop {
    /// The place containing the range being iterated.
    pub(super) range_place: Place,
    /// The element type of the range.
    pub(super) elem_ty: Ty,
    /// The integer type for element (signed or unsigned).
    pub(super) elem_int_type: ElemIntType,
    /// Block containing the `into_iter` call.
    pub(super) into_iter_bb: BasicBlockIdx,
    /// Block containing the `Iterator::next` call.
    pub(super) next_bb: BasicBlockIdx,
    /// Block with the switch on Option discriminant.
    pub(super) switch_bb: BasicBlockIdx,
    /// Block executed when loop should exit (None case).
    pub(super) exit_bb: BasicBlockIdx,
    /// Block executed for each iteration (Some case).
    pub(super) body_bb: BasicBlockIdx,
    /// Local holding the Option result (_opt).
    pub(super) option_local: Local,
    /// Span for the loop (for error messages).
    pub(super) span: Span,
}

/// Detect if a terminator is `<Range<T> as IntoIterator>::into_iter(range)`.
fn detect_range_into_iter(
    terminator: &Terminator,
    locals: &[LocalDecl],
) -> Option<(Place, Ty, ElemIntType, BasicBlockIdx)> {
    let TerminatorKind::Call { func, args, target, .. } = &terminator.kind else {
        return None;
    };

    let func_ty = func.ty(locals).ok()?;
    let TyKind::RigidTy(RigidTy::FnDef(def, generic_args)) = func_ty.kind() else {
        return None;
    };

    let fn_name = def.name();
    if !fn_name.ends_with("::into_iter") && fn_name != "into_iter" {
        return None;
    }
    if !fn_name.contains("IntoIterator") {
        return None;
    }

    let args_vec = &generic_args.0;
    if args_vec.is_empty() {
        return None;
    }

    let range_ty = args_vec[0].ty()?;
    let TyKind::RigidTy(RigidTy::Adt(adt_def, adt_args)) = range_ty.kind() else {
        return None;
    };

    let adt_name = adt_def.name();
    if !is_range_adt(&adt_name, adt_def.kind()) {
        return None;
    }

    let fields = adt_def.variants()[0].fields();
    if fields.len() < 2 {
        return None;
    }

    // Use ADT generic args for element type (field defs have unsubstituted `Idx`). #389.
    let elem_ty =
        adt_args.0.first().and_then(|a| a.ty()).copied().unwrap_or_else(|| fields[0].ty());
    let elem_int_type = match elem_ty.kind() {
        TyKind::RigidTy(RigidTy::Uint(uint_ty)) => ElemIntType::Unsigned(uint_ty),
        TyKind::RigidTy(RigidTy::Int(int_ty)) => ElemIntType::Signed(int_ty),
        _ => {
            // external enum: TyKind
            trace!("Skipping range loop with non-integer element type: {:?}", elem_ty);
            return None;
        }
    };

    if args.is_empty() {
        return None;
    }

    let range_place = match &args[0] {
        Operand::Copy(place) | Operand::Move(place) => place.clone(),
        Operand::Constant(_) => {
            trace!("Skipping constant range operand for into_iter");
            return None;
        }
    };

    let target_bb = (*target)?;

    Some((range_place, elem_ty, elem_int_type, target_bb))
}

fn is_range_adt(adt_name: &str, kind: AdtKind) -> bool {
    if kind != AdtKind::Struct {
        return false;
    }
    if adt_name.ends_with("RangeInclusive") || adt_name.contains("RangeInclusive") {
        return false;
    }
    adt_name.ends_with("::Range") || adt_name == "Range"
}

/// Find the loop structure following an into_iter call.
fn find_loop_structure(
    body: &Body,
    start_bb: BasicBlockIdx,
) -> Option<(BasicBlockIdx, BasicBlockIdx, BasicBlockIdx, BasicBlockIdx, Local)> {
    let locals = body.locals();
    let mut search_bb = start_bb;
    let mut visited = std::collections::HashSet::new();

    while visited.insert(search_bb) {
        let block = &body.blocks[search_bb];

        if let TerminatorKind::Call { func, destination, target, .. } = &block.terminator.kind
            && let Ok(func_ty) = func.ty(locals)
            && let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind()
        {
            let fn_name = def.name();
            // Match both Iterator::next and RangeIteratorImpl::spec_next.
            // Rust's specialization dispatches Range::next() through spec_next
            // in monomorphized MIR (Part of #389).
            let is_iterator_next = fn_name == "next"
                || (fn_name.ends_with("::next") && fn_name.contains("Iterator"))
                || fn_name.ends_with("::spec_next");
            if is_iterator_next {
                let option_local = destination.local;
                let next_target = (*target)?;
                if let Some((exit_bb, body_bb)) =
                    find_option_switch(body, next_target, option_local)
                {
                    return Some((search_bb, next_target, exit_bb, body_bb, option_local));
                }
            }
        }

        match &block.terminator.kind {
            TerminatorKind::Goto { target } => {
                search_bb = *target;
            }
            TerminatorKind::Call { target: Some(target), .. } => {
                search_bb = *target;
            }
            TerminatorKind::Drop { target, .. } => {
                // Follow Drop targets — drops are common between into_iter and next
                search_bb = *target;
            }
            _ => break, // external enum: TerminatorKind
        }
    }

    None
}

fn find_option_switch(
    body: &Body,
    start_bb: BasicBlockIdx,
    _option_local: Local,
) -> Option<(BasicBlockIdx, BasicBlockIdx)> {
    let mut bb = start_bb;
    let mut visited = std::collections::HashSet::new();

    while visited.len() < 5 && visited.insert(bb) {
        if bb >= body.blocks.len() {
            return None;
        }

        let block = &body.blocks[bb];
        match &block.terminator.kind {
            TerminatorKind::SwitchInt { targets, .. } => {
                let branches: Vec<_> = targets.branches().collect();
                let otherwise = targets.otherwise();
                return find_option_branches(&branches, otherwise);
            }
            TerminatorKind::Goto { target } => bb = *target,
            _ => break, // external enum: TerminatorKind
        }
    }

    None
}

fn find_option_branches(
    branches: &[(u128, BasicBlockIdx)],
    otherwise: BasicBlockIdx,
) -> Option<(BasicBlockIdx, BasicBlockIdx)> {
    let mut none_bb = None;
    let mut some_bb = None;

    for (val, target) in branches {
        if *val == 0 {
            none_bb = Some(*target);
        } else if *val == 1 {
            some_bb = Some(*target);
        }
    }

    if let (Some(exit_bb), Some(body_bb)) = (none_bb, some_bb) {
        return Some((exit_bb, body_bb));
    }

    if branches.len() == 1 {
        let (val, target) = branches[0];
        if val == 0 {
            return Some((target, otherwise));
        }
        if val == 1 {
            return Some((otherwise, target));
        }
    }

    None
}

fn find_range_for_loops(body: &Body) -> Vec<RangeForLoop> {
    let mut loops = Vec::new();
    let locals = body.locals();

    for (bb_idx, block) in body.blocks.iter().enumerate() {
        if let Some((range_place, elem_ty, elem_int_type, target_bb)) =
            detect_range_into_iter(&block.terminator, locals)
            && let Some((next_bb, switch_bb, exit_bb, body_bb, option_local)) =
                find_loop_structure(body, target_bb)
        {
            loops.push(RangeForLoop {
                range_place,
                elem_ty,
                elem_int_type,
                into_iter_bb: bb_idx,
                next_bb,
                switch_bb,
                exit_bb,
                body_bb,
                option_local,
                span: block.terminator.span,
            });
        }
    }

    loops
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pass_creation() {
        let _pass = RangeIterUnrollPass::new();
        assert!(matches!(RangeIterUnrollPass::transformation_type(), TransformationType::Stubbing));
    }
}
