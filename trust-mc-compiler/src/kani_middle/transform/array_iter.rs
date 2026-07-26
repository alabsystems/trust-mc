// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! MIR transformation pass for array iteration unrolling.
//!
//! This pass transforms `for x in array` loops from iterator-based to indexed loops.
//! The transformation enables BMC/CHC to verify array iteration without needing
//! full iterator infrastructure (PolymorphicIter, IndexRange, closures, etc.).
//!
//! # Transformation
//!
//! Before:
//! ```text
//! _iter = IntoIterator::into_iter(array)
//! loop {
//!     _opt = Iterator::next(&mut _iter)
//!     switch discriminant(_opt) -> [None: exit, Some: body]
//!     body: x = (_opt as Some).0; ...
//! }
//! ```
//!
//! After:
//! ```text
//! _idx = 0
//! loop {
//!     switch (_idx < N) -> [false: exit, true: body]
//!     body: x = array[_idx]; _idx += 1; ...
//! }
//! ```
//!
//! For small fixed-size arrays, CHC uses a stronger lowering:
//! ```text
//! body0: x = array[0]; ...
//! body1: x = array[1]; ...
//! ...
//! goto exit
//! ```
//! This avoids Array-sorted loop state with symbolic select/store indices.

use super::TransformPass;
use crate::kani_middle::transform::TransformationType;
use crate::kani_middle::transform::body::MutableBody;
use crate::kani_queries::QueryDb;
use crate::rustc_public_bridge::IndexedVal;
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    AggregateKind, BasicBlockIdx, BinOp, Body, ConstOperand, Local, LocalDecl, Mutability, Operand,
    Place, ProjectionElem, Rvalue, Statement, StatementKind, SwitchTargets, Terminator,
    TerminatorKind, UnwindAction,
};
use rustc_public::ty::{MirConst, RigidTy, Span, Ty, TyKind, UintTy};
use std::fmt::Debug;
use tracing::{debug, trace};

const MAX_FINITE_ARRAY_ITER_UNROLL: usize = 8;

/// Array iteration unrolling transformation pass.
///
/// Detects for-loops over arrays and transforms them to simple indexed loops,
/// eliminating the need for full iterator infrastructure.
#[derive(Debug, Default, Clone)]
pub(crate) struct ArrayIterUnrollPass;

impl ArrayIterUnrollPass {
    /// Create a new array iteration unroll pass.
    pub(crate) fn new() -> Self {
        ArrayIterUnrollPass
    }
}

impl TransformPass for ArrayIterUnrollPass {
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        // This is a stubbing pass - we're replacing the iterator with direct indexing
        TransformationType::Stubbing
    }

    fn is_enabled(&self, query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        // AY CHC uses this pass to remove array iterator carrier closures before
        // replacement proof codegen sees them. Keep the explicit unstable flag for
        // non-CHC experiments.
        query_db.args().ay_chc
            || query_db.args().unstable_features.iter().any(|f| f == "array-iter-unroll")
    }

    fn transform(&mut self, _tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        debug!("ArrayIterUnrollPass::transform for {:?}", instance.name());

        // Find array for-loops in the body
        let array_loops = find_array_for_loops(&body);

        if array_loops.is_empty() {
            return (false, body);
        }

        // Transform each loop
        let mut mutable_body = MutableBody::from(body);
        let mut transformed = false;

        for loop_info in &array_loops {
            if transform_array_loop(&mut mutable_body, loop_info) {
                transformed = true;
                debug!(
                    "Transformed array loop: array={:?}, len={}, is_zst={}, into_iter_bb={}",
                    loop_info.array_place,
                    loop_info.array_len,
                    loop_info.is_zst_element,
                    loop_info.into_iter_bb
                );
            }
        }

        // After transformation, eliminate ALL iterator infrastructure from the
        // body. This removes Drop terminators, Call terminators to iterator
        // functions, and replaces iterator local types with () to prevent
        // PolymorphicIter Drop glue monomorphization (which causes UNKNOWN).
        if transformed {
            for loop_info in &array_loops {
                eliminate_iterator_infrastructure(&mut mutable_body, loop_info);
            }
        }

        let new_body = mutable_body.into();
        (transformed, new_body)
    }
}

/// Check if a type is zero-sized (ZST).
///
/// Used to detect ZST element types in arrays (e.g., `()` in `[(); N]`).
/// ZST arrays are passed as `Constant(ZeroSized)` in MIR since total size = N * 0 = 0.
fn is_zst_type(ty: &Ty) -> bool {
    match ty.kind() {
        // Unit type ()
        TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.is_empty() => true,
        // Array of ZST elements is also ZST
        TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => is_zst_type(&elem_ty),
        // Never type ! (uninhabited, but technically ZST)
        TyKind::RigidTy(RigidTy::Never) => true,
        _ => false, // external enum: TyKind
    }
}

/// Information about a detected array for-loop.
#[derive(Debug)]
struct ArrayForLoop {
    /// The place containing the array being iterated.
    /// For ZST constant arrays, this is a dummy place (not used).
    array_place: Place,
    /// The compile-time length of the array (N in [T; N]).
    array_len: usize,
    /// The element type of the array (stored for upstream Kani pattern, not read).
    _elem_ty: Ty,
    /// Whether the element type is zero-sized (e.g., `()`).
    is_zst_element: bool,
    /// Block containing the `into_iter` call.
    into_iter_bb: BasicBlockIdx,
    /// Block containing the `Iterator::next` call.
    next_bb: BasicBlockIdx,
    /// Block with the switch on Option discriminant.
    switch_bb: BasicBlockIdx,
    /// Block executed when loop should exit (None case).
    exit_bb: BasicBlockIdx,
    /// Block executed for each iteration (Some case).
    body_bb: BasicBlockIdx,
    /// Local holding the iterator. Used to eliminate Drop glue after transformation.
    iter_local: Local,
    /// Local holding the Option result (_opt).
    option_local: Local,
    /// Span for the loop (for error messages).
    span: Span,
}

/// Find all array for-loops in the function body.
///
/// Detection pattern:
/// 1. Find `<[T; N] as IntoIterator>::into_iter(array)` calls
/// 2. Trace forward to find the loop structure
fn find_array_for_loops(body: &Body) -> Vec<ArrayForLoop> {
    let mut loops = Vec::new();
    let locals = body.locals();

    for (bb_idx, block) in body.blocks.iter().enumerate() {
        // Look for into_iter calls on arrays
        if let Some((array_place, array_len, elem_ty, is_zst, iter_local, target_bb)) =
            detect_array_into_iter(&block.terminator, locals)
        {
            debug!(
                "Found into_iter call at bb{}: array={:?}, len={}, elem_ty={:?}, is_zst={}",
                bb_idx, array_place, array_len, elem_ty, is_zst
            );

            // Try to find the loop structure starting from target_bb
            if let Some(loop_structure) = find_loop_structure(
                body,
                target_bb,
                iter_local,
                array_place.clone(),
                array_len,
                elem_ty,
            ) {
                loops.push(ArrayForLoop {
                    array_place,
                    array_len,
                    _elem_ty: loop_structure.elem_ty,
                    is_zst_element: is_zst,
                    into_iter_bb: bb_idx,
                    next_bb: loop_structure.next_bb,
                    switch_bb: loop_structure.switch_bb,
                    exit_bb: loop_structure.exit_bb,
                    body_bb: loop_structure.body_bb,
                    iter_local,
                    option_local: loop_structure.option_local,
                    span: block.terminator.span,
                });
            } else if array_len == 0 {
                // Zero-length array: find the exit point and create a simplified loop info
                // that will bypass the iterator infrastructure entirely (#492)
                debug!("Zero-length array at bb{}: trying fallback exit detection", bb_idx);
                if let Some(exit_bb) = find_zero_length_exit(body, target_bb) {
                    debug!("Found exit bb{} for zero-length array at bb{}", exit_bb, bb_idx);
                    // Create a synthetic loop info for zero-length arrays
                    // The transform will replace into_iter with direct goto to exit
                    loops.push(ArrayForLoop {
                        array_place,
                        array_len: 0,
                        _elem_ty: elem_ty,
                        is_zst_element: is_zst,
                        into_iter_bb: bb_idx,
                        // For zero-length arrays, all blocks point to exit since
                        // the loop body never executes
                        next_bb: target_bb,
                        switch_bb: target_bb,
                        exit_bb,
                        body_bb: exit_bb,
                        iter_local,
                        option_local: 0, // Not used for zero-length
                        span: block.terminator.span,
                    });
                }
            }
        }
    }

    loops
}

/// Find the exit block for a zero-length array loop.
///
/// For zero-length arrays, the iterator infrastructure eventually reaches an exit point.
/// We trace through the control flow to find where the loop would exit.
fn find_zero_length_exit(body: &Body, start_bb: BasicBlockIdx) -> Option<BasicBlockIdx> {
    let mut visited = std::collections::HashSet::new();
    let mut stack = vec![start_bb];

    // DFS to find the exit: look for a return or the Option switch's None branch
    while let Some(bb) = stack.pop() {
        if !visited.insert(bb) || bb >= body.blocks.len() {
            continue;
        }

        let block = &body.blocks[bb];

        match &block.terminator.kind {
            TerminatorKind::Return => {
                // Found return - this is the exit
                return Some(bb);
            }
            TerminatorKind::Goto { target } => {
                stack.push(*target);
            }
            TerminatorKind::SwitchInt { targets, .. } => {
                // Check if this looks like an Option discriminant switch:
                // - Has 1 or 2 branches (Option has 2 variants: None=0, Some=1)
                // - Values should be 0 and/or 1
                let branches: Vec<_> = targets.branches().collect();
                let is_option_switch =
                    branches.len() <= 2 && branches.iter().all(|(val, _)| *val <= 1);

                if is_option_switch {
                    // For zero-length arrays, the switch always takes the None branch (value 0)
                    for (val, target) in &branches {
                        if *val == 0 {
                            return Some(*target);
                        }
                    }
                    // If no explicit 0 branch, the otherwise branch is the exit
                    return Some(targets.otherwise());
                }
                // Not an Option switch, continue searching
                // Add all targets to the search
                for (_, target) in branches {
                    stack.push(target);
                }
                stack.push(targets.otherwise());
            }
            TerminatorKind::Call { target: Some(t), .. } => {
                stack.push(*t);
            }
            _ => {} // external enum: TerminatorKind
        }

        // Limit search depth
        if visited.len() > 20 {
            break;
        }
    }

    None
}

/// Detect if a terminator is `<[T; N] as IntoIterator>::into_iter(array)`.
///
/// Returns: (array_place, array_len, elem_ty, is_zst, iter_local, target_bb)
fn detect_array_into_iter(
    terminator: &Terminator,
    locals: &[LocalDecl],
) -> Option<(Place, usize, Ty, bool, Local, BasicBlockIdx)> {
    let TerminatorKind::Call { func, args, destination, target, .. } = &terminator.kind else {
        return None;
    };

    // Get the function type
    let func_ty = func.ty(locals).ok();
    let func_ty = func_ty?;
    let TyKind::RigidTy(RigidTy::FnDef(def, generic_args)) = func_ty.kind() else {
        return None;
    };

    // Check if this is IntoIterator::into_iter
    // def.name() returns full path like "std::iter::IntoIterator::into_iter"
    let fn_name = def.name();
    if !fn_name.ends_with("::into_iter") && fn_name != "into_iter" {
        return None;
    }

    // The function name should contain "IntoIterator" to be the trait impl
    if !fn_name.contains("IntoIterator") {
        trace!("into_iter call but not IntoIterator trait: {}", fn_name);
        return None;
    }

    // Check the first generic arg is an array type [T; N]
    let args_vec = generic_args.0;
    if args_vec.is_empty() {
        return None;
    }

    let first_arg = &args_vec[0];
    let arg_ty = first_arg.ty();
    let arg_ty = arg_ty?;
    let TyKind::RigidTy(RigidTy::Array(elem_ty, const_len)) = arg_ty.kind() else {
        trace!("into_iter on non-array type: {:?}", arg_ty);
        return None;
    };

    // Extract the compile-time length
    let len_result = const_len.eval_target_usize();
    let array_len = len_result.ok()? as usize;
    debug!("Detected array into_iter: elem_ty={:?}, len={}", elem_ty, array_len);

    // Check if element type is ZST
    let is_zst = is_zst_type(&elem_ty);

    // Get the array operand (first argument)
    if args.is_empty() {
        return None;
    }
    let array_place = match &args[0] {
        Operand::Copy(place) | Operand::Move(place) => place.clone(),
        Operand::Constant(_) => {
            // Constant arrays need special handling:
            // - Zero-length [T; 0]: Transform to eliminate iterator infrastructure (#492)
            // - ZST elements [(); N]: Transform but don't index (element is always ())
            // - Non-ZST constant arrays: Rare, skip for now
            //
            // For zero-length arrays, the transformed loop immediately exits
            // (since _idx < N where N=0 means 0 < 0 = false), but we still need
            // the transformation to remove IndexRange::next_unchecked which AY can't handle.
            if array_len == 0 || is_zst {
                debug!(
                    "Constant array (len={}, is_zst={}), using dummy place for transform",
                    array_len, is_zst
                );
                // Create a dummy place - we won't actually index it because:
                // - Zero-length: loop body never executes (_idx < 0 is false)
                // - ZST elements: transform_array_loop generates Rvalue::Aggregate(Tuple, [])
                // Using local 0 (return place) is safe since we never read from it.
                Place { local: 0, projection: vec![] }
            } else {
                // Non-ZST constant arrays are rare. Skip for now.
                trace!("Skipping constant array with len={} in into_iter", array_len);
                return None;
            }
        }
    };

    // Get the destination local (the iterator)
    let iter_local = destination.local;
    let target_bb = (*target)?;

    Some((array_place, array_len, elem_ty, is_zst, iter_local, target_bb))
}

/// Loop structure information for transformation.
struct LoopStructure {
    next_bb: BasicBlockIdx,
    switch_bb: BasicBlockIdx,
    exit_bb: BasicBlockIdx,
    body_bb: BasicBlockIdx,
    option_local: Local,
    elem_ty: Ty,
}

/// Find the loop structure following an into_iter call.
///
/// Pattern we're looking for:
/// ```text
/// bb_header: (target of into_iter)
///   ...
///   call Iterator::next(&mut _iter) -> bb_after_next
///
/// bb_after_next:
///   switchInt(discriminant(_opt)) -> [0: exit, 1: body]
///
/// bb_body:
///   _x = (_opt as Some).0
///   ...
///   goto -> bb_header (or bb_header' with next call)
/// ```
fn find_loop_structure(
    body: &Body,
    start_bb: BasicBlockIdx,
    _iter_local: Local,
    _array_place: Place,
    _array_len: usize,
    elem_ty: Ty,
) -> Option<LoopStructure> {
    // For now, use a simplified heuristic:
    // - Find the first Iterator::next call in or after start_bb
    // - Find the switchInt that tests the Option discriminant
    // - Find the Some/None branches

    let locals = body.locals();

    // Search for the next() call starting from start_bb
    let mut search_bb = start_bb;
    let mut visited = std::collections::HashSet::new();

    while visited.insert(search_bb) {
        let block = &body.blocks[search_bb];

        // Check if terminator is a call to Iterator::next
        if let TerminatorKind::Call { func, destination, target, .. } = &block.terminator.kind
            && let Ok(func_ty) = func.ty(locals)
            && let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind()
        {
            let fn_name = def.name();
            // fn_name may be full path like "std::iter::Iterator::next"
            // Accept any ::next call on the Iterator trait
            let is_iterator_next =
                fn_name == "next" || (fn_name.ends_with("::next") && fn_name.contains("Iterator"));
            if is_iterator_next {
                debug!("Found Iterator::next call at bb{}", search_bb);

                // Found the next call
                let option_local = destination.local;
                let next_target = (*target)?;

                // The next block should have a switchInt on the Option discriminant
                if let Some((exit_bb, body_bb)) =
                    find_option_switch(body, next_target, option_local)
                {
                    return Some(LoopStructure {
                        next_bb: search_bb,
                        switch_bb: next_target,
                        exit_bb,
                        body_bb,
                        option_local,
                        elem_ty,
                    });
                }
            }
        }

        // Follow single-successor paths
        match &block.terminator.kind {
            TerminatorKind::Goto { target } => {
                search_bb = *target;
            }
            TerminatorKind::Call { target: Some(target), .. } => {
                search_bb = *target;
            }
            _ => break, // external enum: TerminatorKind
        }
    }

    None
}

/// Find the switchInt that tests an Option discriminant.
///
/// Returns: (exit_bb for None, body_bb for Some)
///
/// The switch may be in the target block directly, or we may need to follow
/// a goto chain to find it (MIR may have intermediate blocks).
fn find_option_switch(
    body: &Body,
    start_bb: BasicBlockIdx,
    _option_local: Local,
) -> Option<(BasicBlockIdx, BasicBlockIdx)> {
    let mut bb = start_bb;
    let mut visited = std::collections::HashSet::new();

    // Follow goto chains to find the actual switch block (max 5 hops)
    while visited.len() < 5 && visited.insert(bb) {
        if bb >= body.blocks.len() {
            return None;
        }

        let block = &body.blocks[bb];

        match &block.terminator.kind {
            TerminatorKind::SwitchInt { targets, .. } => {
                // Found the switch - extract branches
                let branches: Vec<_> = targets.branches().collect();
                let otherwise = targets.otherwise();
                return find_option_branches(&branches, otherwise);
            }
            TerminatorKind::Goto { target } => {
                // Follow the goto
                bb = *target;
            }
            _ => return None, // external enum: TerminatorKind
        }
    }

    None
}

/// Extract Option branches from a switch
fn find_option_branches(
    branches: &[(u128, BasicBlockIdx)],
    otherwise: BasicBlockIdx,
) -> Option<(BasicBlockIdx, BasicBlockIdx)> {
    if branches.len() == 1 {
        // Single branch + otherwise
        let (val, target) = branches[0];

        // Determine which is None (0) and which is Some (1)
        if val == 0 {
            // val=0 target is None (exit), otherwise is Some (body)
            return Some((target, otherwise));
        } else if val == 1 {
            // val=1 target is Some (body), otherwise is None (exit)
            return Some((otherwise, target));
        }
    } else if branches.len() == 2 {
        // Two explicit branches: (0, exit_bb), (1, body_bb)
        // or (1, body_bb), (0, exit_bb) - need to find them by value
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
    }

    None
}

/// Transform an array for-loop to direct indexed iteration.
fn transform_array_loop(body: &mut MutableBody, loop_info: &ArrayForLoop) -> bool {
    if try_transform_array_loop_without_symbolic_index(body, loop_info) {
        return true;
    }

    // Create the index local (_idx: usize)
    let idx_local = body.new_local(Ty::usize_ty(), loop_info.span, Mutability::Mut);
    debug!("Created index local: _{}", idx_local);

    // Create array length constant
    let len_const = MirConst::try_from_uint(loop_info.array_len as u128, UintTy::Usize)
        .expect("array length should fit in usize");
    let len_operand =
        Operand::Constant(ConstOperand { span: loop_info.span, user_ty: None, const_: len_const });

    // Create a condition local for _idx < N
    let cond_local = body.new_local(Ty::bool_ty(), loop_info.span, Mutability::Not);
    debug!("Created condition local: _{}", cond_local);

    // Step 1: Replace into_iter call with _idx = 0
    // IMPORTANT: Keep existing statements (they may initialize the array)
    {
        let into_iter_block = body.block_mut(loop_info.into_iter_bb);

        // Keep the original target
        let original_target = match &into_iter_block.terminator.kind {
            TerminatorKind::Call { target, .. } => *target,
            _ => return false, // external enum: TerminatorKind
        };

        // DON'T clear statements - they may initialize the array!
        // Just add _idx = 0 at the end
        let zero_const =
            MirConst::try_from_uint(0u128, UintTy::Usize).expect("zero should fit in usize");
        let zero_rvalue = Rvalue::Use(Operand::Constant(ConstOperand {
            span: loop_info.span,
            user_ty: None,
            const_: zero_const,
        }));
        into_iter_block.statements.push(Statement {
            kind: StatementKind::Assign(Place::from(idx_local), zero_rvalue),
            span: loop_info.span,
        });

        // Replace terminator with goto
        if let Some(target) = original_target {
            into_iter_block.terminator =
                Terminator { kind: TerminatorKind::Goto { target }, span: loop_info.span };
        }
    }

    // Step 2: Replace Iterator::next call with condition check
    {
        let next_block = body.block_mut(loop_info.next_bb);

        // Clear statements and add condition computation
        next_block.statements.clear();

        // _cond = _idx < N
        let idx_operand = Operand::Copy(Place::from(idx_local));
        let lt_rvalue = Rvalue::BinaryOp(BinOp::Lt, idx_operand, len_operand);
        next_block.statements.push(Statement {
            kind: StatementKind::Assign(Place::from(cond_local), lt_rvalue),
            span: loop_info.span,
        });

        // Replace terminator with goto to switch block
        next_block.terminator = Terminator {
            kind: TerminatorKind::Goto { target: loop_info.switch_bb },
            span: loop_info.span,
        };
    }

    // Step 3: Replace Option switch with condition switch
    {
        let switch_block = body.block_mut(loop_info.switch_bb);

        // Replace switchInt to use our bool condition
        // Use explicit branches for both cases to match original Option switch pattern
        // 0 (false) -> exit_bb, 1 (true) -> body_bb, otherwise -> exit_bb
        let new_targets = SwitchTargets::new(
            vec![(0, loop_info.exit_bb), (1, loop_info.body_bb)],
            loop_info.exit_bb, // otherwise case (shouldn't happen for bool, but be safe)
        );

        // Clear any statements in the switch block (discriminant computation)
        switch_block.statements.clear();

        switch_block.terminator = Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from(cond_local)),
                targets: new_targets,
            },
            span: loop_info.span,
        };
    }

    // Step 4: In body block, replace Option unwrap with array indexing
    // and add index increment
    {
        let body_block = body.block_mut(loop_info.body_bb);

        // Find and replace the Option::Some unwrap pattern
        // Pattern: _elem = (_opt as Some).0
        // This is an Assign where RHS is Use/Copy/Move of a Place with:
        //   - local = option_local
        //   - projection = [Downcast(1), Field(0, _)]
        // Replace with: _elem = array[_idx] (or _elem = () for ZST)

        for stmt in &mut body_block.statements {
            if let StatementKind::Assign(lhs_place, rvalue) = &mut stmt.kind {
                // Check if RHS is accessing the option_local with Downcast+Field
                // Preserve whether the original operand was Copy or Move for soundness.
                // Non-Copy types (e.g., String) must use Move to transfer ownership.
                let (source_place, is_copy) = match rvalue {
                    Rvalue::Use(Operand::Copy(p)) => (Some(p), true),
                    Rvalue::Use(Operand::Move(p)) => (Some(p), false),
                    _ => (None, false), // external enum: Rvalue
                };

                if let Some(place) = source_place
                    && place.local == loop_info.option_local
                    && is_option_some_field_access(&place.projection)
                {
                    if loop_info.is_zst_element {
                        // For ZST elements (like `()`), generate a unit aggregate
                        // instead of indexing into the array (which doesn't exist).
                        debug!(
                            "Replacing Option::Some unwrap at {:?} with ZST unit value",
                            lhs_place
                        );
                        *rvalue = Rvalue::Aggregate(AggregateKind::Tuple, vec![]);
                    } else {
                        debug!(
                            "Found Option::Some unwrap at {:?}, replacing with array index (copy={})",
                            lhs_place, is_copy
                        );

                        // Replace with array[idx]
                        // Create new place: array_place with Index(idx_local) projection
                        let mut indexed_projection = loop_info.array_place.projection.clone();
                        indexed_projection.push(ProjectionElem::Index(idx_local));

                        let indexed_place = Place {
                            local: loop_info.array_place.local,
                            projection: indexed_projection,
                        };

                        // Preserve original Copy/Move semantics for soundness.
                        // Non-Copy types must use Move to transfer ownership correctly.
                        let operand = if is_copy {
                            Operand::Copy(indexed_place)
                        } else {
                            Operand::Move(indexed_place)
                        };
                        *rvalue = Rvalue::Use(operand);
                    }
                }
            }
        }

        // Add _idx += 1 at the end of statements (before the terminator)
        let one_const =
            MirConst::try_from_uint(1u128, UintTy::Usize).expect("one should fit in usize");
        let one_operand = Operand::Constant(ConstOperand {
            span: loop_info.span,
            user_ty: None,
            const_: one_const,
        });
        let idx_operand = Operand::Copy(Place::from(idx_local));
        let add_rvalue = Rvalue::BinaryOp(BinOp::Add, idx_operand, one_operand);
        body_block.statements.push(Statement {
            kind: StatementKind::Assign(Place::from(idx_local), add_rvalue),
            span: loop_info.span,
        });
    }

    true
}

fn try_transform_array_loop_without_symbolic_index(
    body: &mut MutableBody,
    loop_info: &ArrayForLoop,
) -> bool {
    if loop_info.array_len == 0 {
        debug!(
            "Zero-length array transform: replacing into_iter at bb{} with goto to exit bb{}",
            loop_info.into_iter_bb, loop_info.exit_bb
        );
        body.block_mut(loop_info.into_iter_bb).terminator = Terminator {
            kind: TerminatorKind::Goto { target: loop_info.exit_bb },
            span: loop_info.span,
        };
        return true;
    }
    loop_info.array_len <= MAX_FINITE_ARRAY_ITER_UNROLL
        && try_transform_array_loop_finite_unrolled(body, loop_info)
}

/// Fully unroll a small fixed-size array iterator loop into a straight-line
/// chain with constant array indices.
///
/// This is intentionally narrow: it only handles the common single-body-block
/// loop shape. More complex loop bodies fall back to the existing indexed-loop
/// lowering.
fn try_transform_array_loop_finite_unrolled(
    body: &mut MutableBody,
    loop_info: &ArrayForLoop,
) -> bool {
    let Some(loop_blocks) = collect_finite_loop_body_blocks(body, loop_info) else {
        debug!(
            "array_iter finite unroll skipped: body bb{} shape is too complex",
            loop_info.body_bb
        );
        return false;
    };

    let templates: Vec<_> = loop_blocks.iter().map(|&bb| (bb, body.blocks()[bb].clone())).collect();
    let mut maps = Vec::with_capacity(loop_info.array_len);
    maps.push(loop_blocks.iter().map(|&bb| (bb, bb)).collect::<Vec<_>>());

    for _ in 1..loop_info.array_len {
        let mut map = Vec::with_capacity(loop_blocks.len());
        for (old_bb, template) in &templates {
            let new_bb = body.push_block(template.clone());
            map.push((*old_bb, new_bb));
        }
        maps.push(map);
    }

    {
        let into_iter_block = body.block_mut(loop_info.into_iter_bb);
        into_iter_block.terminator = Terminator {
            kind: TerminatorKind::Goto { target: mapped_block(&maps[0], loop_info.body_bb) },
            span: loop_info.span,
        };
    }

    for iteration in 0..loop_info.array_len {
        for (old_bb, template_block) in &templates {
            let bb = mapped_block(&maps[iteration], *old_bb);
            let block = body.block_mut(bb);
            block.statements = template_block.statements.clone();
            replace_option_unwraps_with_const_array_read(
                &mut block.statements,
                loop_info,
                iteration,
            );
            block.terminator = remap_finite_unroll_terminator(
                &template_block.terminator,
                iteration,
                &maps,
                loop_info,
            );
        }
    }

    debug!(
        "array_iter finite unrolled loop at bb{} into {} constant-index iterations",
        loop_info.into_iter_bb, loop_info.array_len
    );
    true
}

fn collect_finite_loop_body_blocks(
    body: &MutableBody,
    loop_info: &ArrayForLoop,
) -> Option<Vec<BasicBlockIdx>> {
    let mut blocks = Vec::new();
    let mut stack = vec![loop_info.body_bb];
    while let Some(bb) = stack.pop() {
        if bb == loop_info.next_bb || bb == loop_info.switch_bb || bb == loop_info.exit_bb {
            continue;
        }
        if bb >= body.num_blocks() {
            return None;
        }
        if blocks.contains(&bb) {
            continue;
        }
        if blocks.len() >= 32 {
            return None;
        }
        blocks.push(bb);
        for target in terminator_successors(&body.blocks()[bb].terminator) {
            if target != loop_info.next_bb
                && target != loop_info.switch_bb
                && target != loop_info.exit_bb
            {
                stack.push(target);
            }
        }
    }
    blocks.sort_unstable();
    blocks.contains(&loop_info.body_bb).then_some(blocks)
}

fn terminator_successors(term: &Terminator) -> Vec<BasicBlockIdx> {
    let mut targets = Vec::new();
    match &term.kind {
        TerminatorKind::Goto { target } => targets.push(*target),
        TerminatorKind::SwitchInt { targets: switch_targets, .. } => {
            targets.extend(switch_targets.branches().map(|(_, target)| target));
            targets.push(switch_targets.otherwise());
        }
        TerminatorKind::Drop { target, unwind, .. } => {
            targets.push(*target);
            if let UnwindAction::Cleanup(bb) = unwind {
                targets.push(*bb);
            }
        }
        TerminatorKind::Call { target, unwind, .. } => {
            if let Some(target) = target {
                targets.push(*target);
            }
            if let UnwindAction::Cleanup(bb) = unwind {
                targets.push(*bb);
            }
        }
        TerminatorKind::Assert { target, unwind, .. } => {
            targets.push(*target);
            if let UnwindAction::Cleanup(bb) = unwind {
                targets.push(*bb);
            }
        }
        TerminatorKind::Return
        | TerminatorKind::Unreachable
        | TerminatorKind::Resume
        | TerminatorKind::Abort
        | TerminatorKind::InlineAsm { .. } => {}
    }
    targets
}

fn mapped_block(map: &[(BasicBlockIdx, BasicBlockIdx)], target: BasicBlockIdx) -> BasicBlockIdx {
    map.iter().find_map(|(old, new)| (*old == target).then_some(*new)).unwrap_or(target)
}

fn remap_finite_unroll_target(
    target: BasicBlockIdx,
    iteration: usize,
    maps: &[Vec<(BasicBlockIdx, BasicBlockIdx)>],
    loop_info: &ArrayForLoop,
) -> BasicBlockIdx {
    if target == loop_info.next_bb || target == loop_info.switch_bb {
        return maps
            .get(iteration + 1)
            .map(|map| mapped_block(map, loop_info.body_bb))
            .unwrap_or(loop_info.exit_bb);
    }
    mapped_block(&maps[iteration], target)
}

fn remap_finite_unroll_unwind(
    unwind: &UnwindAction,
    iteration: usize,
    maps: &[Vec<(BasicBlockIdx, BasicBlockIdx)>],
    loop_info: &ArrayForLoop,
) -> UnwindAction {
    match unwind {
        UnwindAction::Cleanup(bb) => {
            UnwindAction::Cleanup(remap_finite_unroll_target(*bb, iteration, maps, loop_info))
        }
        UnwindAction::Continue => UnwindAction::Continue,
        UnwindAction::Unreachable => UnwindAction::Unreachable,
        UnwindAction::Terminate => UnwindAction::Terminate,
    }
}

fn remap_finite_unroll_terminator(
    term: &Terminator,
    iteration: usize,
    maps: &[Vec<(BasicBlockIdx, BasicBlockIdx)>],
    loop_info: &ArrayForLoop,
) -> Terminator {
    let kind = match &term.kind {
        TerminatorKind::Goto { target } => TerminatorKind::Goto {
            target: remap_finite_unroll_target(*target, iteration, maps, loop_info),
        },
        TerminatorKind::SwitchInt { discr, targets } => {
            let branches = targets
                .branches()
                .map(|(val, target)| {
                    (val, remap_finite_unroll_target(target, iteration, maps, loop_info))
                })
                .collect();
            TerminatorKind::SwitchInt {
                discr: discr.clone(),
                targets: SwitchTargets::new(
                    branches,
                    remap_finite_unroll_target(targets.otherwise(), iteration, maps, loop_info),
                ),
            }
        }
        TerminatorKind::Drop { place, target, unwind } => TerminatorKind::Drop {
            place: place.clone(),
            target: remap_finite_unroll_target(*target, iteration, maps, loop_info),
            unwind: remap_finite_unroll_unwind(unwind, iteration, maps, loop_info),
        },
        TerminatorKind::Call { func, args, destination, target, unwind } => TerminatorKind::Call {
            func: func.clone(),
            args: args.clone(),
            destination: destination.clone(),
            target: target
                .map(|target| remap_finite_unroll_target(target, iteration, maps, loop_info)),
            unwind: remap_finite_unroll_unwind(unwind, iteration, maps, loop_info),
        },
        TerminatorKind::Assert { cond, expected, msg, target, unwind } => TerminatorKind::Assert {
            cond: cond.clone(),
            expected: *expected,
            msg: msg.clone(),
            target: remap_finite_unroll_target(*target, iteration, maps, loop_info),
            unwind: remap_finite_unroll_unwind(unwind, iteration, maps, loop_info),
        },
        TerminatorKind::Return => TerminatorKind::Return,
        TerminatorKind::Unreachable => TerminatorKind::Unreachable,
        TerminatorKind::Resume => TerminatorKind::Resume,
        TerminatorKind::Abort => TerminatorKind::Abort,
        TerminatorKind::InlineAsm { .. } => term.kind.clone(),
    };
    Terminator { kind, span: term.span }
}

fn replace_option_unwraps_with_const_array_read(
    statements: &mut [Statement],
    loop_info: &ArrayForLoop,
    iteration: usize,
) {
    for stmt in statements {
        let StatementKind::Assign(lhs_place, rvalue) = &mut stmt.kind else {
            continue;
        };

        let (source_place, is_copy) = match rvalue {
            Rvalue::Use(Operand::Copy(p)) => (Some(p), true),
            Rvalue::Use(Operand::Move(p)) => (Some(p), false),
            _ => (None, false),
        };

        let Some(place) = source_place else {
            continue;
        };
        if place.local != loop_info.option_local || !is_option_some_field_access(&place.projection)
        {
            continue;
        }

        if loop_info.is_zst_element {
            debug!("Replacing Option::Some unwrap at {:?} with ZST unit value", lhs_place);
            *rvalue = Rvalue::Aggregate(AggregateKind::Tuple, vec![]);
            continue;
        }

        let mut indexed_projection = loop_info.array_place.projection.clone();
        indexed_projection.push(ProjectionElem::ConstantIndex {
            offset: iteration as u64,
            min_length: loop_info.array_len as u64,
            from_end: false,
        });
        let indexed_place =
            Place { local: loop_info.array_place.local, projection: indexed_projection };

        let operand =
            if is_copy { Operand::Copy(indexed_place) } else { Operand::Move(indexed_place) };
        *rvalue = Rvalue::Use(operand);
    }
}

/// Check if a type debug name belongs to the array-iterator infrastructure family.
/// Part of #3713: matches the full residual carrier set, not only `IntoIter`.
fn is_array_iter_infra_ty_name(ty_name: &str) -> bool {
    ty_name.contains("IntoIter")
        || ty_name.contains("PolymorphicIter")
        || ty_name.contains("IndexRange")
        || ty_name.contains("array::iter::iter_inner")
}

/// Check if a call's function type string represents an array-iterator infrastructure call.
/// Part of #3713: matches broader family than just IntoIter/Iterator::next.
fn is_array_iter_infra_call(ty_str: &str) -> bool {
    ty_str.contains("IntoIter")
        || ty_str.contains("Iterator::next")
        || ty_str.contains("PolymorphicIter")
        || ty_str.contains("IndexRange::next")
        || ty_str.contains("IndexRange::next_unchecked")
}

/// Eliminate all iterator infrastructure from the transformed body.
///
/// After the ArrayIterUnrollPass replaces the for-loop with indexed access, the
/// original iterator locals and calls are unused but may still be present in the
/// MIR (especially in unreachable blocks for zero-length arrays, or in cleanup
/// paths). The reachability collector visits ALL blocks regardless of reachability,
/// so any remaining references to iterator types cause monomorphization of
/// PolymorphicIter Drop glue, which contains unsupported constructs.
///
/// This function:
/// 1. Finds ALL locals with array-iterator infrastructure types
/// 2. Replaces their types with `()` to prevent Drop glue monomorphization
/// 3. Eliminates Drop terminators on those locals
/// 4. Replaces Call terminators to iterator functions with Goto
fn eliminate_iterator_infrastructure(body: &mut MutableBody, loop_info: &ArrayForLoop) {
    let num_blocks = body.num_blocks();
    let unit_ty = Ty::new_tuple(&[]);

    // Step 1: Find ALL locals whose type is part of the array-iterator
    // infrastructure family. This catches IntoIter, PolymorphicIter, IndexRange,
    // and helper closures that the desugaring creates.
    let mut iter_locals = Vec::new();
    for (idx, local_decl) in body.locals().iter().enumerate() {
        let ty_name = format!("{:?}", local_decl.ty);
        if is_array_iter_infra_ty_name(&ty_name) {
            iter_locals.push(idx);
        }
    }
    // Always include the known iter_local from detection
    if !iter_locals.contains(&loop_info.iter_local) {
        iter_locals.push(loop_info.iter_local);
    }

    debug!("Iterator locals to neutralize: {:?}", iter_locals);

    // Step 2: Replace all iterator locals' types with () to prevent Drop glue
    // monomorphization of PolymorphicIter.
    for &local_idx in &iter_locals {
        body.set_local_ty(local_idx, unit_ty);
    }

    // Step 3: Replace Drop terminators on iterator locals with Goto.
    for bb_idx in 0..num_blocks {
        let block = &body.blocks()[bb_idx];
        if let TerminatorKind::Drop { place, target, .. } = &block.terminator.kind {
            if iter_locals.contains(&place.local) && place.projection.is_empty() {
                let target = *target;
                let span = block.terminator.span;
                debug!("Eliminating iterator drop at bb{}: local=_{}", bb_idx, place.local);

                let block = body.block_mut(bb_idx);
                block.terminator = Terminator { kind: TerminatorKind::Goto { target }, span };
            }
        }
    }

    // Step 4: Replace Call terminators to iterator functions with Goto.
    // Matches the full infrastructure family: IntoIter, PolymorphicIter,
    // IndexRange, Iterator::next, and helper calls on infrastructure locals.
    for bb_idx in 0..num_blocks {
        let block = &body.blocks()[bb_idx];
        if let TerminatorKind::Call { func, target, .. } = &block.terminator.kind {
            let is_iter_call = if let Ok(func_ty) = func.ty(body.locals()) {
                let ty_str = format!("{:?}", func_ty);
                is_array_iter_infra_call(&ty_str)
            } else {
                false
            };

            if is_iter_call {
                let goto_target = target.unwrap_or(0); // 0 = entry block fallback
                let span = block.terminator.span;
                debug!("Eliminating iterator call at bb{}", bb_idx);

                let block = body.block_mut(bb_idx);
                block.statements.clear();
                block.terminator =
                    Terminator { kind: TerminatorKind::Goto { target: goto_target }, span };
            }
        }
    }
}

/// Check if a projection represents enum variant field access (typically Option::Some).
///
/// Pattern: [Downcast(_), Field(0, _)] - any downcast followed by field 0.
/// This matches Option::Some (typically variant 1) but also any other enum
/// variant with a single field. This is intentional: the transformation
/// only applies in contexts where we've already verified we're iterating
/// over an array, so any enum unwrap in that context is the iterator result.
fn is_option_some_field_access(projection: &[ProjectionElem]) -> bool {
    // Look for Downcast followed by Field(0)
    let mut found_downcast = false;
    let mut downcast_variant = None;

    for elem in projection {
        match elem {
            ProjectionElem::Downcast(variant_idx) => {
                // Some is typically variant 1 in Option enum
                // But we should accept any downcast as it indicates enum access
                found_downcast = true;
                downcast_variant = Some(variant_idx.to_index());
            }
            ProjectionElem::Field(field_idx, _ty) => {
                // After a downcast, field 0 is the inner value
                if found_downcast && *field_idx == 0 {
                    debug!(
                        "is_option_some_field_access: found Downcast({:?}), Field(0)",
                        downcast_variant
                    );
                    return true;
                }
                // Field without preceding downcast isn't what we're looking for
                return false;
            }
            _ => found_downcast = false, // external enum: ProjectionElem
        }
    }

    false
}

#[cfg(test)]
#[path = "array_iter/tests.rs"]
mod tests;
