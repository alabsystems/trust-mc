// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Implementation of the points-to analysis using Rust's native dataflow framework. This provides
//! necessary aliasing information for instrumenting delayed UB later on.
//!
//! The analysis uses Rust's dataflow framework by implementing appropriate traits to leverage the
//! existing fixpoint solver infrastructure. The main trait responsible for the dataflow analysis
//! behavior is `rustc_mir_dataflow::Analysis`: it provides two methods that are responsible for
//! handling statements and terminators, which we implement.
//!
//! The analysis proceeds by looking at each instruction in the dataflow order and collecting all
//! possible aliasing relations that the instruction introduces. If a terminator is a function call,
//! the analysis recurs into the function and then joins the information retrieved from it into the
//! original graph.
//!
//! For each instruction, the analysis first resolves dereference projections for each place to
//! determine which places it could point to. This is done by finding a set of successors in the
//! graph for each dereference projection.
//!
//! Then, the analysis adds the appropriate edges into the points-to graph. It proceeds until there
//! is no new information to be discovered.
//!
//! Currently, the analysis is not field-sensitive: e.g., if a field of a place aliases to some
//! other place, we treat it as if the place itself aliases to another place.

use crate::{
    intrinsics::Intrinsic,
    kani_middle::{
        points_to::{MemLoc, PointsToGraph},
        reachability::CallGraph,
        transform::RustcInternalMir,
    },
};
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, CallReturnPlaces, Location, NonDivergingIntrinsic, Operand, Place,
        ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorEdges,
        TerminatorKind,
    },
    ty::{Instance, InstanceKind, List, TyCtxt, TyKind, TypingEnv},
};
use rustc_mir_dataflow::{Analysis, Forward, JoinSemiLattice};
use rustc_public::mir::{Body as StableBody, mono::Instance as StableInstance};
use rustc_public::rustc_internal;
use rustc_span::{DUMMY_SP, source_map::Spanned};
use std::collections::HashSet;

/// Main points-to analysis object.
struct PointsToAnalysis<'a, 'tcx> {
    instance: Instance<'tcx>,
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    /// This will be used in the future to resolve function pointer and vtable calls. Currently, we
    /// can resolve call graph edges just by looking at the terminators and erroring if we can't
    /// resolve the callee.
    call_graph: &'a CallGraph,
    /// This graph should contain a subset of the points-to graph reachable from function arguments.
    /// For the entry function it will be empty (as it supposedly does not have any parameters).
    initial_graph: PointsToGraph<'tcx>,
}

/// Public points-to analysis entry point. Performs the analysis on a body, outputting the graph
/// containing aliasing information of the body itself and any body reachable from it.
pub(crate) fn run_points_to_analysis<'tcx>(
    body: &StableBody,
    tcx: TyCtxt<'tcx>,
    instance: StableInstance,
    call_graph: &CallGraph,
) -> PointsToGraph<'tcx> {
    // Dataflow analysis does not yet work with StableMIR, so need to perform backward
    // conversion.
    let internal_instance = rustc_internal::internal(tcx, instance);
    let internal_body = body.internal_mir(tcx);
    PointsToAnalysis::run(
        &internal_body,
        tcx,
        internal_instance,
        call_graph,
        PointsToGraph::empty(),
    )
}

impl<'a, 'tcx> PointsToAnalysis<'a, 'tcx> {
    /// Perform the analysis on a body, outputting the graph containing aliasing information of the
    /// body itself and any body reachable from it.
    fn run(
        body: &'a Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        instance: Instance<'tcx>,
        call_graph: &'a CallGraph,
        initial_graph: PointsToGraph<'tcx>,
    ) -> PointsToGraph<'tcx> {
        let analysis = Self { instance, body, tcx, call_graph, initial_graph };
        // This creates a fixpoint solver using the initial graph, the body, and extra information
        // and solves the dataflow problem, producing the cursor, which contains dataflow state for
        // each instruction in the body.
        let mut cursor =
            analysis.iterate_to_fixpoint(tcx, body, Some(Self::NAME)).into_results_cursor(body);
        // We collect dataflow state at each `Return` terminator to determine the full aliasing
        // graph for the function. This is sound since those are the only places where the function
        // finishes, so the dataflow state at those places will be a union of dataflow states
        // preceding to it, which means every possible execution is taken into account.
        let mut results = PointsToGraph::empty();
        for (idx, bb) in body.basic_blocks.iter().enumerate() {
            if let TerminatorKind::Return = bb.terminator().kind {
                // Switch the cursor to the end of the block ending with `Return`.
                cursor.seek_to_block_end(idx.into());
                // Retrieve the dataflow state and join into the results graph.
                results.join(cursor.get());
            }
        }
        results
    }
}

impl<'tcx> Analysis<'tcx> for PointsToAnalysis<'_, 'tcx> {
    /// Dataflow state at each instruction.
    type Domain = PointsToGraph<'tcx>;

    type Direction = Forward;

    const NAME: &'static str = "PointsToAnalysis";

    /// Dataflow state instantiated at the beginning of each basic block, before the state from
    /// previous basic blocks gets joined into it.
    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        PointsToGraph::empty()
    }

    /// Dataflow state instantiated at the entry into the body; this should be the initial dataflow
    /// graph.
    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        state.join(&self.initial_graph);
    }

    /// Update current dataflow state based on the information we can infer from the given
    /// statement.
    fn apply_primary_statement_effect(
        &self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        _location: Location,
    ) {
        // The only two statements that can introduce new aliasing information are assignments and
        // copies using `copy_nonoverlapping`.
        match &statement.kind {
            StatementKind::Assign(assign_box) => {
                let (place, rvalue) = assign_box.as_ref();
                // Resolve all dereference projections for the lvalue.
                let lvalue_set = state.resolve_place(*place, self.instance);
                // Determine all places rvalue could point to.
                let rvalue_set = self.successors_for_rvalue(state, rvalue);
                // Create an edge between all places which could be lvalue and all places rvalue
                // could be pointing to.
                state.extend(&lvalue_set, &rvalue_set);
            }
            StatementKind::Intrinsic(non_diverging_intrinsic) => {
                match non_diverging_intrinsic.as_ref() {
                    NonDivergingIntrinsic::CopyNonOverlapping(copy_nonoverlapping) => {
                        // Copy between the values pointed by `*const a` and `*mut b` is
                        // semantically equivalent to *b = *a with respect to aliasing.
                        self.apply_copy_effect(
                            state,
                            &copy_nonoverlapping.src,
                            &copy_nonoverlapping.dst,
                        );
                    }
                    NonDivergingIntrinsic::Assume(..) => { /* This is a no-op. */ }
                }
            }
            StatementKind::FakeRead(..)
            | StatementKind::SetDiscriminant { .. }
            | StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..)
            | StatementKind::Retag(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::BackwardIncompatibleDropHint { .. }
            | StatementKind::Nop => { /* This is a no-op with regard to aliasing. */ }
        }
    }

    fn apply_primary_terminator_effect<'mir>(
        &self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        if let TerminatorKind::Call { func, args, destination, .. } = &terminator.kind {
            // Attempt to resolve callee. For now, we panic if the callee cannot be resolved (e.g.,
            // if a function pointer call is used), but we could leverage the call graph to resolve
            // it.
            let instance = match try_resolve_instance(self.body, func, self.tcx) {
                Ok(instance) => instance,
                Err(reason) => {
                    self.apply_unresolved_call_effect(state, args, destination, location, &reason);
                    return terminator.edges();
                }
            };
            match instance.def {
                // Intrinsics could introduce aliasing edges we care about, so need to handle them.
                InstanceKind::Intrinsic(_) => {
                    match Intrinsic::from_instance(&rustc_internal::stable(instance)) {
                        intrinsic if is_identity_aliasing_intrinsic(&intrinsic) => {
                            // Treat the intrinsic as an aggregate, taking a union of all of the
                            // arguments' aliases.
                            let destination_set = state.resolve_place(*destination, self.instance);
                            let operands_set = args
                                .into_iter()
                                .flat_map(|operand| {
                                    self.successors_for_operand(state, &operand.node)
                                })
                                .collect();
                            state.extend(&destination_set, &operands_set);
                        }
                        // All `atomic_cxchg` intrinsics take `dst, old, src` as arguments.
                        // This is equivalent to `destination = *dst; *dst = src`.
                        Intrinsic::AtomicCxchg | Intrinsic::AtomicCxchgWeak => {
                            let src_set = self.successors_for_operand(state, &args[2].node);
                            let dst_set = self.successors_for_deref(state, &args[0].node);
                            let destination_set = state.resolve_place(*destination, self.instance);
                            state.extend(&destination_set, &state.successors(&dst_set));
                            state.extend(&dst_set, &src_set);
                        }
                        // All `atomic_load` intrinsics take `src` as an argument.
                        // This is equivalent to `destination = *src`.
                        Intrinsic::AtomicLoad => {
                            let src_set = self.successors_for_deref(state, &args[0].node);
                            let destination_set = state.resolve_place(*destination, self.instance);
                            state.extend(&destination_set, &state.successors(&src_set));
                        }
                        // All `atomic_store` intrinsics take `dst, val` as arguments.
                        // This is equivalent to `*dst = val`.
                        Intrinsic::AtomicStore => {
                            let dst_set = self.successors_for_deref(state, &args[0].node);
                            let val_set = self.successors_for_operand(state, &args[1].node);
                            state.extend(&dst_set, &val_set);
                        }
                        // All other `atomic` intrinsics take `dst, src` as arguments.
                        // This is equivalent to `destination = *dst; *dst = src`.
                        Intrinsic::AtomicAnd
                        | Intrinsic::AtomicMax
                        | Intrinsic::AtomicMin
                        | Intrinsic::AtomicNand
                        | Intrinsic::AtomicOr
                        | Intrinsic::AtomicUmax
                        | Intrinsic::AtomicUmin
                        | Intrinsic::AtomicXadd
                        | Intrinsic::AtomicXchg
                        | Intrinsic::AtomicXor
                        | Intrinsic::AtomicXsub => {
                            let src_set = self.successors_for_operand(state, &args[1].node);
                            let dst_set = self.successors_for_deref(state, &args[0].node);
                            let destination_set = state.resolve_place(*destination, self.instance);
                            state.extend(&destination_set, &state.successors(&dst_set));
                            state.extend(&dst_set, &src_set);
                        }
                        // Similar to `copy_nonoverlapping`, argument order is `src`, `dst`, `count`.
                        Intrinsic::Copy => {
                            self.apply_copy_effect(state, &args[0].node, &args[1].node);
                        }
                        Intrinsic::TypedSwap => {
                            // Extend from x_set to y_set and vice-versa so that both x and y alias
                            // to a union of places each of them alias to.
                            let x_set = self.successors_for_deref(state, &args[0].node);
                            let y_set = self.successors_for_deref(state, &args[1].node);
                            state.extend(&x_set, &state.successors(&y_set));
                            state.extend(&y_set, &state.successors(&x_set));
                        }
                        // Similar to `copy_nonoverlapping`, argument order is `dst`, `src`, `count`.
                        Intrinsic::VolatileCopyMemory
                        | Intrinsic::VolatileCopyNonOverlappingMemory => {
                            self.apply_copy_effect(state, &args[1].node, &args[0].node);
                        }
                        // Semantically equivalent to dest = *a
                        Intrinsic::VolatileLoad | Intrinsic::UnalignedVolatileLoad => {
                            // Destination of the return value.
                            let lvalue_set = state.resolve_place(*destination, self.instance);
                            let rvalue_set = self.successors_for_deref(state, &args[0].node);
                            state.extend(&lvalue_set, &state.successors(&rvalue_set));
                        }
                        // Semantically equivalent *a = b.
                        Intrinsic::VolatileStore => {
                            let lvalue_set = self.successors_for_deref(state, &args[0].node);
                            let rvalue_set = self.successors_for_operand(state, &args[1].node);
                            state.extend(&lvalue_set, &rvalue_set);
                        }
                        Intrinsic::Unimplemented { .. } => {
                            // This will be taken care of at the codegen level.
                        }
                        intrinsic => {
                            // Unknown intrinsic - use conservative aliasing assumption
                            // rather than panicking. This allows analysis to proceed with
                            // possibly over-approximated aliasing relationships.
                            tracing::warn!(
                                "points_to_analysis: unsupported intrinsic `{intrinsic:?}` in `{}`, \
                                 using conservative aliasing. See: \
                                 https://github.com/model-checking/kani/issues/3300",
                                self.tcx.def_path_str(self.instance.def_id())
                            );
                            // Conservative: assume destination may alias any pointer argument.
                            // This matches the identity aliasing intrinsic behavior.
                            let destination_set = state.resolve_place(*destination, self.instance);
                            let operands_set = args
                                .into_iter()
                                .flat_map(|operand| {
                                    self.successors_for_operand(state, &operand.node)
                                })
                                .collect();
                            state.extend(&destination_set, &operands_set);
                        }
                    }
                }
                _ => {
                    // external enum: InstanceKind
                    if self.tcx.is_foreign_item(instance.def_id()) {
                        match self
                            .tcx
                            .def_path_str_with_args(instance.def_id(), instance.args)
                            .as_str()
                        {
                            // This is an internal function responsible for heap allocation,
                            // which creates a new node we need to add to the points-to graph.
                            "alloc::alloc::__rust_alloc" | "alloc::alloc::__rust_alloc_zeroed" => {
                                let lvalue_set = state.resolve_place(*destination, self.instance);
                                let rvalue_set = HashSet::from([MemLoc::new_heap_allocation(
                                    self.instance,
                                    location,
                                )]);
                                state.extend(&lvalue_set, &rvalue_set);
                            }
                            _ => {} // non-enum: &str (def_path_str)
                        }
                    } else {
                        // Otherwise, handle this as a regular function call.
                        self.apply_regular_call_effect(state, instance, args, destination);
                    }
                }
            }
        }
        terminator.edges()
    }

    /// We don't care about this and just need to implement this to implement the trait.
    fn apply_call_return_effect(
        &self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
    }
}

/// Try retrieving instance for the given function operand.
fn try_resolve_instance<'tcx>(
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Result<Instance<'tcx>, String> {
    let ty = func.ty(body, tcx);
    match ty.kind() {
        TyKind::FnDef(def, args) => {
            // Span here is used for error-reporting, which we don't expect to encounter anyway, so
            // it is ok to use a dummy.
            Ok(Instance::expect_resolve(
                tcx,
                TypingEnv::fully_monomorphized(),
                *def,
                args,
                DUMMY_SP,
            ))
        }
        _ => Err(format!(
            // external enum: TyKind
            "trust_mc was not able to resolve the instance of the function operand `{ty:?}`. Currently, memory initialization checks in presence of function pointers and vtable calls are not supported. For more information about planned support, see https://github.com/model-checking/kani/issues/3300."
        )),
    }
}

impl<'tcx> PointsToAnalysis<'_, 'tcx> {
    /// Update the analysis state according to the operation, which is semantically equivalent to `*to = *from`.
    fn apply_copy_effect(
        &self,
        state: &mut PointsToGraph<'tcx>,
        from: &Operand<'tcx>,
        to: &Operand<'tcx>,
    ) {
        let lvalue_set = self.successors_for_deref(state, to);
        let rvalue_set = self.successors_for_deref(state, from);
        state.extend(&lvalue_set, &state.successors(&rvalue_set));
    }

    /// Find all places where the operand could point to at the current stage of the program.
    fn successors_for_operand(
        &self,
        state: &mut PointsToGraph<'tcx>,
        operand: &Operand<'tcx>,
    ) -> HashSet<MemLoc<'tcx>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                // Find all places which are pointed to by the place.
                state.successors(&state.resolve_place(*place, self.instance))
            }
            Operand::Constant(const_operand) => {
                // Constants could point to a static, so need to check for that.
                if let Some(static_def_id) = const_operand.check_static_ptr(self.tcx) {
                    HashSet::from([MemLoc::new_static_allocation(static_def_id)])
                } else {
                    HashSet::new()
                }
            }
        }
    }

    /// Find all places where the deref of the operand could point to at the current stage of the program.
    fn successors_for_deref(
        &self,
        state: &mut PointsToGraph<'tcx>,
        operand: &Operand<'tcx>,
    ) -> HashSet<MemLoc<'tcx>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => state.resolve_place(
                place.project_deeper(&[ProjectionElem::Deref], self.tcx),
                self.instance,
            ),
            Operand::Constant(const_operand) => {
                // Constants could point to a static, so need to check for that.
                if let Some(static_def_id) = const_operand.check_static_ptr(self.tcx) {
                    HashSet::from([MemLoc::new_static_allocation(static_def_id)])
                } else {
                    HashSet::new()
                }
            }
        }
    }

    /// Update the analysis state according to the regular function call.
    fn apply_regular_call_effect(
        &self,
        state: &mut PointsToGraph<'tcx>,
        instance: Instance<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
    ) {
        // Here we simply call another function, so need to retrieve internal body for it.
        let new_body = {
            let stable_instance = rustc_internal::stable(instance);
            let stable_body = stable_instance.body().expect("instance should have body");
            stable_body.internal_mir(self.tcx)
        };

        // In order to be efficient, create a new graph for the function call analysis, which only
        // contains arguments and statics and anything transitively reachable from them.
        let mut initial_graph = PointsToGraph::empty();
        for arg in args {
            match arg.node {
                Operand::Copy(place) | Operand::Move(place) => {
                    initial_graph
                        .join(&state.transitive_closure(state.resolve_place(place, self.instance)));
                }
                Operand::Constant(_) => {}
            }
        }

        // A missing link is the connections between the arguments in the caller and parameters in
        // the callee, add it to the graph.
        if self.tcx.is_closure_like(instance.def.def_id()) {
            // This means we encountered a closure call.
            // Sanity check. The first argument is the closure itself and the second argument is the tupled arguments from the caller.
            assert!(args.len() == 2);
            // First, connect all upvars.
            let lvalue_set = HashSet::from([MemLoc::new_stack_allocation(
                instance,
                Place { local: 1usize.into(), projection: List::empty() },
            )]);
            let rvalue_set = self.successors_for_operand(state, &args[0].node);
            initial_graph.extend(&lvalue_set, &rvalue_set);
            // Then, connect the argument tuple to each of the spread arguments.
            let spread_arg_set = self.successors_for_operand(state, &args[1].node);
            for i in 0..new_body.arg_count {
                let lvalue_set = HashSet::from([MemLoc::new_stack_allocation(
                    instance,
                    Place {
                        local: (i + 1).into(), // Since arguments in the callee are starting with 1, account for that.
                        projection: List::empty(),
                    },
                )]);
                // This conservatively assumes all arguments alias to all parameters.
                initial_graph.extend(&lvalue_set, &spread_arg_set);
            }
        } else {
            // Otherwise, simply connect all arguments to parameters.
            for (i, arg) in args.iter().enumerate() {
                let lvalue_set = HashSet::from([MemLoc::new_stack_allocation(
                    instance,
                    Place {
                        local: (i + 1).into(), // Since arguments in the callee are starting with 1, account for that.
                        projection: List::empty(),
                    },
                )]);
                let rvalue_set = self.successors_for_operand(state, &arg.node);
                initial_graph.extend(&lvalue_set, &rvalue_set);
            }
        }

        // Run the analysis.
        let new_result =
            PointsToAnalysis::run(&new_body, self.tcx, instance, self.call_graph, initial_graph);
        // Merge the results into the current state.
        state.join(&new_result);

        // Connect the return value to the return destination.
        let lvalue_set = state.resolve_place(*destination, self.instance);
        let rvalue_set = HashSet::from([MemLoc::new_stack_allocation(
            instance,
            Place { local: 0usize.into(), projection: List::empty() },
        )]);
        state.extend(&lvalue_set, &state.successors(&rvalue_set));
    }

    /// Conservatively update the points-to graph when we cannot resolve a callee.
    fn apply_unresolved_call_effect(
        &self,
        state: &mut PointsToGraph<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        location: Location,
        _reason: &str,
    ) {
        let mut all_known = state.all_nodes();
        // Model unknown return values with a fresh heap allocation at this callsite.
        all_known.insert(MemLoc::new_heap_allocation(self.instance, location));

        let mut affected_nodes = HashSet::new();
        for arg in args {
            match &arg.node {
                Operand::Copy(place) | Operand::Move(place) => {
                    let arg_set = state.resolve_place(*place, self.instance);
                    let reachable = state.transitive_closure(arg_set);
                    affected_nodes.extend(reachable.all_nodes());
                }
                Operand::Constant(const_operand) => {
                    if let Some(static_def_id) = const_operand.check_static_ptr(self.tcx) {
                        affected_nodes.insert(MemLoc::new_static_allocation(static_def_id));
                    }
                }
            }
        }

        let destination_set = state.resolve_place(*destination, self.instance);
        if destination_set.is_empty() {
            // If we cannot resolve the destination (e.g., unknown pointees), fall back to the base.
            let destination_base = Place { local: destination.local, projection: List::empty() };
            let fallback =
                HashSet::from([MemLoc::new_stack_allocation(self.instance, destination_base)]);
            state.extend(&fallback, &all_known);
        } else {
            state.extend(&destination_set, &all_known);
        }

        if !affected_nodes.is_empty() {
            state.extend(&affected_nodes, &all_known);
        }
    }

    /// Find all places where the rvalue could point to at the current stage of the program.
    fn successors_for_rvalue(
        &self,
        state: &mut PointsToGraph<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> HashSet<MemLoc<'tcx>> {
        match rvalue {
            // Using the operand unchanged requires determining where it could point, which
            // `successors_for_operand` does.
            Rvalue::Use(operand)
            | Rvalue::ShallowInitBox(operand, _)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::Repeat(operand, ..)
            | Rvalue::WrapUnsafeBinder(operand, _) => self.successors_for_operand(state, operand),
            Rvalue::Ref(_, _, ref_place) | Rvalue::RawPtr(_, ref_place) => {
                // Here, a reference to a place is created, which leaves the place
                // unchanged.
                state.resolve_place(*ref_place, self.instance)
            }
            Rvalue::BinaryOp(bin_op, operands) => {
                let (l_operand, r_operand) = operands.as_ref();
                match *bin_op {
                    BinOp::Offset => {
                        // Offsetting a pointer should still be within the boundaries of the
                        // same object, so we can simply use the operand unchanged.
                        self.successors_for_operand(state, l_operand)
                    }
                    BinOp::Add
                    | BinOp::AddUnchecked
                    | BinOp::AddWithOverflow
                    | BinOp::Sub
                    | BinOp::SubUnchecked
                    | BinOp::SubWithOverflow
                    | BinOp::Mul
                    | BinOp::MulUnchecked
                    | BinOp::MulWithOverflow
                    | BinOp::Div
                    | BinOp::Rem
                    | BinOp::BitXor
                    | BinOp::BitAnd
                    | BinOp::BitOr
                    | BinOp::Shl
                    | BinOp::ShlUnchecked
                    | BinOp::Shr
                    | BinOp::ShrUnchecked => {
                        // While unlikely, those could be pointer addresses, so we need to
                        // track them. We assume that even shifted addresses will be within
                        // the same original object.
                        let mut operand_set = self.successors_for_operand(state, l_operand);
                        operand_set.extend(self.successors_for_operand(state, r_operand));
                        operand_set
                    }
                    BinOp::Eq
                    | BinOp::Lt
                    | BinOp::Le
                    | BinOp::Ne
                    | BinOp::Ge
                    | BinOp::Gt
                    | BinOp::Cmp => {
                        // None of those could yield an address as the result.
                        HashSet::new()
                    }
                }
            }
            Rvalue::UnaryOp(_, operand) => {
                // The same story from BinOp applies here, too. Need to track those things.
                self.successors_for_operand(state, operand)
            }
            Rvalue::NullaryOp(..) | Rvalue::Discriminant(..) => {
                // All of those should yield a constant.
                HashSet::new()
            }
            Rvalue::Aggregate(_, operands) => {
                // Conservatively find a union of all places mentioned here and resolve
                // their pointees.
                operands
                    .iter()
                    .flat_map(|operand| self.successors_for_operand(state, operand))
                    .collect()
            }
            Rvalue::CopyForDeref(place) => {
                // Resolve pointees of a place.
                state.successors(&state.resolve_place(*place, self.instance))
            }
            Rvalue::ThreadLocalRef(def_id) => {
                // We store a def_id of a static.
                HashSet::from([MemLoc::new_static_allocation(*def_id)])
            }
        }
    }
}

fn is_identity_aliasing_intrinsic(intrinsic: &Intrinsic) -> bool {
    match intrinsic {
        Intrinsic::AddWithOverflow
        | Intrinsic::AlignOfVal
        | Intrinsic::ArithOffset
        | Intrinsic::AssertInhabited
        | Intrinsic::AssertMemUninitializedValid
        | Intrinsic::AssertZeroValid
        | Intrinsic::Assume
        | Intrinsic::Bitreverse
        | Intrinsic::BlackBox
        | Intrinsic::Breakpoint
        | Intrinsic::Bswap
        | Intrinsic::CeilF32
        | Intrinsic::CeilF64
        | Intrinsic::CompareBytes
        | Intrinsic::CopySignF32
        | Intrinsic::CopySignF64
        | Intrinsic::CosF32
        | Intrinsic::CosF64
        | Intrinsic::Ctlz
        | Intrinsic::CtlzNonZero
        | Intrinsic::Ctpop
        | Intrinsic::Cttz
        | Intrinsic::CttzNonZero
        | Intrinsic::DiscriminantValue
        | Intrinsic::ExactDiv
        | Intrinsic::Exp2F32
        | Intrinsic::Exp2F64
        | Intrinsic::ExpF32
        | Intrinsic::ExpF64
        | Intrinsic::FabsF32
        | Intrinsic::FabsF64
        | Intrinsic::FaddFast
        | Intrinsic::FdivFast
        | Intrinsic::FloorF32
        | Intrinsic::FloorF64
        | Intrinsic::FmafF32
        | Intrinsic::FmafF64
        | Intrinsic::FmulFast
        | Intrinsic::Forget
        | Intrinsic::FsubFast
        | Intrinsic::IsValStaticallyKnown
        | Intrinsic::Likely
        | Intrinsic::Log10F32
        | Intrinsic::Log10F64
        | Intrinsic::Log2F32
        | Intrinsic::Log2F64
        | Intrinsic::LogF32
        | Intrinsic::LogF64
        | Intrinsic::MaxNumF32
        | Intrinsic::MaxNumF64
        | Intrinsic::MinNumF32
        | Intrinsic::MinNumF64
        | Intrinsic::MulWithOverflow
        | Intrinsic::PowF32
        | Intrinsic::PowF64
        | Intrinsic::PowIF32
        | Intrinsic::PowIF64
        | Intrinsic::PtrGuaranteedCmp
        | Intrinsic::PtrOffsetFrom
        | Intrinsic::PtrOffsetFromUnsigned
        | Intrinsic::RawEq
        | Intrinsic::RetagBoxToRaw
        | Intrinsic::RotateLeft
        | Intrinsic::RotateRight
        | Intrinsic::RoundF32
        | Intrinsic::RoundF64
        | Intrinsic::RoundTiesEvenF32
        | Intrinsic::RoundTiesEvenF64
        | Intrinsic::SaturatingAdd
        | Intrinsic::SaturatingSub
        | Intrinsic::SinF32
        | Intrinsic::SinF64
        | Intrinsic::SizeOfVal
        | Intrinsic::SqrtF32
        | Intrinsic::SqrtF64
        | Intrinsic::SubWithOverflow
        | Intrinsic::Transmute
        | Intrinsic::TruncF32
        | Intrinsic::TruncF64
        | Intrinsic::UncheckedDiv
        | Intrinsic::UncheckedRem
        | Intrinsic::Unlikely
        | Intrinsic::VtableSize
        | Intrinsic::VtableAlign
        | Intrinsic::WrappingAdd
        | Intrinsic::WrappingMul
        | Intrinsic::WrappingSub
        | Intrinsic::WriteBytes => {
            /* Intrinsics that do not interact with aliasing beyond propagating it. */
            true
        }
        Intrinsic::SimdAdd
        | Intrinsic::SimdAnd
        | Intrinsic::SimdDiv
        | Intrinsic::SimdRem
        | Intrinsic::SimdEq
        | Intrinsic::SimdExtract
        | Intrinsic::SimdGe
        | Intrinsic::SimdGt
        | Intrinsic::SimdInsert
        | Intrinsic::SimdLe
        | Intrinsic::SimdLt
        | Intrinsic::SimdMul
        | Intrinsic::SimdNe
        | Intrinsic::SimdOr
        | Intrinsic::SimdShl
        | Intrinsic::SimdShr
        | Intrinsic::SimdShuffle(_)
        | Intrinsic::SimdSub
        | Intrinsic::SimdXor => {
            /* SIMD operations */
            true
        }
        Intrinsic::AtomicFence | Intrinsic::AtomicSingleThreadFence => {
            /* Atomic fences */
            true
        }
        Intrinsic::AlignOf
        | Intrinsic::AtomicAnd
        | Intrinsic::AtomicCxchg
        | Intrinsic::AtomicCxchgWeak
        | Intrinsic::AtomicLoad
        | Intrinsic::AtomicMax
        | Intrinsic::AtomicMin
        | Intrinsic::AtomicNand
        | Intrinsic::AtomicOr
        | Intrinsic::AtomicStore
        | Intrinsic::AtomicUmax
        | Intrinsic::AtomicUmin
        | Intrinsic::AtomicXadd
        | Intrinsic::AtomicXchg
        | Intrinsic::AtomicXor
        | Intrinsic::AtomicXsub
        | Intrinsic::Copy
        | Intrinsic::FloatToIntUnchecked
        | Intrinsic::SimdBitmask
        | Intrinsic::SizeOf
        | Intrinsic::TypedSwap
        | Intrinsic::UnalignedVolatileLoad
        | Intrinsic::VolatileCopyMemory
        | Intrinsic::VolatileCopyNonOverlappingMemory
        | Intrinsic::VolatileLoad
        | Intrinsic::VolatileStore
        | Intrinsic::Unimplemented { .. } => {
            /* Non-identity aliasing or unsupported intrinsics. */
            false
        }
    }
}

#[cfg(test)]
#[allow(clippy::panic)] // Tests use panic! for assertion failures in helper functions
mod tests {
    use super::*;
    use rustc_driver::{Callbacks, Compilation, run_compiler};
    use rustc_hir::def_id::{DefId, DefIndex, LOCAL_CRATE};
    use rustc_interface::interface;
    use rustc_middle::mir::{
        Body, Place, ProjectionElem, TerminatorKind,
        visit::{PlaceContext, Visitor},
    };
    use rustc_middle::ty::TyCtxt;
    use std::collections::HashSet;
    use std::fs;
    use std::path::PathBuf;
    use tempfile::TempDir;

    const TEST_SOURCE: &str = r#"#![allow(dead_code)]
fn callee(p: *const i32) -> *const i32 { p }

fn target_direct(p: *const i32) -> *const i32 {
    let f: fn(*const i32) -> *const i32 = callee;
    f(p)
}

fn target_deref(p: *const i32, out: *mut *const i32) {
    let f: fn(*const i32) -> *const i32 = callee;
    unsafe { *out = f(p); }
}
"#;

    const RESOLVE_PLACE_SOURCE: &str = r#"#![allow(dead_code)]
fn single_deref(p: *const i32) -> i32 {
    unsafe { *p }
}

fn field_then_deref(p: *const (i32, *const i32)) -> i32 {
    unsafe { *(*p).1 }
}
"#;

    struct TestCallbacks<F> {
        callback: Option<F>,
    }

    impl<F> Callbacks for TestCallbacks<F>
    where
        F: for<'tcx> FnOnce(TyCtxt<'tcx>) + Send,
    {
        fn after_analysis<'tcx>(
            &mut self,
            _compiler: &interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> Compilation {
            let callback = self.callback.take().expect("callback already consumed");
            rustc_internal::run(tcx, || callback(tcx))
                .expect("rustc_public bridge should initialize in test callback");
            Compilation::Stop
        }
    }

    fn with_tcx<F>(source: &str, callback: F)
    where
        F: for<'tcx> FnOnce(TyCtxt<'tcx>) + Send,
    {
        use std::sync::atomic::{AtomicU64, Ordering};
        static CRATE_COUNTER: AtomicU64 = AtomicU64::new(0);

        let temp_dir = TempDir::new().expect("create temp dir");
        let src_path: PathBuf = temp_dir.path().join("lib.rs");
        fs::write(&src_path, source).expect("write test source");

        // #1267: Use unique crate name and output directory per test to avoid
        // parallel compilation conflicts when multiple tests run simultaneously.
        let unique_id = CRATE_COUNTER.fetch_add(1, Ordering::SeqCst);
        let crate_name = format!("testcrate_{unique_id}");
        let out_dir = temp_dir.path().join("out");
        fs::create_dir_all(&out_dir).expect("create output dir");

        let mut callbacks = TestCallbacks { callback: Some(callback) };
        let args = vec![
            "rustc".to_string(),
            src_path.to_string_lossy().into_owned(),
            "--crate-type=lib".to_string(),
            format!("--crate-name={crate_name}"),
            "--out-dir".to_string(),
            out_dir.to_string_lossy().into_owned(),
            "--edition=2024".to_string(),
            "-C".to_string(),
            "opt-level=0".to_string(),
        ];
        run_compiler(&args, &mut callbacks);
    }

    fn find_fn_def_id(tcx: TyCtxt<'_>, name: &str) -> rustc_hir::def_id::DefId {
        for def_id in tcx.mir_keys(()) {
            let path = tcx.def_path_str(def_id.to_def_id());
            if path.ends_with(name) {
                return def_id.to_def_id();
            }
        }
        panic!("function {name} not found in mir_keys");
    }

    fn find_instance<'tcx>(tcx: TyCtxt<'tcx>, def_id: rustc_hir::def_id::DefId) -> Instance<'tcx> {
        Instance::expect_resolve(
            tcx,
            TypingEnv::fully_monomorphized(),
            def_id,
            tcx.mk_args(&[]),
            DUMMY_SP,
        )
    }

    struct PlaceCollector<'tcx> {
        places: Vec<Place<'tcx>>,
    }

    impl<'tcx> Visitor<'tcx> for PlaceCollector<'tcx> {
        fn visit_place(
            &mut self,
            place: &Place<'tcx>,
            _context: PlaceContext,
            _location: Location,
        ) {
            self.places.push(*place);
        }
    }

    fn collect_places<'tcx>(body: &'tcx Body<'tcx>) -> Vec<Place<'tcx>> {
        let mut collector = PlaceCollector { places: Vec::new() };
        collector.visit_body(body);
        collector.places
    }

    fn find_unresolved_call<'tcx>(
        tcx: TyCtxt<'tcx>,
        def_id: rustc_hir::def_id::DefId,
    ) -> (
        &'tcx Body<'tcx>,
        Instance<'tcx>,
        Location,
        &'tcx [Spanned<Operand<'tcx>>],
        &'tcx Place<'tcx>,
    ) {
        let instance = Instance::expect_resolve(
            tcx,
            TypingEnv::fully_monomorphized(),
            def_id,
            tcx.mk_args(&[]),
            DUMMY_SP,
        );
        let body = tcx.optimized_mir(def_id);
        for (bb_idx, bb) in body.basic_blocks.iter().enumerate() {
            if let TerminatorKind::Call { func, args, destination, .. } = &bb.terminator().kind {
                let ty = func.ty(body, tcx);
                if !matches!(ty.kind(), TyKind::FnDef(..)) {
                    let location =
                        Location { block: bb_idx.into(), statement_index: bb.statements.len() };
                    return (body, instance, location, args.as_ref(), destination);
                }
            }
        }
        panic!("no unresolved call found");
    }

    #[test]
    fn unresolved_call_effect_adds_edges_for_destination_and_args() {
        with_tcx(TEST_SOURCE, |tcx| {
            let def_id = find_fn_def_id(tcx, "target_direct");
            let (body, instance, location, args, destination) = find_unresolved_call(tcx, def_id);
            let call_graph = CallGraph::default();
            let analysis = PointsToAnalysis {
                instance,
                body,
                tcx,
                call_graph: &call_graph,
                initial_graph: PointsToGraph::empty(),
            };
            let mut state = PointsToGraph::empty();

            assert!(!state.resolve_place(*destination, instance).is_empty());
            analysis.apply_unresolved_call_effect(&mut state, args, destination, location, "test");

            let heap = MemLoc::new_heap_allocation(instance, location);
            let dest_base = Place { local: destination.local, projection: List::empty() };
            let dest_mem = MemLoc::new_stack_allocation(instance, dest_base);
            let dest_successors = state.successors(&HashSet::from([dest_mem]));
            assert!(dest_successors.contains(&heap));

            let arg_place = match &args[0].node {
                Operand::Copy(place) | Operand::Move(place) => *place,
                Operand::Constant(_) => panic!("expected place operand for arg"),
            };
            let arg_base = Place { local: arg_place.local, projection: List::empty() };
            let arg_mem = MemLoc::new_stack_allocation(instance, arg_base);
            let arg_successors = state.successors(&HashSet::from([arg_mem]));
            assert!(arg_successors.contains(&heap));
        });
    }

    #[test]
    fn unresolved_call_effect_fallbacks_when_destination_unresolvable() {
        with_tcx(TEST_SOURCE, |tcx| {
            let def_id = find_fn_def_id(tcx, "target_direct");
            let (body, instance, location, args, destination) = find_unresolved_call(tcx, def_id);
            let call_graph = CallGraph::default();
            let analysis = PointsToAnalysis {
                instance,
                body,
                tcx,
                call_graph: &call_graph,
                initial_graph: PointsToGraph::empty(),
            };
            let mut state = PointsToGraph::empty();

            let destination_base = Place { local: destination.local, projection: List::empty() };
            let deref_destination = destination_base.project_deeper(&[ProjectionElem::Deref], tcx);
            assert!(state.resolve_place(deref_destination, instance).is_empty());
            analysis.apply_unresolved_call_effect(
                &mut state,
                args,
                &deref_destination,
                location,
                "test",
            );

            let heap = MemLoc::new_heap_allocation(instance, location);
            let dest_mem = MemLoc::new_stack_allocation(instance, destination_base);
            let dest_successors = state.successors(&HashSet::from([dest_mem]));
            assert!(dest_successors.contains(&heap));
        });
    }

    #[test]
    fn resolve_place_projection_chain_tracks_exact_alias_set() {
        with_tcx(RESOLVE_PLACE_SOURCE, |tcx| {
            let def_id = find_fn_def_id(tcx, "field_then_deref");
            let instance = find_instance(tcx, def_id);
            let body = tcx.optimized_mir(def_id);
            let chain_place = collect_places(body)
                .into_iter()
                .find(|place| {
                    let deref_count = place
                        .projection
                        .iter()
                        .filter(|elem| matches!(elem, ProjectionElem::Deref))
                        .count();
                    let has_field = place
                        .projection
                        .iter()
                        .any(|elem| matches!(elem, ProjectionElem::Field(..)));
                    deref_count >= 1 && has_field
                })
                .map(|place| {
                    let deref_count = place
                        .projection
                        .iter()
                        .filter(|elem| matches!(elem, ProjectionElem::Deref))
                        .count();
                    if deref_count >= 2 {
                        place
                    } else {
                        place.project_deeper(&[ProjectionElem::Deref], tcx)
                    }
                })
                .expect("field_then_deref should contain a deref+field projection chain");

            let base_place = Place { local: 1u32.into(), projection: List::empty() };
            let base_mem = MemLoc::new_stack_allocation(instance, base_place);
            let tuple_ptr = MemLoc::new_heap_allocation(
                instance,
                Location { block: 0u32.into(), statement_index: 0 },
            );
            let final_target = MemLoc::new_heap_allocation(
                instance,
                Location { block: 0u32.into(), statement_index: 1 },
            );
            let unrelated_source = MemLoc::new_heap_allocation(
                instance,
                Location { block: 1u32.into(), statement_index: 0 },
            );
            let unrelated_target = MemLoc::new_heap_allocation(
                instance,
                Location { block: 1u32.into(), statement_index: 1 },
            );

            let mut graph = PointsToGraph::empty();
            graph.extend(&HashSet::from([base_mem]), &HashSet::from([tuple_ptr]));
            graph.extend(&HashSet::from([tuple_ptr]), &HashSet::from([final_target]));
            graph.extend(&HashSet::from([unrelated_source]), &HashSet::from([unrelated_target]));

            let resolved = graph.resolve_place(chain_place, instance);
            assert_eq!(resolved, HashSet::from([final_target]));
        });
    }

    #[test]
    fn resolve_place_stable_matches_internal_for_same_mir_place() {
        with_tcx(RESOLVE_PLACE_SOURCE, |tcx| {
            let def_id = find_fn_def_id(tcx, "single_deref");
            let instance = find_instance(tcx, def_id);
            let body = tcx.optimized_mir(def_id);
            let deref_place = collect_places(body)
                .into_iter()
                .find(|place| {
                    place
                        .projection
                        .iter()
                        .filter(|elem| matches!(elem, ProjectionElem::Deref))
                        .count()
                        == 1
                })
                .expect("single_deref should contain a single-deref place");

            let base_place = Place { local: 1u32.into(), projection: List::empty() };
            let base_mem = MemLoc::new_stack_allocation(instance, base_place);
            let target = MemLoc::new_heap_allocation(
                instance,
                Location { block: 0u32.into(), statement_index: 0 },
            );
            let mut graph = PointsToGraph::empty();
            graph.extend(&HashSet::from([base_mem]), &HashSet::from([target]));

            let internal = graph.resolve_place(deref_place, instance);
            let stable = graph.resolve_place_stable(
                rustc_internal::stable(deref_place),
                rustc_internal::stable(instance),
                tcx,
            );
            assert_eq!(stable, internal);
            assert_eq!(internal, HashSet::from([target]));
        });
    }

    #[test]
    fn transitive_closure_excludes_unreachable_non_static_but_includes_statics() {
        with_tcx(RESOLVE_PLACE_SOURCE, |tcx| {
            let def_id = find_fn_def_id(tcx, "single_deref");
            let instance = find_instance(tcx, def_id);

            let stack_root = MemLoc::new_stack_allocation(
                instance,
                Place { local: 1u32.into(), projection: List::empty() },
            );
            let heap_reachable = MemLoc::new_heap_allocation(
                instance,
                Location { block: 0u32.into(), statement_index: 0 },
            );
            let heap_unreachable = MemLoc::new_heap_allocation(
                instance,
                Location { block: 0u32.into(), statement_index: 1 },
            );
            let stack_unreachable = MemLoc::new_stack_allocation(
                instance,
                Place { local: 2u32.into(), projection: List::empty() },
            );
            let static_node = MemLoc::new_static_allocation(DefId {
                krate: LOCAL_CRATE,
                index: DefIndex::from_u32(999),
            });

            let mut graph = PointsToGraph::empty();
            graph.extend(&HashSet::from([stack_root]), &HashSet::from([heap_reachable]));
            graph.extend(&HashSet::from([heap_unreachable]), &HashSet::new());
            graph.extend(&HashSet::from([stack_unreachable]), &HashSet::new());
            graph.extend(&HashSet::from([static_node]), &HashSet::new());

            let all_nodes = graph.all_nodes();
            assert!(all_nodes.contains(&heap_unreachable));
            assert!(all_nodes.contains(&stack_unreachable));
            assert!(all_nodes.contains(&static_node));

            let closure = graph.transitive_closure(HashSet::from([stack_root]));
            let closure_nodes = closure.all_nodes();
            assert!(closure_nodes.contains(&stack_root));
            assert!(closure_nodes.contains(&heap_reachable));
            assert!(closure_nodes.contains(&static_node));
            assert!(!closure_nodes.contains(&heap_unreachable));
            assert!(!closure_nodes.contains(&stack_unreachable));
        });
    }
}
