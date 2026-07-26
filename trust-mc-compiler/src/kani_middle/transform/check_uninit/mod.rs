// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Module containing multiple transformation passes that instrument the code to detect possible UB
//! due to the accesses to uninitialized memory.

use crate::kani_middle::transform::body::{
    CheckType, InsertPosition, MutableBody, SourceInstruction,
};
use relevant_instruction::{InitRelevantInstruction, MemoryInitOp};
use rustc_public::{
    mir::{
        AggregateKind, BasicBlock, Body, ConstOperand, Mutability, Operand, Place, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind, UnwindAction, mono::Instance,
    },
    ty::{FnDef, GenericArgKind, GenericArgs, MirConst, RigidTy, Ty, TyConst, TyKind, UintTy},
};
use std::collections::HashMap;

use crate::kani_middle::kani_functions::{
    KaniFunction, KaniModel, try_kani_function_from_instance,
};
pub(crate) use delayed_ub::DelayedUbPass;
pub(crate) use ptr_uninit::UninitPass;
pub(crate) use ty_layout::{PointeeInfo, PointeeLayout};

mod delayed_ub;
mod ptr_uninit;
mod relevant_instruction;
mod ty_layout;

/// Trait that the instrumentation target providers must implement to work with the instrumenter.
pub(super) trait TargetFinder {
    fn find_all(self, body: &MutableBody) -> Vec<InitRelevantInstruction>;
}

const KANI_IS_PTR_INITIALIZED: KaniFunction = KaniFunction::Model(KaniModel::IsPtrInitialized);
const KANI_SET_PTR_INITIALIZED: KaniFunction = KaniFunction::Model(KaniModel::SetPtrInitialized);
const KANI_IS_SLICE_CHUNK_PTR_INITIALIZED: KaniFunction =
    KaniFunction::Model(KaniModel::IsSliceChunkPtrInitialized);
const KANI_SET_SLICE_CHUNK_PTR_INITIALIZED: KaniFunction =
    KaniFunction::Model(KaniModel::SetSliceChunkPtrInitialized);
const KANI_IS_SLICE_PTR_INITIALIZED: KaniFunction =
    KaniFunction::Model(KaniModel::IsSlicePtrInitialized);
const KANI_SET_SLICE_PTR_INITIALIZED: KaniFunction =
    KaniFunction::Model(KaniModel::SetSlicePtrInitialized);
const KANI_IS_STR_PTR_INITIALIZED: KaniFunction =
    KaniFunction::Model(KaniModel::IsStrPtrInitialized);
const KANI_SET_STR_PTR_INITIALIZED: KaniFunction =
    KaniFunction::Model(KaniModel::SetStrPtrInitialized);
const KANI_COPY_INIT_STATE: KaniFunction = KaniFunction::Model(KaniModel::CopyInitState);
const KANI_COPY_INIT_STATE_SINGLE: KaniFunction =
    KaniFunction::Model(KaniModel::CopyInitStateSingle);
const KANI_LOAD_ARGUMENT: KaniFunction = KaniFunction::Model(KaniModel::LoadArgument);
const KANI_STORE_ARGUMENT: KaniFunction = KaniFunction::Model(KaniModel::StoreArgument);

// Function bodies of those functions will not be instrumented as not to cause infinite recursion.
const SKIPPED_ITEMS: &[KaniFunction] = &[
    KANI_IS_PTR_INITIALIZED,
    KANI_SET_PTR_INITIALIZED,
    KANI_IS_SLICE_CHUNK_PTR_INITIALIZED,
    KANI_SET_SLICE_CHUNK_PTR_INITIALIZED,
    KANI_IS_SLICE_PTR_INITIALIZED,
    KANI_SET_SLICE_PTR_INITIALIZED,
    KANI_IS_STR_PTR_INITIALIZED,
    KANI_SET_STR_PTR_INITIALIZED,
    KANI_COPY_INIT_STATE,
    KANI_COPY_INIT_STATE_SINGLE,
    KANI_LOAD_ARGUMENT,
    KANI_STORE_ARGUMENT,
];

/// Instruments the code with checks for uninitialized memory, agnostic to the source of targets.
pub(super) struct UninitInstrumenter<'a> {
    safety_check_type: CheckType,
    unsupported_check_type: CheckType,
    /// Used to cache FnDef lookups of injected memory initialization functions.
    mem_init_fn_cache: &'a mut HashMap<KaniFunction, FnDef>,
}

impl<'a> UninitInstrumenter<'a> {
    /// Create the instrumenter and run it with the given parameters.
    pub(crate) fn run(
        body: Body,
        instance: Instance,
        safety_check_type: CheckType,
        unsupported_check_type: CheckType,
        mem_init_fn_cache: &'a mut HashMap<KaniFunction, FnDef>,
        target_finder: impl TargetFinder,
    ) -> (bool, Body) {
        let mut instrumenter =
            Self { safety_check_type, unsupported_check_type, mem_init_fn_cache };
        let body = MutableBody::from(body);
        let (changed, new_body) = instrumenter.instrument(body, instance, target_finder);
        (changed, new_body.into())
    }

    /// Instrument a body with memory initialization checks, the visitor that generates
    /// instrumentation targets must be provided via a TF type parameter.
    fn instrument(
        &mut self,
        mut body: MutableBody,
        instance: Instance,
        target_finder: impl TargetFinder,
    ) -> (bool, MutableBody) {
        // Need to break infinite recursion when memory initialization checks are inserted, so the
        // internal functions responsible for memory initialization are skipped.
        if try_kani_function_from_instance(instance)
            .map(|f| SKIPPED_ITEMS.contains(&f))
            .unwrap_or(false)
        {
            return (false, body);
        }

        let orig_len = body.blocks().len();
        for instruction in target_finder.find_all(&body).into_iter().rev() {
            let source = instruction.source;
            self.build_check_for_instruction(&mut body, instruction, source);
        }
        (orig_len != body.blocks().len(), body)
    }

    /// Inject memory initialization checks for each operation in an instruction.
    fn build_check_for_instruction(
        &mut self,
        body: &mut MutableBody,
        instruction: InitRelevantInstruction,
        mut source: SourceInstruction,
    ) {
        for operation in instruction.before_instruction {
            self.build_check_for_operation(body, &mut source, operation);
        }
        for operation in instruction.after_instruction {
            self.build_check_for_operation(body, &mut source, operation);
        }
    }

    /// Inject memory initialization check for an operation.
    fn build_check_for_operation(
        &mut self,
        body: &mut MutableBody,
        source: &mut SourceInstruction,
        operation: MemoryInitOp,
    ) {
        if let MemoryInitOp::Unsupported { reason } = &operation {
            self.inject_unsupported_check(body, source, operation.position(), reason);
            return;
        } else if let MemoryInitOp::TriviallyUnsafe { reason } = &operation {
            self.inject_safety_check(body, source, operation.position(), reason);
            return;
        }

        let pointee_info = {
            // Sanity check: memory object primitives only accept pointers.
            let ptr_operand_ty = operation.operand_ty(body);
            let pointee_ty = match ptr_operand_ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) => pointee_ty,
                _ => {
                    // external enum: TyKind
                    unreachable!(
                        "Should only build checks for raw pointers, `{ptr_operand_ty}` encountered."
                    )
                }
            };
            // Calculate pointee layout for byte-by-byte memory initialization checks.
            match PointeeInfo::from_ty(pointee_ty) {
                Ok(type_info) => type_info,
                Err(reason) => {
                    let reason = format!(
                        "trust_mc currently doesn't support checking memory initialization for pointers to `{pointee_ty}. {reason}",
                    );
                    self.inject_unsupported_check(body, source, operation.position(), &reason);
                    return;
                }
            }
        };

        match &operation {
            MemoryInitOp::CheckSliceChunk { .. }
            | MemoryInitOp::Check { .. }
            | MemoryInitOp::CheckRef { .. } => {
                self.build_get_and_check(body, source, operation, pointee_info);
            }
            MemoryInitOp::SetSliceChunk { .. }
            | MemoryInitOp::Set { .. }
            | MemoryInitOp::SetRef { .. }
            | MemoryInitOp::CreateUnion { .. } => {
                self.build_set(body, source, operation, pointee_info);
            }
            MemoryInitOp::Copy { .. } => self.build_copy(body, source, operation, pointee_info),
            MemoryInitOp::AssignUnion { .. } => {
                self.build_assign_union(body, source, operation, pointee_info);
            }
            MemoryInitOp::StoreArgument { .. } | MemoryInitOp::LoadArgument { .. } => {
                self.build_argument_operation(body, source, operation, pointee_info);
            }
            MemoryInitOp::Unsupported { .. } | MemoryInitOp::TriviallyUnsafe { .. } => {
                unreachable!(
                    "Unsupported and TriviallyUnsafe operations should be handled before instrumentation"
                )
            }
        }
    }

    /// Inject a load from memory initialization state and an assertion that all non-padding bytes
    /// are initialized.
    fn build_get_and_check(
        &mut self,
        body: &mut MutableBody,
        source: &mut SourceInstruction,
        operation: MemoryInitOp,
        pointee_info: PointeeInfo,
    ) {
        let ret_place = Place {
            local: body.new_local(Ty::bool_ty(), source.span(body.blocks()), Mutability::Not),
            projection: vec![],
        };
        // Instead of injecting the instrumentation immediately, collect it into a list of
        // statements and a terminator to construct a basic block and inject it at the end.
        let mut statements = vec![];
        let ptr_operand = operation.mk_operand(body, &mut statements, source);
        let terminator = match pointee_info.layout() {
            PointeeLayout::Sized { layout } => {
                let layout_operand = mk_layout_operand(body, &mut statements, source, layout);
                // Depending on whether accessing the known number of elements in the slice, need to
                // pass is as an argument.
                let (diagnostic, args) = match &operation {
                    MemoryInitOp::Check { .. } | MemoryInitOp::CheckRef { .. } => {
                        let diagnostic = KANI_IS_PTR_INITIALIZED;
                        let args = vec![ptr_operand, layout_operand];
                        (diagnostic, args)
                    }
                    MemoryInitOp::CheckSliceChunk { .. } => {
                        let diagnostic = KANI_IS_SLICE_CHUNK_PTR_INITIALIZED;
                        let args = vec![ptr_operand, layout_operand, operation.expect_count()];
                        (diagnostic, args)
                    }
                    MemoryInitOp::Set { .. }
                    | MemoryInitOp::SetSliceChunk { .. }
                    | MemoryInitOp::SetRef { .. }
                    | MemoryInitOp::CreateUnion { .. }
                    | MemoryInitOp::Copy { .. }
                    | MemoryInitOp::AssignUnion { .. }
                    | MemoryInitOp::LoadArgument { .. }
                    | MemoryInitOp::StoreArgument { .. }
                    | MemoryInitOp::Unsupported { .. }
                    | MemoryInitOp::TriviallyUnsafe { .. } => {
                        unreachable!(
                            "build_get_and_check called with non-check operation: {operation:?}"
                        )
                    }
                };
                let is_ptr_initialized_instance = resolve_mem_init_fn(
                    get_mem_init_fn_def(diagnostic, self.mem_init_fn_cache),
                    layout.len(),
                    *pointee_info.ty(),
                );
                Terminator {
                    kind: TerminatorKind::Call {
                        func: Operand::Copy(Place::from(body.new_local(
                            is_ptr_initialized_instance.ty(),
                            source.span(body.blocks()),
                            Mutability::Not,
                        ))),
                        args,
                        destination: ret_place.clone(),
                        target: Some(0), // The current value does not matter, since it will be overwritten in add_bb.
                        unwind: UnwindAction::Terminate,
                    },
                    span: source.span(body.blocks()),
                }
            }
            PointeeLayout::Slice { element_layout } => {
                // Since `str`` is a separate type, need to differentiate between [T] and str.
                let (slicee_ty, diagnostic) = match pointee_info.ty().kind() {
                    TyKind::RigidTy(RigidTy::Slice(slicee_ty)) => {
                        (slicee_ty, KANI_IS_SLICE_PTR_INITIALIZED)
                    }
                    TyKind::RigidTy(RigidTy::Str) => {
                        (Ty::unsigned_ty(UintTy::U8), KANI_IS_STR_PTR_INITIALIZED)
                    }
                    _ => unreachable!("only Slice/Str expected in pointee check"), // external enum: TyKind
                };
                let is_ptr_initialized_instance = resolve_mem_init_fn(
                    get_mem_init_fn_def(diagnostic, self.mem_init_fn_cache),
                    element_layout.len(),
                    slicee_ty,
                );
                let layout_operand =
                    mk_layout_operand(body, &mut statements, source, element_layout);
                Terminator {
                    kind: TerminatorKind::Call {
                        func: Operand::Copy(Place::from(body.new_local(
                            is_ptr_initialized_instance.ty(),
                            source.span(body.blocks()),
                            Mutability::Not,
                        ))),
                        args: vec![ptr_operand, layout_operand],
                        destination: ret_place.clone(),
                        target: Some(0), // The current value does not matter, since it will be overwritten in add_bb.
                        unwind: UnwindAction::Terminate,
                    },
                    span: source.span(body.blocks()),
                }
            }
            PointeeLayout::TraitObject => {
                let reason = "trust_mc does not support reasoning about memory initialization of pointers to trait objects.";
                self.inject_unsupported_check(body, source, operation.position(), reason);
                return;
            }
            PointeeLayout::Union { field_layouts } => {
                // Here we are reading from a pointer to a union. We allow reads of the bytes that
                // are data for *all* union fields (intersection). This is conservative and
                // incomplete: larger field reads can still observe uninitialized bytes beyond the
                // intersection. Full soundness requires per-byte init tracking + field access
                // tracking at use sites.
                let intersection_layout = union_intersection_layout(field_layouts);
                if intersection_layout.iter().all(|byte| !*byte) {
                    let reason = "Interaction between raw pointers and unions is not yet supported (no common initialized bytes).";
                    self.inject_unsupported_check(body, source, operation.position(), reason);
                    return;
                }
                let layout_operand =
                    mk_layout_operand(body, &mut statements, source, &intersection_layout);
                let (diagnostic, args) = match &operation {
                    MemoryInitOp::Check { .. } | MemoryInitOp::CheckRef { .. } => {
                        let diagnostic = KANI_IS_PTR_INITIALIZED;
                        let args = vec![ptr_operand, layout_operand];
                        (diagnostic, args)
                    }
                    MemoryInitOp::CheckSliceChunk { .. } => {
                        let diagnostic = KANI_IS_SLICE_CHUNK_PTR_INITIALIZED;
                        let args = vec![ptr_operand, layout_operand, operation.expect_count()];
                        (diagnostic, args)
                    }
                    MemoryInitOp::Set { .. }
                    | MemoryInitOp::SetSliceChunk { .. }
                    | MemoryInitOp::SetRef { .. }
                    | MemoryInitOp::CreateUnion { .. }
                    | MemoryInitOp::Copy { .. }
                    | MemoryInitOp::AssignUnion { .. }
                    | MemoryInitOp::LoadArgument { .. }
                    | MemoryInitOp::StoreArgument { .. }
                    | MemoryInitOp::Unsupported { .. }
                    | MemoryInitOp::TriviallyUnsafe { .. } => {
                        unreachable!(
                            "build_get_and_check called with non-check operation: {operation:?}"
                        )
                    }
                };
                let is_ptr_initialized_instance = resolve_mem_init_fn(
                    get_mem_init_fn_def(diagnostic, self.mem_init_fn_cache),
                    intersection_layout.len(),
                    *pointee_info.ty(),
                );
                Terminator {
                    kind: TerminatorKind::Call {
                        func: Operand::Copy(Place::from(body.new_local(
                            is_ptr_initialized_instance.ty(),
                            source.span(body.blocks()),
                            Mutability::Not,
                        ))),
                        args,
                        destination: ret_place.clone(),
                        target: Some(0), // The current value does not matter, since it will be overwritten in add_bb.
                        unwind: UnwindAction::Terminate,
                    },
                    span: source.span(body.blocks()),
                }
            }
        };

        // Construct the basic block and insert it into the body.
        body.insert_bb(BasicBlock { statements, terminator }, source, operation.position());

        // Since the check involves a terminator, we cannot add it to the previously constructed
        // basic block. Instead, we insert the check after the basic block.
        let operand_ty = match &operation {
            MemoryInitOp::Check { operand }
            | MemoryInitOp::CheckSliceChunk { operand, .. }
            | MemoryInitOp::CheckRef { operand } => {
                operand.ty(body.locals()).expect("operand should have type")
            }
            MemoryInitOp::Set { .. }
            | MemoryInitOp::SetSliceChunk { .. }
            | MemoryInitOp::SetRef { .. }
            | MemoryInitOp::CreateUnion { .. }
            | MemoryInitOp::Copy { .. }
            | MemoryInitOp::AssignUnion { .. }
            | MemoryInitOp::LoadArgument { .. }
            | MemoryInitOp::StoreArgument { .. }
            | MemoryInitOp::Unsupported { .. }
            | MemoryInitOp::TriviallyUnsafe { .. } => {
                unreachable!("build_get_and_check called with non-check operation: {operation:?}")
            }
        };
        body.insert_check(
            &self.safety_check_type,
            source,
            operation.position(),
            Some(ret_place.local),
            &format!(
                "Undefined Behavior: Reading from an uninitialized pointer of type `{operand_ty}`"
            ),
        );
    }

    /// Inject a store into memory initialization state to initialize or deinitialize all
    /// non-padding bytes.
    fn build_set(
        &mut self,
        body: &mut MutableBody,
        source: &mut SourceInstruction,
        operation: MemoryInitOp,
        pointee_info: PointeeInfo,
    ) {
        let ret_place = Place {
            local: body.new_local(Ty::new_tuple(&[]), source.span(body.blocks()), Mutability::Not),
            projection: vec![],
        };

        // Instead of injecting the instrumentation immediately, collect it into a list of
        // statements and a terminator to construct a basic block and inject it at the end.
        let mut statements = vec![];
        let ptr_operand = operation.mk_operand(body, &mut statements, source);
        let value = operation.expect_value();
        let terminator = match pointee_info.layout() {
            PointeeLayout::Sized { layout } => {
                let layout_operand = mk_layout_operand(body, &mut statements, source, layout);
                // Depending on whether writing to the known number of elements in the slice, need to
                // pass is as an argument.
                let (diagnostic, args) = match &operation {
                    MemoryInitOp::Set { .. } | MemoryInitOp::SetRef { .. } => {
                        let diagnostic = KANI_SET_PTR_INITIALIZED;
                        let args = vec![
                            ptr_operand,
                            layout_operand,
                            Operand::Constant(ConstOperand {
                                span: source.span(body.blocks()),
                                user_ty: None,
                                const_: MirConst::from_bool(value),
                            }),
                        ];
                        (diagnostic, args)
                    }
                    MemoryInitOp::SetSliceChunk { .. } => {
                        let diagnostic = KANI_SET_SLICE_CHUNK_PTR_INITIALIZED;
                        let args = vec![
                            ptr_operand,
                            layout_operand,
                            operation.expect_count(),
                            Operand::Constant(ConstOperand {
                                span: source.span(body.blocks()),
                                user_ty: None,
                                const_: MirConst::from_bool(value),
                            }),
                        ];
                        (diagnostic, args)
                    }
                    MemoryInitOp::Check { .. }
                    | MemoryInitOp::CheckSliceChunk { .. }
                    | MemoryInitOp::CheckRef { .. }
                    | MemoryInitOp::CreateUnion { .. }
                    | MemoryInitOp::Copy { .. }
                    | MemoryInitOp::AssignUnion { .. }
                    | MemoryInitOp::LoadArgument { .. }
                    | MemoryInitOp::StoreArgument { .. }
                    | MemoryInitOp::Unsupported { .. }
                    | MemoryInitOp::TriviallyUnsafe { .. } => {
                        unreachable!("build_set called with non-set operation: {operation:?}")
                    }
                };
                let set_ptr_initialized_instance = resolve_mem_init_fn(
                    get_mem_init_fn_def(diagnostic, self.mem_init_fn_cache),
                    layout.len(),
                    *pointee_info.ty(),
                );
                Terminator {
                    kind: TerminatorKind::Call {
                        func: Operand::Copy(Place::from(body.new_local(
                            set_ptr_initialized_instance.ty(),
                            source.span(body.blocks()),
                            Mutability::Not,
                        ))),
                        args,
                        destination: ret_place,
                        target: Some(0), // this will be overriden in add_bb
                        unwind: UnwindAction::Terminate,
                    },
                    span: source.span(body.blocks()),
                }
            }
            PointeeLayout::Slice { element_layout } => {
                // Since `str`` is a separate type, need to differentiate between [T] and str.
                let (slicee_ty, diagnostic) = match pointee_info.ty().kind() {
                    TyKind::RigidTy(RigidTy::Slice(slicee_ty)) => {
                        (slicee_ty, KANI_SET_SLICE_PTR_INITIALIZED)
                    }
                    TyKind::RigidTy(RigidTy::Str) => {
                        (Ty::unsigned_ty(UintTy::U8), KANI_SET_STR_PTR_INITIALIZED)
                    }
                    _ => unreachable!("only Slice/Str expected in pointee set"), // external enum: TyKind
                };
                let set_ptr_initialized_instance = resolve_mem_init_fn(
                    get_mem_init_fn_def(diagnostic, self.mem_init_fn_cache),
                    element_layout.len(),
                    slicee_ty,
                );
                let layout_operand =
                    mk_layout_operand(body, &mut statements, source, element_layout);
                Terminator {
                    kind: TerminatorKind::Call {
                        func: Operand::Copy(Place::from(body.new_local(
                            set_ptr_initialized_instance.ty(),
                            source.span(body.blocks()),
                            Mutability::Not,
                        ))),
                        args: vec![
                            ptr_operand,
                            layout_operand,
                            Operand::Constant(ConstOperand {
                                span: source.span(body.blocks()),
                                user_ty: None,
                                const_: MirConst::from_bool(value),
                            }),
                        ],
                        destination: ret_place,
                        target: Some(0), // The current value does not matter, since it will be overwritten in add_bb.
                        unwind: UnwindAction::Terminate,
                    },
                    span: source.span(body.blocks()),
                }
            }
            PointeeLayout::TraitObject => {
                unreachable!("Cannot change the initialization state of a trait object directly.");
            }
            PointeeLayout::Union { field_layouts } => {
                // Writing union data, which could be either creating a union from scratch or
                // performing some pointer operations with it. If we are creating a union from
                // scratch, an operation will contain a union field.

                // Design decision (#1872): If we don't have a union field, we are either creating
                // a pointer to a union or assigning to one. In the former case, returning early
                // would be safe since the union is already tracked. In the latter case, union
                // assignment should be used instead of raw pointer writes.
                //
                // We inject `assert!(false)` here as a conservative approach:
                // - This is SOUND: verification fails rather than producing false negatives
                // - Full intersection checking would require active-field tracking throughout
                //   the program, which is substantial complexity for an edge case
                // - Users can refactor code to use union assignment instead
                let union_field = if let Some(field) = operation.union_field() {
                    field
                } else {
                    let reason =
                        "Interaction between raw pointers and unions is not yet supported.";
                    self.inject_unsupported_check(body, source, operation.position(), reason);
                    return;
                };
                let layout = &field_layouts[union_field];
                let layout_operand = mk_layout_operand(body, &mut statements, source, layout);
                let diagnostic = KANI_SET_PTR_INITIALIZED;
                let args = vec![
                    ptr_operand,
                    layout_operand,
                    Operand::Constant(ConstOperand {
                        span: source.span(body.blocks()),
                        user_ty: None,
                        const_: MirConst::from_bool(value),
                    }),
                ];
                let set_ptr_initialized_instance = resolve_mem_init_fn(
                    get_mem_init_fn_def(diagnostic, self.mem_init_fn_cache),
                    layout.len(),
                    *pointee_info.ty(),
                );
                Terminator {
                    kind: TerminatorKind::Call {
                        func: Operand::Copy(Place::from(body.new_local(
                            set_ptr_initialized_instance.ty(),
                            source.span(body.blocks()),
                            Mutability::Not,
                        ))),
                        args,
                        destination: ret_place,
                        target: Some(0), // this will be overriden in add_bb
                        unwind: UnwindAction::Terminate,
                    },
                    span: source.span(body.blocks()),
                }
            }
        };
        // Construct the basic block and insert it into the body.
        body.insert_bb(BasicBlock { statements, terminator }, source, operation.position());
    }

    /// Copy memory initialization state from one pointer to the other.
    fn build_copy(
        &mut self,
        body: &mut MutableBody,
        source: &mut SourceInstruction,
        operation: MemoryInitOp,
        pointee_info: PointeeInfo,
    ) {
        let ret_place = Place {
            local: body.new_local(Ty::new_tuple(&[]), source.span(body.blocks()), Mutability::Not),
            projection: vec![],
        };
        let layout_size =
            pointee_info.layout().maybe_size().expect("layout should have known size");
        let copy_init_state_instance = resolve_mem_init_fn(
            get_mem_init_fn_def(KANI_COPY_INIT_STATE, self.mem_init_fn_cache),
            layout_size,
            *pointee_info.ty(),
        );
        let position = operation.position();
        let (from, to) = operation.expect_copy_operands();
        let count = operation.expect_count();
        body.insert_call(
            &copy_init_state_instance,
            source,
            position,
            vec![from, to, count],
            ret_place,
        );
    }

    /// Instrument the code to pass information about arguments containing unions. Whenever a
    /// function is called and some of the arguments contain unions, we store the information. And
    /// when we enter the callee, we load the information.
    fn build_argument_operation(
        &mut self,
        body: &mut MutableBody,
        source: &mut SourceInstruction,
        operation: MemoryInitOp,
        pointee_info: PointeeInfo,
    ) {
        let ret_place = Place {
            local: body.new_local(Ty::new_tuple(&[]), source.span(body.blocks()), Mutability::Not),
            projection: vec![],
        };
        let mut statements = vec![];
        let layout_size =
            pointee_info.layout().maybe_size().expect("layout should have known size");
        let diagnostic = match operation {
            MemoryInitOp::LoadArgument { .. } => KANI_LOAD_ARGUMENT,
            MemoryInitOp::StoreArgument { .. } => KANI_STORE_ARGUMENT,
            MemoryInitOp::Check { .. }
            | MemoryInitOp::CheckSliceChunk { .. }
            | MemoryInitOp::CheckRef { .. }
            | MemoryInitOp::Set { .. }
            | MemoryInitOp::SetSliceChunk { .. }
            | MemoryInitOp::SetRef { .. }
            | MemoryInitOp::CreateUnion { .. }
            | MemoryInitOp::Copy { .. }
            | MemoryInitOp::AssignUnion { .. }
            | MemoryInitOp::Unsupported { .. }
            | MemoryInitOp::TriviallyUnsafe { .. } => {
                unreachable!(
                    "build_argument_operation called with non-argument operation: {operation:?}"
                )
            }
        };
        let argument_operation_instance = resolve_mem_init_fn(
            get_mem_init_fn_def(diagnostic, self.mem_init_fn_cache),
            layout_size,
            *pointee_info.ty(),
        );
        let operand = operation.mk_operand(body, &mut statements, source);
        let argument_no = operation.expect_argument_no();
        let terminator = Terminator {
            kind: TerminatorKind::Call {
                func: Operand::Copy(Place::from(body.new_local(
                    argument_operation_instance.ty(),
                    source.span(body.blocks()),
                    Mutability::Not,
                ))),
                args: vec![
                    operand,
                    Operand::Constant(ConstOperand {
                        span: source.span(body.blocks()),
                        user_ty: None,
                        const_: MirConst::try_from_uint(argument_no as u128, UintTy::Usize)
                            .expect("argument number should fit in usize"),
                    }),
                ],
                destination: ret_place,
                target: Some(0), // this will be overriden in add_bb
                unwind: UnwindAction::Terminate,
            },
            span: source.span(body.blocks()),
        };

        // Construct the basic block and insert it into the body.
        body.insert_bb(BasicBlock { statements, terminator }, source, operation.position());
    }

    /// Copy memory initialization state from one union variable to another.
    fn build_assign_union(
        &mut self,
        body: &mut MutableBody,
        source: &mut SourceInstruction,
        operation: MemoryInitOp,
        pointee_info: PointeeInfo,
    ) {
        let ret_place = Place {
            local: body.new_local(Ty::new_tuple(&[]), source.span(body.blocks()), Mutability::Not),
            projection: vec![],
        };
        let mut statements = vec![];
        let layout_size =
            pointee_info.layout().maybe_size().expect("layout should have known size");
        let copy_init_state_instance = resolve_mem_init_fn(
            get_mem_init_fn_def(KANI_COPY_INIT_STATE_SINGLE, self.mem_init_fn_cache),
            layout_size,
            *pointee_info.ty(),
        );
        let (from, to) = operation.expect_assign_union_operands(body, &mut statements, source);
        let terminator = Terminator {
            kind: TerminatorKind::Call {
                func: Operand::Copy(Place::from(body.new_local(
                    copy_init_state_instance.ty(),
                    source.span(body.blocks()),
                    Mutability::Not,
                ))),
                args: vec![from, to],
                destination: ret_place,
                target: Some(0), // this will be overriden in add_bb
                unwind: UnwindAction::Terminate,
            },
            span: source.span(body.blocks()),
        };

        // Construct the basic block and insert it into the body.
        body.insert_bb(BasicBlock { statements, terminator }, source, operation.position());
    }

    fn inject_safety_check(
        &self,
        body: &mut MutableBody,
        source: &mut SourceInstruction,
        position: InsertPosition,
        reason: &str,
    ) {
        let span = source.span(body.blocks());
        let rvalue = Rvalue::Use(Operand::Constant(ConstOperand {
            const_: MirConst::from_bool(false),
            span,
            user_ty: None,
        }));
        let result = body.insert_assignment(rvalue, source, position);
        body.insert_check(&self.safety_check_type, source, position, Some(result), reason);
    }

    fn inject_unsupported_check(
        &self,
        body: &mut MutableBody,
        source: &mut SourceInstruction,
        position: InsertPosition,
        reason: &str,
    ) {
        body.insert_check(&self.unsupported_check_type, source, position, None, reason);
    }
}

/// Create an operand from a bit array that represents a byte mask for a type layout where padding
/// bytes are marked as `false` and data bytes are marked as `true`.
///
/// For example, the layout for:
/// ```
/// [repr(C)]
/// struct {
///     a: u16,
///     b: u8
/// }
/// ```
/// will have the following byte mask `[true, true, true, false]`.
pub(crate) fn mk_layout_operand(
    body: &mut MutableBody,
    statements: &mut Vec<Statement>,
    source: &mut SourceInstruction,
    layout_byte_mask: &[bool],
) -> Operand {
    let span = source.span(body.blocks());
    let rvalue = Rvalue::Aggregate(
        AggregateKind::Array(Ty::bool_ty()),
        layout_byte_mask
            .iter()
            .map(|byte| {
                Operand::Constant(ConstOperand {
                    span: source.span(body.blocks()),
                    user_ty: None,
                    const_: MirConst::from_bool(*byte),
                })
            })
            .collect(),
    );
    let ret_ty = rvalue.ty(body.locals()).expect("rvalue should have type");
    let result = body.new_local(ret_ty, span, Mutability::Not);
    let stmt = Statement { kind: StatementKind::Assign(Place::from(result), rvalue), span };
    statements.push(stmt);

    Operand::Move(Place { local: result, projection: vec![] })
}

fn union_intersection_layout(field_layouts: &[Vec<bool>]) -> Vec<bool> {
    let max_len = field_layouts.iter().map(Vec::len).max().unwrap_or(0);
    let mut intersection = vec![true; max_len];
    for idx in 0..max_len {
        let mut all_set = true;
        for layout in field_layouts {
            if idx >= layout.len() || !layout[idx] {
                all_set = false;
                break;
            }
        }
        intersection[idx] = all_set;
    }
    intersection
}

/// Retrieve a function definition by diagnostic string, caching the result.
pub(crate) fn get_mem_init_fn_def(
    diagnostic: KaniFunction,
    cache: &mut HashMap<KaniFunction, FnDef>,
) -> FnDef {
    cache[&diagnostic]
}

/// Resolves a given memory initialization function with passed type parameters.
pub(crate) fn resolve_mem_init_fn(
    fn_def: FnDef,
    layout_size: usize,
    associated_type: Ty,
) -> Instance {
    Instance::resolve(
        fn_def,
        &GenericArgs(vec![
            GenericArgKind::Const(
                TyConst::try_from_target_usize(layout_size as u64)
                    .expect("layout size should fit in u64"),
            ),
            GenericArgKind::Type(associated_type),
        ]),
    )
    .expect("mem init function should be resolvable")
}

#[cfg(test)]
mod tests {
    use super::union_intersection_layout;

    #[test]
    fn union_intersection_handles_length_mismatch() {
        let layout_a = vec![true, true];
        let layout_b = vec![true];
        let intersection = union_intersection_layout(&[layout_a, layout_b]);
        assert_eq!(intersection, vec![true, false]);
    }

    #[test]
    fn union_intersection_filters_non_common_bytes() {
        let layout_a = vec![true, false, true];
        let layout_b = vec![true, true, false];
        let intersection = union_intersection_layout(&[layout_a, layout_b]);
        assert_eq!(intersection, vec![true, false, false]);
    }

    // Additional edge cases (Part of #2190)

    #[test]
    fn union_intersection_empty_input() {
        let intersection = union_intersection_layout(&[]);
        assert_eq!(intersection, Vec::<bool>::new());
    }

    #[test]
    fn union_intersection_single_field() {
        let layout = vec![true, false, true];
        let intersection = union_intersection_layout(&[layout]);
        assert_eq!(intersection, vec![true, false, true]);
    }

    #[test]
    fn union_intersection_all_true() {
        let layout_a = vec![true, true, true];
        let layout_b = vec![true, true, true];
        let intersection = union_intersection_layout(&[layout_a, layout_b]);
        assert_eq!(intersection, vec![true, true, true]);
    }

    #[test]
    fn union_intersection_all_false() {
        let layout_a = vec![false, false, false];
        let layout_b = vec![false, false, false];
        let intersection = union_intersection_layout(&[layout_a, layout_b]);
        assert_eq!(intersection, vec![false, false, false]);
    }

    #[test]
    fn union_intersection_three_fields() {
        let layout_a = vec![true, true, false, true];
        let layout_b = vec![true, false, true, true];
        let layout_c = vec![true, true, true, false];
        let intersection = union_intersection_layout(&[layout_a, layout_b, layout_c]);
        // Only byte 0 is true in all three
        assert_eq!(intersection, vec![true, false, false, false]);
    }
}
