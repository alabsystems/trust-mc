// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Utility functions that allow us to modify a function body.
//!
//! NOTE: rustc PR #138536 (merged 2025-03-22) added MutMirVisitor to Stable MIR,
//! but this module provides additional infrastructure (InsertPosition, block
//! splitting, instrumentation APIs) not available in upstream. See #1297.

use crate::kani_middle::kani_functions::KaniHook;
use crate::kani_queries::QueryDb;
use rustc_middle::mir::Const as InternalMirConst;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::ty::{ScalarInt, TyCtxt, TypingEnv};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::*;
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgs, IntTy, MirConst, Span, Ty, UintTy};
use std::fmt::Debug;
use std::mem;

#[derive(Debug)]
/// This structure mimics a Body that can actually be modified.
pub(crate) struct MutableBody {
    blocks: Vec<BasicBlock>,

    /// Declarations of locals within the function.
    ///
    /// The first local is the return value pointer, followed by `arg_count`
    /// locals for the function arguments, followed by any user-declared
    /// variables and temporaries.
    locals: Vec<LocalDecl>,

    /// The number of arguments this function takes.
    arg_count: usize,

    /// Debug information pertaining to user variables, including captures.
    var_debug_info: Vec<VarDebugInfo>,

    /// Mark an argument (which must be a tuple) as getting passed as its individual components.
    ///
    /// This is used for the "rust-call" ABI such as closures.
    spread_arg: Option<Local>,

    /// The span that covers the entire function body.
    span: Span,
}

/// Denotes whether instrumentation should be inserted before or after the source instruction.
///
/// This enum controls both where new code is inserted and how the `SourceInstruction` reference
/// is updated after the insertion.
///
/// # Semantics
///
/// | Position | Inserted code runs... | After call, `source` points to... |
/// |----------|----------------------|-----------------------------------|
/// | `Before` | Before the original instruction | The same original instruction |
/// | `After`  | After the original instruction | The newly inserted code |
///
/// # Choosing the Right Position
///
/// - **`Before`**: Use when you need to check conditions or set up state before an operation
///   executes. Common for safety checks, precondition assertions.
///
/// - **`After`**: Use when you need to observe or record results after an operation completes.
///   Common for tracking state changes, postcondition checks, or when building code that
///   depends on the result of the source instruction.
///
/// # Example: Inserting Multiple Items
///
/// When inserting multiple items sequentially, the order depends on the position:
///
/// ```text
/// // InsertPosition::Before - items appear in insertion order
/// body.insert_stmt(stmt_a, &mut source, InsertPosition::Before); // A runs first
/// body.insert_stmt(stmt_b, &mut source, InsertPosition::Before); // B runs second
/// // Final order: [A, B, original_instruction]
///
/// // InsertPosition::After - items appear in reverse insertion order
/// body.insert_stmt(stmt_a, &mut source, InsertPosition::After); // A inserted after original
/// body.insert_stmt(stmt_b, &mut source, InsertPosition::After); // B inserted after A
/// // Final order: [original_instruction, A, B]
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InsertPosition {
    /// Insert before the source instruction. The `source` reference remains pointing to
    /// the original instruction after the insertion.
    Before,
    /// Insert after the source instruction. The `source` reference is updated to point
    /// to the newly inserted code.
    After,
}

impl MutableBody {
    /// Get the basic blocks of this builder.
    pub(crate) fn blocks(&self) -> &[BasicBlock] {
        &self.blocks
    }

    pub(crate) fn replace_statement_kind(&mut self, bb: usize, idx: usize, kind: StatementKind) {
        self.blocks
            .get_mut(bb)
            .and_then(|block| block.statements.get_mut(idx))
            .expect("statement location should be valid")
            .kind = kind;
    }

    pub(crate) fn locals(&self) -> &[LocalDecl] {
        &self.locals
    }

    /// Set the type of a local variable.
    ///
    /// Used by the ArrayIterUnrollPass to replace the iterator local's type
    /// with `()` after transformation, preventing monomorphization of the
    /// iterator's Drop glue (which contains unsupported constructs).
    pub(crate) fn set_local_ty(&mut self, local: Local, ty: Ty) {
        self.locals[local].ty = ty;
    }

    pub(crate) fn arg_count(&self) -> usize {
        self.arg_count
    }

    pub(crate) fn var_debug_info(&self) -> &Vec<VarDebugInfo> {
        &self.var_debug_info
    }

    /// Create a mutable body from the original MIR body.
    ///
    /// # Contracts
    ///
    /// REQUIRES: body is valid MIR (well-formed basic blocks, locals, terminators)
    /// ENSURES: self.blocks == body.blocks
    /// ENSURES: self.locals == body.locals().to_vec()
    /// ENSURES: self.arg_count == body.arg_locals().len()
    /// ENSURES: self.spread_arg == body.spread_arg()
    /// ENSURES: self.var_debug_info == body.var_debug_info
    /// ENSURES: self.span == body.span
    /// ENSURES: Semantic equivalence: self.into() produces a Body equivalent to the input
    pub(crate) fn from(body: Body) -> Self {
        MutableBody {
            locals: body.locals().to_vec(),
            arg_count: body.arg_locals().len(),
            spread_arg: body.spread_arg(),
            blocks: body.blocks,
            var_debug_info: body.var_debug_info,
            span: body.span,
        }
    }

    /// Create the new body consuming this mutable body.
    ///
    /// # Contracts
    ///
    /// REQUIRES: self.blocks contains valid basic blocks (all terminator targets in bounds)
    /// REQUIRES: self.locals[0..arg_count+1] contains return local followed by arg locals
    /// REQUIRES: All local references in blocks are valid indices into self.locals
    /// ENSURES: Returned Body is valid MIR
    /// ENSURES: Returned Body preserves the semantics of the original Body used in from()
    ///          (modulo any transformations applied to self between from() and into())
    pub(crate) fn into(self) -> Body {
        Body::new(
            self.blocks,
            self.locals,
            self.arg_count,
            self.var_debug_info,
            self.spread_arg,
            self.span,
        )
    }

    /// Add a new local to the body with the given attributes.
    pub(crate) fn new_local(&mut self, ty: Ty, span: Span, mutability: Mutability) -> Local {
        let decl = LocalDecl { ty, span, mutability };
        let local = self.locals.len();
        self.locals.push(decl);
        local
    }

    pub(crate) fn new_str_operand(&mut self, msg: &str, span: Span) -> Operand {
        let literal = MirConst::from_str(msg);
        self.new_const_operand(literal, span)
    }

    pub(crate) fn new_uint_operand(&mut self, val: u128, uint_ty: UintTy, span: Span) -> Operand {
        let literal = MirConst::try_from_uint(val, uint_ty)
            .expect("uint value should be representable in uint type");
        self.new_const_operand(literal, span)
    }

    /// Create an operand for a signed integer constant of type `int_ty`.
    ///
    /// The constant's MIR type is the SIGNED type, not the same-width unsigned
    /// one. That distinction is load-bearing: `Rvalue::ty` for an arithmetic
    /// `BinaryOp` asserts `lhs_ty == rhs_ty` (rustc_middle `BinOp::ty`), so a
    /// `u32` literal used as the right operand of an `i32` add is ill-typed MIR
    /// and ICEs the moment anything asks the rvalue for its type.
    ///
    /// `rustc_public::ty::MirConst` only exposes `try_from_uint`, so the signed
    /// constant is built on the internal side (`ScalarInt::try_from_int`, which
    /// does the two's-complement truncation against the TARGET-computed layout
    /// size — correct for `isize` on a 32-bit target too) and converted back
    /// with `rustc_internal::stable`, which interns it so that a later
    /// `internal()` round-trip yields the same constant.
    pub(crate) fn new_int_operand(
        &mut self,
        tcx: TyCtxt<'_>,
        val: i128,
        int_ty: IntTy,
        span: Span,
    ) -> Operand {
        let ty = match int_ty {
            IntTy::I8 => tcx.types.i8,
            IntTy::I16 => tcx.types.i16,
            IntTy::I32 => tcx.types.i32,
            IntTy::I64 => tcx.types.i64,
            IntTy::I128 => tcx.types.i128,
            IntTy::Isize => tcx.types.isize,
        };
        let typing_env = TypingEnv::fully_monomorphized();
        let size = tcx
            .layout_of(typing_env.as_query_input(ty))
            .unwrap_or_else(|e| panic!("no layout for signed integer type {ty:?}: {e:?}"))
            .size;
        let scalar = ScalarInt::try_from_int(val, size)
            .unwrap_or_else(|| panic!("{val} is not representable in {ty:?}"));
        let literal =
            rustc_internal::stable(InternalMirConst::from_scalar(tcx, Scalar::Int(scalar), ty));
        self.new_const_operand(literal, span)
    }

    fn new_const_operand(&mut self, literal: MirConst, span: Span) -> Operand {
        Operand::Constant(ConstOperand { span, user_ty: None, const_: literal })
    }

    /// Create a raw pointer of `*mut type` and return a new local where that value is stored.
    pub(crate) fn insert_ptr_cast(
        &mut self,
        from: Operand,
        pointee_ty: Ty,
        mutability: Mutability,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) -> Local {
        assert!(
            from.ty(self.locals()).expect("operand should have type in locals").kind().is_raw_ptr()
        );
        let target_ty = Ty::new_ptr(pointee_ty, mutability);
        let rvalue = Rvalue::Cast(CastKind::PtrToPtr, from, target_ty);
        self.insert_assignment(rvalue, source, position)
    }

    /// Add a new assignment for the given binary operation.
    ///
    /// Return the local where the result is saved.
    pub(crate) fn insert_binary_op(
        &mut self,
        bin_op: BinOp,
        lhs: Operand,
        rhs: Operand,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) -> Local {
        let rvalue = Rvalue::BinaryOp(bin_op, lhs, rhs);
        self.insert_assignment(rvalue, source, position)
    }

    /// Add a new assignment.
    ///
    /// Return the local where the result is saved.
    pub(crate) fn insert_assignment(
        &mut self,
        rvalue: Rvalue,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) -> Local {
        let span = source.span(&self.blocks);
        let ret_ty = rvalue.ty(&self.locals).expect("rvalue should have type in locals");
        let result = self.new_local(ret_ty, span, Mutability::Not);
        let stmt = Statement { kind: StatementKind::Assign(Place::from(result), rvalue), span };
        self.insert_stmt(stmt, source, position);
        result
    }

    /// Add a new assignment to an existing place.
    pub(crate) fn assign_to(
        &mut self,
        place: Place,
        rvalue: Rvalue,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) {
        let span = source.span(&self.blocks);
        let stmt = Statement { kind: StatementKind::Assign(place, rvalue), span };
        self.insert_stmt(stmt, source, position);
    }

    /// Add a new assert to the basic block indicated by the given index.
    ///
    /// The new assertion will have the same span as the source instruction, and the basic block
    /// will be split. If `InsertPosition` is `InsertPosition::Before`, `source` will point to the
    /// same instruction as before. If `InsertPosition` is `InsertPosition::After`, `source` will
    /// point to the new terminator.
    pub(crate) fn insert_check(
        &mut self,
        check_type: &CheckType,
        source: &mut SourceInstruction,
        position: InsertPosition,
        value: Option<Local>,
        msg: &str,
    ) {
        let new_bb = self.blocks.len();
        let span = source.span(&self.blocks);
        let msg_op = self.new_str_operand(msg, span);
        let (assert_fn, args) = match check_type {
            CheckType::SafetyCheck(assert_fn) | CheckType::SafetyCheckNoAssume(assert_fn) => {
                let value_local =
                    value.expect("SafetyCheck requires a boolean value to be provided");
                assert_eq!(
                    self.locals[value_local].ty,
                    Ty::bool_ty(),
                    "Expected boolean value as the assert input"
                );
                (assert_fn, vec![Operand::Move(Place::from(value_local)), msg_op])
            }
            CheckType::UnsupportedCheck(assert_fn) => {
                assert!(value.is_none());
                (assert_fn, vec![msg_op])
            }
        };
        let assert_op =
            Operand::Copy(Place::from(self.new_local(assert_fn.ty(), span, Mutability::Not)));
        let kind = TerminatorKind::Call {
            func: assert_op,
            args,
            destination: Place {
                local: self.new_local(Ty::new_tuple(&[]), span, Mutability::Not),
                projection: vec![],
            },
            target: Some(new_bb),
            unwind: UnwindAction::Terminate,
        };
        let terminator = Terminator { kind, span };
        self.insert_terminator(source, position, terminator);
    }

    /// Add a new call to the basic block indicated by the given index.
    ///
    /// The new call will have the same span as the source instruction, and the basic block will be
    /// split. If `InsertPosition` is `InsertPosition::Before`, `source` will point to the same
    /// instruction as before. If `InsertPosition` is `InsertPosition::After`, `source` will point
    /// to the new terminator.
    pub(crate) fn insert_call(
        &mut self,
        callee: &Instance,
        source: &mut SourceInstruction,
        position: InsertPosition,
        args: Vec<Operand>,
        destination: Place,
    ) {
        let new_bb = self.blocks.len();
        let span = source.span(&self.blocks);
        let callee_op =
            Operand::Copy(Place::from(self.new_local(callee.ty(), span, Mutability::Not)));
        let kind = TerminatorKind::Call {
            func: callee_op,
            args,
            destination,
            target: Some(new_bb),
            unwind: UnwindAction::Terminate,
        };
        let terminator = Terminator { kind, span };
        self.insert_terminator(source, position, terminator);
    }

    /// Split a basic block and use the new terminator in the basic block that was split. If
    /// `InsertPosition` is `InsertPosition::Before`, `source` will point to the same instruction as
    /// before. If `InsertPosition` is `InsertPosition::After`, `source` will point to the new
    /// terminator.
    fn split_bb(
        &mut self,
        source: &mut SourceInstruction,
        position: InsertPosition,
        new_term: Terminator,
    ) {
        match position {
            InsertPosition::Before => {
                self.split_bb_before(source, new_term);
            }
            InsertPosition::After => {
                self.split_bb_after(source, new_term);
            }
        }
    }

    /// Split a basic block right before the source location.
    /// `source` will point to the same instruction as before after the function is done.
    fn split_bb_before(&mut self, source: &mut SourceInstruction, new_term: Terminator) {
        let new_bb_idx = self.blocks.len();
        let (idx, bb) = match source {
            SourceInstruction::Statement { idx, bb } => {
                let (orig_idx, orig_bb) = (*idx, *bb);
                *idx = 0;
                *bb = new_bb_idx;
                (orig_idx, orig_bb)
            }
            SourceInstruction::Terminator { bb } => {
                let (orig_idx, orig_bb) = (self.blocks[*bb].statements.len(), *bb);
                *bb = new_bb_idx;
                (orig_idx, orig_bb)
            }
        };
        let old_term = mem::replace(&mut self.blocks[bb].terminator, new_term);
        let bb_stmts = &mut self.blocks[bb].statements;
        let remaining = bb_stmts.split_off(idx);
        let new_bb = BasicBlock { statements: remaining, terminator: old_term };
        self.blocks.push(new_bb);
    }

    /// Split a basic block right after the source location.
    /// `source` will point to the new terminator after the function is done.
    fn split_bb_after(&mut self, source: &mut SourceInstruction, mut new_term: Terminator) {
        let new_bb_idx = self.blocks.len();
        match source {
            // Split the current block after the statement located at `source`
            // and move the remaining statements into the new one.
            SourceInstruction::Statement { idx, bb } => {
                let (orig_idx, orig_bb) = (*idx, *bb);
                let old_term = mem::replace(&mut self.blocks[orig_bb].terminator, new_term);
                let bb_stmts = &mut self.blocks[orig_bb].statements;
                let remaining = bb_stmts.split_off(orig_idx + 1);
                let new_bb = BasicBlock { statements: remaining, terminator: old_term };
                self.blocks.push(new_bb);
                // Update the source to point at the terminator.
                *source = SourceInstruction::Terminator { bb: orig_bb };
            }
            // Make the terminator at `source` point at the new block, the terminator of which is
            // provided by the caller.
            SourceInstruction::Terminator { bb } => {
                let current_term = &mut self
                    .blocks
                    .get_mut(*bb)
                    .expect("basic block index should be valid")
                    .terminator;
                let target_bb = get_mut_target_ref(current_term);
                let new_target_bb = get_mut_target_ref(&mut new_term);
                // Swap the targets of the newly inserted terminator and the original one. This is
                // an easy way to make the original terminator point to the new basic block with the
                // new terminator.
                std::mem::swap(new_target_bb, target_bb);
                // Update the source to point at the terminator.
                *bb = new_bb_idx;
                self.blocks.push(BasicBlock { statements: vec![], terminator: new_term });
            }
        }
    }

    /// Insert basic block before or after the source instruction and update `source` accordingly. If
    /// `InsertPosition` is `InsertPosition::Before`, `source` will point to the same instruction as
    /// before. If `InsertPosition` is `InsertPosition::After`, `source` will point to the
    /// terminator of the newly inserted basic block.
    pub(crate) fn insert_bb(
        &mut self,
        mut bb: BasicBlock,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) {
        // Splitting adds 1 block, so the added block index is len + 1;
        let split_bb_idx = self.blocks().len();
        let inserted_bb_idx = self.blocks().len() + 1;
        // Update the terminator of the basic block to point at the remaining part of the split
        // basic block.
        let target = get_mut_target_ref(&mut bb.terminator);
        *target = split_bb_idx;
        let new_term = Terminator {
            kind: TerminatorKind::Goto { target: inserted_bb_idx },
            span: source.span(&self.blocks),
        };
        self.split_bb(source, position, new_term);
        self.blocks.push(bb);
    }

    /// Insert a terminator at the given source location, splitting the basic block.
    ///
    /// This creates a new basic block and redirects control flow through the inserted terminator.
    /// The original code after the split point is moved to the new block.
    ///
    /// # Position Semantics
    ///
    /// - `InsertPosition::Before`: The inserted terminator executes before the source instruction.
    ///   After the call, `source` still points to the same original instruction (now in a new block).
    ///
    /// - `InsertPosition::After`: The inserted terminator executes after the source instruction.
    ///   After the call, `source` points to the newly inserted terminator.
    ///
    /// # Use Cases
    ///
    /// - Inserting `Return` or `Unreachable` terminators when generating synthetic bodies
    /// - Inserting placeholder terminators (like `SwitchInt`) that will be configured later
    /// - Adding control flow for instrumentation (assertions, calls) - prefer `insert_check`
    ///   or `insert_call` for these common cases
    ///
    /// # Example
    ///
    /// ```text
    /// // Insert a Return terminator before the current instruction
    /// body.insert_terminator(
    ///     &mut source,
    ///     InsertPosition::Before,
    ///     Terminator { kind: TerminatorKind::Return, span },
    /// );
    /// ```
    pub(crate) fn insert_terminator(
        &mut self,
        source: &mut SourceInstruction,
        position: InsertPosition,
        terminator: Terminator,
    ) {
        self.split_bb(source, position, terminator);
    }

    /// Insert statement before or after the source instruction and update the source as needed. If
    /// `InsertPosition` is `InsertPosition::Before`, `source` will point to the same instruction as
    /// before. If `InsertPosition` is `InsertPosition::After`, `source` will point to the
    /// newly inserted statement.
    pub(crate) fn insert_stmt(
        &mut self,
        new_stmt: Statement,
        source: &mut SourceInstruction,
        position: InsertPosition,
    ) {
        match position {
            InsertPosition::Before => {
                match source {
                    SourceInstruction::Statement { idx, bb } => {
                        self.blocks[*bb].statements.insert(*idx, new_stmt);
                        *idx += 1;
                    }
                    SourceInstruction::Terminator { bb } => {
                        // Append statements at the end of the basic block.
                        self.blocks[*bb].statements.push(new_stmt);
                    }
                }
            }
            InsertPosition::After => {
                let new_bb_idx = self.blocks.len();
                let span = source.span(&self.blocks);
                match source {
                    SourceInstruction::Statement { idx, bb } => {
                        self.blocks[*bb].statements.insert(*idx + 1, new_stmt);
                        *idx += 1;
                    }
                    SourceInstruction::Terminator { bb } => {
                        // Create a new basic block, as we need to append a statement after the terminator.
                        let current_terminator = &mut self
                            .blocks
                            .get_mut(*bb)
                            .expect("basic block index should be valid")
                            .terminator;
                        // Update target of the terminator.
                        let target_bb = get_mut_target_ref(current_terminator);
                        *source = SourceInstruction::Statement { idx: 0, bb: new_bb_idx };
                        let new_bb = BasicBlock {
                            statements: vec![new_stmt],
                            terminator: Terminator {
                                kind: TerminatorKind::Goto { target: *target_bb },
                                span,
                            },
                        };
                        *target_bb = new_bb_idx;
                        self.blocks.push(new_bb);
                    }
                }
            }
        }
    }

    /// Clear all the existing logic of this body and turn it into a simple `return`.
    ///
    /// This function can be used when a new implementation of the body is needed.
    /// For example, Kani intrinsics usually have a dummy body, which is replaced
    /// by the compiler. This function allow us to delete the dummy body before
    /// creating a new one.
    ///
    /// Keep all the locals untouched, so they can be reused by the passes if needed.
    pub(crate) fn clear_body(&mut self, kind: TerminatorKind) {
        self.blocks.clear();
        let terminator = Terminator { kind, span: self.span };
        self.blocks.push(BasicBlock { statements: Vec::default(), terminator });
    }

    /// Replace statements from the given basic block
    pub(crate) fn replace_statements(
        &mut self,
        source_instruction: &SourceInstruction,
        new_stmts: Vec<Statement>,
    ) {
        self.blocks
            .get_mut(source_instruction.bb())
            .expect("source instruction basic block should be valid")
            .statements = new_stmts;
    }

    /// Replace a terminator from the given basic block
    pub(crate) fn replace_terminator(
        &mut self,
        source_instruction: &SourceInstruction,
        new_term: Terminator,
    ) {
        self.blocks
            .get_mut(source_instruction.bb())
            .expect("source instruction basic block should be valid")
            .terminator = new_term;
    }

    /// Remove the given statement.
    pub(crate) fn remove_stmt(&mut self, bb: BasicBlockIdx, stmt: usize) {
        self.blocks[bb].statements.remove(stmt);
    }

    /// Get the number of basic blocks.
    pub(crate) fn num_blocks(&self) -> usize {
        self.blocks.len()
    }

    /// Push a new basic block to the end of the body.
    /// Returns the index of the new block.
    pub(crate) fn push_block(&mut self, block: BasicBlock) -> BasicBlockIdx {
        let idx = self.blocks.len();
        self.blocks.push(block);
        idx
    }

    /// Get a mutable reference to a basic block for direct manipulation.
    ///
    /// This is a low-level API that provides direct access to a block's statements and terminator.
    /// Use this when the higher-level insertion APIs (`insert_stmt`, `insert_call`, etc.) don't
    /// fit your transformation needs.
    ///
    /// # When to Use
    ///
    /// - **Bulk modifications**: Replacing all statements in a block, clearing a block
    /// - **Direct terminator replacement**: Changing a terminator's kind or targets without
    ///   splitting the block
    /// - **Loop transformations**: Modifying loop headers/latches that require coordinated
    ///   changes across multiple blocks
    ///
    /// # When NOT to Use
    ///
    /// - **Inserting instrumentation**: Use `insert_check`, `insert_call`, or `insert_stmt`
    ///   which handle block splitting and source tracking automatically
    /// - **Adding new blocks**: Use `insert_bb` or `push_block` instead
    ///
    /// # Caution
    ///
    /// Direct block manipulation can invalidate `SourceInstruction` references pointing to
    /// the modified block. If you're iterating with a `SourceInstruction`, prefer the
    /// higher-level insertion APIs.
    ///
    /// # Example
    ///
    /// ```text
    /// // Replace terminator directly (e.g., changing loop iteration bounds)
    /// let block = body.block_mut(loop_header_bb);
    /// block.terminator = Terminator {
    ///     kind: TerminatorKind::Goto { target: new_target },
    ///     span: block.terminator.span,
    /// };
    /// ```
    pub(crate) fn block_mut(&mut self, bb: BasicBlockIdx) -> &mut BasicBlock {
        &mut self.blocks[bb]
    }
}

#[derive(Clone, Debug)]
pub(crate) enum CheckType {
    SafetyCheck(Instance),
    SafetyCheckNoAssume(Instance),
    UnsupportedCheck(Instance),
}

impl CheckType {
    /// This will create the type of safety check that is available in the current crate, attempting
    /// to create a check that generates an assertion following by an assumption of the same
    /// assertion.
    pub(crate) fn new_safety_check_assert_assume(queries: &QueryDb) -> CheckType {
        let fn_def = queries.kani_functions()[&KaniHook::SafetyCheck.into()];
        CheckType::SafetyCheck(
            Instance::resolve(fn_def, &GenericArgs(vec![]))
                .expect("SafetyCheck function should be resolvable"),
        )
    }

    /// This will create the type of safety check that is available in the current crate, attempting
    /// to create a check that generates an assertion, but not following by an assumption.
    pub(crate) fn new_safety_check_assert_no_assume(queries: &QueryDb) -> CheckType {
        let fn_def = queries.kani_functions()[&KaniHook::SafetyCheckNoAssume.into()];
        CheckType::SafetyCheckNoAssume(
            Instance::resolve(fn_def, &GenericArgs(vec![]))
                .expect("SafetyCheckNoAssume function should be resolvable"),
        )
    }

    /// This will create the type of operation-unsupported check that is available in the current
    /// crate, attempting to create a check that generates an assertion following by an assumption
    /// of the same assertion.
    pub(crate) fn new_unsupported_check_assert_assume_false(queries: &QueryDb) -> CheckType {
        let fn_def = queries.kani_functions()[&KaniHook::UnsupportedCheck.into()];
        CheckType::UnsupportedCheck(
            Instance::resolve(fn_def, &GenericArgs(vec![]))
                .expect("UnsupportedCheck function should be resolvable"),
        )
    }
}

/// We store the index of an instruction to avoid borrow checker issues and unnecessary copies.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum SourceInstruction {
    Statement { idx: usize, bb: BasicBlockIdx },
    Terminator { bb: BasicBlockIdx },
}

impl SourceInstruction {
    pub(crate) fn span(&self, blocks: &[BasicBlock]) -> Span {
        match *self {
            SourceInstruction::Statement { idx, bb } => blocks[bb].statements[idx].span,
            SourceInstruction::Terminator { bb } => blocks[bb].terminator.span,
        }
    }

    pub(crate) fn bb(&self) -> BasicBlockIdx {
        match *self {
            SourceInstruction::Statement { bb, .. } | SourceInstruction::Terminator { bb } => bb,
        }
    }
}

/// Basic mutable body visitor.
///
/// We removed many methods for simplicity.
///
/// Upstream contribution candidate: <https://github.com/rust-lang/project-stable-mir/issues/81>
///
/// This code was based on the existing MirVisitor:
/// <https://github.com/rust-lang/rust/blob/master/compiler/stable_mir/src/mir/visit.rs>
pub(crate) trait MutMirVisitor {
    fn visit_body(&mut self, body: &mut MutableBody) {
        self.super_body(body);
    }

    fn visit_basic_block(&mut self, bb: &mut BasicBlock) {
        self.super_basic_block(bb);
    }

    fn visit_statement(&mut self, stmt: &mut Statement) {
        self.super_statement(stmt);
    }

    fn visit_terminator(&mut self, term: &mut Terminator) {
        self.super_terminator(term);
    }

    fn visit_rvalue(&mut self, rvalue: &mut Rvalue) {
        self.super_rvalue(rvalue);
    }

    fn visit_operand(&mut self, _operand: &mut Operand) {}

    fn super_body(&mut self, body: &mut MutableBody) {
        for bb in &mut body.blocks {
            self.visit_basic_block(bb);
        }
    }

    fn super_basic_block(&mut self, bb: &mut BasicBlock) {
        for stmt in &mut bb.statements {
            self.visit_statement(stmt);
        }
        self.visit_terminator(&mut bb.terminator);
    }

    fn super_statement(&mut self, stmt: &mut Statement) {
        match &mut stmt.kind {
            StatementKind::Assign(_, rvalue) => {
                self.visit_rvalue(rvalue);
            }
            StatementKind::Intrinsic(intrinsic) => match intrinsic {
                NonDivergingIntrinsic::Assume(operand) => {
                    self.visit_operand(operand);
                }
                NonDivergingIntrinsic::CopyNonOverlapping(CopyNonOverlapping {
                    src,
                    dst,
                    count,
                }) => {
                    self.visit_operand(src);
                    self.visit_operand(dst);
                    self.visit_operand(count);
                }
            },
            StatementKind::FakeRead(_, _)
            | StatementKind::SetDiscriminant { .. }
            | StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Retag(_, _)
            | StatementKind::PlaceMention(_)
            | StatementKind::AscribeUserType { .. }
            | StatementKind::Coverage(_)
            | StatementKind::ConstEvalCounter
            | StatementKind::Nop => {}
        }
    }

    fn super_terminator(&mut self, term: &mut Terminator) {
        let Terminator { kind, .. } = term;
        match kind {
            TerminatorKind::Assert { cond, .. } => {
                self.visit_operand(cond);
            }
            TerminatorKind::Call { func, args, .. } => {
                self.visit_operand(func);
                for arg in args {
                    self.visit_operand(arg);
                }
            }
            TerminatorKind::SwitchInt { discr, .. } => {
                self.visit_operand(discr);
            }
            TerminatorKind::InlineAsm { .. } => {
                // we don't support inline assembly.
            }
            TerminatorKind::Return
            | TerminatorKind::Goto { .. }
            | TerminatorKind::Resume
            | TerminatorKind::Abort
            | TerminatorKind::Drop { .. }
            | TerminatorKind::Unreachable => {}
        }
    }

    fn super_rvalue(&mut self, rvalue: &mut Rvalue) {
        match rvalue {
            Rvalue::Aggregate(_, operands) => {
                for op in operands {
                    self.visit_operand(op);
                }
            }
            Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                self.visit_operand(lhs);
                self.visit_operand(rhs);
            }
            Rvalue::Cast(_, op, _) => {
                self.visit_operand(op);
            }
            Rvalue::Repeat(op, _) => {
                self.visit_operand(op);
            }
            Rvalue::ShallowInitBox(op, _) => self.visit_operand(op),
            Rvalue::UnaryOp(_, op) | Rvalue::Use(op) => {
                self.visit_operand(op);
            }
            Rvalue::AddressOf(..) => {}
            Rvalue::CopyForDeref(_) | Rvalue::Discriminant(_) | Rvalue::Len(_) => {}
            Rvalue::Ref(..) => {}
            Rvalue::ThreadLocalRef(_) => {}
            Rvalue::NullaryOp(..) => {}
        }
    }
}

fn get_mut_target_ref(terminator: &mut Terminator) -> &mut BasicBlockIdx {
    match &mut terminator.kind {
        TerminatorKind::Assert { target, .. }
        | TerminatorKind::Drop { target, .. }
        | TerminatorKind::Goto { target }
        | TerminatorKind::Call { target: Some(target), .. } => target,
        TerminatorKind::Return => unreachable!(
            "Cannot insert instructions after Return terminator: control does not continue. \
             This indicates a transformation attempted to modify a non-continuable control flow point."
        ),
        TerminatorKind::Unreachable => unreachable!(
            "Cannot insert instructions after Unreachable terminator: control does not continue. \
             This indicates a transformation attempted to modify a non-continuable control flow point."
        ),
        TerminatorKind::Resume => unreachable!(
            "Cannot insert instructions after Resume terminator: control does not continue. \
             This indicates a transformation attempted to modify a non-continuable control flow point."
        ),
        TerminatorKind::Abort => unreachable!(
            "Cannot insert instructions after Abort terminator: control does not continue. \
             This indicates a transformation attempted to modify a non-continuable control flow point."
        ),
        TerminatorKind::SwitchInt { .. } => unreachable!(
            "Cannot insert instructions after SwitchInt terminator: it has multiple targets. \
             Transformations should handle SwitchInt branches individually."
        ),
        TerminatorKind::Call { target: None, .. } => unreachable!(
            "Cannot insert instructions after diverging Call terminator: control does not continue. \
             This indicates a transformation attempted to modify a diverging function call."
        ),
        TerminatorKind::InlineAsm { .. } => unreachable!(
            "Cannot insert instructions after InlineAsm terminator: \
             InlineAsm is not supported for verification and should have been rejected earlier."
        ),
    }
}
