// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Common parameter bundles for CHC call dispatch functions.
//!
//! - [`ChcCallContext`]: for call handlers with a resolved target block.
//! - [`DispatchCallContext`]: for dispatch-layer trait methods where `target`
//!   is `Option<BasicBlockIdx>` (handles diverging-call routing).
//! - [`CallEmitContext`]: lightweight rule-emission bundle for non-stub call
//!   handlers (vtable intrinsics, UnsafeCell::get, raw_eq, etc.).
//!
//! Part of #2381: CHC codegen ~88 clippy::too_many_arguments suppressions.
//! Part of #3517: parameter reduction via context structs.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use std::collections::HashSet;

use crate::codegen_ay::stubs::StubKind;

use super::RelationApp;

/// Common parameter bundle for CHC call dispatch functions.
///
/// Carries the parameters shared by virtually all `codegen_call_*` methods:
/// the stub kind, MIR call arguments, destination place, target block,
/// source relation, accumulated constraints, and the set of modified locals.
pub(in crate::codegen_ay::chc) struct ChcCallContext<'a> {
    pub stub: StubKind,
    pub args: &'a [Operand],
    pub destination: &'a Place,
    pub target: BasicBlockIdx,
    pub from_app: &'a RelationApp,
    pub stmt_constraints: &'a [Expr],
    pub modified_locals: &'a HashSet<usize>,
}

/// Common parameter bundle for CHC call dispatch-layer functions.
///
/// Carries the parameters shared by `try_dispatch_call_*` trait methods.
/// Unlike [`ChcCallContext`], `target` is `&Option<BasicBlockIdx>` because
/// dispatch-layer functions handle the diverging-call (target=None) case.
pub(in crate::codegen_ay::chc) struct DispatchCallContext<'a> {
    pub bb_idx: usize,
    pub func: &'a Operand,
    pub args: &'a [Operand],
    pub destination: &'a Place,
    pub target: &'a Option<BasicBlockIdx>,
    pub from_app: &'a RelationApp,
    pub stmt_constraints: &'a [Expr],
    pub modified_locals: &'a HashSet<usize>,
    /// Cached result of `resolve_callee_path(func)`, resolved once at dispatch
    /// entry to avoid redundant re-resolution across the 26-step dispatch chain.
    /// Part of #3726.
    pub callee_path: Option<String>,
}

/// Lightweight rule-emission bundle for non-stub call handlers.
///
/// Carries the shared parameters needed to emit CHC goto-rules from call
/// terminators that are NOT dispatched through the stub system (e.g., vtable
/// intrinsics, `UnsafeCell::get`, `raw_eq`). Unlike [`ChcCallContext`], this
/// does not carry `stub: StubKind`.
///
/// Part of #3517: reduces parameter counts on call handler functions.
pub(in crate::codegen_ay::chc) struct CallEmitContext<'a> {
    pub args: &'a [Operand],
    pub destination: &'a Place,
    pub target: BasicBlockIdx,
    pub from_app: &'a RelationApp,
    pub stmt_constraints: &'a [Expr],
    pub modified_locals: &'a HashSet<usize>,
}

impl<'a> From<&ChcCallContext<'a>> for CallEmitContext<'a> {
    fn from(cx: &ChcCallContext<'a>) -> Self {
        Self {
            args: cx.args,
            destination: cx.destination,
            target: cx.target,
            from_app: cx.from_app,
            stmt_constraints: cx.stmt_constraints,
            modified_locals: cx.modified_locals,
        }
    }
}
