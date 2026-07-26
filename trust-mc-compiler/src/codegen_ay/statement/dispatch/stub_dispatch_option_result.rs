// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Option/Result stub dispatch helpers.
//!
//! Extracted from `stub_dispatch.rs` per #2246 to keep the main dispatch
//! table concise.

use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::CallDispatchOutcome;
use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::stubs::StubKind;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Convert a handled Option/Result stub into an explicit dispatch outcome.
    pub(in crate::codegen_ay::statement) fn outcome_or_fallthrough(
        result: Option<BasicBlockIdx>,
    ) -> CallDispatchOutcome {
        CallDispatchOutcome::from_fallthrough_result(result)
    }

    /// Dispatch Option/Result stubs.
    pub(in crate::codegen_ay::statement) fn try_codegen_option_result_stub(
        &mut self,
        stub_kind: StubKind,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> CallDispatchOutcome {
        if matches!(stub_kind, StubKind::OptionUnwrapUnchecked) {
            debug!("codegen_stubbed_call: Option::unwrap_unchecked - delegating to option unwrap");
            return Self::outcome_or_fallthrough(self.codegen_option_unwrap(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::ResultIsOk) {
            debug!("codegen_stubbed_call: Result::is_ok");
            return Self::outcome_or_fallthrough(self.codegen_result_is_ok(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::ResultIsErr) {
            debug!("codegen_stubbed_call: Result::is_err");
            return Self::outcome_or_fallthrough(self.codegen_result_is_err(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::OptionIsSome | StubKind::OptionIsNone) {
            debug!("codegen_stubbed_call: Option::is_some/is_none - no BMC stub needed");
            return CallDispatchOutcome::Miss;
        }
        if matches!(stub_kind, StubKind::OptionUnwrapOr) {
            debug!("codegen_stubbed_call: Option::unwrap_or");
            return Self::outcome_or_fallthrough(self.codegen_option_unwrap_or(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::ResultUnwrapOr) {
            debug!("codegen_stubbed_call: Result::unwrap_or");
            return Self::outcome_or_fallthrough(self.codegen_result_unwrap_or(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::OptionExpect) {
            debug!("codegen_stubbed_call: Option::expect - delegating to option unwrap");
            return Self::outcome_or_fallthrough(self.codegen_option_unwrap(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::ResultUnwrap) {
            debug!("codegen_stubbed_call: Result::unwrap");
            return Self::outcome_or_fallthrough(self.codegen_result_unwrap(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::ResultExpect) {
            debug!("codegen_stubbed_call: Result::expect - delegating to result unwrap");
            return Self::outcome_or_fallthrough(self.codegen_result_unwrap(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::ResultUnwrapErr) {
            debug!("codegen_stubbed_call: Result::unwrap_err");
            return Self::outcome_or_fallthrough(self.codegen_result_unwrap_err(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::OptionUnwrapOrElse) {
            debug!("codegen_stubbed_call: Option::unwrap_or_else");
            return Self::outcome_or_fallthrough(self.codegen_option_unwrap_or_else(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::ResultUnwrapOrElse) {
            debug!("codegen_stubbed_call: Result::unwrap_or_else");
            return Self::outcome_or_fallthrough(self.codegen_result_unwrap_or_else(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::OptionAndThen | StubKind::OptionMap) {
            // R1: `Option::and_then`/`map` carry a user closure. The prior symbolic
            // over-approximation (`codegen_symbolic_result` / `codegen_option_map`)
            // never RAN the closure, so the result was unconstrained — any
            // downstream equality (e.g. the ay-pb `eval_lit` Option chain
            // `.checked_sub(1).and_then(..).and_then(|i| a.get(i)).copied()`)
            // then admitted a spurious CTREX. Prefer MIR-inlining the REAL library
            // body: `match self { Some(x) => f(x), None => None }` inlines the
            // Some/None discriminant split and `f(x)` inlines the closure via the
            // existing `codegen_closure_call` / `try_inline_small_instance_call`
            // path; the flattened-Option-return re-keying (inline_body.rs) links the
            // callee result onto the destination — exactly the route `OptionCopied`
            // already relies on (it returns `Miss` for the same reason).
            //
            // Fall back to the sound symbolic over-approximation ONLY when the
            // inline DECLINES (loop / depth / recursion cap / arity / non-DAG body),
            // so there is no completeness regression on non-inlining and_then/map.
            if let Some(next) = self.try_codegen_fn_inline_call(func, args, destination, target) {
                debug!("codegen_stubbed_call: Option::and_then/map — inlined real body");
                return CallDispatchOutcome::Continue(next);
            }
            debug!(
                "codegen_stubbed_call: Option::and_then/map — inline declined, symbolic fallback"
            );
            return match stub_kind {
                StubKind::OptionAndThen => Self::outcome_or_fallthrough(
                    self.codegen_option_and_then(args, destination, target),
                ),
                _ => {
                    Self::outcome_or_fallthrough(self.codegen_option_map(args, destination, target))
                }
            };
        }
        if matches!(stub_kind, StubKind::OptionOkOrElse) {
            debug!("codegen_stubbed_call: Option::ok_or_else");
            return Self::outcome_or_fallthrough(self.codegen_option_ok_or_else(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::ResultMap) {
            debug!("codegen_stubbed_call: Result::map");
            return Self::outcome_or_fallthrough(self.codegen_result_map(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::ResultAndThen) {
            debug!("codegen_stubbed_call: Result::and_then");
            return Self::outcome_or_fallthrough(self.codegen_result_and_then(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::ResultMapErr) {
            debug!("codegen_stubbed_call: Result::map_err");
            return Self::outcome_or_fallthrough(self.codegen_result_map_err(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::ResultOk) {
            debug!("codegen_stubbed_call: Result::ok");
            return Self::outcome_or_fallthrough(self.codegen_result_ok(args, destination, target));
        }
        if matches!(stub_kind, StubKind::ResultErr) {
            debug!("codegen_stubbed_call: Result::err");
            return Self::outcome_or_fallthrough(self.codegen_result_err(
                args,
                destination,
                target,
            ));
        }
        if matches!(stub_kind, StubKind::OptionCopied) {
            // Prefer a direct flattened-Option copy (value semantics: `.copied()`
            // / `.cloned()` of a reference is the identity on the stored value).
            // This consumes a flattened `Option<&T>` (e.g. from R2's `slice::get`)
            // without the MIR-inline path's reference deref, which would synthesize
            // a fresh UNCONSTRAINED pointee for the flattened payload. Fall back to
            // Miss (MIR inline) when `self` isn't a resolvable flattened Option —
            // no regression on the cases the inline path already handles.
            if let Some(bb) = self.codegen_option_copied(args, destination, target) {
                debug!("codegen_stubbed_call: Option::copied - direct flattened copy");
                return CallDispatchOutcome::Continue(bb);
            }
            debug!("codegen_stubbed_call: Option::copied - no BMC stub, MIR inline fallback");
            return CallDispatchOutcome::Miss;
        }
        CallDispatchOutcome::Miss
    }
}
