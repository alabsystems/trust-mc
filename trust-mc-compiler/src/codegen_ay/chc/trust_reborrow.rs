// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Trust toolchain: `Rvalue::Reborrow` fails closed in the CHC engine.
//!
//! `Rvalue::Reborrow(target_ty, mutability, place)` is Trust's MIR for
//! user-definable ADT reborrowing (`#![feature(reborrow)]`, the `Reborrow` /
//! `CoerceShared` traits). rustc documents it as a bitwise copy of `place`,
//! into the same type for `Mut` and into the `CoerceShared` target type for
//! `Not`, whose layout is equal only "currently".
//!
//! The CHC engine has no encoding for it. Treating it as `Use(Copy(place))`
//! would also have to reproduce every side table the `Use` arms maintain (ref
//! targets, alloc ids, slice metadata, vtables, pointer-identity traces) and
//! every analysis that recognises `Use`, and the `Not` form changes the sort.
//! Upstream Kani's GOTO backend reports it as unsupported for the same reason.
//! So it fails closed, in three places:
//!
//! * [`ChcCtx::fail_close_reborrow_body`] — once per translated body, before
//!   any rule is emitted. This covers analyses over the body that never reach
//!   an rvalue evaluator (use/alias/taint/escape scans with `_` arms).
//! * `translate_rvalue_with_modified` and `inline_rvalue_to_expr` — the two
//!   rvalue evaluators, so a `Reborrow` executed inside an inlined callee or
//!   closure body fails closed too, then takes the caller's existing
//!   unsupported-rvalue path.
//!
//! All three record [`REBORROW_UNSUPPORTED`], which `fallback_soundness` does
//! not list, so it is `FailClose`: the driver's Step C turns any Success
//! harness carrying it into an OverApproximation counterexample (Unknown), and
//! a counterexample is never certified Genuine.
//!
//! Two helper contexts are built outside `translate_inner`, so the body guard
//! never runs for them and their recorded reasons never reach a verdict:
//!
//! * BMC quantifier unrolling (`statement::codegen_kani_call`) declines when
//!   the closure body assigns a `Reborrow` ([`body_has_reborrow`]), or when
//!   [`ChcCtx::recorded_reborrow_unsupported`] is set after translating it
//!   (a `Reborrow` in an inlined callee). The caller's
//!   `unsupported_with_fallback` then demotes the verdict.
//! * Loop-invariant formula extraction (`codegen_ay::loop_invariant`)
//!   evaluates through `translate_rvalue_with_env`, whose catch-all arm
//!   returns `None` for a `Reborrow`, so no formula is extracted and the driver
//!   skips the hint. A formula would only be a candidate lemma that the CHC
//!   solver checks, never an assumption.

use rustc_public::mir::{Body, Rvalue, StatementKind};
use tracing::debug;

use super::codegen_ctx::ChcCtx;

/// Fail-close sound-fallback reason for any `Rvalue::Reborrow`.
pub(in crate::codegen_ay::chc) const REBORROW_UNSUPPORTED: &str = "rvalue_reborrow_unsupported";

/// `true` when some statement of `body` assigns an `Rvalue::Reborrow`.
///
/// An `Rvalue` only occurs as the source of `StatementKind::Assign`.
pub(in crate::codegen_ay) fn body_has_reborrow(body: &Body) -> bool {
    body.blocks
        .iter()
        .flat_map(|block| &block.statements)
        .any(|statement| matches!(&statement.kind, StatementKind::Assign(_, Rvalue::Reborrow(..))))
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Record [`REBORROW_UNSUPPORTED`] once when the translated body contains a
    /// `Reborrow`. Called from `translate_inner` before any rule is emitted.
    pub(in crate::codegen_ay::chc) fn fail_close_reborrow_body(&mut self) {
        if body_has_reborrow(self.body) {
            debug!(fn_name = %self.fn_name, "CHC: body contains Rvalue::Reborrow — fail-closed");
            self.record_sound_fallback_reason(REBORROW_UNSUPPORTED);
            self.reborrow_unsupported_recorded = true;
        }
    }

    /// Record [`REBORROW_UNSUPPORTED`] at an rvalue evaluator that met a
    /// `Reborrow`. The evaluator then returns `None`.
    pub(in crate::codegen_ay::chc) fn record_reborrow_unsupported(&mut self, site: &'static str) {
        debug!(fn_name = %self.fn_name, site, "CHC: Rvalue::Reborrow has no encoding — fail-closed");
        self.record_sound_fallback_reason(REBORROW_UNSUPPORTED);
        self.reborrow_unsupported_recorded = true;
    }

    /// Whether this context has recorded [`REBORROW_UNSUPPORTED`].
    pub(in crate::codegen_ay) fn recorded_reborrow_unsupported(&self) -> bool {
        self.reborrow_unsupported_recorded
    }
}
