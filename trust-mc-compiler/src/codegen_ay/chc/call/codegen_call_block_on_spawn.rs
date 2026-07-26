// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Spawn scheduler fallback logic for `block_on_with_spawn`.
//!
//! Extracted from `codegen_call_block_on.rs` for file-size compliance.
//! Part of #4075.

use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::inline_body::InlineReturn;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Read the current `virtual_missing_vtable` count for this function,
    /// or 0 if spawn is not active.
    pub(in crate::codegen_ay::chc) fn spawn_vtable_miss_count_if_active(
        &self,
        is_spawn: bool,
    ) -> usize {
        if !is_spawn {
            return 0;
        }
        super::codegen_ctx::diagnostics::GLOBAL_COUNTERS
            .get_translation_drop_site_reason_count_for_fn(&self.fn_name, "virtual_missing_vtable")
    }

    /// Part of #4075 D3: detect excessive vtable misses from spawn scheduler
    /// inline walk BEFORE emitting inline result. Vtable misses indicate the
    /// model failed to cover dispatch sites.
    pub(in crate::codegen_ay::chc) fn try_claim_spawn_vtable_fallback(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        is_spawn: bool,
        virtual_missing_vtable_before: usize,
        inline_result: &Option<InlineReturn>,
        callee_name: &str,
    ) -> bool {
        if !is_spawn {
            return false;
        }
        const SPAWN_VTABLE_THRESHOLD: usize = 10;
        if inline_result.is_none() {
            // Keep the spawn vtable model alive for downstream dyn/virtual
            // dispatch when the wrapper inline walk itself bails out.
            if let Some(model) = self.spawn_scheduler_vtable_model.as_mut() {
                model.next_poll_idx = 0;
            }
            return false;
        }
        let virtual_missing_vtable_after = super::codegen_ctx::diagnostics::GLOBAL_COUNTERS
            .get_translation_drop_site_reason_count_for_fn(&self.fn_name, "virtual_missing_vtable");
        let virtual_missing_vtable_delta =
            virtual_missing_vtable_after.saturating_sub(virtual_missing_vtable_before);
        if virtual_missing_vtable_delta <= SPAWN_VTABLE_THRESHOLD {
            return false;
        }
        self.spawn_scheduler_vtable_model = None;
        self.record_sound_fallback_reason("block_on_spawn_scheduler_overapprox");
        super::codegen_call_fallback_emit::emit_sound_fallback_goto(
            self,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dcx.destination.local],
            dcx.stmt_constraints,
        );
        debug!(
            bb_idx = dcx.bb_idx,
            callee = %callee_name,
            virtual_missing_vtable_delta,
            "block_on: spawn — vtable miss fallback (#4075 D3)"
        );
        true
    }

    /// Part of #4075: After emitting the spawn scheduler inline result, check
    /// whether the expansion produced an excessive number of rules. The spawn
    /// scheduler body (Scheduler::run with loop replay, Vec/Option/dyn Future
    /// operations) can expand to 400K+ rules that cause solver OOM/timeout.
    ///
    /// When the rule count exceeds the threshold, truncate the emitted rules
    /// back to the pre-inline count and replace with a single sound
    /// over-approximation goto. This is safe because overapprox is sound.
    pub(in crate::codegen_ay::chc) fn try_truncate_spawn_rule_budget(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        target: usize,
        rule_count_before: usize,
        callee_name: &str,
    ) {
        const SPAWN_RULE_COUNT_THRESHOLD: usize = 200_000;
        let rule_count_delta = self.vc.rules.len().saturating_sub(rule_count_before);
        if rule_count_delta <= SPAWN_RULE_COUNT_THRESHOLD {
            return;
        }
        self.record_sound_fallback_reason("block_on_spawn_scheduler_rule_budget");
        self.vc.rules.truncate(rule_count_before);
        super::codegen_call_fallback_emit::emit_sound_fallback_goto(
            self,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dcx.destination.local],
            dcx.stmt_constraints,
        );
        debug!(
            bb_idx = dcx.bb_idx,
            callee = %callee_name,
            rule_count_delta,
            "block_on: spawn — rule budget exceeded, truncated to sound fallback (#4075)"
        );
    }
}
