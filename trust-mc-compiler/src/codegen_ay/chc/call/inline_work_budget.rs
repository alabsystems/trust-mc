// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A harness-wide bound on recursive and speculative inline translation.
//!
//! Depth bounds one call chain; local loop/block limits restart for each
//! body. Neither bounds a branching tree of dyn-drop candidates. Charge body
//! entries, speculative attempts and block visits against one monotone budget
//! on ChcCtx, including work whose heap effects are rolled back.

use super::ChcCtx;

pub(in crate::codegen_ay::chc) const INLINE_WORK_BUDGET_EXHAUSTED: &str =
    "inline_work_budget_exhausted";

/// Keep the depth needed by real iterator helper chains while bounding the
/// total work independently of that depth and of candidate/branch fanout.
const MAX_INLINE_WORK: usize = 16_384;

pub(in crate::codegen_ay::chc) struct InlineWorkBudget {
    limit: usize,
    spent: usize,
    reported: bool,
}

impl Default for InlineWorkBudget {
    fn default() -> Self {
        Self { limit: MAX_INLINE_WORK, spent: 0, reported: false }
    }
}

impl InlineWorkBudget {
    /// Whether the refusal needs its first diagnostic booking. Work is never
    /// refunded, and a refusal never returns a substitute value or check.
    fn spend(&mut self) -> Result<(), bool> {
        if self.spent >= self.limit {
            let first = !self.reported;
            self.reported = true;
            Err(first)
        } else {
            self.spent += 1;
            Ok(())
        }
    }

    #[cfg(test)]
    fn with_limit(limit: usize) -> Self {
        Self { limit, ..Self::default() }
    }
}

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn spend_inline_work(&mut self) -> Option<()> {
        match self.inline_work_budget.spend() {
            Ok(()) => Some(()),
            Err(first) => {
                if first {
                    self.record_sound_fallback_reason(INLINE_WORK_BUDGET_EXHAUSTED);
                }
                None
            }
        }
    }
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod tests;
