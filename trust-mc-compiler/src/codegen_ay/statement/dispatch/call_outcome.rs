// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared call-dispatch outcome contract for BMC statement codegen.

use rustc_public::mir::BasicBlockIdx;

/// Explicit outcome for BMC statement call dispatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::codegen_ay::statement) enum CallDispatchOutcome {
    Miss,
    Continue(BasicBlockIdx),
    Diverge,
    FallthroughToUnsupported,
}

impl CallDispatchOutcome {
    /// Convert a handled call target into explicit continue/diverge states.
    pub(in crate::codegen_ay::statement) fn from_handled_target(
        target: Option<BasicBlockIdx>,
    ) -> Self {
        match target {
            Some(bb) => Self::Continue(bb),
            None => Self::Diverge,
        }
    }

    /// Convert a legacy `Option<Option<BasicBlockIdx>>` dispatcher result.
    /// Outer None = miss, inner None = diverge, inner Some = continue.
    pub(in crate::codegen_ay::statement) fn from_nested_target(
        result: Option<Option<BasicBlockIdx>>,
    ) -> Self {
        match result {
            Some(target) => Self::from_handled_target(target),
            None => Self::Miss,
        }
    }

    /// Convert a handled codegen result where `None` means "use generic unsupported fallback".
    pub(in crate::codegen_ay::statement) fn from_fallthrough_result(
        result: Option<BasicBlockIdx>,
    ) -> Self {
        match result {
            Some(bb) => Self::Continue(bb),
            None => Self::FallthroughToUnsupported,
        }
    }

    /// Convert a legacy `Option<BasicBlockIdx>` dispatcher result where
    /// `None` means "no match" (miss).
    pub(in crate::codegen_ay::statement) fn from_optional_target(
        result: Option<BasicBlockIdx>,
    ) -> Self {
        match result {
            Some(bb) => Self::Continue(bb),
            None => Self::Miss,
        }
    }
}
