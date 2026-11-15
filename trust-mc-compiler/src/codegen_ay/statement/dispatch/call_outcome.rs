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

    /// Convert a stub encoder's `Option<Option<BasicBlockIdx>>` for a call whose
    /// MIR return target is `target`. An inner `None` on a call that returns is
    /// an ENCODING FAILURE: mapping it to `Diverge` dropped the successor edge,
    /// and the successor block was then entered as reachable with an empty
    /// environment, every read a free value with no record
    /// (kani/Realloc/two_reallocs.rs, kani/Vectors/vector_extend_bytes.rs,
    /// certified Genuine). It is the unsupported-call fallback instead. A call
    /// with no return target really diverges.
    pub(in crate::codegen_ay::statement) fn from_nested_target_for_call(
        result: Option<Option<BasicBlockIdx>>,
        target: Option<BasicBlockIdx>,
    ) -> Self {
        match result {
            None => Self::Miss,
            Some(Some(bb)) => Self::Continue(bb),
            Some(None) if target.is_some() => Self::FallthroughToUnsupported,
            Some(None) => Self::Diverge,
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
