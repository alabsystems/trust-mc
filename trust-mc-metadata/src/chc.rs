// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use strum_macros::{AsRefStr, Display, EnumString, VariantNames};

/// CHC memory tracking precision level for AY backend.
///
/// Controls how memory operations (loads/stores through pointers) are modeled
/// in CHC encoding. Higher precision enables verification of more properties
/// but may increase solver complexity.
///
/// CHC memory precision levels defined below.
#[derive(
    Debug,
    Default,
    Display,
    Clone,
    Copy,
    AsRefStr,
    EnumString,
    VariantNames,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    clap::ValueEnum
)]
#[strum(serialize_all = "snake_case")]
pub enum ChcTrackLevel {
    /// Register-only tracking (default). Memory operations havoc/no-op.
    /// Suitable for simple integer programs without pointer reasoning.
    #[default]
    Reg,
    /// Pointer validity tracking. Loads havoc, but r_ok checks emitted.
    /// Suitable for bounds/OOB checking without full memory modeling.
    Ptr,
    /// Full memory tracking. Uses select(mem,addr)/store(mem,addr,val).
    /// Suitable for complete pointer verification.
    Mem,
}

/// CHC encoding step granularity for AY backend (#112).
///
/// Controls whether CHC predicates are emitted per basic block (small step)
/// or per loop-free CFG fragment (large step). Large-step encoding reduces
/// predicate count, which helps PDR's PDR algorithm converge on loops.
///
/// Reference: SeaHorn `--step` flag (small/large/fsmall/flarge).
#[derive(
    Debug,
    Default,
    Display,
    Clone,
    Copy,
    AsRefStr,
    EnumString,
    VariantNames,
    PartialEq,
    Eq,
    clap::ValueEnum
)]
#[strum(serialize_all = "snake_case")]
pub enum ChcStepMode {
    /// One predicate per MIR basic block.
    Small,
    /// One predicate per cut point (loop headers + entry/exit).
    /// Loop-free fragments between cut points collapse into single rules.
    Large,
    /// Per-function auto-detection: use `Large` for functions with loops,
    /// `Small` for acyclic functions. Resolved in `mir_to_chc()` before
    /// CHC encoding begins.
    #[default]
    Auto,
}
