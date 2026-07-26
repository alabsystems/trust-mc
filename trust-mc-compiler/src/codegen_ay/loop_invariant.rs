// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Loop invariant formula extraction via CHC context.
//!
//! Extracted from `context/artifact.rs` to break the context→chc import cycle
//! (Part of #2997: split codegen_ay into subcrates).
//!
//! This module sits at the `codegen_ay` level where it can import both
//! `context` types (config) and `chc` types (ChcCtx, WideMemMode).

use crate::codegen_ay::chc::{ChcConfig, ChcCtx, ExprEnv, WideMemMode};
use crate::kani_middle::transform::ExtractedLoopInvariant;
use rustc_public::DefId;
use rustc_public::ty::ClosureDef;
use rustc_public_bridge::IndexedVal;

/// Extract a loop invariant formula from a closure body using the CHC encoder.
///
/// Part of #972, #1562: Formula extraction from closure bodies.
/// Moved from `AYCtx::extract_loop_invariant_formula` to break context→chc cycle.
pub(in crate::codegen_ay) fn extract_loop_invariant_formula(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    harness_name: &str,
    inv: &ExtractedLoopInvariant,
    chc_track_level: crate::args::ChcTrackLevel,
    chc_step_mode: crate::args::ChcStepMode,
    ay_wide_mem: bool,
) -> Option<String> {
    let closure_def_index = inv.closure_def_index?;
    let def_id = <DefId as IndexedVal>::to_val(closure_def_index as usize);
    let closure_def = ClosureDef(def_id);
    let body = closure_def.body()?;

    let cfg = ChcConfig {
        track_level: chc_track_level,
        step_mode: chc_step_mode,
        wide_mem: WideMemMode::from(ay_wide_mem),
        ..ChcConfig::default()
    };
    let mut chc_ctx = ChcCtx::new(tcx, &body, harness_name, cfg);
    let expr = chc_ctx.extract_loop_invariant_formula(&inv.captured_vars)?;
    let mut formula = expr.to_string();

    let mut replacements: Vec<(String, String)> = inv
        .captured_vars
        .iter()
        .enumerate()
        .map(|(idx, local)| {
            use std::fmt::Write;
            let mut from = String::with_capacity(harness_name.len() + 10);
            from.push('_');
            from.push_str(harness_name);
            from.push('_');
            let _ = write!(from, "{local}");
            let mut to = String::with_capacity(12);
            to.push_str("captured_");
            let _ = write!(to, "{idx}");
            (from, to)
        })
        .collect();
    replacements.sort_by(|a, b| b.0.len().cmp(&a.0.len()));
    for (from, to) in replacements {
        formula = formula.replace(&from, &to);
    }

    Some(formula)
}
