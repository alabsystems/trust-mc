// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AY solver output parsing.
//!
//! This module parses SMT solver output and converts it to trust-mc verification results.
//! Submodules:
//! - `vc_artifact`: VC artifact loading and path helpers
//! - `violation`: Violation and cover property parsing
//! - `trace`: SMT model value parsing for trace extraction

mod trace;
pub(crate) mod vc_artifact;
mod violation;

// Re-export crate-internal items — all callers use `crate::ay_parse::*`
// Trace parsing used by call_ay.rs:
pub(crate) use trace::parse_kani_any_trace;
// VC artifact I/O used by call_ay.rs and call_ay/chc.rs:
#[cfg(feature = "ay-chc-native")]
pub(crate) use vc_artifact::load_loop_hints;
pub(crate) use vc_artifact::{
    ChcArtifactProperty, load_chc_property_table, load_vc_artifact, vc_artifact_path_for_smt,
};
// Violation/cover parsing used by call_ay.rs:
pub(crate) use violation::{
    apply_kani_property_naming, apply_loop_contract_naming, build_cover_properties_from_sat_checks,
    build_coverage_results_from_sat_checks, build_success_properties,
    determine_failed_from_properties, parse_cover_properties, parse_cover_sat_check_output,
    parse_coverage_results, parse_solver_output, parse_violation_entry_names,
    parse_violation_properties,
};
