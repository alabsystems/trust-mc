// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SMT-LIB2 file I/O operations.
//!
//! This module handles reading and preprocessing SMT files for solver invocation.
//!
//! Submodules:
//! - `classifier`: SMT logic classification (Linear, NIA, NRA, DtBvArrays) and HORN detection
//! - `datatypes`: datatype-declaration block collection and decidability analysis
//! - `declarations`: violation and cover declaration extraction
//! - `nonlinear`: typed-variable collection and nonlinear detection helpers

mod classifier;
pub(crate) mod datatypes;
mod declarations;
mod nonlinear;
#[cfg(test)]
mod tests;

pub(crate) use classifier::{
    SmtLogicClass, classify_smt_logic_from_content, content_uses_horn_logic,
};
pub(crate) use declarations::{
    build_cover_sat_query, build_cover_sat_query_for_chc, extract_cover_declarations_from_content,
    extract_coverage_declarations_from_content, extract_reach_declarations_from_content,
    extract_violation_declarations_from_content, strip_cover_assertions_for_chc_solver,
};
