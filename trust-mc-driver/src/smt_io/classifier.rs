// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SMT logic classification: Linear, NIA, NRA, DtBvArrays.
//!
//! Scans SMT-LIB2 content to determine the arithmetic complexity and theory
//! combination, selecting the appropriate solver strategy. Also provides
//! HORN logic detection for CHC mode selection.

#[cfg(test)]
use anyhow::{Context, Result};
use std::collections::HashSet;
#[cfg(test)]
use std::path::Path;

use super::datatypes::content_has_complex_datatypes;
use super::nonlinear::{collect_typed_var, detect_nonlinear_in_content};

/// Result of SMT logic classification.
///
/// Indicates the arithmetic complexity detected in an SMT file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SmtLogicClass {
    /// Linear integer/real arithmetic only - decidable, complete solvers
    Linear,
    /// Non-linear integer arithmetic detected - undecidable, incomplete
    Nia,
    /// Non-linear real arithmetic detected - decidable but expensive/incomplete
    Nra,
    /// Datatypes combined with BV or Arrays - AY solver gap (ay#1766)
    /// AY loses DT axioms when BV/Arrays are present; demote results.
    DtBvArrays,
}

/// Check if an SMT file uses HORN logic (CHC mode).
///
/// HORN logic is used for Constrained Horn Clause (CHC) solving with ay-chc.
/// This function detects if the SMT file is in CHC mode.
///
/// REQUIRES: smt_file exists and is readable
/// ENSURES: result.is_ok() implies result == file contains "(set-logic HORN)"
#[cfg(test)]
pub(crate) fn smt_file_uses_horn_logic(smt_file: &Path) -> Result<bool> {
    let content = std::fs::read_to_string(smt_file)
        .with_context(|| format!("Failed to read SMT file: {}", smt_file.display()))?;
    Ok(content_uses_horn_logic(&content))
}

/// Check if SMT content uses HORN logic (CHC mode).
///
/// Part of #2942: content-based variant avoids redundant file reads.
pub(crate) fn content_uses_horn_logic(content: &str) -> bool {
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("(set-logic") && trimmed.contains("HORN") {
            return true;
        }
    }
    false
}

/// Classify the arithmetic logic used in an SMT file.
///
/// Scans the SMT-LIB2 file to detect non-linear arithmetic patterns:
/// - NIA: multiplication of two non-constant integer expressions
/// - NRA: multiplication of two non-constant real expressions
/// - Division by a non-constant expression
///
/// This is a heuristic classifier with trade-offs:
/// - May produce false positives (classifying linear as non-linear) due to
///   conservative identifier detection
/// - May produce false negatives if non-linear terms span multiple lines
///   (line-based pattern matching limitation)
///
/// REQUIRES: smt_file exists and is readable
/// ENSURES: result.is_ok()
///
/// NIA policy: classify SMT logic to select solver strategy.
#[cfg(test)]
pub(crate) fn classify_smt_logic(smt_file: &Path) -> Result<SmtLogicClass> {
    let content = std::fs::read_to_string(smt_file)
        .with_context(|| format!("Failed to read SMT file: {}", smt_file.display()))?;
    Ok(classify_smt_logic_from_content(&content))
}

/// Classify SMT logic tier from content string.
///
/// Part of #2942: content-based variant avoids redundant file reads.
pub(crate) fn classify_smt_logic_from_content(content: &str) -> SmtLogicClass {
    // Detect complex datatype declarations (including multi-line declarations).
    // Part of #2851: BV-only datatypes should not trigger DtBvArrays demotion.
    let has_complex_dt = content_has_complex_datatypes(content);

    // Single pass for BV/Arrays features and typed variable collection.
    let mut has_bv = false;
    let mut has_arrays = false;
    let mut int_vars: HashSet<&str> = HashSet::new();
    let mut real_vars: HashSet<&str> = HashSet::new();

    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with(';') {
            continue;
        }

        // Bitvector sorts/ops/literals
        if !has_bv && line_has_bitvectors(trimmed) {
            has_bv = true;
        }

        // Array sorts/ops
        if !has_arrays
            && (trimmed.contains("(Array ")
                || trimmed.contains("(select ")
                || trimmed.contains("(store "))
        {
            has_arrays = true;
        }

        // Collect typed variable declarations
        collect_typed_var(trimmed, &mut int_vars, &mut real_vars);
    }

    // DT+BV/Arrays combination (AY solver gap - ay#1766)
    // Only demote when complex DTs (with Int/Real/Array/nested-DT fields) are present.
    // BV-only structs like Range<u32> are decidable and should not trigger demotion.
    if has_complex_dt && (has_bv || has_arrays) {
        return SmtLogicClass::DtBvArrays;
    }

    // Second pass: detect non-linear patterns using collected variables
    let has_nonlinear_int = detect_nonlinear_in_content(content, &int_vars);
    let has_nonlinear_real = detect_nonlinear_in_content(content, &real_vars);

    if has_nonlinear_int {
        return SmtLogicClass::Nia;
    }
    if has_nonlinear_real {
        return SmtLogicClass::Nra;
    }

    SmtLogicClass::Linear
}

/// Check if a single line contains bitvector indicators.
/// Extracted from content_has_bitvectors for single-pass classification.
fn line_has_bitvectors(trimmed: &str) -> bool {
    trimmed.contains("BitVec")
        || trimmed.contains("#x")
        || trimmed.contains("#b")
        || trimmed.contains("bvadd")
        || trimmed.contains("bvsub")
        || trimmed.contains("bvmul")
        || trimmed.contains("bvudiv")
        || trimmed.contains("bvsdiv")
        || trimmed.contains("bvurem")
        || trimmed.contains("bvsrem")
        || trimmed.contains("bvand")
        || trimmed.contains("bvor")
        || trimmed.contains("bvxor")
        || trimmed.contains("bvshl")
        || trimmed.contains("bvlshr")
        || trimmed.contains("bvashr")
        || trimmed.contains("bvnot")
        || trimmed.contains("bvneg")
        || trimmed.contains("bvult")
        || trimmed.contains("bvslt")
        || trimmed.contains("bvule")
        || trimmed.contains("bvsle")
        || trimmed.contains("bvugt")
        || trimmed.contains("bvsgt")
        || trimmed.contains("bvuge")
        || trimmed.contains("bvsge")
        || trimmed.contains("(concat ")
        || trimmed.contains("(_ extract")
        || trimmed.contains("zero_extend")
        || trimmed.contains("sign_extend")
}
