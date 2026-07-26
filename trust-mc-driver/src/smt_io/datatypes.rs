// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Datatype-declaration block collection and decidability analysis helpers.
//!
//! Handles SMT-LIB2 `declare-datatype` / `declare-datatypes` declarations:
//! collecting multi-line blocks, extracting field sorts, and determining
//! whether a datatype is decidable (BV/Bool-only) or requires incomplete
//! theory interaction (Int/Real/nested-DT).

#[cfg(test)]
use anyhow::{Context, Result};
use std::collections::HashSet;
#[cfg(test)]
use std::path::Path;

/// Check if an SMT file contains datatype declarations.
///
/// This detects if the SMT file uses SMT-LIB2 datatype declarations.
/// Previously used to guard AY-native solver (ay#517), now kept for diagnostics.
/// AY's datatype theory is fully implemented as of ay#517 closure.
///
/// REQUIRES: smt_file exists and is readable
/// ENSURES: result.is_ok() implies result == file contains (declare-datatype|declare-datatypes)
/// ENSURES: result == true iff file has line starting with "(declare-datatype" or "(declare-datatypes"
#[cfg(test)]
pub(crate) fn smt_file_has_datatypes(smt_file: &Path) -> Result<bool> {
    let content = std::fs::read_to_string(smt_file)
        .with_context(|| format!("Failed to read SMT file: {}", smt_file.display()))?;

    // Check for SMT-LIB2 datatype declaration commands
    // - (declare-datatype Name ...) - single datatype
    // - (declare-datatypes ...) - multiple mutually recursive datatypes
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("(declare-datatype") || trimmed.starts_with("(declare-datatypes") {
            return Ok(true);
        }
    }

    Ok(false)
}

/// Check if content contains any datatype declaration with non-decidable fields.
///
/// Handles both single-line and multi-line datatype declarations by first
/// collecting complete declaration blocks, then using fixpoint iteration to
/// determine which DTs are decidable (including nested DTs whose all leaf
/// fields are BV/Bool/Array(BV,BV)).
///
/// Part of #2979: Nested tuples like `((u32, bool), u8)` emit DT declarations
/// where the outer DT references the inner DT name. The old per-declaration
/// check treated any DT name reference as non-decidable, causing spurious
/// DtBvArrays demotion. The fixpoint algorithm resolves transitive decidability.
pub(super) fn content_has_complex_datatypes(content: &str) -> bool {
    let decl_blocks = collect_datatype_decl_blocks(content);
    if decl_blocks.is_empty() {
        return false;
    }

    // Parse each declaration: extract (name, field_sorts).
    // Parametric declarations (declare-datatypes) are conservatively complex.
    let mut dt_entries: Vec<(String, Vec<&str>)> = Vec::new();
    let mut has_parametric = false;

    for decl in &decl_blocks {
        if decl.starts_with("(declare-datatypes") {
            has_parametric = true;
            continue;
        }
        if let Some(name) = extract_dt_name(decl) {
            let field_sorts = extract_field_sorts(decl);
            dt_entries.push((name.to_string(), field_sorts));
        }
    }

    // Fixpoint iteration: find all DTs whose fields are decidable
    // (BV/Bool/Array(BV,BV) or references to other decidable DTs).
    let mut decidable_dt_names: HashSet<&str> = HashSet::new();
    loop {
        let mut changed = false;
        for (name, field_sorts) in &dt_entries {
            if decidable_dt_names.contains(name.as_str()) {
                continue;
            }
            let all_decidable =
                field_sorts.iter().all(|s| is_decidable_field_sort(s, &decidable_dt_names));
            if all_decidable {
                decidable_dt_names.insert(name);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // A file has complex DTs if any non-parametric DT is NOT decidable,
    // or if there are parametric DTs (conservatively complex).
    if has_parametric {
        return true;
    }
    dt_entries.iter().any(|(name, _)| !decidable_dt_names.contains(name.as_str()))
}

/// Extract the datatype name from a `(declare-datatype Name ...)` block.
///
/// Returns the first token after `(declare-datatype `.
fn extract_dt_name(decl: &str) -> Option<&str> {
    let rest = decl.strip_prefix("(declare-datatype")?;
    let rest = rest.trim_start();
    // Name ends at whitespace or '('
    let end = rest.find(|c: char| c.is_whitespace() || c == '(').unwrap_or(rest.len());
    let name = &rest[..end];
    if name.is_empty() { None } else { Some(name) }
}

/// Collect complete datatype declaration blocks from SMT-LIB content.
///
/// Supports multi-line declarations by tracking parenthesis balance from a line
/// starting with `(declare-datatype` or `(declare-datatypes` until the block closes.
pub(super) fn collect_datatype_decl_blocks(content: &str) -> Vec<String> {
    let mut blocks = Vec::new();
    let mut current = String::new();
    let mut collecting = false;
    let mut paren_depth: i32 = 0;

    for line in content.lines() {
        let code = line.split(';').next().unwrap_or("").trim();
        if code.is_empty() {
            continue;
        }

        if !collecting {
            if code.starts_with("(declare-datatype") || code.starts_with("(declare-datatypes") {
                collecting = true;
                current.clear();
                current.push_str(code);
                paren_depth = paren_balance_delta(code);
                if paren_depth <= 0 {
                    blocks.push(std::mem::take(&mut current));
                    collecting = false;
                }
            }
            continue;
        }

        if !current.ends_with(' ') {
            current.push(' ');
        }
        current.push_str(code);
        paren_depth += paren_balance_delta(code);
        if paren_depth <= 0 {
            blocks.push(std::mem::take(&mut current));
            collecting = false;
        }
    }

    if collecting && !current.is_empty() {
        // Incomplete declaration: preserve block for conservative handling.
        blocks.push(current);
    }

    blocks
}

fn paren_balance_delta(line: &str) -> i32 {
    line.bytes().fold(0, |delta, byte| match byte {
        b'(' => delta + 1,
        b')' => delta - 1,
        _ => delta,
    })
}

/// Check if a single `declare-datatype` line contains field sorts that require incomplete theory.
///
/// A datatype is "decidable" if all constructor fields have sorts that are decidable
/// in combination with the DT theory: `(_ BitVec N)`, `Bool`, or `(Array BV BV)`.
/// Nullary constructors (no fields) are allowed.
///
/// Returns true if ANY field has a sort that requires incomplete theory interaction
/// (e.g., `Int`, `Real`, or a nested datatype reference).
///
/// NOTE: This is a per-declaration check that does NOT resolve nested DT references.
/// For cross-declaration decidability (e.g., nested tuples), use
/// `content_has_complex_datatypes` which does fixpoint iteration.
///
/// Conservative: returns true (triggers demotion) for `declare-datatypes` (parametric)
/// since those are rare and harder to parse.
///
/// Part of #2851, refined by #2876.
#[cfg(test)]
pub(super) fn datatype_decl_has_non_bv_fields(line: &str) -> bool {
    // Parametric datatypes (declare-datatypes) are rare; conservatively demote.
    if line.starts_with("(declare-datatypes") {
        return true;
    }

    // Structure (depth shown):
    //   0: (declare-datatype
    //   1:   Name
    //   1:   (                         <- constructor list open
    //   2:     (Ctor                   <- constructor open
    //   3:       (fieldname Sort)      <- field selector
    //   2:     )                       <- constructor close
    //   1:   )                         <- constructor list close
    //   0: )                           <- declare-datatype close
    //
    // Field selectors appear at depth 3 inside a constructor (depth 2).
    // We track paren depth relative to the whole line and extract field sorts
    // at depth 4 (field selector open = depth 4 inside the full s-expr).
    //
    // Full line nesting: (declare-datatype Name ((Ctor (fld Sort))))
    //                    1                      2 3    4

    for field_sort in extract_field_sorts(line) {
        if !is_decidable_sort(field_sort) {
            return true;
        }
    }

    false
}

/// Extract field sort strings from a `declare-datatype` line.
///
/// Tracks paren depth to find field selectors (at depth 4 in the full s-expr).
/// Returns the sort portion of each `(fieldname Sort)` pattern.
pub(super) fn extract_field_sorts(line: &str) -> Vec<&str> {
    let mut sorts = Vec::new();
    let bytes = line.as_bytes();
    let len = bytes.len();
    let mut i = 0;
    let mut depth: u32 = 0;

    while i < len {
        match bytes[i] {
            b'(' => {
                depth += 1;
                // At depth 4, we're entering a field selector: (fieldname Sort)
                if depth == 4 {
                    i += 1;
                    // Skip whitespace
                    while i < len && bytes[i] == b' ' {
                        i += 1;
                    }
                    // Skip field name
                    while i < len && bytes[i] != b' ' && bytes[i] != b')' {
                        i += 1;
                    }
                    // If space follows, read the sort
                    if i < len && bytes[i] == b' ' {
                        i += 1; // skip space
                        let sort_start = i;
                        if i < len && bytes[i] == b'(' {
                            // Compound sort like (_ BitVec 32)
                            let mut inner_depth: u32 = 1;
                            i += 1;
                            while i < len && inner_depth > 0 {
                                if bytes[i] == b'(' {
                                    inner_depth += 1;
                                } else if bytes[i] == b')' {
                                    inner_depth -= 1;
                                }
                                i += 1;
                            }
                            sorts.push(&line[sort_start..i]);
                        } else {
                            // Simple sort: Bool, Int, Real, or DT name
                            while i < len && bytes[i] != b')' && bytes[i] != b' ' {
                                i += 1;
                            }
                            let sort = &line[sort_start..i];
                            if !sort.is_empty() {
                                sorts.push(sort);
                            }
                        }
                    }
                    // Skip to closing paren of the field selector
                    while i < len && bytes[i] != b')' {
                        i += 1;
                    }
                    // Don't increment i here; the ')' will be handled in the next iteration
                    continue;
                }
                i += 1;
            }
            b')' => {
                depth = depth.saturating_sub(1);
                i += 1;
            }
            _ => {
                i += 1;
            }
        }
    }

    sorts
}

/// Check if a sort string is decidable without DT theory interaction.
///
/// Accepts: `Bool`, `(_ BitVec N)`, and `(Array S1 S2)` where S1 and S2
/// are themselves decidable. Array(BV,BV) is in QF_ABV (decidable), so
/// a Datatype containing only BV, Bool, and Array(BV,BV) fields does not
/// trigger the DT+BV demotion (ay#1766 is about DT+Int/Real interaction,
/// not DT+Array(BV,BV)).
///
/// Part of #2876: Vec/Slice Datatype sorts embed `fld_data: Array(BV64, BV32)`
/// which was incorrectly classified as complex, causing spurious DtBvArrays
/// demotion for heap_realloc harnesses.
pub(super) fn is_decidable_sort(sort: &str) -> bool {
    sort == "Bool" || sort.starts_with("(_ BitVec") || is_bv_array_sort(sort)
}

/// Context-aware decidability check used by the cross-declaration fixpoint.
///
/// A field sort is decidable-in-context when it is:
/// - a leaf-decidable sort (`Bool`, `(_ BitVec N)`, or `(Array S1 S2)` where
///   both `S1`/`S2` are leaf-decidable), per [`is_decidable_sort`]; OR
/// - a bare reference to an already-decidable datatype name; OR
/// - an `(Array IndexSort ElemSort)` whose `IndexSort` is decidable-in-context
///   and whose `ElemSort` is decidable-in-context — crucially, this admits
///   arrays whose ELEMENT is a decidable datatype (e.g.
///   `(Array (_ BitVec 64) PbTerm)` where `PbTerm` flattens to BV/Bool/Array
///   leaves). Such a sort lives in QF_ADTBV (datatypes + arrays + bitvectors,
///   all finite element sorts), which is decidable, so it must NOT trigger the
///   conservative DT+BV demotion (ay#1766 targets DT+Int/Real interaction).
///
/// Part of #1766 follow-up: `is_decidable_sort` is intentionally a pure leaf
/// check (it must answer `false` for any bare DT name), so the DT-name and
/// nested-array-of-DT reasoning lives here where the set of decidable DT names
/// is available.
fn is_decidable_field_sort(sort: &str, decidable_dt_names: &HashSet<&str>) -> bool {
    if is_decidable_sort(sort) || decidable_dt_names.contains(sort) {
        return true;
    }
    // (Array IndexSort ElemSort) with both operands decidable-in-context.
    if let Some(inner) = sort.strip_prefix("(Array ").and_then(|s| s.strip_suffix(')')) {
        if let Some((index_sort, elem_sort)) = split_two_sorts(inner) {
            return is_decidable_field_sort(index_sort, decidable_dt_names)
                && is_decidable_field_sort(elem_sort, decidable_dt_names);
        }
    }
    false
}

/// Check if a sort string is `(Array S1 S2)` where both S1 and S2 are decidable.
fn is_bv_array_sort(sort: &str) -> bool {
    let Some(inner) = sort.strip_prefix("(Array ") else {
        return false;
    };
    let Some(inner) = inner.strip_suffix(')') else {
        return false;
    };
    // Split into index sort and element sort.
    // Sorts can be compound like `(_ BitVec 64)`, so we need paren-aware splitting.
    let Some((index_sort, elem_sort)) = split_two_sorts(inner) else {
        return false;
    };
    is_decidable_sort(index_sort) && is_decidable_sort(elem_sort)
}

/// Split a string containing exactly two SMT sorts separated by whitespace.
///
/// Handles compound sorts like `(_ BitVec 64)` by tracking parenthesis depth.
fn split_two_sorts(s: &str) -> Option<(&str, &str)> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }
    let bytes = s.as_bytes();
    let mut depth: u32 = 0;
    let mut i = 0;
    // Walk the first sort
    loop {
        if i >= bytes.len() {
            return None; // Only one sort
        }
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth = depth.saturating_sub(1),
            b' ' if depth == 0 => break,
            _ => {}
        }
        i += 1;
    }
    let first = &s[..i];
    let rest = s[i..].trim_start();
    if rest.is_empty() {
        return None;
    }
    Some((first, rest))
}
