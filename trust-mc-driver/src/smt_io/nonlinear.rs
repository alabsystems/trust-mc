// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Typed-variable collection and nonlinear arithmetic detection helpers.
//!
//! Scans SMT-LIB2 content for `declare-const`/`declare-fun` to build sets of
//! Int and Real variable names, then detects non-linear patterns (variable *
//! variable multiplication, division by variable) for NIA/NRA classification.

use std::collections::HashSet;

/// Check if SMT content contains bitvector sorts or operations.
///
/// Detects:
/// - `(_ BitVec N)` sort declarations
/// - BV operations: bvadd, bvmul, bvor, etc.
/// - Hex/binary BV literals: #xNN, #bNN
///
/// Retained for unit tests. Production path uses single-pass classify_smt_logic.
#[cfg(test)]
pub(super) fn content_has_bitvectors(content: &str) -> bool {
    for line in content.lines() {
        let trimmed = line.trim();
        // Skip comments
        if trimmed.starts_with(';') {
            continue;
        }
        // (_ BitVec N) sort
        if trimmed.contains("BitVec") {
            return true;
        }
        // Hex/binary BV literals (#xNN, #bNN)
        if trimmed.contains("#x") || trimmed.contains("#b") {
            return true;
        }
        // BV operations (bvadd, bvmul, bvor, bvand, bvshl, etc.)
        if trimmed.contains("bvadd")
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
        {
            return true;
        }
    }
    false
}

/// Check if SMT content contains array sorts or operations.
///
/// Retained for unit tests. Production path uses single-pass classify_smt_logic.
#[cfg(test)]
pub(super) fn content_has_arrays(content: &str) -> bool {
    for line in content.lines() {
        let trimmed = line.trim();
        // Skip comments
        if trimmed.starts_with(';') {
            continue;
        }
        // (Array K V) sort
        if trimmed.contains("(Array ") {
            return true;
        }
        // Array operations
        if trimmed.contains("(select ") || trimmed.contains("(store ") {
            return true;
        }
    }
    false
}

/// Check if SMT content contains datatype declarations.
///
/// Retained for unit tests. Production path uses single-pass classify_smt_logic.
#[cfg(test)]
pub(super) fn content_has_datatypes(content: &str) -> bool {
    for line in content.lines() {
        let trimmed = line.trim();
        // Skip comments
        if trimmed.starts_with(';') {
            continue;
        }
        if trimmed.starts_with("(declare-datatype") || trimmed.starts_with("(declare-datatypes") {
            return true;
        }
    }
    false
}

/// Collect typed variable names from a declaration line.
///
/// Returns borrowed slices into `trimmed` to avoid allocations.
pub(super) fn collect_typed_var<'a>(
    trimmed: &'a str,
    int_vars: &mut HashSet<&'a str>,
    real_vars: &mut HashSet<&'a str>,
) {
    // (declare-const name Type)
    if let Some(rest) = trimmed.strip_prefix("(declare-const ")
        && let Some(name_end) = rest.find(' ')
    {
        let name = &rest[..name_end];
        let type_part = rest[name_end..].trim();
        if type_part.starts_with("Int") {
            int_vars.insert(name);
        } else if type_part.starts_with("Real") {
            real_vars.insert(name);
        }
    }

    // (declare-fun name () Type)
    if let Some(rest) = trimmed.strip_prefix("(declare-fun ")
        && let Some(paren_start) = rest.find('(')
        && let Some(paren_end) = rest[paren_start..].find(')')
    {
        let name = rest[..paren_start].trim();
        let after_params = rest[paren_start + paren_end + 1..].trim();
        if after_params.starts_with("Int") {
            int_vars.insert(name);
        } else if after_params.starts_with("Real") {
            real_vars.insert(name);
        }
    }
}

/// Check if content contains non-linear patterns involving the given variables.
///
/// Detects patterns like:
/// - `(* var1 var2)` where both are variables
/// - `(/ expr var)` where divisor is a variable
///
/// This is a simple pattern-based heuristic, not a full S-expression parser.
pub(super) fn detect_nonlinear_in_content(content: &str, vars: &HashSet<&str>) -> bool {
    // Simple heuristic: look for (* and (/ patterns
    // Then check if operands are variables (not constants)

    for line in content.lines() {
        let trimmed = line.trim();

        // Skip comments
        if trimmed.starts_with(';') {
            continue;
        }

        // Look for ALL multiplication patterns on this line: (* a b)
        // A line like "(+ (* x 5) (* y z))" has two multiplications
        let mut search_start = 0;
        while let Some(mult_offset) = trimmed[search_start..].find("(* ") {
            let mult_start = search_start + mult_offset;
            let after_mult = &trimmed[mult_start + 3..];
            if check_nonlinear_args(after_mult, vars) {
                return true;
            }
            search_start = mult_start + 3;
        }

        // Look for ALL division patterns on this line: (/ a b) where b is a variable
        let mut search_start = 0;
        while let Some(div_offset) = trimmed[search_start..].find("(/ ") {
            let div_start = search_start + div_offset;
            let after_div = &trimmed[div_start + 3..];
            if check_division_by_var(after_div, vars) {
                return true;
            }
            search_start = div_start + 3;
        }
    }

    false
}

/// Check if a multiplication has two non-constant operands (non-linear).
///
/// Heuristic: if at least two operands are known variables of the same type
/// (not numeric literals), then the multiplication is non-linear.
///
/// Only counts variables explicitly in the provided `vars` set to avoid misclassifying
/// NRA (Real) as NIA (Int) when both type sets contain different variables.
pub(super) fn check_nonlinear_args(args_str: &str, vars: &HashSet<&str>) -> bool {
    let operands = split_top_level_operands(args_str);

    let mut var_operand_count = 0;
    for operand in &operands {
        if operand_has_var(operand, vars) {
            var_operand_count += 1;
            if var_operand_count >= 2 {
                return true;
            }
        }
    }

    // Non-linear if at least two operand expressions contain variables
    false
}

/// Check if a division has a known variable anywhere in the divisor expression.
///
/// Only detects division by variables explicitly in the provided `vars` set
/// to avoid misclassifying NRA as NIA.
pub(super) fn check_division_by_var(args_str: &str, vars: &HashSet<&str>) -> bool {
    let operands = split_top_level_operands(args_str);
    if operands.len() < 2 {
        return false;
    }

    // Any divisor operand containing a variable makes this non-linear.
    for operand in operands.iter().skip(1) {
        if operand_has_var(operand, vars) {
            return true;
        }
    }

    false
}

/// Split the arguments of an S-expression into top-level operand slices.
///
/// The input is expected to begin after the operator token, e.g. for `(* x y)`
/// this function receives `"x y)"`. Parsing stops at the first unmatched `)`,
/// so trailing expressions on the same line are ignored.
///
/// Returns borrowed slices into `args_str` to avoid allocations.
fn split_top_level_operands(args_str: &str) -> Vec<&str> {
    let mut operands = Vec::new();
    let mut depth: i32 = 0;
    let mut token_start: Option<usize> = None;

    for (i, ch) in args_str.char_indices() {
        match ch {
            '(' => {
                if depth == 0 && token_start.is_none() {
                    token_start = Some(i);
                }
                depth += 1;
            }
            ')' => {
                if depth == 0 {
                    // Unmatched ')' — flush any pending token and stop
                    if let Some(start) = token_start {
                        let slice = args_str[start..i].trim();
                        if !slice.is_empty() {
                            operands.push(slice);
                        }
                    }
                    break;
                }
                depth -= 1;
                if depth == 0 {
                    // End of a parenthesized sub-expression
                    if let Some(start) = token_start {
                        let slice = args_str[start..=i].trim();
                        if !slice.is_empty() {
                            operands.push(slice);
                        }
                        token_start = None;
                    }
                }
            }
            c if c.is_whitespace() && depth == 0 => {
                if let Some(start) = token_start {
                    let slice = args_str[start..i].trim();
                    if !slice.is_empty() {
                        operands.push(slice);
                    }
                    token_start = None;
                }
            }
            _ => {
                if token_start.is_none() {
                    token_start = Some(i);
                }
            }
        }
    }

    // Flush any remaining token (no closing ')' found)
    if let Some(start) = token_start {
        let slice = args_str[start..].trim();
        if !slice.is_empty() {
            operands.push(slice);
        }
    }

    operands
}

/// Check if an operand expression contains a known variable.
fn operand_has_var(operand: &str, vars: &HashSet<&str>) -> bool {
    operand
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .filter(|s| !s.is_empty())
        .any(|token| !is_numeric_literal(token) && vars.contains(token))
}

/// Check if a string looks like a numeric literal.
///
/// Recognizes:
/// - Decimal integers: `123`, `-42`
/// - Decimal reals: `3.14`, `-1.5`
/// - SMT-LIB2 hex: `#x1A`, `#xFF`
/// - SMT-LIB2 binary: `#b1010`, `#b0001`
pub(super) fn is_numeric_literal(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }

    // SMT-LIB2 hexadecimal: #xNN...
    if let Some(hex_part) = s.strip_prefix("#x") {
        return !hex_part.is_empty() && hex_part.chars().all(|c| c.is_ascii_hexdigit());
    }

    // SMT-LIB2 binary: #bNN...
    if let Some(bin_part) = s.strip_prefix("#b") {
        return !bin_part.is_empty() && bin_part.chars().all(|c| c == '0' || c == '1');
    }

    let s = s.trim_start_matches('-');
    if s.is_empty() {
        return false;
    }

    // Integer literal
    if s.chars().all(|c| c.is_ascii_digit()) {
        return true;
    }

    // Decimal literal
    if s.contains('.') {
        let parts: Vec<&str> = s.split('.').collect();
        if parts.len() == 2 {
            return parts[0].chars().all(|c| c.is_ascii_digit())
                && parts[1].chars().all(|c| c.is_ascii_digit());
        }
    }

    false
}
