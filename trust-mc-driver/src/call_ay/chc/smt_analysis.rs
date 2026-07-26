// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SMT text analysis helpers for CHC solver integration.
//!
//! Pure functions that inspect SMT-LIB2 content for structural patterns.
//! No solver invocation or I/O — only string analysis.

/// #4058: detect recursive unwind assertion evidence in SMT content.
///
/// Prefer the explicit compiler marker when present, but also recognize the
/// fail-closed inline fallback symbol so the driver can honor recursive unwind
/// failures even before the marker plumbing is committed.
pub(crate) fn smt_has_recursive_unwind_assertion(smt_content: &str) -> bool {
    smt_content.contains("; RECURSIVE_UNWIND_ASSERTION:")
        || smt_content.contains("__assert_fail_inline_recursive_unwind")
}

/// Detect CHC systems where `error` is queried but no rule can derive it.
///
/// A rule with an explicitly false body, such as `(rule (=> false error))`,
/// is not an error derivation. Treating it as one forces the native CHC solver
/// to classify a trivially unreachable query, which can degrade to UNKNOWN on
/// degenerate HORN inputs.
pub(crate) fn smt_error_query_is_trivially_safe(smt_content: &str) -> bool {
    smt_content.contains("(query error)")
        && !smt_rule_blocks(smt_content).iter().any(|rule| smt_rule_may_derive_error(rule))
}

/// Detect a queried `error` relation whose only derivations are explicit
/// false-bodied obligations, for example `(rule (=> false error))`.
///
/// This shape is produced by compiler-side straight-line discharge. Unlike a
/// missing error rule, it preserves an error-headed proof obligation and can be
/// reported as a clean proof when the trivial-safety check short-circuits it.
pub(crate) fn smt_error_query_has_false_error_obligation(smt_content: &str) -> bool {
    smt_content.contains("(query error)")
        && smt_rule_blocks(smt_content).iter().any(|rule| smt_rule_has_false_error_head(rule))
}

fn smt_rule_blocks(smt_content: &str) -> Vec<String> {
    let smt_content = smt_syntax_projection(smt_content);
    let mut blocks = Vec::new();
    let mut search_start = 0usize;

    while let Some(relative_start) = smt_content[search_start..].find("(rule") {
        let start = search_start + relative_start;
        let mut depth = 0i32;
        let mut end = None;

        for (offset, ch) in smt_content[start..].char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(start + offset + ch.len_utf8());
                        break;
                    }
                }
                _ => {}
            }
        }

        if let Some(end) = end {
            blocks.push(smt_content[start..end].to_string());
            search_start = end;
        } else {
            blocks.push(smt_content[start..].to_string());
            break;
        }
    }

    blocks
}

fn smt_syntax_projection(smt_content: &str) -> String {
    let mut projected = String::with_capacity(smt_content.len());
    let mut chars = smt_content.chars().peekable();
    let mut in_comment = false;
    let mut in_string = false;
    let mut in_quoted_symbol = false;

    while let Some(ch) = chars.next() {
        if in_comment {
            if ch == '\n' {
                projected.push('\n');
                in_comment = false;
            } else {
                projected.push(' ');
            }
            continue;
        }

        if in_string {
            projected.push(' ');
            if ch == '"' {
                if chars.peek() == Some(&'"') {
                    projected.push(' ');
                    chars.next();
                } else {
                    in_string = false;
                }
            }
            continue;
        }

        if in_quoted_symbol {
            projected.push(' ');
            if ch == '|' {
                in_quoted_symbol = false;
            }
            continue;
        }

        match ch {
            ';' => {
                projected.push(' ');
                in_comment = true;
            }
            '"' => {
                projected.push(' ');
                in_string = true;
            }
            '|' => {
                projected.push(' ');
                in_quoted_symbol = true;
            }
            _ => projected.push(ch),
        }
    }

    projected
}

fn smt_rule_may_derive_error(rule: &str) -> bool {
    let Some(sexp) = parse_smt_sexp(rule) else {
        return rule.split_whitespace().any(|token| token == "error" || token == "(error)");
    };
    let SmtSexp::List(items) = sexp else {
        return false;
    };
    if !matches!(items.first(), Some(SmtSexp::Atom(atom)) if atom == "rule") {
        return false;
    }
    let Some(payload) = items.get(1) else {
        return false;
    };
    smt_formula_may_derive_error(unwrap_smt_attributes(payload))
}

fn smt_rule_has_false_error_head(rule: &str) -> bool {
    let Some(sexp) = parse_smt_sexp(rule) else {
        return false;
    };
    let SmtSexp::List(items) = sexp else {
        return false;
    };
    if !matches!(items.first(), Some(SmtSexp::Atom(atom)) if atom == "rule") {
        return false;
    }
    let Some(payload) = items.get(1) else {
        return false;
    };
    smt_formula_has_false_error_head(unwrap_smt_attributes(payload))
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SmtSexp {
    Atom(String),
    List(Vec<SmtSexp>),
}

fn parse_smt_sexp(input: &str) -> Option<SmtSexp> {
    let tokens = smt_tokens(input);
    let mut pos = 0usize;
    let sexp = parse_smt_sexp_tokens(&tokens, &mut pos)?;
    (pos == tokens.len()).then_some(sexp)
}

fn smt_tokens(input: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    for ch in input.chars() {
        match ch {
            '(' | ')' => {
                if !current.is_empty() {
                    tokens.push(std::mem::take(&mut current));
                }
                tokens.push(ch.to_string());
            }
            ch if ch.is_whitespace() => {
                if !current.is_empty() {
                    tokens.push(std::mem::take(&mut current));
                }
            }
            _ => current.push(ch),
        }
    }
    if !current.is_empty() {
        tokens.push(current);
    }
    tokens
}

fn parse_smt_sexp_tokens(tokens: &[String], pos: &mut usize) -> Option<SmtSexp> {
    let token = tokens.get(*pos)?;
    if token == "(" {
        *pos += 1;
        let mut items = Vec::new();
        while tokens.get(*pos).is_some_and(|token| token != ")") {
            items.push(parse_smt_sexp_tokens(tokens, pos)?);
        }
        if tokens.get(*pos)? != ")" {
            return None;
        }
        *pos += 1;
        Some(SmtSexp::List(items))
    } else if token == ")" {
        None
    } else {
        *pos += 1;
        Some(SmtSexp::Atom(token.clone()))
    }
}

fn unwrap_smt_attributes(mut expr: &SmtSexp) -> &SmtSexp {
    while let SmtSexp::List(items) = expr {
        if matches!(items.first(), Some(SmtSexp::Atom(atom)) if atom == "!")
            && let Some(payload) = items.get(1)
        {
            expr = payload;
        } else {
            break;
        }
    }
    expr
}

fn smt_formula_may_derive_error(formula: &SmtSexp) -> bool {
    let formula = unwrap_smt_attributes(formula);
    if smt_head_is_error(formula) {
        return true;
    }
    let SmtSexp::List(items) = formula else {
        return false;
    };
    if !matches!(items.first(), Some(SmtSexp::Atom(atom)) if atom == "=>") {
        return false;
    }
    let Some(head) = items.last() else {
        return false;
    };
    smt_head_is_error(unwrap_smt_attributes(head))
        && items.get(1).is_none_or(|body| !smt_body_is_false(body))
}

fn smt_formula_has_false_error_head(formula: &SmtSexp) -> bool {
    let formula = unwrap_smt_attributes(formula);
    let SmtSexp::List(items) = formula else {
        return false;
    };
    if !matches!(items.first(), Some(SmtSexp::Atom(atom)) if atom == "=>") {
        return false;
    }
    let Some(head) = items.last() else {
        return false;
    };
    smt_head_is_error(unwrap_smt_attributes(head)) && items.get(1).is_some_and(smt_body_is_false)
}

fn smt_head_is_error(expr: &SmtSexp) -> bool {
    match unwrap_smt_attributes(expr) {
        SmtSexp::Atom(atom) => atom == "error",
        SmtSexp::List(items) => {
            items.len() == 1
                && matches!(items.first(), Some(SmtSexp::Atom(atom)) if atom == "error")
        }
    }
}

fn smt_body_is_false(expr: &SmtSexp) -> bool {
    match unwrap_smt_attributes(expr) {
        SmtSexp::Atom(atom) => atom == "false",
        SmtSexp::List(items) => match items.first() {
            Some(SmtSexp::Atom(atom)) if atom == "and" => {
                items.iter().skip(1).any(smt_body_is_false)
            }
            Some(SmtSexp::Atom(atom)) if atom == "or" => {
                !items.is_empty() && items.iter().skip(1).all(smt_body_is_false)
            }
            Some(SmtSexp::Atom(atom)) if atom == "not" => {
                matches!(items.get(1), Some(SmtSexp::Atom(inner)) if inner == "true")
            }
            _ => false,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::{smt_error_query_has_false_error_obligation, smt_error_query_is_trivially_safe};

    #[test]
    fn detects_no_error_rule_as_trivially_safe() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
(query error)
";

        assert!(smt_error_query_is_trivially_safe(smt));
    }

    #[test]
    fn ignores_false_error_rule_for_trivial_safety() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
(rule (=> false error))
(query error)
";

        assert!(smt_error_query_is_trivially_safe(smt));
        assert!(smt_error_query_has_false_error_obligation(smt));
    }

    #[test]
    fn ignores_multiline_false_error_rule_for_trivial_safety() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
(rule
  (=>
    false
    (error)))
(query error)
";

        assert!(smt_error_query_is_trivially_safe(smt));
        assert!(smt_error_query_has_false_error_obligation(smt));
    }

    #[test]
    fn keeps_true_error_derivation_non_trivial() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
(rule (=> true error))
(query error)
";

        assert!(!smt_error_query_is_trivially_safe(smt));
        assert!(!smt_error_query_has_false_error_obligation(smt));
    }

    #[test]
    fn keeps_mixed_false_and_true_error_derivation_non_trivial() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
(rule (=> false error))
(rule (=> true error))
(query error)
";

        assert!(!smt_error_query_is_trivially_safe(smt));
        assert!(smt_error_query_has_false_error_obligation(smt));
    }

    #[test]
    fn ignores_rule_like_text_and_parentheses_in_comments() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
; (rule (=> true error)) )
(rule (=> false error))
(query error)
";

        assert!(smt_error_query_is_trivially_safe(smt));
    }

    #[test]
    fn keeps_attributed_true_error_derivation_non_trivial() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
(rule (! (=> true error) :named |rule with ) in quoted symbol|))
(query error)
";

        assert!(!smt_error_query_is_trivially_safe(smt));
    }

    #[test]
    fn keeps_attributed_guarded_error_derivation_non_trivial() {
        let smt = "\
(set-logic HORN)
(declare-rel bb0 ())
(declare-rel error ())
(rule bb0)
(rule (! (=> bb0 error) :named guarded_error))
(query error)
";

        assert!(!smt_error_query_is_trivially_safe(smt));
    }

    #[test]
    fn ignores_attributed_false_error_derivation_for_trivial_safety() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
(rule (! (=> false error) :named unreachable_error))
(query error)
";

        assert!(smt_error_query_is_trivially_safe(smt));
        assert!(smt_error_query_has_false_error_obligation(smt));
    }

    #[test]
    fn no_error_rule_is_not_false_error_obligation() {
        let smt = "\
(set-logic HORN)
(declare-rel error ())
(query error)
";

        assert!(smt_error_query_is_trivially_safe(smt));
        assert!(!smt_error_query_has_false_error_obligation(smt));
    }
}
