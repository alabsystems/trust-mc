// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Loop invariant hint conversion for CHC verification.
//!
//! Converts `LoopInvariantHint` from trust_mc_core into `LemmaHint` for ay-chc's
//! PDR engines. Handles variable renaming from captured_N placeholders to
//! canonical predicate argument names.

use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

use anyhow::Result;
use ay::chc::{ChcExpr, ChcParser, ClauseHead, LemmaHint, Predicate, canonical_var_name};
use regex::Regex;

fn captured_var_regex() -> &'static Regex {
    static CAPTURED_VAR_RE: OnceLock<Regex> = OnceLock::new();
    CAPTURED_VAR_RE.get_or_init(|| Regex::new(r"\bcaptured_(\d+)\b").expect("valid regex"))
}

fn bitvec_sort_regex() -> &'static Regex {
    static BITVEC_SORT_RE: OnceLock<Regex> = OnceLock::new();
    BITVEC_SORT_RE.get_or_init(|| Regex::new(r"\(\s*_\s+BitVec\s+(\d+)\s*\)").expect("valid regex"))
}

/// Minimal s-expression node for the Int→BV hint coercion.
enum SexprNode {
    Atom(String),
    List(Vec<SexprNode>),
}

fn parse_sexpr(input: &str) -> Option<SexprNode> {
    let mut tokens = Vec::new();
    let mut cur = String::new();
    for ch in input.chars() {
        match ch {
            '(' | ')' => {
                if !cur.is_empty() {
                    tokens.push(std::mem::take(&mut cur));
                }
                tokens.push(ch.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    tokens.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        tokens.push(cur);
    }

    fn parse_tokens(tokens: &[String], pos: &mut usize) -> Option<SexprNode> {
        let token = tokens.get(*pos)?;
        *pos += 1;
        if token == "(" {
            let mut items = Vec::new();
            while tokens.get(*pos).is_some_and(|t| t != ")") {
                items.push(parse_tokens(tokens, pos)?);
            }
            if tokens.get(*pos)? != ")" {
                return None;
            }
            *pos += 1;
            Some(SexprNode::List(items))
        } else if token == ")" {
            None
        } else {
            Some(SexprNode::Atom(token.clone()))
        }
    }

    let mut pos = 0;
    let node = parse_tokens(&tokens, &mut pos)?;
    (pos == tokens.len()).then_some(node)
}

/// Rewrite an Int-syntax hint term to unsigned-BV syntax.
///
/// Returns the rewritten text plus the term's inferred bit-width (`None` for
/// Boolean terms and literals whose width comes from a sibling). Fails (None
/// overall) on any construct it cannot faithfully coerce — the caller then
/// keeps the original parse error and the hint is skipped, never mangled.
fn rewrite_bv_node(
    node: &SexprNode,
    widths: &HashMap<String, u32>,
) -> Option<(String, Option<u32>)> {
    match node {
        SexprNode::Atom(atom) => {
            if let Some(&w) = widths.get(atom) {
                return Some((atom.clone(), Some(w)));
            }
            if atom.chars().all(|c| c.is_ascii_digit()) {
                // Bare literal: width resolved by the enclosing operator.
                return Some((atom.clone(), None));
            }
            // Unknown non-literal atom (e.g. `true`, or a var the predicate
            // does not type as BV): pass through with no width claim.
            Some((atom.clone(), None))
        }
        SexprNode::List(items) => {
            let [SexprNode::Atom(op), rest @ ..] = items.as_slice() else {
                return None;
            };
            let bool_op = |mapped: &str| -> Option<(String, Option<u32>)> {
                let parts: Vec<String> = rest
                    .iter()
                    .map(|c| rewrite_bv_node(c, widths).map(|(t, _)| t))
                    .collect::<Option<_>>()?;
                Some((format!("({} {})", mapped, parts.join(" ")), None))
            };
            let width_op = |mapped: &str, yields_width: bool| -> Option<(String, Option<u32>)> {
                let children: Vec<(String, Option<u32>)> =
                    rest.iter().map(|c| rewrite_bv_node(c, widths)).collect::<Option<_>>()?;
                // Operand width: agreed non-literal width among children.
                let mut width: Option<u32> = None;
                for (_, w) in &children {
                    match (width, w) {
                        (None, Some(w)) => width = Some(*w),
                        (Some(prev), Some(w)) if prev != *w => return None,
                        _ => {}
                    }
                }
                let w = width?;
                let parts: Vec<String> = children
                    .into_iter()
                    .map(|(text, cw)| {
                        if cw.is_none() && text.chars().all(|c| c.is_ascii_digit()) {
                            format!("(_ bv{text} {w})")
                        } else {
                            text
                        }
                    })
                    .collect();
                Some((format!("({} {})", mapped, parts.join(" ")), yields_width.then_some(w)))
            };
            match op.as_str() {
                // Loop-contract measures/invariants are unsigned (the
                // decreases transform guards on Uint); use unsigned compares.
                ">=" => width_op("bvuge", false),
                ">" => width_op("bvugt", false),
                "<=" => width_op("bvule", false),
                "<" => width_op("bvult", false),
                "=" => width_op("=", false),
                "distinct" => width_op("distinct", false),
                "+" => width_op("bvadd", true),
                "-" => width_op("bvsub", true),
                "*" => width_op("bvmul", true),
                "not" | "and" | "or" | "xor" | "=>" => bool_op(op),
                _ => None,
            }
        }
    }
}

/// Coerce an Int-syntax hint formula onto BitVec-sorted predicate arguments.
///
/// The compiler-side extractor (`smt2.rs`) emits Int syntax (`(>= captured_0
/// 2)`) regardless of capture sorts. For BV-sorted relation args that script
/// fails to parse; this rewrites comparisons/arithmetic to unsigned BV ops and
/// decimal literals to sized `(_ bvK W)` constants. Part of #40.
fn bv_coerce_formula(predicate: &Predicate, formula: &str) -> Option<String> {
    let bv_re = bitvec_sort_regex();
    let mut widths: HashMap<String, u32> = HashMap::new();
    for (idx, sort) in predicate.arg_sorts.iter().enumerate() {
        if let Some(caps) = bv_re.captures(&sort.to_string()) {
            if let Ok(w) = caps[1].parse::<u32>() {
                widths.insert(canonical_var_name(predicate.id, idx), w);
            }
        }
    }
    if widths.is_empty() {
        return None;
    }
    let node = parse_sexpr(formula)?;
    let (rewritten, _) = rewrite_bv_node(&node, &widths)?;
    Some(rewritten)
}

pub(crate) fn parse_loop_hint_formula(predicate: &Predicate, formula: &str) -> Result<ChcExpr> {
    let relation_name = "trust_mc_loop_hint_rel";
    let canonical_vars: Vec<String> = predicate
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(idx, _)| canonical_var_name(predicate.id, idx))
        .collect();
    let relation_sorts =
        predicate.arg_sorts.iter().map(ToString::to_string).collect::<Vec<_>>().join(" ");
    let var_decls = canonical_vars
        .iter()
        .zip(predicate.arg_sorts.iter())
        .map(|(name, sort)| format!("(declare-var {name} {sort})"))
        .collect::<Vec<_>>()
        .join("\n");
    let head_app = if canonical_vars.is_empty() {
        relation_name.to_string()
    } else {
        format!("({relation_name} {})", canonical_vars.join(" "))
    };
    let script = format!(
        "(set-logic HORN)\n\
         (declare-rel {relation_name} ({relation_sorts}))\n\
         {var_decls}\n\
         (rule (=> {formula} {head_app}))\n\
         (query {relation_name})\n"
    );

    let parsed = ChcParser::parse(&script).map_err(|e| {
        anyhow::anyhow!("failed to parse loop hint formula `{formula}` ({e}); script: {script}")
    })?;
    let clause = parsed
        .clauses()
        .iter()
        .find(|clause| matches!(&clause.head, ClauseHead::Predicate(_, _)))
        .ok_or_else(|| anyhow::anyhow!("internal error: missing synthetic hint clause"))?;
    Ok(clause.body.constraint.clone().unwrap_or_else(|| ChcExpr::bool_const(true)))
}

pub(crate) fn convert_loop_hints_to_lemma_hints(
    problem: &ay::chc::ChcProblem,
    loop_hints: &[trust_mc_core::LoopInvariantHint],
    verbose: bool,
) -> Vec<LemmaHint> {
    let mut converted = Vec::new();
    let captured_re = captured_var_regex();
    let mut predicates_by_name = HashMap::new();
    for predicate in problem.predicates() {
        predicates_by_name.entry(predicate.name.as_str()).or_insert(predicate);
    }
    let mut seen_rewritten_hints = HashSet::new();

    for hint in loop_hints {
        let Some(predicate) = predicates_by_name.get(hint.relation_name.as_str()).copied() else {
            if verbose {
                tracing::warn!(
                    "[AY-chc] skipping loop hint for unknown relation `{}`",
                    hint.relation_name
                );
            }
            continue;
        };

        let Some(formula) = hint.formula_smt2.as_deref() else {
            if verbose {
                tracing::warn!(
                    "[AY-chc] skipping loop hint for relation `{}`: no formula extracted (formula_smt2 is None)",
                    hint.relation_name
                );
            }
            continue;
        };
        let rewritten = captured_re
            .replace_all(formula, |caps: &regex::Captures<'_>| {
                let captured_idx = caps[1].parse::<usize>().ok();
                let state_idx = captured_idx.and_then(|idx| {
                    hint.captured_state_indices
                        .as_ref()
                        .and_then(|indices| indices.get(idx).copied())
                        .or_else(|| (idx < predicate.arg_sorts.len()).then_some(idx))
                });
                state_idx
                    .map(|idx| canonical_var_name(predicate.id, idx))
                    .unwrap_or_else(|| caps[0].to_string())
            })
            .into_owned();

        if !seen_rewritten_hints.insert((predicate.id, rewritten.clone())) {
            continue;
        }

        let unresolved_capture_vars = captured_re.is_match(&rewritten);
        let parsed_formula = if unresolved_capture_vars {
            Err(anyhow::anyhow!("unresolved captured_N placeholders remained after rewrite"))
        } else {
            // Part of #40: the compiler emits Int-syntax formulas (`(>=
            // captured_0 2)`) regardless of capture sorts. When the hint
            // references BitVec-sorted predicate args, coerce to unsigned-BV
            // syntax first; a hint left in Int syntax either fails to parse
            // or parses ill-sorted. Falls back to the raw formula when no BV
            // arg is referenced or the shape is unsupported.
            let effective =
                bv_coerce_formula(predicate, &rewritten).unwrap_or_else(|| rewritten.clone());
            parse_loop_hint_formula(predicate, &effective)
        };

        let formula_expr = match parsed_formula {
            Ok(expr) => expr,
            Err(err) => {
                tracing::warn!(
                    "[AY-chc] skipping loop hint for relation `{}`: formula parse failed: {}",
                    hint.relation_name,
                    err
                );
                continue;
            }
        };

        converted.push(LemmaHint::new(
            predicate.id,
            formula_expr,
            hint.priority,
            "trust_mc-loop-hint",
        ));
    }

    converted
}

#[cfg(test)]
mod tests {
    use super::{convert_loop_hints_to_lemma_hints, parse_loop_hint_formula};
    use ay::chc::{ChcExpr, ChcOp, ChcParser, EngineConfig, PortfolioConfig};

    #[test]
    fn convert_loop_hints_maps_captured_vars_to_canonical_names() {
        let problem = ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel harness__bb3 (Int Int))
            (declare-var x Int)
            (declare-var y Int)
            (rule (=> true (harness__bb3 x y)))
            (query harness__bb3)
            "#,
        )
        .expect("valid synthetic CHC");

        let hints = vec![
            trust_mc_core::LoopInvariantHint::new("harness__bb3", 3)
                .with_captured_vars(vec![42])
                .with_captured_state_indices(vec![1])
                .with_priority(17)
                .with_formula_smt2("(>= captured_0 0)"),
        ];

        let converted = convert_loop_hints_to_lemma_hints(&problem, &hints, false);
        assert_eq!(converted.len(), 1, "expected one converted loop hint");
        assert_eq!(converted[0].priority, 17);
        assert_eq!(converted[0].source, "trust_mc-loop-hint");

        match &converted[0].formula {
            ChcExpr::Op(ChcOp::Ge, args) => {
                assert_eq!(args.len(), 2);
                match args[0].as_ref() {
                    ChcExpr::Var(var) => {
                        assert_eq!(var.name, "__p0_a1");
                    }
                    other => panic!("expected lhs var in >= formula, got {other:?}"),
                }
            }
            other => panic!("expected >= formula for converted hint, got {other:?}"),
        }
    }

    #[test]
    fn convert_loop_hints_skips_hints_without_formula() {
        let problem = ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel harness__bb3 (Int Int))
            (declare-var x Int)
            (declare-var y Int)
            (rule (=> true (harness__bb3 x y)))
            (query harness__bb3)
            "#,
        )
        .expect("valid synthetic CHC");

        let hints = vec![
            trust_mc_core::LoopInvariantHint::new("harness__bb3", 3)
                .with_captured_vars(vec![42])
                .with_captured_state_indices(vec![1])
                .with_priority(17),
        ];

        let converted = convert_loop_hints_to_lemma_hints(&problem, &hints, true);
        assert_eq!(
            converted.len(),
            0,
            "hints without formula_smt2 should be skipped, not converted to true"
        );
    }

    #[test]
    fn convert_loop_hints_deduplicates_rewritten_formulas() {
        let problem = ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel harness__bb3 (Int Int))
            (declare-var x Int)
            (declare-var y Int)
            (rule (=> true (harness__bb3 x y)))
            (query harness__bb3)
            "#,
        )
        .expect("valid synthetic CHC");

        let hints = vec![
            trust_mc_core::LoopInvariantHint::new("harness__bb3", 3)
                .with_captured_vars(vec![10])
                .with_captured_state_indices(vec![1])
                .with_priority(11)
                .with_formula_smt2("(>= captured_0 0)"),
            trust_mc_core::LoopInvariantHint::new("harness__bb3", 3)
                .with_captured_vars(vec![20, 10])
                .with_captured_state_indices(vec![0, 1])
                .with_priority(99)
                .with_formula_smt2("(>= captured_1 0)"),
        ];

        let converted = convert_loop_hints_to_lemma_hints(&problem, &hints, false);
        assert_eq!(
            converted.len(),
            1,
            "equivalent rewritten loop hints should be parsed and injected once"
        );
        assert_eq!(converted[0].priority, 11, "first duplicate hint should be preserved");
    }

    #[test]
    fn convert_loop_hints_coerces_int_formula_onto_bitvec_args() {
        // Part of #40: the compiler-side extractor emits Int syntax; for
        // BitVec-sorted predicate args the hint must be coerced to unsigned
        // BV ops with sized literals, not silently skipped.
        let problem = ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel harness__bb2 ((_ BitVec 8) (_ BitVec 8)))
            (declare-var x (_ BitVec 8))
            (declare-var y (_ BitVec 8))
            (rule (=> true (harness__bb2 x y)))
            (query harness__bb2)
            "#,
        )
        .expect("valid synthetic CHC");

        let hints = vec![
            trust_mc_core::LoopInvariantHint::new("harness__bb2", 2)
                .with_captured_vars(vec![7])
                .with_captured_state_indices(vec![1])
                .with_formula_smt2("(>= captured_0 2)"),
        ];
        let converted = convert_loop_hints_to_lemma_hints(&problem, &hints, true);
        assert_eq!(converted.len(), 1, "BV-sorted hint must convert via the coercion fallback");
        let formula_dbg = format!("{:?}", converted[0].formula).to_lowercase();
        assert!(
            formula_dbg.contains("uge"),
            "expected unsigned BV comparison in coerced hint, got {formula_dbg}"
        );
    }

    #[test]
    fn bv_coerce_formula_sizes_literals_and_maps_ops() {
        let problem = ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel r ((_ BitVec 8)))
            (declare-var x (_ BitVec 8))
            (rule (=> true (r x)))
            (query r)
            "#,
        )
        .expect("valid synthetic CHC");
        let predicate =
            problem.predicates().iter().find(|p| p.name == "r").expect("predicate exists");
        let var = super::canonical_var_name(predicate.id, 0);

        let coerced = super::bv_coerce_formula(predicate, &format!("(>= {var} 2)"))
            .expect("coercion should succeed");
        assert_eq!(coerced, format!("(bvuge {var} (_ bv2 8))"));

        // Unsupported shape (unknown op) must fail closed, not mangle.
        assert!(super::bv_coerce_formula(predicate, &format!("(bvweird {var} 2)")).is_none());
    }

    #[test]
    fn parse_loop_hint_formula_parses_comparison_constraints() {
        let problem = ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel harness__bb3 (Int Int))
            (declare-var x Int)
            (declare-var y Int)
            (rule (=> true (harness__bb3 x y)))
            (query harness__bb3)
            "#,
        )
        .expect("valid synthetic CHC");
        let predicate = problem
            .predicates()
            .iter()
            .find(|pred| pred.name == "harness__bb3")
            .expect("predicate exists");

        let parsed =
            parse_loop_hint_formula(predicate, "(>= __p0_a1 0)").expect("formula should parse");
        match &parsed {
            ChcExpr::Op(ChcOp::Ge, args) => {
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected >= expression, got {other:?}"),
        }
    }

    #[test]
    fn convert_loop_hints_are_applied_to_all_pdr_engines() {
        let problem = ChcParser::parse(
            r#"
            (set-logic HORN)
            (declare-rel harness__bb1 (Int))
            (declare-var x Int)
            (rule (=> true (harness__bb1 x)))
            (query harness__bb1)
            "#,
        )
        .expect("valid synthetic CHC");

        let hints = vec![
            trust_mc_core::LoopInvariantHint::new("harness__bb1", 1)
                .with_captured_vars(vec![0])
                .with_formula_smt2("(>= captured_0 0)"),
        ];
        let lemma_hints = convert_loop_hints_to_lemma_hints(&problem, &hints, false);
        assert_eq!(lemma_hints.len(), 1, "expected one converted hint");

        let mut config = PortfolioConfig::default();
        config.set_pdr_user_hints(lemma_hints);

        let pdr_hint_counts: Vec<usize> = config
            .engines()
            .iter()
            .filter_map(|engine| match engine {
                EngineConfig::Pdr(pdr) => Some(pdr.user_hints.len()),
                _ => None,
            })
            .collect();
        assert!(!pdr_hint_counts.is_empty(), "default portfolio should include PDR engines");
        assert!(
            pdr_hint_counts.iter().all(|count| *count == 1),
            "all PDR engines must receive exactly one user hint, got {pdr_hint_counts:?}"
        );
    }
}
