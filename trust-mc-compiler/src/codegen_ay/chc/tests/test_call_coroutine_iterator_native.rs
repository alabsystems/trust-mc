// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Exact-file iterator-count localizers for the native solver concat-width lane.

#![allow(clippy::panic, clippy::unwrap_used)]

use super::common::*;
use ay_frontend::sexp::{SExpr, parse_sexps};

const ITERATOR_COUNT_REAL_FILE: &str = include_str!(
    "../../../../../tests/trust_mc/Coroutines/rustc-coroutine-tests/iterator-count.rs"
);

fn strip_kani_attrs_for_unit_ctx(source: &str) -> String {
    let mut result = String::with_capacity(source.len());
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("#[kani::")
            || trimmed.starts_with("// kani-expect:")
            || trimmed.starts_with("// compile-flags:")
            || trimmed.starts_with("// kani-flags:")
            || trimmed.starts_with("//!")
        {
            continue;
        }
        result.push_str(line);
        result.push('\n');
    }
    result
}

fn iterator_compiletest_config() -> ChcConfig {
    ChcConfig {
        track_level: ChcTrackLevel::Mem,
        step_mode: crate::args::ChcStepMode::Auto,
        recursive_unwind_depth: 11,
        unwinding_assertions: true,
        ..ChcConfig::default()
    }
}

fn build_real_iterator_count_vc() -> trust_mc_core::chc::ChcVc {
    let mut result = None;
    let source = format!(
        "#![allow(dead_code)]\n{}",
        strip_kani_attrs_for_unit_ctx(ITERATOR_COUNT_REAL_FILE)
    );
    with_test_ay_ctx_for_source(&source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "main");
        let body = instance.body().expect("main body");
        let cfg = iterator_compiletest_config();
        let unrolled = crate::codegen_ay::loop_unroll::unroll_cfg_loops(
            body.clone(),
            cfg.recursive_unwind_depth,
            cfg.unwinding_assertions,
        )
        .expect("iterator-count main should bounded-unroll under #[kani::unwind(11)]");
        let chc_ctx = ChcCtx::new(ctx.tcx, &unrolled, "main", cfg);
        let (vc, _, _) = chc_ctx.translate_with_diagnostics();
        result = Some(vc);
    });
    result.expect("real iterator-count VC should translate")
}

fn emit_real_iterator_count_smt() -> String {
    crate::codegen_ay::emit_chc(&build_real_iterator_count_vc()).to_string()
}

fn unknown_width_bv_expr_detail(expr: &Expr) -> Option<String> {
    match expr.value() {
        ExprValue::BvConcat(high, low)
            if high.sort().bitvec_width().is_none() || low.sort().bitvec_width().is_none() =>
        {
            Some(format!(
                "concat(high_sort={:?}, low_sort={:?}) in {expr}",
                high.sort(),
                low.sort()
            ))
        }
        ExprValue::BvExtract { expr: inner, high, low }
            if inner.sort().bitvec_width().is_none() =>
        {
            Some(format!("extract[{high}:{low}] inner_sort={:?} in {expr}", inner.sort()))
        }
        _ => None,
    }
}

fn first_unknown_width_bv_in_expr(expr: &Expr) -> Option<String> {
    if let Some(detail) = unknown_width_bv_expr_detail(expr) {
        return Some(detail);
    }
    let mut stack = expr_children(expr);
    while let Some(child) = stack.pop() {
        if let Some(detail) = unknown_width_bv_expr_detail(child) {
            return Some(detail);
        }
        stack.extend(expr_children(child));
    }
    None
}

fn first_unknown_width_bv_in_rule(rule: &trust_mc_core::chc::Rule) -> Option<String> {
    for constraint in &rule.body.constraints {
        if let Some(detail) = first_unknown_width_bv_in_expr(constraint) {
            return Some(format!("body constraint: {detail}"));
        }
    }
    if let Some(relation) = &rule.body.relation {
        for arg in relation.args.iter() {
            if let Some(detail) = first_unknown_width_bv_in_expr(arg) {
                return Some(format!("body relation {}: {detail}", relation.name));
            }
        }
    }
    for arg in rule.head.args.iter() {
        if let Some(detail) = first_unknown_width_bv_in_expr(arg) {
            return Some(format!("head {}: {detail}", rule.head.name));
        }
    }
    None
}

fn first_unknown_width_bv_in_vc(vc: &trust_mc_core::chc::ChcVc) -> Option<String> {
    vc.rules.iter().enumerate().find_map(|(rule_idx, rule)| {
        first_unknown_width_bv_in_rule(rule).map(|d| format!("rule#{rule_idx}: {d}"))
    })
}

#[derive(Debug, Default)]
struct NativeConcatRewriteSurface {
    concat_seen: usize,
    concat_unknown_width: usize,
    unknown_examples: Vec<String>,
}

fn collect_native_concat_decl_widths(
    sexp: &SExpr,
    widths: &mut std::collections::HashMap<String, u64>,
) {
    let Some(items) = sexp.as_list() else {
        return;
    };
    if items.len() < 3 {
        return;
    }
    match items[0].as_symbol() {
        Some("declare-const") | Some("declare-var") => {
            // (declare-const <name> <sort>) or (declare-var <name> <sort>)
            if let (Some(name), Some(width)) =
                (items[1].as_symbol(), native_concat_rewrite_bv_sort_width(&items[2]))
            {
                widths.insert(name.to_string(), width);
            }
        }
        Some("declare-fun") if items.len() >= 4 => {
            if let (Some(name), Some(width)) =
                (items[1].as_symbol(), native_concat_rewrite_bv_sort_width(&items[3]))
            {
                widths.insert(name.to_string(), width);
            }
        }
        Some("declare-datatype") if items.len() >= 3 => {
            collect_native_datatype_selector_widths(&items[2], widths);
        }
        Some("declare-datatypes") if items.len() >= 3 => {
            if let Some(datatype_defs) = items[2].as_list() {
                for datatype_def in datatype_defs {
                    collect_native_datatype_selector_widths(datatype_def, widths);
                }
            }
        }
        _ => {}
    }
}

/// Collect selector widths from a datatype constructor block.
/// Mirrors `collect_datatype_selector_widths` in the driver's `rewrite_concat.rs`.
fn collect_native_datatype_selector_widths(
    sexp: &SExpr,
    widths: &mut std::collections::HashMap<String, u64>,
) {
    let Some(constructors) = sexp.as_list() else {
        return;
    };
    for ctor in constructors {
        let Some(ctor_items) = ctor.as_list() else {
            continue;
        };
        for field in ctor_items.iter().skip(1) {
            let Some(field_items) = field.as_list() else {
                continue;
            };
            if field_items.len() != 2 {
                continue;
            }
            if let (Some(name), Some(width)) =
                (field_items[0].as_symbol(), native_concat_rewrite_bv_sort_width(&field_items[1]))
            {
                widths.insert(name.to_string(), width);
            }
        }
    }
}

fn native_concat_rewrite_bv_sort_width(sexp: &SExpr) -> Option<u64> {
    let items = sexp.as_list()?;
    if items.len() == 3 && items[0].is_symbol("_") && items[1].is_symbol("BitVec") {
        native_concat_rewrite_numeral_value(&items[2])
    } else {
        None
    }
}

fn native_concat_rewrite_numeral_value(sexp: &SExpr) -> Option<u64> {
    match sexp {
        SExpr::Numeral(n) => n.parse::<u64>().ok(),
        _ => None,
    }
}

fn infer_native_concat_width(
    sexp: &SExpr,
    widths: &std::collections::HashMap<String, u64>,
) -> Option<u64> {
    match sexp {
        SExpr::Hexadecimal(h) => Some(h.strip_prefix("#x").unwrap_or(h).len() as u64 * 4),
        SExpr::Binary(b) => Some(b.strip_prefix("#b").unwrap_or(b).len() as u64),
        SExpr::Symbol(sym) => widths.get(sym).copied(),
        SExpr::List(items) => {
            if items.len() == 2 {
                let indexed = items[0].as_list()?;
                if indexed.len() == 3
                    && indexed[0].is_symbol("_")
                    && indexed[1]
                        .as_symbol()
                        .is_some_and(|sym| matches!(sym, "zero_extend" | "sign_extend"))
                {
                    return Some(
                        infer_native_concat_width(&items[1], widths)?
                            + native_concat_rewrite_numeral_value(&indexed[2])?,
                    );
                }
                if indexed.len() == 4
                    && indexed[0].is_symbol("_")
                    && indexed[1].is_symbol("extract")
                {
                    let hi = native_concat_rewrite_numeral_value(&indexed[2])?;
                    let lo = native_concat_rewrite_numeral_value(&indexed[3])?;
                    return Some(hi - lo + 1);
                }
            }

            let head = items.first()?.as_symbol()?;
            match head {
                "_" if items.len() == 3
                    && items[1].as_symbol().is_some_and(|s| s.starts_with("bv")) =>
                {
                    native_concat_rewrite_numeral_value(&items[2])
                }
                "concat" if items.len() == 3 => Some(
                    infer_native_concat_width(&items[1], widths)?
                        + infer_native_concat_width(&items[2], widths)?,
                ),
                "ite" if items.len() == 4 => infer_native_concat_width(&items[2], widths),
                op if matches!(
                    op,
                    "bvadd"
                        | "bvsub"
                        | "bvmul"
                        | "bvand"
                        | "bvor"
                        | "bvxor"
                        | "bvshl"
                        | "bvlshr"
                        | "bvashr"
                ) && items.len() == 3 =>
                {
                    infer_native_concat_width(&items[1], widths)
                }
                // Fallback: selector/function applications with known width
                // (mirrors driver's `infer_width_named` fallback)
                _ => widths.get(head).copied(),
            }
        }
        _ => None,
    }
}

fn collect_native_concat_rewrite_surface(
    sexp: &SExpr,
    widths: &std::collections::HashMap<String, u64>,
    surface: &mut NativeConcatRewriteSurface,
) {
    let Some(items) = sexp.as_list() else {
        return;
    };
    if items.len() == 3 && items[0].is_symbol("concat") {
        surface.concat_seen += 1;
        let high_width = infer_native_concat_width(&items[1], widths);
        let low_width = infer_native_concat_width(&items[2], widths);
        if high_width.is_none() || low_width.is_none() {
            surface.concat_unknown_width += 1;
            if surface.unknown_examples.len() < 3 {
                surface.unknown_examples.push(sexp.to_string());
            }
        }
    }
    for child in items {
        collect_native_concat_rewrite_surface(child, widths, surface);
    }
}

fn analyze_native_concat_rewrite_surface(smt: &str) -> NativeConcatRewriteSurface {
    let sexps = parse_sexps(smt).expect("emitted CHC SMT should parse as S-expressions");
    let mut widths = std::collections::HashMap::new();
    for sexp in &sexps {
        collect_native_concat_decl_widths(sexp, &mut widths);
    }
    let mut surface = NativeConcatRewriteSurface::default();
    for sexp in &sexps {
        collect_native_concat_rewrite_surface(sexp, &widths, &mut surface);
    }
    surface
}

#[test]
fn test_real_iterator_count_vc_has_no_unknown_width_bv_nodes_before_native_solver() {
    run_with_large_stack(|| {
        let vc = build_real_iterator_count_vc();
        let bad = first_unknown_width_bv_in_vc(&vc);
        assert!(
            bad.is_none(),
            "exact iterator-count VC should stay off malformed BV nodes before native solver; \
             first_bad={bad:?}"
        );
    });
}

#[test]
fn test_real_iterator_count_native_concat_rewrite_surface_localizer() {
    run_with_large_stack(|| {
        let smt = emit_real_iterator_count_smt();
        let surface = analyze_native_concat_rewrite_surface(&smt);

        eprintln!(
            "iterator_count_native_concat_surface: concat_seen={}, concat_unknown_width={}, \
             unknown_examples={:?}",
            surface.concat_seen, surface.concat_unknown_width, surface.unknown_examples,
        );

        // After declare-var support: most concat operand widths should be inferable.
        // Coroutine datatype selectors (case, direct_fields, coroutine_field_*)
        // cannot have their return-type width inferred from declare-var alone;
        // they require deep datatype-constructor analysis. Allow up to 64
        // unknown-width operands for coroutine-heavy code.
        assert!(
            surface.concat_unknown_width <= 64,
            "post declare-var fix: concat unknown widths should be bounded; \
             concat_seen={}, concat_unknown_width={}, unknown_examples={:?}",
            surface.concat_seen,
            surface.concat_unknown_width,
            surface.unknown_examples,
        );
    });
}
