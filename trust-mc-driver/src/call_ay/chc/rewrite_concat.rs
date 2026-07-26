// Copyright 2026 Andrew Yates, Inc.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Optional concat-to-arithmetic compatibility rewriter for native ay-chc.
//!
//! The normal path leaves SMT-LIB unchanged. When the caller explicitly enables
//! the compatibility mode, this module rewrites `(concat a b)` into equivalent
//! bit-vector arithmetic:
//!
//! ```smt2
//! (concat a b) => (bvor (bvshl ((_ zero_extend wb) a) (_ bv{wb} {wa+wb}))
//!                       ((_ zero_extend wa) b))
//! ```
//!
//! where `wa` and `wb` are the inferred bit-widths of operands `a` and `b`.

use std::collections::HashMap;

use ay_frontend::sexp::{SExpr, parse_sexps};

#[derive(Debug, Default)]
pub(crate) struct SortEnv {
    bv_widths: HashMap<String, u64>,
    array_value_widths: HashMap<String, u64>,
}

impl SortEnv {
    #[cfg(test)]
    pub(crate) fn insert_bv_width(&mut self, name: impl Into<String>, width: u64) {
        self.bv_widths.insert(name.into(), width);
    }

    #[cfg(test)]
    pub(crate) fn insert_array_value_width(&mut self, name: impl Into<String>, width: u64) {
        self.array_value_widths.insert(name.into(), width);
    }

    fn record_symbol_sort(&mut self, name: &str, sort: &SExpr) {
        match parse_sort_info(sort) {
            Some(SortInfo::BitVec(width)) => {
                self.bv_widths.insert(name.to_string(), width);
            }
            Some(SortInfo::Array { value_width }) => {
                self.array_value_widths.insert(name.to_string(), value_width);
            }
            None => {}
        }
    }

    fn bv_width(&self, name: &str) -> Option<u64> {
        self.bv_widths.get(name).copied()
    }

    fn array_value_width(&self, name: &str) -> Option<u64> {
        self.array_value_widths.get(name).copied()
    }
}

#[derive(Debug, Clone, Copy)]
enum SortInfo {
    BitVec(u64),
    Array { value_width: u64 },
}

/// Result of a concat rewrite pass over an SMT-LIB stream.
#[derive(Debug)]
pub(crate) struct RewriteResult {
    /// Rewritten SMT-LIB text.
    pub output: String,
    /// Number of `concat` nodes encountered.
    pub seen: usize,
    /// Number of `concat` nodes successfully rewritten.
    pub rewritten: usize,
    /// Number of `concat` nodes skipped because width inference was incomplete.
    pub skipped: usize,
}

/// Rewrite `(concat ...)` nodes for the native ay-chc parser.
///
/// Parses the full S-expression stream, collects width declarations, then
/// rewrites concat nodes whose operand widths can be inferred. Nodes with
/// unknown widths are left unchanged and counted in `skipped`.
pub(crate) fn rewrite_concat_for_native_parser(input: &str) -> anyhow::Result<RewriteResult> {
    let sexps = parse_sexps(input)
        .map_err(|e| anyhow::anyhow!("concat-rewrite: failed to parse S-expression stream: {e}"))?;

    let mut widths = SortEnv::default();
    for sexp in &sexps {
        collect_declarations(sexp, &mut widths);
    }

    let mut stats = Stats::default();
    let rewritten: Vec<SExpr> =
        sexps.into_iter().map(|s| rewrite(s, &widths, &mut stats)).collect();

    use std::fmt::Write;
    let mut output = String::with_capacity(input.len());
    for (i, sexp) in rewritten.iter().enumerate() {
        if i > 0 {
            output.push('\n');
        }
        write!(output, "{sexp}").expect("write to String is infallible");
    }
    output.push('\n');

    Ok(RewriteResult {
        output,
        seen: stats.seen,
        rewritten: stats.rewritten,
        skipped: stats.skipped,
    })
}

#[derive(Default)]
struct Stats {
    seen: usize,
    rewritten: usize,
    skipped: usize,
}

/// Collect bit-vector width declarations from `declare-const`, `declare-var`,
/// and `declare-fun`.
///
/// Recognises:
/// - `(declare-const x (_ BitVec W))`
/// - `(declare-var x (_ BitVec W))`
/// - `(declare-fun f (...) (_ BitVec W))`
/// - `(declare-var mem (Array (_ BitVec I) (_ BitVec W)))`
/// - datatype selector declarations carrying bit-vector sorts
fn collect_declarations(sexp: &SExpr, widths: &mut SortEnv) {
    let items = match sexp.as_list() {
        Some(items) => items,
        None => return,
    };
    if items.len() < 3 {
        return;
    }

    let cmd = match items[0].as_symbol() {
        Some(s) => s,
        None => return,
    };

    match cmd {
        "declare-const" | "declare-var" => {
            if let Some(name) = items[1].as_symbol() {
                widths.record_symbol_sort(name, &items[2]);
            }
        }
        "declare-fun" => {
            if items.len() >= 4 {
                if let Some(name) = items[1].as_symbol() {
                    widths.record_symbol_sort(name, &items[3]);
                }
            }
        }
        "declare-datatype" if items.len() >= 3 => {
            collect_datatype_selector_widths(&items[2], widths);
        }
        "declare-datatypes" if items.len() >= 3 => {
            if let Some(datatype_defs) = items[2].as_list() {
                for datatype_def in datatype_defs {
                    collect_datatype_selector_widths(datatype_def, widths);
                }
            }
        }
        _ => {}
    }
}

fn bv_sort_width(sexp: &SExpr) -> Option<u64> {
    let items = sexp.as_list()?;
    if items.len() == 3 && items[0].is_symbol("_") && items[1].is_symbol("BitVec") {
        numeral_value(&items[2])
    } else {
        None
    }
}

fn parse_sort_info(sexp: &SExpr) -> Option<SortInfo> {
    if let Some(width) = bv_sort_width(sexp) {
        return Some(SortInfo::BitVec(width));
    }

    array_sort_value_width(sexp).map(|value_width| SortInfo::Array { value_width })
}

fn array_sort_value_width(sexp: &SExpr) -> Option<u64> {
    let items = sexp.as_list()?;
    if items.len() == 3 && items[0].is_symbol("Array") { bv_sort_width(&items[2]) } else { None }
}

fn numeral_value(sexp: &SExpr) -> Option<u64> {
    match sexp {
        SExpr::Numeral(n) => n.parse::<u64>().ok(),
        _ => None,
    }
}

fn collect_datatype_selector_widths(sexp: &SExpr, widths: &mut SortEnv) {
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
            if let Some(name) = field_items[0].as_symbol() {
                widths.record_symbol_sort(name, &field_items[1]);
            }
        }
    }
}

fn rewrite(mut sexp: SExpr, widths: &SortEnv, stats: &mut Stats) -> SExpr {
    let items = match &mut sexp {
        SExpr::List(items) => std::mem::take(items),
        _ => return sexp,
    };

    let items: Vec<SExpr> = items.into_iter().map(|c| rewrite(c, widths, stats)).collect();

    if is_concat(&items) {
        stats.seen += 1;
        match try_rewrite_concat(&items[1], &items[2], widths) {
            Some(replacement) => {
                stats.rewritten += 1;
                replacement
            }
            None => {
                stats.skipped += 1;
                SExpr::List(items)
            }
        }
    } else {
        SExpr::List(items)
    }
}

fn is_concat(items: &[SExpr]) -> bool {
    items.len() == 3 && items[0].is_symbol("concat")
}

fn try_rewrite_concat(a: &SExpr, b: &SExpr, widths: &SortEnv) -> Option<SExpr> {
    let wa = infer_width(a, widths)?;
    let wb = infer_width(b, widths)?;
    let total = wa + wb;

    let a_extended = mk_indexed("zero_extend", wb, a.clone());
    let shift_amount = mk_bv_literal(wb, total);
    let a_shifted = SExpr::List(vec![SExpr::Symbol("bvshl".to_string()), a_extended, shift_amount]);

    let b_extended = mk_indexed("zero_extend", wa, b.clone());

    Some(SExpr::List(vec![SExpr::Symbol("bvor".to_string()), a_shifted, b_extended]))
}

fn mk_indexed(op: &str, param: u64, arg: SExpr) -> SExpr {
    SExpr::List(vec![
        SExpr::List(vec![
            SExpr::Symbol("_".to_string()),
            SExpr::Symbol(op.to_string()),
            SExpr::Numeral(param.to_string()),
        ]),
        arg,
    ])
}

fn mk_bv_literal(value: u64, width: u64) -> SExpr {
    SExpr::List(vec![
        SExpr::Symbol("_".to_string()),
        SExpr::Symbol(format!("bv{value}")),
        SExpr::Numeral(width.to_string()),
    ])
}

/// Infer the bit-width of an S-expression.
///
/// Supported forms include literals, declared symbols, array selects, concat,
/// extract, zero/sign extension, width-preserving bit-vector operators, and
/// bit-vector typed `ite` expressions.
pub(crate) fn infer_width(sexp: &SExpr, widths: &SortEnv) -> Option<u64> {
    match sexp {
        SExpr::Hexadecimal(h) => {
            let digits = h.strip_prefix("#x").unwrap_or(h);
            Some(digits.len() as u64 * 4)
        }
        SExpr::Binary(b) => {
            let digits = b.strip_prefix("#b").unwrap_or(b);
            Some(digits.len() as u64)
        }
        SExpr::Symbol(name) => widths.bv_width(name.as_str()),
        SExpr::List(items) => infer_width_list(items, widths),
        _ => None,
    }
}

fn infer_width_list(items: &[SExpr], widths: &SortEnv) -> Option<u64> {
    if items.is_empty() {
        return None;
    }

    if items.len() == 3 && items[0].is_symbol("_") {
        if let Some(sym) = items[1].as_symbol() {
            if let Some(rest) = sym.strip_prefix("bv") {
                if rest.parse::<u64>().is_ok() {
                    return numeral_value(&items[2]);
                }
            }
        }
    }

    if let Some(indexed_items) = items[0].as_list() {
        if indexed_items.len() >= 3 && indexed_items[0].is_symbol("_") {
            if let Some(op) = indexed_items[1].as_symbol() {
                return infer_width_indexed(op, indexed_items, &items[1..], widths);
            }
        }
        if indexed_items.len() == 3 && indexed_items[0].is_symbol("as") {
            if let Some(name) = indexed_items[1].as_symbol() {
                return infer_width_named(name, &items[1..], widths);
            }
        }
    }

    if let Some(op) = items[0].as_symbol() {
        return infer_width_named(op, &items[1..], widths);
    }

    None
}

fn infer_width_indexed(
    op: &str,
    indexed_items: &[SExpr],
    args: &[SExpr],
    widths: &SortEnv,
) -> Option<u64> {
    match op {
        "extract" if indexed_items.len() == 4 && args.len() == 1 => {
            let hi = numeral_value(&indexed_items[2])?;
            let lo = numeral_value(&indexed_items[3])?;
            Some(hi - lo + 1)
        }
        "zero_extend" | "sign_extend" if indexed_items.len() == 3 && args.len() == 1 => {
            let n = numeral_value(&indexed_items[2])?;
            let base = infer_width(&args[0], widths)?;
            Some(base + n)
        }
        _ => None,
    }
}

fn infer_width_named(op: &str, args: &[SExpr], widths: &SortEnv) -> Option<u64> {
    match op {
        "select" if args.len() == 2 => infer_array_value_width(&args[0], widths),
        "concat" if args.len() == 2 => {
            let wa = infer_width(&args[0], widths)?;
            let wb = infer_width(&args[1], widths)?;
            Some(wa + wb)
        }
        "bvadd" | "bvsub" | "bvmul" | "bvand" | "bvor" | "bvxor" | "bvshl" | "bvlshr"
        | "bvashr" | "bvnot" | "bvneg"
            if !args.is_empty() =>
        {
            infer_width(&args[0], widths)
        }
        "ite" if args.len() == 3 => infer_width(&args[1], widths),
        _ => widths.bv_width(op),
    }
}

fn infer_array_value_width(sexp: &SExpr, widths: &SortEnv) -> Option<u64> {
    match sexp {
        SExpr::Symbol(name) => widths.array_value_width(name.as_str()),
        SExpr::List(items) => infer_array_value_width_list(items, widths),
        _ => None,
    }
}

fn infer_array_value_width_list(items: &[SExpr], widths: &SortEnv) -> Option<u64> {
    if items.is_empty() {
        return None;
    }

    if let Some(indexed_items) = items[0].as_list() {
        if indexed_items.len() == 3
            && indexed_items[0].is_symbol("as")
            && indexed_items[1].is_symbol("const")
        {
            return array_sort_value_width(&indexed_items[2]);
        }
    }

    if let Some(op) = items[0].as_symbol() {
        return match op {
            "store" if items.len() == 4 => infer_array_value_width(&items[1], widths),
            "ite" if items.len() == 4 => infer_array_value_width(&items[2], widths),
            _ => widths.array_value_width(op),
        };
    }

    None
}
