// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The R2 native-surface **re-keyer**: mechanically rewrite a corpus test
//! source from the legacy `#[kani::proof]` + `kani::any()` spelling to the
//! native `#[kani::harness]` spelling (two-language design E7/R2), where —
//! and only where — the rewrite is certain:
//!
//! ```text
//! #[kani::proof]                      #[kani::harness]
//! fn h() {                            fn h(x: u32) {
//!     let x: u32 = kani::any();  →
//!     kani::assume(x < 10);               assume(x < 10);
//!     assert!(x + 1 <= 10);               assert!(x + 1 <= 10);
//! }                                   }
//! ```
//!
//! Top-of-body `let x: T = kani::any();` bindings hoist into parameters, the
//! `kani::` prefix drops from `any()`/`assume()` (the harness body imports the
//! bare vocabulary), and everything else is preserved. Hoisted lines are
//! replaced by *blank* lines so every remaining statement keeps its original
//! line number (expected-output files sometimes quote locations).
//!
//! **Fail-closed:** any construct outside the certain fragment leaves the
//! whole unit in the legacy spelling, byte-identical, with a machine-readable
//! reason. The provenance of every unit is `rekey:native` or
//! `rekey:legacy(<reason>)`. Verdict identity for rewritten units holds by
//! construction: `#[kani::harness]` expands to the same `#[kanitool::proof]`
//! marker as `#[kani::proof]` with an equivalent `kani::any()` preamble.

use std::collections::BTreeSet;

/// Which harness spelling a run drives the corpus in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, clap::ValueEnum)]
pub enum Surface {
    /// Run the corpus verbatim (`#[kani::proof]` spelling). Byte-identical to
    /// runs before `--surface` existed.
    #[default]
    Legacy,
    /// Mechanically re-key each expressible unit to the native
    /// `#[kani::harness]` spelling before compilation; inexpressible units
    /// run legacy with a recorded reason.
    Native,
}

impl Surface {
    pub fn as_str(self) -> &'static str {
        match self {
            Surface::Legacy => "legacy",
            Surface::Native => "native",
        }
    }
}

/// Outcome of re-keying one unit's source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rekey {
    /// The unit is (now) entirely in the native spelling. `source` is the
    /// rewritten file — equal to the input when nothing needed rewriting
    /// (`rewritten == 0`), which is what makes the re-keyer idempotent.
    Native {
        source: String,
        /// `#[kani::proof]` harnesses rewritten to `#[kani::harness]`.
        rewritten: usize,
        /// `let x: T = kani::any();` bindings hoisted into parameters.
        hoisted_params: usize,
    },
    /// The unit stays in the legacy spelling, byte-identical, because the
    /// mechanical rewrite is not certain for it.
    Legacy { reason: String },
}

impl Rekey {
    /// The per-unit provenance string recorded in run results.
    pub fn provenance(&self) -> String {
        match self {
            Rekey::Native { .. } => "rekey:native".to_string(),
            Rekey::Legacy { reason } => format!("rekey:legacy({reason})"),
        }
    }
}

/// Re-key one corpus test source. All-or-nothing per file: every
/// `#[kani::proof]` harness must be expressible, otherwise the whole file is
/// left legacy (a single unit must have a single spelling provenance).
pub fn rekey_source(src: &str) -> Rekey {
    let legacy = |reason: &str| Rekey::Legacy { reason: reason.to_string() };

    let Ok(stripped) = strip_noncode(src) else {
        return legacy("unparseable_source");
    };
    debug_assert_eq!(stripped.len(), src.len());

    let orig_lines: Vec<&str> = src.split('\n').collect();
    let strip_lines: Vec<&str> = stripped.split('\n').collect();

    // Anchors: attribute-only lines that are exactly `#[kani::proof]`.
    let anchors: Vec<usize> = strip_lines
        .iter()
        .enumerate()
        .filter(|(_, l)| l.trim() == "#[kani::proof]")
        .map(|(i, _)| i)
        .collect();

    // Account for every proof-ish marker in code (comments/strings excluded).
    if stripped.contains("kani::proof_for_contract") {
        return legacy("proof_for_contract");
    }
    if stripped.contains("#[kani::proof(") {
        return legacy("proof_args");
    }
    let marker_count = count_token_occurrences(&stripped, "kani::proof");
    let bare_proof = stripped.contains("#[proof]");
    if anchors.is_empty() && marker_count == 0 && !bare_proof {
        // Nothing legacy to rewrite (e.g. an already-native file): no-op.
        return Rekey::Native { source: src.to_string(), rewritten: 0, hoisted_params: 0 };
    }
    if marker_count != anchors.len() || bare_proof {
        // A `kani::proof` spelled any other way (cfg_attr, aliased import,
        // same-line attr+fn, trailing comment on the attr line, …) — we
        // cannot be certain we saw every harness, so touch nothing.
        return legacy("unmatched_proof_marker");
    }

    // ---- file-level gates (only relevant when there is work to do) --------
    if header_expects_check_fail(&orig_lines) {
        // The oracle is a *compile* failure; rewriting could change the
        // diagnostic and thus the verdict.
        return legacy("check_fail_oracle");
    }
    if has_external_file_refs(&strip_lines) {
        // The rewritten copy is compiled from a different directory; relative
        // `mod x;` / `include!` references would break.
        return legacy("external_file_refs");
    }
    if defines_vocab_item(&stripped) {
        // A local `fn any` / `fn assume` collides with the bare vocabulary
        // the native harness imports.
        return legacy("vocab_shadowed");
    }

    let Ok(all_mod_at_line) = module_context_per_line(&strip_lines) else {
        return legacy("unparseable_source");
    };

    let mut plans: Vec<HarnessPlan> = Vec::new();
    for &anchor in &anchors {
        match plan_harness(&orig_lines, &strip_lines, &all_mod_at_line, anchor) {
            Ok(plan) => plans.push(plan),
            Err(reason) => return Rekey::Legacy { reason },
        }
    }

    // ---- apply -------------------------------------------------------------
    let mut new_lines: Vec<String> = orig_lines.iter().map(|s| s.to_string()).collect();
    let mut hoisted_params = 0usize;
    for plan in &plans {
        new_lines[plan.attr_line] =
            new_lines[plan.attr_line].replacen("#[kani::proof]", "#[kani::harness]", 1);
        new_lines[plan.fn_line] = plan.new_fn_line.clone();
        for &h in &plan.hoisted_lines {
            new_lines[h] = String::new();
        }
        hoisted_params += plan.hoisted_lines.len();
        if let Some((b0, b1)) = plan.body_range {
            for i in b0..b1 {
                if plan.hoisted_lines.contains(&i) {
                    continue;
                }
                let replaced = drop_kani_prefix(&new_lines[i], strip_lines[i]);
                new_lines[i] = replaced;
            }
        }
    }

    Rekey::Native { source: new_lines.join("\n"), rewritten: plans.len(), hoisted_params }
}

// ---------------------------------------------------------------------------
// per-harness planning
// ---------------------------------------------------------------------------

struct HarnessPlan {
    attr_line: usize,
    fn_line: usize,
    new_fn_line: String,
    /// Body line range (exclusive of the `fn` line and the closing `}`).
    body_range: Option<(usize, usize)>,
    hoisted_lines: BTreeSet<usize>,
}

fn plan_harness(
    orig_lines: &[&str],
    strip_lines: &[&str],
    all_mod_at_line: &[bool],
    anchor: usize,
) -> Result<HarnessPlan, String> {
    if !all_mod_at_line[anchor] {
        // Inside an impl/trait/fn/… — `#[kani::harness]` is only certain on
        // free functions at module scope.
        return Err("nested_context".to_string());
    }

    // Collect the attribute group around the anchor (other attrs compose with
    // `#[kani::harness]` unchanged, but only a known-safe set of kani ones).
    // Non-kani attributes (e.g. `#[test]`) pass through verbatim BUT suppress
    // param-hoisting: `#[test]` requires a zero-arg fn, and any foreign
    // attribute may constrain the signature — the bindings stay in the body as
    // bare `any()` (semantically identical), which composes with every attr
    // exactly as the legacy zero-arg `#[kani::proof]` did. Found by the first
    // corpus burndown: kani/Options/check_tests.rs (#[test] + hoisted param =
    // libtest rejection, exit 101).
    let mut kani_attrs: Vec<String> = Vec::new();
    let mut has_non_kani_attr = false;
    // Upward: contiguous attribute / comment lines.
    let mut i = anchor;
    while i > 0 {
        i -= 1;
        let t = strip_lines[i].trim();
        let ot = orig_lines[i].trim();
        if t.is_empty() {
            if ot.is_empty() || ot.starts_with("//") {
                continue; // comment-only or blank line inside the group
            }
            break;
        }
        if t.starts_with("#[") {
            if !t.ends_with(']') {
                return Err("multiline_attr".to_string());
            }
            if let Some(name) = kani_attr_name(t) {
                kani_attrs.push(name);
            } else {
                has_non_kani_attr = true;
            }
            continue;
        }
        break;
    }
    // Downward: attribute / comment lines until the `fn` line.
    let mut j = anchor + 1;
    let fn_line = loop {
        let Some(t) = strip_lines.get(j).map(|l| l.trim()) else {
            return Err("unrecognized_signature".to_string());
        };
        if t.is_empty() {
            j += 1;
            continue;
        }
        if t.starts_with("#[") {
            if !t.ends_with(']') {
                return Err("multiline_attr".to_string());
            }
            if let Some(name) = kani_attr_name(t) {
                kani_attrs.push(name);
            } else {
                has_non_kani_attr = true;
            }
            j += 1;
            continue;
        }
        break j;
    };
    for name in &kani_attrs {
        match name.as_str() {
            "proof" => return Err("duplicate_proof_attr".to_string()),
            "should_panic" | "unwind" | "solver" | "stub" | "use_stub_set" | "recursion" => {}
            other => return Err(format!("kani_attr({other})")),
        }
    }

    let sig = parse_fn_line(orig_lines[fn_line], strip_lines[fn_line])?;

    if sig.empty_body {
        return Ok(HarnessPlan {
            attr_line: anchor,
            fn_line,
            new_fn_line: format!("{}{}() {{}}", sig.indent, sig.pre),
            body_range: None,
            hoisted_lines: BTreeSet::new(),
        });
    }

    // Body extent: match the opening brace, closing `}` alone on its line.
    let open_col = strip_lines[fn_line].rfind('{').expect("sig ends with brace");
    let (close_line, _close_col) =
        find_matching_close(strip_lines, fn_line, open_col).ok_or("unparseable_source")?;
    if strip_lines[close_line].trim() != "}" {
        return Err("unparseable_source".to_string());
    }
    let body = (fn_line + 1, close_line);

    // Every `kani::<api>` in the body must be in the bare-vocabulary set.
    for i in body.0..body.1 {
        for name in kani_api_names(strip_lines[i]) {
            if name != "any" && name != "assume" {
                return Err(format!("kani_api({name})"));
            }
        }
    }
    // No pre-existing *bare* `any` / `assume` uses: the injected
    // `use kani::{any, assume};` would change what they resolve to.
    for i in body.0..body.1 {
        if has_bare_vocab_use(strip_lines[i]) {
            return Err("bare_vocab".to_string());
        }
    }

    // Hoist the maximal top-of-body prefix of `let x: T = kani::any();`.
    // Under a foreign attribute (`#[test]`, …) hoisting is SUPPRESSED: the
    // signature must stay zero-arg, so bindings remain in-body as bare `any()`.
    let mut hoisted_lines: BTreeSet<usize> = BTreeSet::new();
    let mut params: Vec<String> = Vec::new();
    for i in body.0..body.1 {
        if has_non_kani_attr {
            break;
        }
        let t = strip_lines[i].trim();
        if t.is_empty() {
            continue; // blank / comment-only lines stay put
        }
        match parse_any_binding(t) {
            Some(AnyBinding { param: Some(p) }) => {
                hoisted_lines.insert(i);
                params.push(p);
            }
            _ => break,
        }
    }

    // Retained `kani::any` uses must be whole-statement bindings at the
    // harness body's statement level (no loops / nested blocks).
    let mut depth: i32 = 1;
    for i in body.0..body.1 {
        let line = strip_lines[i];
        let mut search = 0usize;
        while let Some(off) = line[search..].find("kani::any") {
            let pos = search + off;
            let before_ok = pos == 0 || !is_ident_char(line[..pos].chars().next_back().unwrap());
            let after = line[pos + "kani::any".len()..].chars().next();
            let is_any = before_ok && !after.map(is_ident_char).unwrap_or(false);
            if is_any && !hoisted_lines.contains(&i) {
                let depth_here = depth + brace_delta(&line[..pos]);
                if depth_here != 1 {
                    return Err("any_in_nested_block".to_string());
                }
                if parse_any_binding(line.trim()).is_none() {
                    return Err("non_binding_any".to_string());
                }
            }
            search = pos + "kani::any".len();
        }
        depth += brace_delta(line);
    }

    let new_fn_line = format!("{}{}({}) {{", sig.indent, sig.pre, params.join(", "));
    Ok(HarnessPlan {
        attr_line: anchor,
        fn_line,
        new_fn_line,
        body_range: Some(body),
        hoisted_lines,
    })
}

// ---------------------------------------------------------------------------
// signature parsing
// ---------------------------------------------------------------------------

struct FnSig {
    indent: String,
    /// Everything up to (not including) the parameter parens, e.g. `pub fn check`.
    pre: String,
    empty_body: bool,
}

fn parse_fn_line(orig: &str, strip: &str) -> Result<FnSig, String> {
    let t = strip.trim();
    if token_present(t, "async") {
        return Err("async_harness".to_string());
    }
    if token_present(t, "unsafe") || token_present(t, "extern") || token_present(t, "const") {
        return Err("unrecognized_signature".to_string());
    }
    let (core, empty_body) = if let Some(c) = t.strip_suffix("{}") {
        (c.trim_end(), true)
    } else if let Some(c) = t.strip_suffix("{ }") {
        (c.trim_end(), true)
    } else if let Some(c) = t.strip_suffix('{') {
        (c.trim_end(), false)
    } else {
        return Err("unrecognized_signature".to_string());
    };
    let Some(inner_and_pre) = core.strip_suffix(')') else {
        return Err("unrecognized_signature".to_string());
    };
    let Some(paren) = inner_and_pre.rfind('(') else {
        return Err("unrecognized_signature".to_string());
    };
    if !inner_and_pre[paren + 1..].trim().is_empty() {
        // A legacy proof harness never takes parameters; anything here is a
        // shape we do not understand.
        return Err("unrecognized_signature".to_string());
    }
    let pre = inner_and_pre[..paren].trim_end();
    if pre.ends_with("->") {
        return Err("unrecognized_signature".to_string());
    }
    if pre.contains('<') || pre.ends_with('>') {
        return Err("generic_harness".to_string());
    }
    let name_len = pre.chars().rev().take_while(|&c| is_ident_char(c)).count();
    if name_len == 0 {
        return Err("unrecognized_signature".to_string());
    }
    let rest = pre[..pre.len() - name_len].trim_end();
    let Some(vis) = rest.strip_suffix("fn") else {
        return Err("unrecognized_signature".to_string());
    };
    let vis = vis.trim_end();
    let vis_ok = vis.is_empty()
        || vis == "pub"
        || (vis.starts_with("pub") && vis[3..].trim_start().starts_with('(') && vis.ends_with(')'));
    if !vis_ok {
        return Err("unrecognized_signature".to_string());
    }
    let indent: String = orig.chars().take_while(|c| c.is_whitespace()).collect();
    Ok(FnSig { indent, pre: pre.to_string(), empty_body })
}

// ---------------------------------------------------------------------------
// `let <pat>[: <ty>] = kani::any[::<T>]();` parsing
// ---------------------------------------------------------------------------

struct AnyBinding {
    /// `Some("mut x: u32")` when hoistable into a parameter; `None` when it is
    /// a well-formed binding that must stay in the body (untyped, non-ident
    /// pattern, or a type that cannot appear in a signature).
    param: Option<String>,
}

fn parse_any_binding(stmt: &str) -> Option<AnyBinding> {
    let t = stmt.trim();
    let inner = t.strip_prefix("let ")?.strip_suffix(';')?.trim();
    // Exactly one top-level `=` (the binding's); the RHS is a bare any() call.
    let eq = single_assign_eq(inner)?;
    let (lhs, rhs) = (inner[..eq].trim(), inner[eq + 1..].trim());

    let turbofish: Option<&str> = {
        let r = rhs.strip_prefix("kani::any")?;
        if r.trim() == "()" {
            None
        } else {
            let r = r.trim_start().strip_prefix("::<")?;
            let ty = r.strip_suffix("()").map(str::trim_end)?.strip_suffix('>')?;
            Some(ty.trim())
        }
    };

    let (is_mut, pat) = match lhs.strip_prefix("mut ") {
        Some(rest) => (true, rest.trim()),
        None => (false, lhs),
    };
    let (pat, annot): (&str, Option<&str>) = match annotation_colon(pat) {
        Some(c) => (pat[..c].trim_end(), Some(pat[c + 1..].trim())),
        None => (pat, None),
    };
    let ty = annot.or(turbofish);

    let hoistable = pat.chars().all(is_ident_char)
        && !pat.is_empty()
        && ty.is_some_and(|ty| {
            !ty.is_empty()
                && !token_present(ty, "_")
                && !token_present(ty, "impl")
                && !token_present(ty, "dyn")
                && !ty.contains('&')
        });
    let param = hoistable
        .then(|| format!("{}{}: {}", if is_mut { "mut " } else { "" }, pat, ty.unwrap()));
    Some(AnyBinding { param })
}

/// Byte index of the single top-level `=` in a binding, rejecting statements
/// with comparison / arrow / compound tokens that would make the split unsafe.
fn single_assign_eq(s: &str) -> Option<usize> {
    let b = s.as_bytes();
    let mut found: Option<usize> = None;
    for (i, &c) in b.iter().enumerate() {
        if c != b'=' {
            continue;
        }
        let prev = i.checked_sub(1).map(|p| b[p]);
        let next = b.get(i + 1).copied();
        if matches!(prev, Some(b'=') | Some(b'<') | Some(b'>') | Some(b'!'))
            || matches!(next, Some(b'=') | Some(b'>'))
        {
            return None; // `==`, `<=`, `>=`, `!=`, `=>` — not the simple form
        }
        if found.is_some() {
            return None;
        }
        found = Some(i);
    }
    found
}

/// The `:` that separates pattern from type annotation — the first `:` that is
/// not part of a `::`. `None` when the binding is untyped.
fn annotation_colon(s: &str) -> Option<usize> {
    let b = s.as_bytes();
    for (i, &c) in b.iter().enumerate() {
        if c != b':' {
            continue;
        }
        let prev_is = i.checked_sub(1).map(|p| b[p] == b':').unwrap_or(false);
        let next_is = b.get(i + 1).map(|&n| n == b':').unwrap_or(false);
        if !prev_is && !next_is {
            return Some(i);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// body scans
// ---------------------------------------------------------------------------

/// Every `<ident>` in `kani::<ident>` occurrences on a (stripped) line.
fn kani_api_names(line: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut search = 0usize;
    while let Some(off) = line[search..].find("kani::") {
        let pos = search + off;
        search = pos + "kani::".len();
        if pos > 0 && is_ident_char(line[..pos].chars().next_back().unwrap()) {
            continue; // `mykani::…`
        }
        let name: String = line[search..].chars().take_while(|&c| is_ident_char(c)).collect();
        if !name.is_empty() {
            out.push(name);
        }
    }
    out
}

/// A *bare* (unqualified, non-method) use of `any` / `assume` on a (stripped)
/// line — the injected `use kani::{any, assume};` would capture it.
fn has_bare_vocab_use(line: &str) -> bool {
    for word in ["any", "assume"] {
        let mut search = 0usize;
        while let Some(off) = line[search..].find(word) {
            let pos = search + off;
            search = pos + word.len();
            let before = line[..pos].chars().next_back();
            let after = line[pos + word.len()..].chars().next();
            if before.map(is_ident_char).unwrap_or(false)
                || after.map(is_ident_char).unwrap_or(false)
            {
                continue; // part of a longer identifier
            }
            // Qualified (`kani::any`) or method (`.any(`) positions are fine.
            let prev_nonspace = line[..pos].trim_end().chars().next_back();
            if !matches!(prev_nonspace, Some(':') | Some('.')) {
                return true;
            }
        }
    }
    false
}

fn brace_delta(s: &str) -> i32 {
    let mut d = 0i32;
    for c in s.chars() {
        match c {
            '{' => d += 1,
            '}' => d -= 1,
            _ => {}
        }
    }
    d
}

fn find_matching_close(
    strip_lines: &[&str],
    open_line: usize,
    open_col: usize,
) -> Option<(usize, usize)> {
    let mut depth = 0i32;
    for (li, line) in strip_lines.iter().enumerate().skip(open_line) {
        let start = if li == open_line { open_col } else { 0 };
        for (ci, c) in line[start..].char_indices() {
            match c {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        return Some((li, start + ci));
                    }
                }
                _ => {}
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// file-level helpers
// ---------------------------------------------------------------------------

fn kani_attr_name(attr_line_trimmed: &str) -> Option<String> {
    let rest = attr_line_trimmed.strip_prefix("#[kani::")?;
    let name: String = rest.chars().take_while(|&c| is_ident_char(c)).collect();
    (!name.is_empty()).then_some(name)
}

/// Mirrors `discover::header_expects_check_fail`.
fn header_expects_check_fail(orig_lines: &[&str]) -> bool {
    orig_lines.iter().take(80).any(|line| {
        let l = line.trim_start_matches(['/', ' ']).trim();
        l.starts_with("kani-check-fail")
    })
}

fn has_external_file_refs(strip_lines: &[&str]) -> bool {
    strip_lines.iter().any(|l| {
        let t = l.trim();
        let mod_decl = (t.strip_prefix("pub mod ").or_else(|| t.strip_prefix("mod ")))
            .is_some_and(|rest| rest.trim_end().ends_with(';'));
        mod_decl
            || t.contains("include!")
            || t.contains("include_str!")
            || t.contains("include_bytes!")
            || t.contains("#[path")
    })
}

/// A locally-defined `fn any` / `fn assume` anywhere in the file.
fn defines_vocab_item(stripped: &str) -> bool {
    for word in ["any", "assume"] {
        let mut search = 0usize;
        while let Some(off) = stripped[search..].find(word) {
            let pos = search + off;
            search = pos + word.len();
            let before = stripped[..pos].chars().next_back();
            let after = stripped[pos + word.len()..].chars().next();
            if before.map(is_ident_char).unwrap_or(false)
                || after.map(is_ident_char).unwrap_or(false)
            {
                continue;
            }
            if stripped[..pos].trim_end().ends_with("fn") {
                return true;
            }
        }
    }
    false
}

/// Occurrences of `needle` as a token (next char not an identifier char,
/// previous char not an identifier char or `(`-opener continuation).
fn count_token_occurrences(stripped: &str, needle: &str) -> usize {
    let mut n = 0usize;
    let mut search = 0usize;
    while let Some(off) = stripped[search..].find(needle) {
        let pos = search + off;
        search = pos + needle.len();
        let before = stripped[..pos].chars().next_back();
        let after = stripped[search..].chars().next();
        if before.map(is_ident_char).unwrap_or(false) || after.map(is_ident_char).unwrap_or(false)
        {
            continue;
        }
        n += 1;
    }
    n
}

/// For each line: is every enclosing brace opener (at the line's start) a
/// `mod`? Free functions at module scope are the only certain harness context.
fn module_context_per_line(strip_lines: &[&str]) -> Result<Vec<bool>, ()> {
    #[derive(PartialEq)]
    enum Opener {
        Mod,
        Other,
    }
    fn classify_opener(pending: &str) -> Opener {
        let mut kind = Opener::Other;
        let mut seen_any = false;
        for tok in pending.split(|c: char| !is_ident_char(c)).filter(|t| !t.is_empty()) {
            match tok {
                "mod" => {
                    kind = Opener::Mod;
                    seen_any = true;
                }
                "impl" | "trait" | "fn" | "struct" | "enum" | "union" | "match" | "unsafe"
                | "extern" | "if" | "else" | "while" | "for" | "loop" => {
                    kind = Opener::Other;
                    seen_any = true;
                }
                _ => {}
            }
        }
        if seen_any { kind } else { Opener::Other }
    }
    let mut stack: Vec<Opener> = Vec::new();
    let mut pending = String::new();
    let mut out = Vec::with_capacity(strip_lines.len());
    for line in strip_lines {
        out.push(stack.iter().all(|o| *o == Opener::Mod));
        for c in line.chars() {
            match c {
                '{' => {
                    let kind = classify_opener(&pending);
                    stack.push(kind);
                    pending.clear();
                }
                '}' => {
                    if stack.pop().is_none() {
                        return Err(());
                    }
                    pending.clear();
                }
                _ => pending.push(c),
            }
        }
        pending.push(' ');
    }
    if !stack.is_empty() {
        return Err(());
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// editing
// ---------------------------------------------------------------------------

/// Remove the `kani::` prefix from `kani::any` / `kani::assume` occurrences on
/// one line — only at code positions (per the stripped view), so string
/// literals and comments mentioning `kani::any` stay untouched.
fn drop_kani_prefix(orig_line: &str, strip_line: &str) -> String {
    let mut cuts: Vec<usize> = Vec::new();
    for api in ["kani::any", "kani::assume"] {
        let mut search = 0usize;
        while let Some(off) = strip_line[search..].find(api) {
            let pos = search + off;
            search = pos + api.len();
            let before = strip_line[..pos].chars().next_back();
            let after = strip_line[search..].chars().next();
            if before.map(|c| is_ident_char(c) || c == ':').unwrap_or(false)
                || after.map(is_ident_char).unwrap_or(false)
            {
                continue; // `mykani::…`, `::kani::…` (absolute path), `kani::any_where`
            }
            cuts.push(pos);
        }
    }
    cuts.sort_unstable();
    let mut out = String::with_capacity(orig_line.len());
    let mut at = 0usize;
    for cut in cuts {
        out.push_str(&orig_line[at..cut]);
        at = cut + "kani::".len();
    }
    out.push_str(&orig_line[at..]);
    out
}

// ---------------------------------------------------------------------------
// comment / string stripping (byte-length preserving)
// ---------------------------------------------------------------------------

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Replace the contents of comments, string literals and char literals with
/// spaces, preserving byte offsets and newlines, so structural scans (braces,
/// attributes, `kani::` calls) only ever see code.
fn strip_noncode(src: &str) -> Result<String, ()> {
    let chars: Vec<(usize, char)> = src.char_indices().collect();
    let n = chars.len();
    let mut out = String::with_capacity(src.len());
    let blank = |out: &mut String, c: char| {
        if c == '\n' {
            out.push('\n');
        } else {
            for _ in 0..c.len_utf8() {
                out.push(' ');
            }
        }
    };
    let mut i = 0usize;
    while i < n {
        let c = chars[i].1;
        // Line comment.
        if c == '/' && i + 1 < n && chars[i + 1].1 == '/' {
            while i < n && chars[i].1 != '\n' {
                blank(&mut out, chars[i].1);
                i += 1;
            }
            continue;
        }
        // Block comment (nesting).
        if c == '/' && i + 1 < n && chars[i + 1].1 == '*' {
            let mut depth = 1usize;
            blank(&mut out, '/');
            blank(&mut out, '*');
            i += 2;
            while i < n && depth > 0 {
                if chars[i].1 == '/' && i + 1 < n && chars[i + 1].1 == '*' {
                    depth += 1;
                    blank(&mut out, '/');
                    blank(&mut out, '*');
                    i += 2;
                } else if chars[i].1 == '*' && i + 1 < n && chars[i + 1].1 == '/' {
                    depth -= 1;
                    blank(&mut out, '*');
                    blank(&mut out, '/');
                    i += 2;
                } else {
                    blank(&mut out, chars[i].1);
                    i += 1;
                }
            }
            if depth > 0 {
                return Err(());
            }
            continue;
        }
        // Raw string r"…" / r#"…"# (not part of an identifier).
        if c == 'r' && (i == 0 || !is_ident_char(chars[i - 1].1)) {
            let mut j = i + 1;
            let mut hashes = 0usize;
            while j < n && chars[j].1 == '#' {
                hashes += 1;
                j += 1;
            }
            if j < n && chars[j].1 == '"' {
                // Blank from the opening quote content to the closing quote.
                for k in i..=j {
                    blank(&mut out, chars[k].1);
                }
                i = j + 1;
                loop {
                    if i >= n {
                        return Err(());
                    }
                    if chars[i].1 == '"' {
                        let mut close = 0usize;
                        while close < hashes && i + 1 + close < n && chars[i + 1 + close].1 == '#'
                        {
                            close += 1;
                        }
                        if close == hashes {
                            for k in i..=i + hashes {
                                blank(&mut out, chars[k].1);
                            }
                            i += hashes + 1;
                            break;
                        }
                    }
                    blank(&mut out, chars[i].1);
                    i += 1;
                }
                continue;
            }
        }
        // String literal.
        if c == '"' {
            blank(&mut out, '"');
            i += 1;
            loop {
                if i >= n {
                    return Err(());
                }
                match chars[i].1 {
                    '\\' => {
                        blank(&mut out, '\\');
                        i += 1;
                        if i < n {
                            blank(&mut out, chars[i].1);
                            i += 1;
                        }
                    }
                    '"' => {
                        blank(&mut out, '"');
                        i += 1;
                        break;
                    }
                    other => {
                        blank(&mut out, other);
                        i += 1;
                    }
                }
            }
            continue;
        }
        // Char literal vs lifetime.
        if c == '\'' {
            let next = chars.get(i + 1).map(|&(_, c)| c);
            if next == Some('\\') {
                // Escaped char literal: blank to the closing quote.
                blank(&mut out, '\'');
                blank(&mut out, '\\');
                i += 2;
                if i < n {
                    if chars[i].1 == 'u' && chars.get(i + 1).map(|&(_, c)| c) == Some('{') {
                        while i < n && chars[i].1 != '}' {
                            blank(&mut out, chars[i].1);
                            i += 1;
                        }
                    }
                    if i < n {
                        blank(&mut out, chars[i].1);
                        i += 1;
                    }
                }
                if i < n && chars[i].1 == '\'' {
                    blank(&mut out, '\'');
                    i += 1;
                } else {
                    return Err(());
                }
                continue;
            }
            if chars.get(i + 2).map(|&(_, c)| c) == Some('\'') && next != Some('\'') {
                // 'x' plain char literal.
                for k in i..=i + 2 {
                    blank(&mut out, chars[k].1);
                }
                i += 3;
                continue;
            }
            // Lifetime — keep as code.
            out.push('\'');
            i += 1;
            continue;
        }
        out.push(c);
        i += 1;
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// small token helper
// ---------------------------------------------------------------------------

fn token_present(s: &str, tok: &str) -> bool {
    s.split(|c: char| !is_ident_char(c)).any(|t| t == tok)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn native(src: &str) -> (String, usize, usize) {
        match rekey_source(src) {
            Rekey::Native { source, rewritten, hoisted_params } => {
                (source, rewritten, hoisted_params)
            }
            Rekey::Legacy { reason } => panic!("expected native, got legacy({reason})"),
        }
    }

    fn legacy_reason(src: &str) -> String {
        match rekey_source(src) {
            Rekey::Legacy { reason } => reason,
            Rekey::Native { .. } => panic!("expected legacy, got native"),
        }
    }

    // ---- the canonical rewrite ---------------------------------------------

    #[test]
    fn simple_hoist_and_assume_rewrite() {
        let src = "\
#[kani::proof]
fn check() {
    let x: u32 = kani::any();
    kani::assume(x < 10);
    assert!(x + 1 <= 10);
}
";
        let want = "\
#[kani::harness]
fn check(x: u32) {

    assume(x < 10);
    assert!(x + 1 <= 10);
}
";
        let (out, rewritten, hoisted) = native(src);
        assert_eq!(out, want);
        assert_eq!(rewritten, 1);
        assert_eq!(hoisted, 1);
    }

    #[test]
    fn multiple_params_mut_array_and_turbofish() {
        let src = "\
#[kani::proof]
pub fn check_all() {
    let mut n: u32 = kani::any();
    let xs: [u8; 4] = kani::any();
    let k = kani::any::<u16>();
    kani::assume(n <= 100);
    n += 1;
    assert!(n as usize + xs.len() + k as usize > 0);
}
";
        let (out, rewritten, hoisted) = native(src);
        assert_eq!(rewritten, 1);
        assert_eq!(hoisted, 3);
        assert!(out.contains("pub fn check_all(mut n: u32, xs: [u8; 4], k: u16) {"));
        assert!(out.contains("assume(n <= 100);"));
        assert!(!out.contains("kani::any") && !out.contains("kani::assume"));
    }

    /// Line numbers are preserved: hoisted bindings become blank lines.
    #[test]
    fn line_count_preserved() {
        let src = "#[kani::proof]\nfn f() {\n    let a: u8 = kani::any();\n    assert!(a >= 0);\n}\n";
        let (out, ..) = native(src);
        assert_eq!(src.matches('\n').count(), out.matches('\n').count());
        // The assert stays on its original (4th) line.
        assert_eq!(out.split('\n').nth(3).unwrap().trim(), "assert!(a >= 0);");
    }

    /// A binding after the hoistable prefix stays in the body, prefix-dropped.
    #[test]
    fn retained_midbody_binding() {
        let src = "\
#[kani::proof]
fn f() {
    let a: u8 = kani::any();
    kani::assume(a < 5);
    let b: u8 = kani::any();
    assert!(a + b < 300);
}
";
        let (out, _, hoisted) = native(src);
        assert_eq!(hoisted, 1);
        assert!(out.contains("fn f(a: u8) {"));
        assert!(out.contains("let b: u8 = any();"));
    }

    /// An untyped top-of-body binding cannot become a parameter; it stops the
    /// hoist prefix and stays in the body (still the native vocabulary).
    #[test]
    fn untyped_binding_retained_not_hoisted() {
        let src = "\
#[kani::proof]
fn f() {
    let a = kani::any();
    take_u8(a);
}
fn take_u8(_x: u8) {}
";
        let (out, _, hoisted) = native(src);
        assert_eq!(hoisted, 0);
        assert!(out.contains("fn f() {"));
        assert!(out.contains("let a = any();"));
    }

    /// `assume` rewrites everywhere in the body, even nested.
    #[test]
    fn assume_rewrites_at_any_depth() {
        let src = "\
#[kani::proof]
fn f() {
    let a: u8 = kani::any();
    if a > 1 {
        kani::assume(a < 100);
    }
    assert!(a < 100 || a <= 1);
}
";
        let (out, ..) = native(src);
        assert!(out.contains("        assume(a < 100);"));
    }

    #[test]
    fn empty_body_harness() {
        let src = "#[kani::proof]\nfn trivially_ok() {}\n";
        let (out, rewritten, hoisted) = native(src);
        assert_eq!(out, "#[kani::harness]\nfn trivially_ok() {}\n");
        assert_eq!((rewritten, hoisted), (1, 0));
    }

    /// Composable kani attributes ride along unchanged.
    #[test]
    fn composable_attrs_preserved() {
        let src = "\
#[kani::proof]
#[kani::unwind(3)]
#[kani::should_panic]
fn f() {
    let a: u8 = kani::any();
    assert!(a < 10);
}
";
        let (out, ..) = native(src);
        assert!(out.contains("#[kani::harness]\n#[kani::unwind(3)]\n#[kani::should_panic]"));
    }

    // ---- idempotence ---------------------------------------------------------

    #[test]
    fn rewriting_native_output_is_a_noop() {
        let src = "\
#[kani::proof]
fn check() {
    let x: u32 = kani::any();
    kani::assume(x < 10);
    let y: u32 = kani::any();
    assert!(x + y >= x);
}
";
        let (once, rewritten, _) = native(src);
        assert_eq!(rewritten, 1);
        let (twice, rewritten2, hoisted2) = native(&once);
        assert_eq!(twice, once);
        assert_eq!((rewritten2, hoisted2), (0, 0));
    }

    /// An already-native file (no legacy harness at all) passes through.
    #[test]
    fn already_native_file_is_noop() {
        let src = "\
#[kani::harness]
fn check(n: u32) {
    assume(n < 10);
    assert!(n + 1 <= 10);
}
";
        let (out, rewritten, hoisted) = native(src);
        assert_eq!(out, src);
        assert_eq!((rewritten, hoisted), (0, 0));
    }

    // ---- inexpressible cases -------------------------------------------------

    #[test]
    fn non_binding_any_stays_legacy() {
        let src = "\
#[kani::proof]
fn f() {
    if kani::any() {
        assert!(true);
    }
}
";
        assert_eq!(legacy_reason(src), "non_binding_any");
        // …also as a call argument.
        let src2 = "#[kani::proof]\nfn f() {\n    take(kani::any());\n}\n";
        assert_eq!(legacy_reason(src2), "non_binding_any");
        // …also as a non-trivial RHS.
        let src3 = "#[kani::proof]\nfn f() {\n    let x: u8 = kani::any() + 1;\n}\n";
        assert_eq!(legacy_reason(src3), "non_binding_any");
    }

    #[test]
    fn any_inside_a_loop_stays_legacy() {
        let src = "\
#[kani::proof]
fn f() {
    for _ in 0..3 {
        let x: u8 = kani::any();
        assert!(x as u16 <= 255);
    }
}
";
        assert_eq!(legacy_reason(src), "any_in_nested_block");
        // `while kani::any()` is a non-binding condition.
        let src2 = "#[kani::proof]\nfn f() {\n    while kani::any() {\n        break;\n    }\n}\n";
        assert_eq!(legacy_reason(src2), "non_binding_any");
    }

    #[test]
    fn other_kani_apis_stay_legacy() {
        let src = "\
#[kani::proof]
fn f() {
    let x: u8 = kani::any_where(|v: &u8| *v < 10);
    assert!(x < 10);
}
";
        assert_eq!(legacy_reason(src), "kani_api(any_where)");
        let src2 = "#[kani::proof]\nfn f() {\n    kani::cover!(true);\n}\n";
        assert_eq!(legacy_reason(src2), "kani_api(cover)");
    }

    #[test]
    fn generics_and_async_stay_legacy() {
        let src = "#[kani::proof]\nfn f<T: Default>() {\n    let _ = T::default();\n}\n";
        assert_eq!(legacy_reason(src), "generic_harness");
        let src2 = "#[kani::proof]\nasync fn f() {\n    assert!(true);\n}\n";
        assert_eq!(legacy_reason(src2), "async_harness");
    }

    #[test]
    fn proof_variants_stay_legacy() {
        let src = "#[kani::proof_for_contract(add)]\nfn f() {\n    let _ = add(1, 2);\n}\n";
        assert_eq!(legacy_reason(src), "proof_for_contract");
        let src2 = "#[kani::proof(schedule = RoundRobin::default())]\nasync fn f() {}\n";
        assert_eq!(legacy_reason(src2), "proof_args");
    }

    #[test]
    fn unanchored_proof_spellings_stay_legacy() {
        // cfg_attr-guarded proof attr: we cannot be certain we saw the harness.
        let src = "#[cfg_attr(kani, kani::proof)]\nfn f() {\n    assert!(true);\n}\n";
        assert_eq!(legacy_reason(src), "unmatched_proof_marker");
        // Aliased import spelling.
        let src2 = "use kani::proof;\n#[proof]\nfn f() {\n    assert!(true);\n}\n";
        assert_eq!(legacy_reason(src2), "unmatched_proof_marker");
    }

    #[test]
    fn check_fail_oracle_stays_legacy() {
        let src = "\
// kani-check-fail
#[kani::proof]
fn f() {
    let x: u32 = kani::any();
    assert!(x >= 0);
}
";
        assert_eq!(legacy_reason(src), "check_fail_oracle");
    }

    #[test]
    fn external_file_refs_stay_legacy() {
        let src = "mod helpers;\n#[kani::proof]\nfn f() {\n    helpers::go();\n}\n";
        assert_eq!(legacy_reason(src), "external_file_refs");
        let src2 = "#[kani::proof]\nfn f() {\n    include!(\"other.rs\");\n}\n";
        assert_eq!(legacy_reason(src2), "external_file_refs");
    }

    #[test]
    fn vocabulary_collisions_stay_legacy() {
        // A local `fn any` would be shadowed by the injected import.
        let src = "fn any() -> u8 { 3 }\n#[kani::proof]\nfn f() {\n    let x: u8 = kani::any();\n    assert!(x >= 0);\n}\n";
        assert_eq!(legacy_reason(src), "vocab_shadowed");
        // A pre-existing bare call would be re-bound by the injected import.
        let src2 = "use kani::any;\n#[kani::proof]\nfn f() {\n    let x: u8 = any();\n    assert!(x >= 0);\n}\n";
        assert_eq!(legacy_reason(src2), "bare_vocab");
    }

    #[test]
    fn nested_and_attr_oddities_stay_legacy() {
        // Harness inside an impl block.
        let src = "struct S;\nimpl S {\n    #[kani::proof]\n    fn f() {\n        assert!(true);\n    }\n}\n";
        assert_eq!(legacy_reason(src), "nested_context");
        // Duplicate proof attribute.
        let src2 = "#[kani::proof]\n#[kani::proof]\nfn f() {\n    assert!(true);\n}\n";
        assert_eq!(legacy_reason(src2), "duplicate_proof_attr");
        // A kani attribute outside the composable set.
        let src3 = "#[kani::proof]\n#[kani::ensures(|r| true)]\nfn f() {\n    assert!(true);\n}\n";
        assert_eq!(legacy_reason(src3), "kani_attr(ensures)");
        // Multi-line attribute between proof and fn.
        let src4 = "#[kani::proof]\n#[kani::stub(a,\n    b)]\nfn f() {\n    assert!(true);\n}\n";
        assert_eq!(legacy_reason(src4), "multiline_attr");
    }

    #[test]
    fn unrecognized_signatures_stay_legacy() {
        // Parameters on a legacy proof fn (not a shape we understand).
        let src = "#[kani::proof]\nfn f(x: u32) {\n    assert!(x >= 0);\n}\n";
        assert_eq!(legacy_reason(src), "unrecognized_signature");
        // unsafe fn.
        let src2 = "#[kani::proof]\nunsafe fn f() {\n    assert!(true);\n}\n";
        assert_eq!(legacy_reason(src2), "unrecognized_signature");
        // Brace on the next line (non-rustfmt shape).
        let src3 = "#[kani::proof]\nfn f()\n{\n    assert!(true);\n}\n";
        assert_eq!(legacy_reason(src3), "unrecognized_signature");
    }

    /// All-or-nothing: one inexpressible harness keeps the whole file legacy.
    #[test]
    fn all_or_nothing_per_file() {
        let src = "\
#[kani::proof]
fn good() {
    let x: u8 = kani::any();
    assert!(x as u16 <= 255);
}

#[kani::proof]
fn bad() {
    take(kani::any());
}
";
        assert_eq!(legacy_reason(src), "non_binding_any");
    }

    /// Multiple expressible harnesses all rewrite.
    #[test]
    fn multiple_harnesses_all_rewrite() {
        let src = "\
#[kani::proof]
fn a() {
    let x: u8 = kani::any();
    assert!(x as u16 <= 255);
}

#[kani::proof]
fn b() {
    let y: i32 = kani::any();
    kani::assume(y > 0);
    assert!(y >= 1);
}
";
        let (out, rewritten, hoisted) = native(src);
        assert_eq!((rewritten, hoisted), (2, 2));
        assert!(out.contains("fn a(x: u8) {"));
        assert!(out.contains("fn b(y: i32) {"));
    }

    // ---- comments and strings are inert ---------------------------------------

    #[test]
    fn strings_and_comments_do_not_confuse_the_scanner() {
        let src = "\
// This test used to use #[kani::proof] twice.
#[kani::proof]
fn f() {
    let x: u8 = kani::any();
    let msg = \"kani::any() failed { badly\";
    assert!(x as usize <= msg.len() + 300);
}
";
        let (out, rewritten, _) = native(src);
        assert_eq!(rewritten, 1);
        // The comment and the string literal are untouched.
        assert!(out.contains("// This test used to use #[kani::proof] twice."));
        assert!(out.contains("\"kani::any() failed { badly\""));
        assert!(out.contains("fn f(x: u8) {"));
    }

    #[test]
    fn foreign_attr_suppresses_hoist_but_still_rekeys() {
        // Regression: kani/Options/check_tests.rs — a `#[test]`-composed
        // harness must stay ZERO-ARG (libtest rejects parameters), so the
        // binding is retained in-body as bare `any()`; the attr still rewrites.
        let src = "\
#[cfg(test)]
mod test {
    #[test]
    #[kani::proof]
    fn test_harness() {
        let input: i32 = kani::any();
        kani::assume(input > 1);
        assert!(input > 0);
    }
}
";
        let (out, rewritten, hoisted) = native(src);
        assert_eq!(rewritten, 1);
        assert_eq!(hoisted, 0, "foreign attr must suppress hoisting");
        assert!(out.contains("#[test]"), "foreign attr passes through");
        assert!(out.contains("#[kani::harness]"));
        assert!(out.contains("fn test_harness() {"), "signature stays zero-arg");
        assert!(out.contains("let input: i32 = any();"), "binding retained, prefix dropped");
        assert!(out.contains("assume(input > 1);"));
        // Idempotent: rewriting the output is a no-op.
        let (out2, rewritten2, _) = native(&out);
        assert_eq!(rewritten2, 0);
        assert_eq!(out2, out);
    }

    // ---- provenance ------------------------------------------------------------

    #[test]
    fn provenance_strings() {
        let n = Rekey::Native { source: String::new(), rewritten: 1, hoisted_params: 2 };
        assert_eq!(n.provenance(), "rekey:native");
        let l = Rekey::Legacy { reason: "non_binding_any".into() };
        assert_eq!(l.provenance(), "rekey:legacy(non_binding_any)");
    }
}
