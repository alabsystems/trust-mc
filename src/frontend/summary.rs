// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `--summary`: a scannable verdict table for a whole run.
//!
//! # Why this exists
//!
//! The engine reports each harness as it finishes, which is right for a long
//! run but poor for reading afterwards. On a crate with five harnesses the
//! failing ones arrive in scheduler order, each verdict sits pages away from
//! the harness name that owns it, and the closing block lists the failures by
//! NAME only:
//!
//! ```text
//! Verification failed for - proofs::backoff_shifts_too_far
//! Verification failed for - proofs::shard_divides_by_zero
//! ```
//!
//! — no reason, no file, no line. To learn what to open you scrolled back
//! through the interleaved stream and matched blocks by eye.
//!
//! # How
//!
//! It renders the `--proof-summary-json` artifact rather than parsing the
//! prose stream, so it cannot drift out of step with the engine's wording, and
//! `failed_checks` carries the reason and position for each failure. When the
//! caller already asked for that artifact, theirs is reused and nothing extra
//! is written.

use std::ffi::OsString;
use std::path::{Path, PathBuf};

/// What `--summary` asked for, and where the artifact will land.
pub(crate) struct SummaryRequest {
    pub(crate) wanted: bool,
    /// A `--proof-summary-json` the caller already passed: reuse it rather
    /// than writing a second copy of the same data.
    pub(crate) existing: Option<OsString>,
}

/// Split `--summary` out of the command line.
///
/// It is a FRONT-DOOR flag: the engine has never heard of it, and passing it
/// through would be rejected as an unknown argument.
pub(crate) fn take_summary_flag(argv: &[OsString]) -> (SummaryRequest, Vec<OsString>) {
    let mut wanted = false;
    let mut existing = None;
    let mut rest = Vec::with_capacity(argv.len());
    let mut idx = 0;
    while idx < argv.len() {
        let arg = &argv[idx];
        idx += 1;
        let Some(text) = arg.to_str() else {
            rest.push(arg.clone());
            continue;
        };
        if text == "--summary" {
            wanted = true;
            continue;
        }
        // Remember the caller's own artifact path, in either spelling, and
        // still forward the flag.
        if text == "--proof-summary-json" {
            rest.push(arg.clone());
            if let Some(value) = argv.get(idx) {
                existing = Some(value.clone());
                rest.push(value.clone());
                idx += 1;
            }
            continue;
        }
        if let Some(value) = text.strip_prefix("--proof-summary-json=") {
            existing = Some(OsString::from(value));
        }
        rest.push(arg.clone());
    }
    (SummaryRequest { wanted, existing }, rest)
}

/// A per-run temporary path for the artifact, when the caller supplied none.
pub(crate) fn scratch_artifact_path() -> PathBuf {
    std::env::temp_dir().join(format!("trust-mc-summary-{}.json", std::process::id()))
}

/// How many failing checks a harness shows before the list is elided.
const MAX_DETAIL_ROWS: usize = 4;

/// One harness row, in the order this tool wants to show them.
struct Row {
    harness: String,
    proved: bool,
    /// The status word in the left column.
    ///
    /// Every non-proved harness used to read `FAILED`, which is the one word
    /// that fits three different pieces of news: the solver never decided, the
    /// assumptions were contradictory so nothing was verified, or a check
    /// really can fail. Only the third is "your code is wrong".
    label: &'static str,
    detail: Vec<String>,
}

/// The status word for a harness, from the artifact's `verdict` token.
///
/// Unknown tokens fall back to `FAILED`: the artifact is additive by contract,
/// so a token this build has never heard of must still render as "not proved"
/// rather than being dropped or crashing the table.
fn row_label(verdict: Option<&str>, proved: bool) -> &'static str {
    if proved {
        return "proved";
    }
    match verdict.unwrap_or("failed") {
        "vacuous" => "VACUOUS",
        "inconclusive_undecided" => "UNDECIDED",
        "inconclusive_no_checks" => "NO-CHECKS",
        "uncertified_counterexample" => "UNCERTIFIED",
        _ => "FAILED",
    }
}

/// Print the verdict table. Returns false when the artifact could not be read,
/// so the caller can stay quiet rather than print a broken table.
pub(crate) fn render(path: &Path) -> bool {
    let Ok(text) = std::fs::read_to_string(path) else {
        return false;
    };
    let Some(rows) = parse(&text) else {
        return false;
    };
    if rows.is_empty() {
        return false;
    }

    let proved = rows.iter().filter(|r| r.proved).count();
    let failed = rows.len() - proved;
    // The classes that are NOT "your code is wrong" get their own tally, so a
    // run whose five red rows are all "the solver ran out of budget" says so on
    // the first line. `failed` still counts every non-proved row, because that
    // is the number people already read off this header.
    let mut breakdown = String::new();
    for (label, word) in [
        ("VACUOUS", "vacuous"),
        ("UNDECIDED", "undecided"),
        ("NO-CHECKS", "no checks"),
        ("UNCERTIFIED", "uncertified"),
    ] {
        let count = rows.iter().filter(|r| r.label == label).count();
        if count > 0 {
            breakdown.push_str(&format!(" · {count} {word}"));
        }
    }
    println!();
    // "trust-mc summary" rather than "Summary": the engine's own closing block
    // is headed "Manual Harness Summary:", so a bare "Summary:" collides with
    // it — anything grepping for one finds the other. (It caught this test
    // three times before the name changed.)
    println!(
        "trust-mc summary: {} harness{} · {proved} proved · {failed} failed{breakdown}",
        rows.len(),
        if rows.len() == 1 { "" } else { "es" }
    );
    println!();

    // Failures first: they are the only rows anyone has to act on. Within a
    // group, sort by name — the engine reports in scheduler order, which
    // varies run to run and with --jobs, and a summary you cannot diff between
    // two CI runs is much less useful than one you can.
    let mut rows = rows;
    rows.sort_by(|a, b| b.proved.cmp(&a.proved).reverse().then_with(|| a.harness.cmp(&b.harness)));
    // One column width for the whole table, wide enough for the longest word
    // actually used and never narrower than `FAILED`/`proved` — so a table with
    // nothing but those two keeps exactly the layout it has always had.
    let width = rows.iter().map(|r| r.label.len()).max().unwrap_or(6).max(6);
    let indent = " ".repeat(width + 4);
    for row in rows.iter().filter(|r| !r.proved) {
        println!("  {:<width$}  {}", row.label, row.harness);
        for line in &row.detail {
            println!("{indent}{line}");
        }
    }
    if failed > 0 && proved > 0 {
        println!();
    }
    for row in rows.iter().filter(|r| r.proved) {
        // No trailing padding: a trailing run of spaces survives copy/paste and
        // shows up in every diff of captured output.
        println!("  {:<width$}  {}", row.label, row.harness);
    }
    true
}

/// Read the fields this table needs out of the artifact.
///
/// Hand-rolled rather than pulled in with a JSON dependency: the frontend has
/// none today, and `--help` / `doctor` must keep working with nothing
/// installed. Returns `None` if the shape is not what we expect, which the
/// caller turns into silence rather than a wrong table.
fn parse(text: &str) -> Option<Vec<Row>> {
    let harnesses_at = text.find("\"harnesses\"")?;
    let body = &text[harnesses_at..];
    let mut rows = Vec::new();
    for chunk in body.split("\"harness\":").skip(1) {
        let harness = json_string_after(chunk, 0)?;
        let status = field_string(chunk, "\"status\":")?;
        let effective = field_bool(chunk, "\"effective_success\":");
        let proved = effective.unwrap_or(status == "success");
        // `verdict` is the finer answer `status` cannot give; both are optional
        // here so an artifact written by an older engine still renders.
        let verdict = field_string(chunk, "\"verdict\":");
        let verdict_description = field_string(chunk, "\"verdict_description\":");
        let label = row_label(verdict, proved);

        let mut detail = Vec::new();
        if !proved {
            for check in chunk.split("\"description\":").skip(1) {
                let Some(description) = json_string_after(check, 0) else { continue };
                let where_ = position(check);
                detail.push(match where_ {
                    Some(w) => format!("{description}  ({w})"),
                    None => description,
                });
                // Collect one MORE than we will show, so the elision marker is
                // added only when something is actually elided. Breaking at
                // exactly the display limit printed "..." under a harness with
                // precisely 4 failing checks and nothing hidden — a summary
                // that claims to be hiding something it is not is worse than
                // one that shows everything.
                if detail.len() > MAX_DETAIL_ROWS {
                    break;
                }
            }
            if detail.len() > MAX_DETAIL_ROWS {
                detail.truncate(MAX_DETAIL_ROWS);
                detail.push("...".to_string());
            }
            // A row whose label is not the plain `FAILED` needs its one
            // sentence of explanation, ABOVE any checks: "every check is
            // provably unreachable" and "the solver ran out of budget" are the
            // whole finding, and for the uncertified case the caveat changes
            // what the listed checks mean. The engine ships the sentence in the
            // artifact so this table needs no copy of the vocabulary.
            if label != "FAILED"
                && let Some(reason) = verdict_description
            {
                detail.insert(0, reason.to_string());
            }
            if detail.is_empty() {
                detail.push(match (verdict_description, status) {
                    (Some(reason), _) => reason.to_string(),
                    (None, "failure") => "failed; run without --summary for the checks".to_string(),
                    (None, other) => other.to_string(),
                });
            }
        }
        rows.push(Row { harness, proved, label, detail });
    }
    Some(rows)
}

/// `file:line:column` for one failed check, as much of it as the artifact has.
fn position(chunk: &str) -> Option<String> {
    let file = field_string(chunk, "\"file\":")?;
    let line = field_string(chunk, "\"line\":");
    let column = field_string(chunk, "\"column\":");
    Some(match (line, column) {
        (Some(l), Some(c)) => format!("{file}:{l}:{c}"),
        (Some(l), None) => format!("{file}:{l}"),
        _ => file.to_string(),
    })
}

/// The next JSON string starting at or after `from`.
fn json_string_after(text: &str, from: usize) -> Option<String> {
    let open = text[from..].find('"')? + from + 1;
    let mut out = String::new();
    let mut chars = text[open..].chars();
    while let Some(c) = chars.next() {
        match c {
            '"' => return Some(out),
            '\\' => out.push(chars.next()?),
            _ => out.push(c),
        }
    }
    None
}

/// The string value of `key`, searched only within this harness's chunk.
fn field_string<'a>(chunk: &'a str, key: &str) -> Option<&'a str> {
    let at = chunk.find(key)? + key.len();
    let open = chunk[at..].find('"')? + at + 1;
    let close = chunk[open..].find('"')? + open;
    Some(&chunk[open..close])
}

fn field_bool(chunk: &str, key: &str) -> Option<bool> {
    let at = chunk.find(key)? + key.len();
    let rest = chunk[at..].trim_start();
    if rest.starts_with("true") {
        Some(true)
    } else if rest.starts_with("false") {
        Some(false)
    } else {
        None
    }
}

#[cfg(test)]
#[path = "summary_tests.rs"]
mod tests;
