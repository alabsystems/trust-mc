// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Triage: group non-parity harnesses by normalized root cause so the burndown
//! points straight at the highest-frequency gaps to close next.

use std::collections::BTreeMap;

use crate::model::{Classification, TestResult};

struct Bucket {
    count: usize,
    examples: Vec<String>,
}

/// Normalize a result's note/markers into a stable root-cause key: strip
/// absolute paths, run-specific numbers, and durations so like causes collapse.
fn root_cause_key(r: &TestResult) -> String {
    let class = r.classification.map(Classification::as_str).unwrap_or("?");
    let mut note = r.note.clone();
    if note.is_empty() {
        note = match r.ctrex_category.as_deref() {
            Some(c) => format!("ctrex={c}"),
            None => "(no note)".to_string(),
        };
    }
    // Collapse paths and digits to make causes comparable.
    let mut out = String::with_capacity(note.len());
    let mut last_was_num = false;
    for ch in note.chars() {
        if ch == '/' {
            // Drop path segments down to a placeholder.
            if !out.ends_with('…') {
                out.push('…');
            }
        } else if ch.is_ascii_digit() {
            if !last_was_num {
                out.push('#');
            }
            last_was_num = true;
            continue;
        } else {
            out.push(ch);
        }
        last_was_num = false;
    }
    let head: String = out.split_whitespace().take(14).collect::<Vec<_>>().join(" ");
    format!("[{class}] {}", head.chars().take(140).collect::<String>())
}

pub fn render_triage(results: &[TestResult], only: Option<&str>, top: usize) -> String {
    let mut buckets: BTreeMap<String, Bucket> = BTreeMap::new();
    let mut considered = 0usize;
    for r in results {
        let class = r.classification.unwrap_or(Classification::Skipped);
        if class.is_parity() {
            continue;
        }
        if let Some(filter) = only {
            if class.as_str() != filter {
                continue;
            }
        }
        considered += 1;
        let key = root_cause_key(r);
        let b = buckets.entry(key).or_insert(Bucket { count: 0, examples: Vec::new() });
        b.count += 1;
        if b.examples.len() < 3 {
            b.examples.push(format!("{}/{}", r.suite, r.file));
        }
    }
    let mut ranked: Vec<(&String, &Bucket)> = buckets.iter().collect();
    ranked.sort_by(|a, b| b.1.count.cmp(&a.1.count).then(a.0.cmp(b.0)));

    let mut o = String::new();
    o.push_str(&format!(
        "Triage — {considered} non-parity harness(es){}, {} distinct root cause(s):\n\n",
        only.map(|f| format!(" (class={f})")).unwrap_or_default(),
        ranked.len()
    ));
    for (key, b) in ranked.into_iter().take(top) {
        o.push_str(&format!("{:>4}  {}\n", b.count, key));
        o.push_str(&format!("      e.g. {}\n", b.examples.join(" · ")));
    }
    o
}
