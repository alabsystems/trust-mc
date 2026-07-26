// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Static pattern lint: verify that SOUND fallback sites maintain the
//! fresh-symbolic invariant. Part of #4165, #134.
//!
//! The critical invariant: `record_sound_fallback_reason` and
//! `record_sound_fallback_categorized` call sites must produce fresh
//! unconstrained symbolic values (over-approximation). A SOUND site that
//! returns a concrete value (e.g., `false`, `0`) can produce a **false PROOF**
//! that bypasses BMC cross-check entirely (#3897 class).
//!
//! This test scans production source files for dangerous concrete-value
//! patterns near SOUND fallback recording calls and fails if any are found.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use std::path::{Path, PathBuf};

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                collect_rs_files(&path, out);
            } else if path.extension() == Some("rs".as_ref()) {
                out.push(path);
            }
        }
    }
}

/// Returns true if the line is inside a test module or test function context.
fn is_test_context(lines: &[&str], line_idx: usize) -> bool {
    // Look backwards for #[test] or #[cfg(test)] or mod tests
    let start = line_idx.saturating_sub(30);
    for i in (start..line_idx).rev() {
        let l = lines[i].trim();
        if l == "#[test]" || l == "#[cfg(test)]" || l.starts_with("mod test") {
            return true;
        }
        // Stop searching if we hit a function definition (we've left the context)
        if l.starts_with("pub fn ") || l.starts_with("fn ") || l.starts_with("pub(") {
            break;
        }
    }
    false
}

/// Part of #4165, #134: Verify that SOUND fallback sites maintain the
/// fresh-symbolic invariant. Scans production CHC source for dangerous
/// concrete-value patterns near `record_sound_fallback_reason` /
/// `record_sound_fallback_categorized` calls.
#[test]
fn test_sound_fallback_sites_use_fresh_symbolic() {
    let chc_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/codegen_ay/chc");

    let mut violations = Vec::new();

    let mut rs_files = Vec::new();
    collect_rs_files(&chc_dir, &mut rs_files);

    // Dangerous patterns: concrete values that should never appear near a
    // SOUND fallback site. If a SOUND site returns one of these instead of
    // a fresh symbolic, it can produce false proofs (#3897 class).
    let dangerous_patterns: &[&str] = &[
        "Bool::from(false)",
        "Bool::from(true)",
        "Int::from_i64(0)",
        "Int::from_i64(1)",
        "Bool::FALSE",
        "Bool::TRUE",
    ];

    for path in &rs_files {
        let path_str = path.to_str().unwrap_or("");
        // Skip test files and backup files
        if path_str.contains("/tests/") || path_str.contains(".worker_backup") {
            continue;
        }
        let content = match std::fs::read_to_string(path) {
            Ok(c) => c,
            Err(_) => continue,
        };
        let lines: Vec<&str> = content.lines().collect();

        for (i, line) in lines.iter().enumerate() {
            // Only check lines that actually call the SOUND fallback recording
            if !line.contains("record_sound_fallback_reason")
                && !line.contains("record_sound_fallback_categorized")
            {
                continue;
            }
            // Skip function definitions (the fn signature itself)
            if line.contains("fn record_sound_fallback") {
                continue;
            }
            // Skip if this is inside test code
            if is_test_context(&lines, i) {
                continue;
            }

            // Check surrounding context (10 lines before, 10 after)
            let start = i.saturating_sub(10);
            let end = (i + 11).min(lines.len());
            let context_str = lines[start..end].join("\n");

            for pattern in dangerous_patterns {
                if context_str.contains(pattern) {
                    // Extract relative path for readable output
                    let rel = path_str
                        .find("src/codegen_ay/chc/")
                        .map(|pos| &path_str[pos..])
                        .unwrap_or(path_str);
                    violations.push(format!(
                        "  {}:{} — concrete value '{}' near SOUND fallback",
                        rel,
                        i + 1,
                        pattern,
                    ));
                }
            }
        }
    }

    assert!(
        violations.is_empty(),
        "SOUND fallback sites must use fresh symbolic values, not concrete.\n\
         Violations (#3897 class — false proof risk):\n{}",
        violations.join("\n")
    );
}

/// Part of #4165: Verify the `record_sound_fallback_concrete_override` method
/// exists and increments both the sound fallback counter AND the demoted
/// fallback counter (triggering BMC cross-check).
#[test]
fn test_sound_fallback_concrete_override_increments_both_counters() {
    use super::common::*;

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn override_probe(x: u32) -> u32 { x }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "override_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "override_probe", ChcConfig::default());

        let before_sound = chc_ctx.sound_fallback_count();
        let before_demoted = chc_ctx.fallback_count;

        chc_ctx.record_sound_fallback_concrete_override("test_concrete_override_probe");

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound + 1,
            "concrete override must increment sound fallback counter"
        );
        assert_eq!(
            chc_ctx.fallback_count,
            before_demoted + 1,
            "concrete override must increment demoted fallback counter \
             (triggers BMC cross-check)"
        );
    });
}

/// Part of #4165: Verify that no production code currently calls
/// `record_sound_fallback_concrete_override`. This method exists as a
/// safety valve — 0 initial callers is correct.
#[test]
fn test_no_production_callers_of_concrete_override() {
    let chc_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/codegen_ay/chc");

    let mut rs_files = Vec::new();
    collect_rs_files(&chc_dir, &mut rs_files);

    let mut callers = Vec::new();

    for path in &rs_files {
        let path_str = path.to_str().unwrap_or("");
        if path_str.contains("/tests/") || path_str.contains(".worker_backup") {
            continue;
        }
        let content = match std::fs::read_to_string(path) {
            Ok(c) => c,
            Err(_) => continue,
        };

        for (i, line) in content.lines().enumerate() {
            if line.contains("record_sound_fallback_concrete_override") {
                // Skip the method definition itself
                if line.contains("fn record_sound_fallback_concrete_override") {
                    continue;
                }
                let rel = path_str
                    .find("src/codegen_ay/chc/")
                    .map(|pos| &path_str[pos..])
                    .unwrap_or(path_str);
                callers.push(format!("  {}:{}", rel, i + 1));
            }
        }
    }

    assert!(
        callers.is_empty(),
        "record_sound_fallback_concrete_override should have 0 production callers \
         initially. Found {} caller(s):\n{}",
        callers.len(),
        callers.join("\n")
    );
}
