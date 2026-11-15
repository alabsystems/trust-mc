// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Source lint: the engine spawns no external tool (design trust-mc-reds-final
//! §7.1, E1 + E2).
//!
//! Every `.rs` file under `trust-mc-compiler/src/` — tests included, since that
//! is where the spawns were — is scanned after its comments and string literals
//! are removed, and none may spell `Command::new`. The engine's solver is ay,
//! linked in process; its compiler is the `librustc_driver` it links. A tool
//! taken by bare name from PATH is not the one a measurement names: the test
//! oracles that spawned `z3` and `rustc` that way failed on a host where the
//! names resolve to a launcher that refuses them, and on another host they
//! would have silently run a different solver or compiler.
//!
//! The ALLOWLIST is empty. Scope stated: the driver (`trust-mc-driver`) spawns
//! `git` and its route tests spawn `cargo`; those are outside this lint (design
//! residual 7).
//!
//! Evidence rung: a test. Run by `scripts/check-trust-lane-build.sh`
//! (`-- single_rule no_tool_by_name`).

#![allow(clippy::unwrap_used)]

use std::path::Path;

use super::test_source_scan::{collect_rs_files, strip_comments_and_strings, tokens};

/// Files (relative to `trust-mc-compiler/src/`) allowed to spawn a process.
const ALLOWLIST: &[&str] = &[];

fn spawns_in(src: &str) -> Vec<usize> {
    let toks = tokens(&strip_comments_and_strings(src));
    let seq = ["Command", "::", "new", "("];
    (0..toks.len())
        .filter(|&i| {
            toks.len() - i >= seq.len() && seq.iter().zip(&toks[i..]).all(|(w, (g, _))| w == g)
        })
        .map(|i| toks[i].1)
        .collect()
}

#[test]
fn no_tool_by_name_in_engine_sources() {
    let root = Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../trust-mc-compiler/src"));
    let mut files = Vec::new();
    collect_rs_files(root, &mut files);
    assert!(files.len() > 200, "expected to scan trust-mc-compiler/src, found {}", files.len());
    let mut report = Vec::new();
    for path in &files {
        let rel = path.strip_prefix(root).unwrap().to_string_lossy().replace('\\', "/");
        if ALLOWLIST.contains(&rel.as_str()) {
            continue;
        }
        for line in spawns_in(&std::fs::read_to_string(path).unwrap()) {
            report.push(format!("  trust-mc-compiler/src/{rel}:{line}: `Command::new`"));
        }
    }
    assert!(
        report.is_empty(),
        "the engine spawns a process (solve with ay in process; compile with the linked \
         librustc_driver):\n{}",
        report.join("\n")
    );
}

#[test]
fn no_tool_by_name_scanner_sees_code_not_comments() {
    assert_eq!(spawns_in("fn f() {\n    let c = Command::new(\"z3\");\n}"), vec![2]);
    assert_eq!(spawns_in("fn f() {\n let c = std::process::Command :: new(p);\n}"), vec![2]);
    assert!(spawns_in("// Command::new(\"z3\")\nfn f() {}").is_empty());
    assert!(spawns_in("fn f() -> &'static str { \"Command::new(rustc)\" }").is_empty());
}
