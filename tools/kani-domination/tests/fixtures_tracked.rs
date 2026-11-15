// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Every file the sources `include_str!`/`include_bytes!` must be one git can
//! track. The scorer tests embed 14 driver transcripts named `*.out`, which the
//! repository root's `.gitignore` (`*.out`) kept out of every commit: the tests
//! compiled only on the machine that wrote them, and a fresh checkout failed with
//! `couldn't read src/fixtures/self-report/kani__Invariant__percentage.rs.out`.
//!
//! An integration test on purpose: it compiles without the unit-test module, so
//! it reports the ignored paths even when those `include_str!`s cannot build.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Every `include_str!("…")` / `include_bytes!("…")` literal path in `file`,
/// resolved against the file's own directory (the macros' rule).
fn included_paths(file: &Path) -> Vec<PathBuf> {
    let text = std::fs::read_to_string(file).expect("read a source file");
    let dir = file.parent().expect("a source file has a directory");
    let mut out = Vec::new();
    for mac in ["include_str!(\"", "include_bytes!(\""] {
        let mut rest = text.as_str();
        while let Some(i) = rest.find(mac) {
            let after = &rest[i + mac.len()..];
            let end = after.find('"').expect("a closed string literal");
            out.push(dir.join(&after[..end]));
            rest = &after[end..];
        }
    }
    out
}

fn rust_sources(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).expect("read a source directory") {
        let path = entry.expect("a directory entry").path();
        if path.is_dir() {
            rust_sources(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

/// `git check-ignore --no-index` answers from the ignore rules alone, so a
/// path is caught whether or not it is tracked, or even present.
fn ignored_by_git(path: &Path) -> bool {
    let status = Command::new("git")
        .arg("-C")
        .arg(path.parent().expect("a path with a directory"))
        .args(["check-ignore", "--no-index", "-q", "--"])
        .arg(path.file_name().expect("a file name"))
        .status()
        .expect("git is on PATH (this test reads the repository's ignore rules)");
    match status.code() {
        Some(0) => true,
        Some(1) => false,
        other => panic!(
            "git check-ignore failed ({other:?}) for {}: not inside a git work tree?",
            path.display()
        ),
    }
}

#[test]
fn every_embedded_fixture_is_trackable_by_git() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut sources = Vec::new();
    rust_sources(&src, &mut sources);
    let embedded: Vec<PathBuf> = sources.iter().flat_map(|f| included_paths(f)).collect();
    assert!(
        embedded.iter().filter(|p| p.starts_with(src.join("fixtures"))).count() >= 18,
        "the scorer tests embed at least the 18 files under src/fixtures/: {embedded:#?}"
    );
    let ignored: Vec<&PathBuf> = embedded.iter().filter(|p| ignored_by_git(p)).collect();
    assert!(
        ignored.is_empty(),
        "these embedded files are git-ignored, so a fresh checkout cannot compile the tests: {ignored:#?}"
    );
}
