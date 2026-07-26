// Copyright Kani Contributors
// Modifications Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::env::var;
use std::process::Command;

fn main() {
    // We want to know what target triple we were built with, but this isn't normally provided to us.
    // Note the difference between:
    // https://doc.rust-lang.org/cargo/reference/environment-variables.html#environment-variables-cargo-sets-for-crates
    // https://doc.rust-lang.org/cargo/reference/environment-variables.html#environment-variables-cargo-sets-for-build-scripts
    // So "repeat" the info from build script (here) to our crate's build environment.
    let target = var("TARGET").expect("TARGET env var must be set by Cargo for build scripts");
    println!("cargo:rustc-env=TARGET={target}");

    // Capture git commit hash for development version info (#387).
    let commit_hash_short = Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());

    // Also capture the full-length commit hash for the staleness-check shim
    // (`scripts/cargo-trust-mc`). The shim compares this to `git rev-parse HEAD`
    // and refuses to run if the installed binary is behind the repo.
    //
    // Fall back to `unknown-sha` on tarball/non-git installs. The shim treats
    // `unknown-sha` as "skip check with an info line" so bootstrap builds are
    // not blocked (see scripts/cargo-trust-mc).
    let commit_hash_full = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown-sha".to_string());

    // Cheap dirty detection. `git diff-index --quiet HEAD --` exits 0 when
    // the tracked tree matches HEAD and 1 when it differs. It does NOT scan
    // untracked files (those don't affect reproducibility) so it is fast
    // even on large trees. We intentionally do NOT emit rerun-if-changed on
    // the working tree — this flag reflects the tree state at the last
    // rebuild, which is the right granularity: any source edit triggers a
    // rebuild, which re-runs this script, which refreshes the flag.
    let dirty = Command::new("git")
        .args(["diff-index", "--quiet", "HEAD", "--"])
        .status()
        .ok()
        .map(|s| if s.success() { "0" } else { "1" })
        .unwrap_or("0");

    println!("cargo:rustc-env=GIT_COMMIT={commit_hash_short}");
    println!("cargo:rustc-env=TRUST_MC_GIT_SHA={commit_hash_full}");
    println!("cargo:rustc-env=TRUST_MC_GIT_DIRTY={dirty}");

    // Only rebuild when HEAD changes (new commit), not on every staging operation.
    // Previously included `.git/index` which triggered rebuilds on every `git add`.
    println!("cargo:rerun-if-changed=.git/HEAD");
    // Track the ref file that HEAD points to (e.g., refs/heads/main) so we
    // detect new commits on the current branch.
    if let Ok(head_content) = std::fs::read_to_string(".git/HEAD")
        && let Some(ref_path) = head_content.trim().strip_prefix("ref: ")
    {
        println!("cargo:rerun-if-changed=.git/{ref_path}");
    }
}
