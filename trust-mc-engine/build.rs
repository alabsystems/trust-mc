// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Build script for the trust-mc engine rlib.
//!
//! The engine's sources live in `trust-mc-compiler/src` (see `Cargo.toml`), so
//! this script carries the two compile-time facts those sources read:
//!
//! * `cfg(trust_toolchain)`, which selects the Trust compiler's rustc_public /
//!   rustc_middle API shapes (see `src/rustc_compat.rs`). Without it the crate
//!   compiles against the frozen nightly-2025-12-03 API -- STOCK-AS-ORACLE:
//!   that nightly comparison baseline only, kept by the owner's ruling of
//!   2026-09-29.
//! * `TRUST_MC_GIT_SHA` / `TRUST_MC_GIT_DIRTY`, the provenance of this build.
//!
//! It emits no link arguments. The embedded binary (`trust-mc-compiler`) owns
//! its rpath, and the backend cdylib must carry none.

use std::env;
use std::process::Command;

/// Whether the compiler Cargo selected (`RUSTC`) is the Trust toolchain.
///
/// Trust identifies itself with a `trust:` line in `rustc -vV`; stock rustup
/// nightlies (the frozen Kani-compatibility lane) print no such line. Any failure
/// to run the probe answers `false`, which selects the frozen-nightly code paths:
/// on a Trust compiler those fail to type-check loudly rather than silently
/// compiling a different program.
fn rustc_is_trust_toolchain() -> bool {
    let Some(rustc) = env::var_os("RUSTC") else {
        return false;
    };
    let Ok(output) = Command::new(rustc).arg("-vV").output() else {
        return false;
    };
    output.status.success()
        && String::from_utf8_lossy(&output.stdout).lines().any(|line| line.starts_with("trust:"))
}

pub fn main() {
    println!("cargo:rerun-if-env-changed=RUSTC");

    println!("cargo::rustc-check-cfg=cfg(trust_toolchain)");
    if rustc_is_trust_toolchain() {
        println!("cargo:rustc-cfg=trust_toolchain");
    }

    // Symmetric to trust-mc-compiler/build.rs and trust_mc-driver/build.rs:
    // `unknown-sha` on tarball installs, which the staleness shim skips.
    let commit_hash_full = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown-sha".to_string());

    let dirty = Command::new("git")
        .args(["diff-index", "--quiet", "HEAD", "--"])
        .status()
        .ok()
        .map(|s| if s.success() { "0" } else { "1" })
        .unwrap_or("0");

    println!("cargo:rustc-env=TRUST_MC_GIT_SHA={commit_hash_full}");
    println!("cargo:rustc-env=TRUST_MC_GIT_DIRTY={dirty}");

    // Resolve the git paths through `git rev-parse --git-path`: this script
    // runs in the package directory, where no `.git` exists (and in a worktree
    // or submodule `.git` is a file). Cargo treats a missing rerun-if-changed
    // path as always dirty, so a literal `.git/HEAD` reran this script and
    // recompiled the crate on every invocation. Paths that do not resolve to an
    // existing file (no git, a packed ref) are not registered. Same approach as
    // trust-mc-driver/build.rs.
    let git_path = |rel: &str| -> Option<String> {
        let out = Command::new("git")
            .args(["rev-parse", "--path-format=absolute", "--git-path", rel])
            .output()
            .ok()
            .filter(|o| o.status.success())?;
        let path = String::from_utf8_lossy(&out.stdout).trim().to_string();
        (!path.is_empty() && std::path::Path::new(&path).is_file()).then_some(path)
    };
    if let Some(head) = git_path("HEAD") {
        println!("cargo:rerun-if-changed={head}");
    }
    let symbolic_ref = Command::new("git")
        .args(["symbolic-ref", "-q", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .filter(|r| !r.is_empty());
    if let Some(ref_path) = symbolic_ref {
        if let Some(ref_file) = git_path(&ref_path) {
            println!("cargo:rerun-if-changed={ref_file}");
        } else {
            // The branch ref is packed (`git pack-refs`, or an automatic gc
            // run by any worktree of the repository), so it has no loose
            // file, and in a linked worktree HEAD ("ref: refs/heads/<b>")
            // does not change on a commit. A commit made after packing then
            // left the embedded sha stale (measured 2026-09-27: a bundle
            // built after commit 63fd640bf reported 70aecce71, dirty). Watch
            // `packed-refs` and the directory the next commit writes the
            // loose ref into; only existing paths are registered.
            if let Some(packed) = git_path("packed-refs") {
                println!("cargo:rerun-if-changed={packed}");
            }
            if let Some(dir) = Command::new("git")
                .args(["rev-parse", "--path-format=absolute", "--git-path", &ref_path])
                .output()
                .ok()
                .filter(|o| o.status.success())
                .map(|o| std::path::PathBuf::from(String::from_utf8_lossy(&o.stdout).trim()))
                .and_then(|loose| loose.parent().map(std::path::Path::to_path_buf))
                .filter(|dir| dir.is_dir())
            {
                println!("cargo:rerun-if-changed={}", dir.display());
            }
        }
    }
}
