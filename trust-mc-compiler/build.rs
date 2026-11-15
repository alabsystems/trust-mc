// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::env;
use std::path::PathBuf;
use std::process::Command;

macro_rules! path_str {
    ($input:expr) => {
        String::from(
            $input
                .iter()
                .collect::<PathBuf>()
                .to_str()
                .unwrap_or_else(|| panic!("Invalid path {}", stringify!($input))),
        )
    };
}

fn active_rustc_sysroot_lib() -> Option<String> {
    let rustc = env::var_os("RUSTC")?;
    let output = Command::new(rustc).args(["--print", "sysroot"]).output().ok()?;
    if !output.status.success() {
        return None;
    }
    let sysroot = String::from_utf8(output.stdout).ok()?;
    let sysroot = sysroot.trim();
    if sysroot.is_empty() {
        return None;
    }
    Some(path_str!([sysroot, "lib"]))
}

/// `<sysroot>/lib` of the compiler cargo builds this crate with, which holds the
/// `librustc_driver` it links: the Trust seal under `targo`. Not a rustup
/// toolchain directory: that follows a moving channel link (and a targo build
/// sets no `RUSTUP_TOOLCHAIN`), while the sysroot names the exact build.
fn rustc_driver_rpath() -> String {
    active_rustc_sysroot_lib().expect("RUSTC must print a sysroot (`$RUSTC --print sysroot`)")
}

/// Set by `build-trust-mc bundle` (tools/build-trust-mc/src/release.rs) for the
/// release build: the binary then carries no absolute path to the build seal.
const RELEASE_BUNDLE_ENV: &str = "MC_RELEASE_BUNDLE";

/// Configure the compiler to build the trust-mc-compiler binary: a rustc driver
/// rpath'd to the `librustc_driver` of the compiler that builds it (the Trust
/// seal; the frozen comparison nightly on that lane).
pub fn main() {
    println!("cargo:rerun-if-env-changed=RUSTC");
    println!("cargo:rerun-if-env-changed={RELEASE_BUNDLE_ENV}");

    // A development build runs from target/ against the seal that built it, so
    // it is rpath'd to that seal's lib by absolute path. A release bundle is
    // installed elsewhere and must not name the build host's seal (a $HOME path,
    // and on the build host a driver dyld would load ahead of the installed
    // link): it keeps only the relative rpath below.
    if env::var_os(RELEASE_BUNDLE_ENV).is_none() {
        let rustc_lib = rustc_driver_rpath();
        println!("cargo:rustc-link-arg-bin=trust-mc-compiler=-Wl,-rpath,{rustc_lib}");
    }

    // An installed bundle (and the release build's own target/trust-mc) links the
    // seal as `toolchain` beside `bin` (`trust-mc setup --use-local-toolchain`).
    let origin = if cfg!(target_os = "macos") { "@loader_path" } else { "$ORIGIN" };
    println!("cargo:rustc-link-arg-bin=trust-mc-compiler=-Wl,-rpath,{origin}/../toolchain/lib");

    // Capture git commit hash so the staleness-check shim (`scripts/cargo-trust_mc`)
    // can detect when an installed compiler is out of date. Symmetric to
    // trust_mc-driver/build.rs — see that file for the full rationale. Falls back
    // to `unknown-sha` on tarball installs; the shim treats that as "skip
    // check".
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

    // Only rebuild when HEAD changes, not on every `git add` (same tradeoff
    // as trust_mc-driver/build.rs). The engine's `cfg(trust_toolchain)` probe
    // lives in trust-mc-engine/build.rs; nothing in this package reads it.
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
