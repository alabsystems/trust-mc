// Copyright Kani Contributors
// Modifications Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::env::var;
use std::process::Command;

#[path = "../src/build_frontend.rs"]
mod build_frontend;

fn main() {
    // The sysroot of the compiler building this crate. `build-dev` builds
    // trust-mc-compiler in the same cargo invocation, so its `bin/targo` is the
    // cargo the DevCli route must run (src/session/cargo.rs) -- found here, not
    // through rustup, whose channel a targo build never names. A compiler that
    // cannot report a sysroot records nothing, and the driver then refuses.
    // (No `TRUST_` prefix: authenticated Targo refuses build-script
    // `rustc-env` names in that authority namespace.) Only the `cli` binary
    // reads it, so the library build the trust superproject's bootstrap makes
    // (default-features = false, through bootstrap's rustc shim) is unchanged.
    // A release bundle (`MC_RELEASE_BUNDLE`, set by `build-trust-mc bundle`)
    // records none: the build host's seal path means nothing where the bundle is
    // installed, which runs its own `toolchain/bin/targo` instead.
    if var("CARGO_FEATURE_CLI").is_ok() {
        println!("cargo:rerun-if-env-changed=RUSTC");
        println!("cargo:rerun-if-env-changed=MC_RELEASE_BUNDLE");
        let release_bundle = std::env::var_os("MC_RELEASE_BUNDLE").is_some();
        println!("cargo:rustc-env=MC_DRIVER_RELEASE_BUNDLE={}", u8::from(release_bundle));
        // Packaged AY authority must never read this development checkout.
        let workspace_root = if release_bundle {
            String::new()
        } else {
            var("CARGO_MANIFEST_DIR").expect("Cargo supplies the package directory")
        };
        println!("cargo:rustc-env=MC_DRIVER_BUILD_WORKSPACE_ROOT={workspace_root}");
        println!("cargo:rerun-if-env-changed=RUSTUP_TOOLCHAIN");
        // A missing Targo is never a reason to fall back to Cargo on Trust.
        // Record the frontend's build identity; the only stock exception is
        // the explicitly selected, frozen Kani comparison oracle.
        let verbose = var("RUSTC")
            .ok()
            .and_then(|rustc| Command::new(rustc).arg("-vV").output().ok())
            .filter(|out| out.status.success())
            .map(|out| String::from_utf8_lossy(&out.stdout).into_owned())
            .unwrap_or_default();
        let host = var("HOST").unwrap_or_default();
        let channel = var("RUSTUP_TOOLCHAIN").ok();
        let sysroot = var("RUSTC")
            .ok()
            .and_then(|rustc| Command::new(rustc).args(["--print", "sysroot"]).output().ok())
            .filter(|out| out.status.success())
            .map(|out| String::from_utf8_lossy(&out.stdout).trim().to_string())
            .filter(|sysroot| !sysroot.is_empty() && !sysroot.contains('\n'));
        let frontend = build_frontend::classify(
            &verbose,
            channel.as_deref(),
            &host,
            sysroot.as_deref().map(std::path::Path::new),
        );
        println!("cargo:rustc-env=MC_DRIVER_BUILD_FRONTEND={frontend}");
        if !release_bundle && let Some(sysroot) = sysroot {
            println!("cargo:rustc-env=MC_DRIVER_BUILD_SYSROOT={sysroot}");
        }
    }

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
    //
    // The paths MUST be resolved through `git rev-parse --git-path`, never
    // spelled as a literal `.git/HEAD`: build scripts run with cwd = this
    // package dir (trust-mc-driver/), where no `.git` exists at all — the
    // repository's git dir is one level up, and when trust-mc is consumed as a
    // git submodule (trust's first-party/trust-mc) it is a gitlink FILE whose
    // real dir lives under the superproject's `.git/modules/...`. Cargo treats
    // a `rerun-if-changed` path that does not exist as ALWAYS DIRTY, so the
    // literal spelling re-ran this script on every cargo invocation and
    // recompiled trust-mc-driver -> trust-bmc -> trust-router -> targo-trust
    // and rustc_mir_transform -> rustc_driver each time. Measured in trust's
    // `x.py build --stage 2` (2026-08-22, aarch64-apple-darwin, seed
    // 1.99.0-trust): every re-invocation relinked the stage1 trustc (53s) and
    // rebuilt stage1 std (49s), and the fresher stage1 trustc mtime made
    // bootstrap's clear_if_dirty wipe the stage2 tool target dirs, so stage2
    // cargo (3m21s) and stage2 targo-trust (~600 crates) restarted from zero
    // on every run — the build could never converge under a 10-minute
    // per-invocation budget. A path that cannot be resolved or does not exist
    // is simply not registered (the GIT_* values then refresh only when some
    // other input changes), which is the documented fallback for tarball /
    // non-git installs anyway.
    let git_path = |rel: &str| -> Option<String> {
        let out = Command::new("git")
            .args(["rev-parse", "--git-path", rel])
            .output()
            .ok()
            .filter(|o| o.status.success())?;
        let path = String::from_utf8_lossy(&out.stdout).trim().to_string();
        (!path.is_empty() && std::path::Path::new(&path).is_file()).then_some(path)
    };
    if let Some(head) = git_path("HEAD") {
        println!("cargo:rerun-if-changed={head}");
    }
    // Track the ref file that HEAD points to (e.g., refs/heads/main) so we
    // detect new commits on the current branch. `symbolic-ref -q` fails on a
    // detached HEAD (the normal submodule state), and a packed ref has no
    // loose file — both cases fall through to HEAD alone, which still changes
    // on every checkout/commit in those states.
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
