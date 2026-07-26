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

fn rustup_toolchain_lib() -> Option<String> {
    let rustup_home = env::var("RUSTUP_HOME").ok()?;
    let rustup_tc = env::var("RUSTUP_TOOLCHAIN").ok()?;
    Some(path_str!([&rustup_home, "toolchains", &rustup_tc, "lib"]))
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

fn rustc_driver_rpath() -> String {
    rustup_toolchain_lib()
        .or_else(active_rustc_sysroot_lib)
        .expect("RUSTUP_HOME/RUSTUP_TOOLCHAIN must be set, or RUSTC must print a sysroot")
}

/// Configure the compiler to build the trust-mc-compiler binary. We currently support building
/// trust-mc-compiler with nightly only. The rpath follows rustup in dev builds and
/// falls back to the active RUSTC sysroot for self-contained toolchains.
pub fn main() {
    println!("cargo:rerun-if-env-changed=RUSTUP_HOME");
    println!("cargo:rerun-if-env-changed=RUSTUP_TOOLCHAIN");
    println!("cargo:rerun-if-env-changed=RUSTC");
    let rustc_lib = rustc_driver_rpath();
    println!("cargo:rustc-link-arg-bin=trust-mc-compiler=-Wl,-rpath,{rustc_lib}");

    // While we hard-code the above for development purposes, for a release/install we look
    // in a relative location for a symlink to the local rust toolchain
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
    // as trust_mc-driver/build.rs).
    println!("cargo:rerun-if-changed=.git/HEAD");
    if let Ok(head_content) = std::fs::read_to_string(".git/HEAD")
        && let Some(ref_path) = head_content.trim().strip_prefix("ref: ")
    {
        println!("cargo:rerun-if-changed=.git/{ref_path}");
    }
}
