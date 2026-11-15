// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! In order to avoid introducing a large amount of OS-specific workarounds into the main
//! "flow" of code in setup.rs, this module contains all functions that implement os-specific
//! workarounds.

use std::path::Path;
use std::process::Command;
use std::time::Duration;

use anyhow::{Context, Result};
use os_info::Info;

use crate::cmd::AutoRun;

/// Timeout for patchelf operations (30 seconds per file).
const PATCHELF_TIMEOUT: Duration = Duration::from_secs(30);

/// This is the final step of setup, where we look for OSes that require additional setup steps
/// beyond the usual ones that we have done already.
pub(crate) fn setup_os_hacks(kani_dir: &Path, os: &Info) -> Result<()> {
    match os.os_type() {
        os_info::Type::NixOS => setup_nixos_patchelf(kani_dir),
        os_info::Type::Linux => {
            // NixOs containers are detected as Unknown Linux, so use a fallback hack:
            if std::env::var_os("NIX_CC").is_some() && Path::new("/etc/nix").exists() {
                return setup_nixos_patchelf(kani_dir);
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// On NixOS, the dynamic linker does not live at the standard path, and so our downloaded
/// pre-built binaries need patching. (The bundle no longer ships upstream Kani's kissat
/// SAT solver, which also needed a C++ standard library rpath: trust-mc's solver is ay.)
fn setup_nixos_patchelf(kani_dir: &Path) -> Result<()> {
    // Encode our assumption that we're working on x86 here, because when we add ARM
    // support, we need to look for a different path.
    // Prevents clippy error.
    let target = "x86_64-unknown-linux-gnu";
    assert_eq!(env!("TARGET"), target);
    if let Ok(linker) = Path::new("/lib64/ld-linux-x86-64.so.2").canonicalize()
        && linker.exists()
        && !linker.to_string_lossy().contains("-stub-ld-")
    {
        // looks like a valid linker, I guess things are fine?
        return Ok(());
    }

    println!("[NixOS detected] Applying 'patchelf' to downloaded binaries");

    // Find the correct dynamic linker:
    // `interp=$(cat $NIX_CC/nix-support/dynamic-linker)`
    let nix_cc = std::env::var_os("NIX_CC")
        .context("On NixOS but 'NIX_CC` environment variable not set, couldn't apply patchelf.")?;
    let path = Path::new(&nix_cc).join("nix-support/dynamic-linker");
    let interp_raw = std::fs::read_to_string(path)
        .context("Couldn't read $NIX_CC/nix-support/dynamic-linker")?;
    let interp = interp_raw.trim();

    let patch_interp = |file: &Path| -> Result<()> {
        Command::new("patchelf")
            .args(["--set-interpreter", interp])
            .arg(file)
            .run_with_timeout(PATCHELF_TIMEOUT)
    };

    let bin = kani_dir.join("bin");

    for filename in &["trust-mc-compiler", "trust-mc-driver"] {
        patch_interp(&bin.join(filename))?;
    }

    Ok(())
}
