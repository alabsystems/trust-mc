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

use anyhow::{Context, Result, bail};
use os_info::Info;

use crate::cmd::AutoRun;

/// Timeout for nix-instantiate operations (2 minutes).
const NIX_TIMEOUT: Duration = Duration::from_secs(120);
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
/// pre-built binaries need patching.
/// In addition, the C++ standard library (needed by the kissat SAT solver) also does not
/// have a standard path, and so we need to inject an rpath into that binary to get it
/// to successfully link at runtime.
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

    // Find the correct path to link C++ stdlib:
    // `rpath=$(nix-instantiate --eval -E "(import <nixpkgs> {}).stdenv.cc.cc.lib.outPath")/lib`
    // Use timeout to prevent hanging on slow nix evaluation.
    let rpath_output = run_nix_instantiate()?;
    let rpath_raw = std::str::from_utf8(&rpath_output)?;
    // The output is in quotes, remove them:
    let rpath_prefix = rpath_raw.trim().trim_matches('"');
    let rpath = format!("{rpath_prefix}/lib");

    let patch_interp = |file: &Path| -> Result<()> {
        Command::new("patchelf")
            .args(["--set-interpreter", interp])
            .arg(file)
            .run_with_timeout(PATCHELF_TIMEOUT)
    };
    let patch_rpath = |file: &Path| -> Result<()> {
        Command::new("patchelf")
            .args(["--set-rpath", &rpath])
            .arg(file)
            .run_with_timeout(PATCHELF_TIMEOUT)
    };

    let bin = kani_dir.join("bin");

    for filename in &["trust-mc-compiler", "trust-mc-driver"] {
        patch_interp(&bin.join(filename))?;
    }
    let kissat = bin.join("kissat");
    patch_interp(&kissat)?;
    patch_rpath(&kissat)?;

    Ok(())
}

/// Run nix-instantiate with a timeout to find C++ stdlib path.
///
/// Returns the stdout bytes on success, or an error if the command fails or times out.
fn run_nix_instantiate() -> Result<Vec<u8>> {
    use std::process::Stdio;
    use std::sync::mpsc;

    let child = Command::new("nix-instantiate")
        .args(["--eval", "-E", "(import <nixpkgs> {}).stdenv.cc.cc.lib.outPath"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    #[cfg(unix)]
    let child_pid = child.id();

    let (tx, rx) = mpsc::channel();

    std::thread::spawn(move || {
        let result = child.wait_with_output();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(NIX_TIMEOUT) {
        Ok(result) => {
            let output = result?;
            if !output.status.success() {
                bail!("Failed to find C++ standard library with `nix-instantiate`");
            }
            Ok(output.stdout)
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            #[cfg(unix)]
            {
                unsafe {
                    libc::kill(child_pid as i32, libc::SIGKILL);
                }
            }
            bail!("nix-instantiate timed out after {}s", NIX_TIMEOUT.as_secs())
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            bail!("nix-instantiate thread panicked unexpectedly")
        }
    }
}
