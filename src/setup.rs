// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module contains all first-time setup code done as part of `cargo kani setup`.

use std::env;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use anyhow::{Context, Result, bail};

use crate::cmd::AutoRun;
use crate::os_hacks;

/// Comes from our Cargo.toml manifest file. Must correspond to our release verion.
const VERSION: &str = env!("CARGO_PKG_VERSION");
/// Set by our `build.rs`, reflects the Rust target triple we're building for
const TARGET: &str = env!("TARGET");
const RELEASE_OWNER: &str = "alabsystems";
const RELEASE_REPO: &str = "trust-mc";
const RELEASE_ARCHIVE_PREFIX: &str = "trust-mc";

/// The directory where Kani is installed, either:
///  * (custom) `${KANI_HOME}/kani-<VERSION>` if the environment variable
///    `KANI_HOME` is set.
///  * (default) `${HOME}/.kani/kani-<VERSION>` where `HOME` is the canonical
///    definition of home directory used by Cargo and rustup.
pub(crate) fn kani_dir() -> Result<PathBuf> {
    let kani_dir = match env::var("KANI_HOME") {
        Ok(val) => custom_kani_dir(val),
        Err(_) => default_kani_dir()?,
    };
    let kani_dir = kani_dir.join(format!("kani-{VERSION}"));
    Ok(kani_dir)
}

/// Returns the custom Kani home directory: `${KANI_HOME}`
fn custom_kani_dir(path: String) -> PathBuf {
    // We don't check if it doesn't exist since we create it later
    PathBuf::from(path)
}

/// Returns the default Kani home directory: `${HOME}/.kani`
fn default_kani_dir() -> Result<PathBuf> {
    let home_dir = home::home_dir().expect("couldn't find home directory");
    if !home_dir.is_dir() {
        bail!("got home directory `{}` which isn't a directory", home_dir.display());
    }
    let kani_dir = home_dir.join(".kani");
    Ok(kani_dir)
}

/// Sets up Kani by unpacking/installing to `~/.kani/kani-VERSION`
pub(crate) fn setup(
    use_local_bundle: Option<OsString>,
    use_local_toolchain: Option<OsString>,
) -> Result<()> {
    let kani_dir = kani_dir()?;
    let os = os_info::get();

    println!("[0/5] Running trust-mc first-time setup...");

    println!("[1/5] Ensuring the existence of: {}", kani_dir.display());
    std::fs::create_dir_all(&kani_dir)?;

    setup_kani_bundle(&kani_dir, use_local_bundle)?;

    setup_rust_toolchain(&kani_dir, use_local_toolchain)?;

    os_hacks::setup_os_hacks(&kani_dir, &os)?;

    println!("[5/5] Successfully completed trust-mc first-time setup.");

    Ok(())
}

/// Timeout for tar extraction operations (5 minutes).
const TAR_TIMEOUT: Duration = Duration::from_secs(300);
/// Timeout for curl download operations (10 minutes).
const CURL_TIMEOUT: Duration = Duration::from_secs(600);

/// Download and unpack the Kani release bundle
fn setup_kani_bundle(kani_dir: &Path, use_local_bundle: Option<OsString>) -> Result<()> {
    // e.g. `~/.kani/`
    let base_dir = kani_dir.parent().expect("No base directory?");

    if let Some(pathstr) = use_local_bundle {
        println!("[2/5] Installing local trust-mc bundle: {}", pathstr.to_string_lossy());
        let path = Path::new(&pathstr).canonicalize()?;
        // When given a local bundle, it's often "-latest" but we expect "-1.0" or something.
        // tar supports "stripping" the first directory from the bundle, so do that and
        // extract it directly into the expected (kani_dir) directory (instead of base_dir).
        Command::new("tar")
            .arg("--strip-components=1")
            .arg("-zxf")
            .arg(&path)
            .current_dir(kani_dir)
            .run_with_timeout(TAR_TIMEOUT)
            .context(
                "Failed to extract tar file, try removing trust-mc setup located in .kani in your home directory and restarting",
            )?;
    } else {
        let filename = download_filename();
        println!("[2/5] Downloading trust-mc release bundle: {}", filename);
        fail_if_unsupported_target()?;
        let bundle = base_dir.join(filename);
        Command::new("curl")
            .args(["-sSLf", "-o"])
            .arg(&bundle)
            .arg(download_url())
            .run_with_timeout(CURL_TIMEOUT)
            .context("Failed to download trust-mc release bundle")?;

        Command::new("tar")
            .arg("zxf")
            .arg(&bundle)
            .current_dir(base_dir)
            .run_with_timeout(TAR_TIMEOUT)?;

        std::fs::remove_file(bundle)?;
    }
    Ok(())
}

/// Reads the Rust toolchain version that Kani was built against from the file in
/// the Kani release bundle (unpacked in `kani_dir`).
pub(crate) fn get_rust_toolchain_version(kani_dir: &Path) -> Result<String> {
    std::fs::read_to_string(kani_dir.join("rust-toolchain-version"))
        .context("Reading release bundle rust-toolchain-version")
}

pub(crate) fn get_rustc_version_from_build(kani_dir: &Path) -> Result<String> {
    std::fs::read_to_string(kani_dir.join("rustc-version"))
        .context("Reading release bundle rustc-version")
}

/// Timeout for rustup toolchain install operations (10 minutes).
const RUSTUP_TIMEOUT: Duration = Duration::from_secs(600);

/// Install the Rust toolchain version we require
fn setup_rust_toolchain(kani_dir: &Path, use_local_toolchain: Option<OsString>) -> Result<String> {
    // Currently this means we require the bundle to have been unpacked first!
    let toolchain_version = get_rust_toolchain_version(kani_dir)?;
    let rustc_version = get_rustc_version_from_build(kani_dir)?.trim().to_string();

    // Symlink to a local toolchain if the user explicitly requests
    if let Some(local_toolchain_path) = use_local_toolchain {
        let toolchain_path = Path::new(&local_toolchain_path);

        let custom_toolchain_rustc_version =
            get_rustc_version_from_local_toolchain(local_toolchain_path.clone())?;

        if rustc_version == custom_toolchain_rustc_version {
            symlink_rust_toolchain(toolchain_path, kani_dir)?;
            println!(
                "[3/5] Installing rust toolchain from path provided: {}",
                toolchain_path.to_string_lossy()
            );
            return Ok(toolchain_version);
        }
        bail!(
            "The toolchain with rustc {:?} being used to setup is not the same as the one trust-mc used in its release bundle {:?}. Try to setup with the same version as the bundle.",
            custom_toolchain_rustc_version,
            rustc_version,
        );
    }

    // This is the default behaviour when no explicit path to a toolchain is mentioned
    println!("[3/5] Installing rust toolchain version: {}", toolchain_version);
    Command::new("rustup")
        .args(["toolchain", "install", &toolchain_version])
        .run_with_timeout(RUSTUP_TIMEOUT)?;
    let toolchain = home::rustup_home()?.join("toolchains").join(&toolchain_version);
    symlink_rust_toolchain(&toolchain, kani_dir)?;
    Ok(toolchain_version)
}

// This ends the setup steps above.
//
// Just putting a bit of space between that and the helper functions below.

/// The filename of the release bundle
fn download_filename() -> String {
    format!("{RELEASE_ARCHIVE_PREFIX}-{VERSION}-{TARGET}.tar.gz")
}

/// Get the version of rustc that is being used to setup kani by the user
fn get_rustc_version_from_local_toolchain(path: OsString) -> Result<String> {
    let path = Path::new(&path);
    let rustc_path = path.join("bin").join("rustc");

    let output = Command::new(rustc_path).arg("--version").output();

    match output {
        Ok(output) => {
            if output.status.success() {
                Ok(String::from_utf8(output.stdout).map(|s| s.trim().to_string())?)
            } else {
                bail!(
                    "Could not parse rustc version string. Toolchain installation likely invalid. "
                );
            }
        }
        Err(_) => bail!("Could not get rustc version. Toolchain installation likely invalid"),
    }
}

/// The download URL for this version of Kani
fn download_url() -> String {
    let tag: &str = &format!("{RELEASE_ARCHIVE_PREFIX}-{VERSION}");
    let file: &str = &download_filename();
    format!("https://github.com/{RELEASE_OWNER}/{RELEASE_REPO}/releases/download/{tag}/{file}")
}

/// Give users a better error message than "404" if we're on an unsupported platform.
/// This is called just before we try to download the release bundle.
fn fail_if_unsupported_target() -> Result<()> {
    // This is basically going to be reduced to a compile-time constant
    match TARGET {
        "x86_64-unknown-linux-gnu"
        | "x86_64-apple-darwin"
        | "aarch64-unknown-linux-gnu"
        | "aarch64-apple-darwin" => Ok(()),
        _ => bail!("trust-mc does not support this platform (Rust target {})", TARGET),
    }
}

/// Creates a `kani_dir/toolchain` symlink pointing to `toolchain`.
fn symlink_rust_toolchain(toolchain: &Path, kani_dir: &Path) -> Result<()> {
    let path = kani_dir.join("toolchain");
    // We want setup to be idempotent, so if the symlink already exists, delete instead of failing
    if path.exists() && path.is_symlink() {
        std::fs::remove_file(&path)?;
    }
    #[cfg(unix)]
    std::os::unix::fs::symlink(toolchain, path)?;
    // The toolchain is a directory, so Windows needs `symlink_dir`. Creating it
    // may require Developer Mode or elevation; if the OS refuses, the error is
    // propagated rather than silently skipping the link.
    #[cfg(windows)]
    std::os::windows::fs::symlink_dir(toolchain, path)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn release_bundle_filename_uses_trust_mc_archive_name() {
        assert_eq!(download_filename(), format!("trust-mc-{VERSION}-{TARGET}.tar.gz"));
    }

    #[test]
    fn release_download_url_uses_trust_mc_repository_and_archive_name() {
        assert_eq!(
            download_url(),
            format!(
                "https://github.com/alabsystems/trust-mc/releases/download/trust-mc-{VERSION}/trust-mc-{VERSION}-{TARGET}.tar.gz"
            )
        );
    }
}
