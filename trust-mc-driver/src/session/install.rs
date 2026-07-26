// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Installation detection and path resolution.
//!
//! Determines whether trust-mc is running from a development repo or a release bundle,
//! and provides paths to compiler binaries, sysroot libraries, and toolchain info.
//!
//! Zero coupling to `KaniSession` or process execution. Uses `std::path`, `std::env`, `anyhow`.

use anyhow::{Context, Result, bail};
use std::path::{Path, PathBuf};

const TRUST_MC_SYSROOT_ENV_VAR: &str = "TRUST_MC_SYSROOT";

/// Represents where we detected trust_mc, with helper methods for using that information to find critical paths
pub(crate) enum InstallType {
    /// We're operating in a a checked out repo that's been built locally.
    /// The path here is to the root of the repo.
    DevRepo(PathBuf),
    /// We're operating from a release bundle (made with `build-trust-mc release`).
    /// The path here to where this release bundle has been unpacked.
    Release(PathBuf),
}

impl InstallType {
    pub(crate) fn new() -> Result<Self> {
        let sysroot = trust_mc_sysroot();
        Self::new_with_sysroot(sysroot.as_deref())
    }

    fn new_with_sysroot(sysroot: Option<&Path>) -> Result<Self> {
        if let Some(sysroot) = sysroot {
            return Ok(InstallType::Release(sysroot.to_path_buf()));
        }

        let path = bin_folder()?;
        if let Some(root) = dev_repo_root_from_bin_dir(&path) {
            Ok(InstallType::DevRepo(root))
        } else if path.ends_with("bin") {
            Ok(InstallType::Release(
                path.parent().expect("bin directory should have a parent").to_path_buf(),
            ))
        } else {
            bail!(
                "Unable to determine installation location. {} doesn't look typical",
                path.display()
            )
        }
    }

    pub(crate) fn kani_compiler(&self) -> Result<PathBuf> {
        match self {
            Self::DevRepo(_) => {
                // Use bin_folder to hide debug/release differences.
                let path = bin_folder()?.join("trust-mc-compiler");
                expect_path(path)
            }
            Self::Release(release) => {
                let path = release.join("bin/trust-mc-compiler");
                expect_path(path)
            }
        }
    }
}

/// Return the path for the folder where the current executable is located.
fn bin_folder() -> Result<PathBuf> {
    let exe = std::env::current_exe().context("Cannot determine current executable location")?;
    let dir = exe.parent().context("Executable isn't in a directory")?.to_owned();
    Ok(dir)
}

fn dev_repo_root_from_bin_dir(path: &Path) -> Option<PathBuf> {
    if path.ends_with("target/trust-mc/bin") {
        return path.parent()?.parent()?.parent().map(Path::to_path_buf);
    }

    let profile = path.file_name()?.to_str()?;
    if profile != "debug" && profile != "release" {
        return None;
    }

    let parent = path.parent()?;
    let parent_name = parent.file_name()?.to_str()?;
    if parent_name == "target" {
        return parent.parent().map(Path::to_path_buf);
    }

    if parent_name.starts_with("worker_") {
        let target_dir = parent.parent()?;
        if target_dir.file_name()?.to_str()? == "target" {
            return target_dir.parent().map(Path::to_path_buf);
        }
    }

    let target_dir = parent.parent()?;
    if target_dir.file_name()?.to_str()? == "target" {
        return target_dir.parent().map(Path::to_path_buf);
    }

    None
}

pub(super) fn trust_mc_sysroot() -> Option<PathBuf> {
    std::env::var_os(TRUST_MC_SYSROOT_ENV_VAR).map(PathBuf::from)
}

pub(super) fn release_cargo_path(root: &Path) -> PathBuf {
    root.join("toolchain").join("bin").join("cargo")
}

fn sysroot_override_subdir(sysroot: Option<&Path>, subdir: &str) -> Result<Option<PathBuf>> {
    let Some(sysroot) = sysroot else {
        return Ok(None);
    };
    let path = sysroot.join(subdir);
    if path.exists() {
        Ok(Some(path))
    } else {
        bail!(
            "{TRUST_MC_SYSROOT_ENV_VAR} set to {} but {} does not exist",
            sysroot.display(),
            path.display()
        );
    }
}

/// Return the path for the folder where the pre-compiled rust libraries are located.
pub(crate) fn lib_folder() -> Result<PathBuf> {
    let sysroot = trust_mc_sysroot();
    library_folder_with_sysroot("lib", sysroot.as_deref())
}

/// Return the path for the folder where the pre-compiled rust libraries are located.
pub(crate) fn lib_playback_folder() -> Result<PathBuf> {
    let sysroot = trust_mc_sysroot();
    library_folder_with_sysroot("playback/lib", sysroot.as_deref())
}

/// Return the path for the folder where the pre-compiled rust libraries with no_core.
pub(crate) fn lib_no_core_folder() -> Result<PathBuf> {
    let sysroot = trust_mc_sysroot();
    library_folder_with_sysroot("no_core/lib", sysroot.as_deref())
}

// Keep the process-environment read at the public boundary. Tests inject the
// override here instead of mutating process-global state shared with other tests.
fn library_folder_with_sysroot(subdir: &str, sysroot: Option<&Path>) -> Result<PathBuf> {
    if let Some(path) = sysroot_override_subdir(sysroot, subdir)? {
        return Ok(path);
    }
    let install = InstallType::new_with_sysroot(sysroot)?;
    match install {
        InstallType::DevRepo(root) => Ok(root.join("target/trust-mc").join(subdir)),
        InstallType::Release(root) => Ok(root.join(subdir)),
    }
}

/// Return the shorthand for the toolchain used by this trust-mc version.
///
/// This shorthand can be used to select the exact toolchain version that matches the one used to
/// build the current trust-mc version.
pub(crate) fn toolchain_shorthand() -> String {
    format!("+{}", rustup_toolchain())
}

/// The rustup toolchain trust-mc selects for its cargo subprocesses. Prefers the
/// value baked at build time (set when built under rustup — the toolchain trust-mc
/// links against), then the runtime `RUSTUP_TOOLCHAIN`, then `stable`. Using
/// `option_env!` instead of `env!` lets trust-mc build outside a rustup shell
/// (e.g. under `RUSTC_BOOTSTRAP`) without a hard compile-time failure.
pub(crate) fn rustup_toolchain() -> String {
    option_env!("RUSTUP_TOOLCHAIN")
        .map(str::to_string)
        .or_else(|| std::env::var("RUSTUP_TOOLCHAIN").ok())
        .unwrap_or_else(|| "stable".to_string())
}

/// A quick helper to say "hey, we expected this thing to be here but it's not!"
fn expect_path(path: PathBuf) -> Result<PathBuf> {
    if path.exists() {
        Ok(path)
    } else {
        bail!(
            "Unable to find {}. Looked for {}",
            path.file_name().map(|n| n.to_string_lossy()).unwrap_or_default(),
            path.display()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{InstallType, dev_repo_root_from_bin_dir, library_folder_with_sysroot};
    use std::path::Path;
    use tempfile::TempDir;

    #[test]
    fn detects_standard_cargo_dev_repo_root() {
        let root = dev_repo_root_from_bin_dir(Path::new("/repo/trust_mc/target/debug"))
            .expect("standard cargo debug path should resolve");
        assert_eq!(root, Path::new("/repo/trust_mc"));
    }

    #[test]
    fn detects_worker_debug_dev_repo_root() {
        let root = dev_repo_root_from_bin_dir(Path::new("/repo/trust_mc/target/worker_2/debug"))
            .expect("worker debug path should resolve");
        assert_eq!(root, Path::new("/repo/trust_mc"));
    }

    #[test]
    fn detects_worker_release_dev_repo_root() {
        let root = dev_repo_root_from_bin_dir(Path::new("/repo/trust_mc/target/worker_7/release"))
            .expect("worker release path should resolve");
        assert_eq!(root, Path::new("/repo/trust_mc"));
    }

    #[test]
    fn detects_custom_target_dir_dev_repo_root() {
        let root = dev_repo_root_from_bin_dir(Path::new("/repo/trust_mc/target/user/release"))
            .expect("custom target dir should resolve");
        assert_eq!(root, Path::new("/repo/trust_mc"));
    }

    #[test]
    fn trust_mc_sysroot_override_resolves_all_library_roots() {
        let temp = TempDir::new().expect("temp dir should be created");
        std::fs::create_dir_all(temp.path().join("lib")).expect("lib dir should exist");
        std::fs::create_dir_all(temp.path().join("playback/lib"))
            .expect("playback lib dir should exist");
        std::fs::create_dir_all(temp.path().join("no_core/lib"))
            .expect("no_core lib dir should exist");
        assert_eq!(
            library_folder_with_sysroot("lib", Some(temp.path()))
                .expect("override lib should resolve"),
            temp.path().join("lib")
        );
        assert_eq!(
            library_folder_with_sysroot("playback/lib", Some(temp.path()))
                .expect("override playback lib should resolve"),
            temp.path().join("playback/lib")
        );
        assert_eq!(
            library_folder_with_sysroot("no_core/lib", Some(temp.path()))
                .expect("override no_core lib should resolve"),
            temp.path().join("no_core/lib")
        );

        match InstallType::new_with_sysroot(Some(temp.path()))
            .expect("override install type should resolve")
        {
            InstallType::Release(root) => assert_eq!(root, temp.path()),
            InstallType::DevRepo(root) => {
                panic!("expected release-style sysroot override, got dev repo {}", root.display())
            }
        }
    }

    #[test]
    fn trust_mc_sysroot_override_rejects_missing_lib_dir() {
        let temp = TempDir::new().expect("temp dir should be created");

        let err = library_folder_with_sysroot("lib", Some(temp.path()))
            .expect_err("missing override lib dir should error");
        let message = err.to_string();
        assert!(message.contains("TRUST_MC_SYSROOT"), "unexpected error: {message}");
        assert!(
            message.contains("does not exist"),
            "missing-path error should mention missing dir: {message}"
        );
    }
}
