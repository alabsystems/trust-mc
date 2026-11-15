// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module contains all first-time setup code done as part of `cargo kani setup`.

use std::env;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use anyhow::{Context, Result, bail};

use crate::cmd::AutoRun;
use crate::os_hacks;

// Share the exact Trust/frozen-oracle identity policy with the driver build.
mod build_frontend {
    include!(concat!(env!("CARGO_MANIFEST_DIR"), "/src/build_frontend.rs"));
}

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SetupToolchain {
    Trust,
    FrozenOracle,
}

fn setup_toolchain_policy(
    channel: &str,
    has_local_toolchain: bool,
    oracle_reason: Option<&OsStr>,
) -> Result<SetupToolchain> {
    let channel = channel.trim();
    let frozen = "nightly-2025-12-03";
    let mode = if channel == "trust" {
        SetupToolchain::Trust
    } else if channel == frozen || channel == format!("{frozen}-{TARGET}") {
        if oracle_reason.is_none_or(|reason| reason.to_string_lossy().trim().is_empty()) {
            bail!("the frozen Kani oracle requires a nonblank ATERM_STOCK_REASON");
        }
        SetupToolchain::FrozenOracle
    } else {
        bail!(
            "bundle toolchain {channel:?} is not Trust or the explicitly authorized frozen Kani oracle"
        );
    };
    if !has_local_toolchain {
        bail!(
            "setup does not install compiler toolchains; name an already installed matching \
             toolchain with trust-mc setup --use-local-toolchain <toolchain directory>"
        );
    }
    Ok(mode)
}

fn require_local_tools(toolchain: &Path, mode: SetupToolchain) -> Result<()> {
    let names: &[&str] = match mode {
        // rustc is the existing read-only producer/consumer version comparison.
        SetupToolchain::Trust => &["targo", "trustc", "rustc"],
        SetupToolchain::FrozenOracle => &["cargo", "rustc"],
    };
    for name in names {
        let path = toolchain.join("bin").join(format!("{name}{}", std::env::consts::EXE_SUFFIX));
        if !path.is_file() {
            bail!("local toolchain is incomplete: {} is missing", path.display());
        }
    }
    Ok(())
}

fn local_compiler_output(toolchain: &Path, args: &[&str]) -> Result<String> {
    let rustc = toolchain.join("bin").join(format!("rustc{}", std::env::consts::EXE_SUFFIX));
    let output = Command::new(&rustc)
        .args(args)
        .output()
        .with_context(|| format!("cannot probe local compiler {}", rustc.display()))?;
    if !output.status.success() {
        bail!("local compiler probe {} {:?} failed", rustc.display(), args);
    }
    String::from_utf8(output.stdout).context("local compiler probe printed non-UTF-8")
}

fn require_frozen_local_identity(toolchain: &Path, channel: &str) -> Result<()> {
    let verbose = local_compiler_output(toolchain, &["-vV"])?;
    let reported = local_compiler_output(toolchain, &["--print", "sysroot"])?;
    let sysroot = Path::new(reported.trim())
        .canonicalize()
        .context("local frozen compiler reported an unavailable sysroot")?;
    if sysroot != toolchain {
        bail!(
            "local frozen compiler reports sysroot {}, not the selected {}",
            sysroot.display(),
            toolchain.display()
        );
    }
    if build_frontend::classify(&verbose, Some(channel.trim()), TARGET, Some(&sysroot))
        != "frozen-kani-oracle"
    {
        bail!("local toolchain is not the exact frozen Kani oracle nightly-2025-12-03");
    }
    Ok(())
}

/// Link a matching installed toolchain; setup never downloads a compiler.
fn setup_rust_toolchain(kani_dir: &Path, use_local_toolchain: Option<OsString>) -> Result<String> {
    setup_rust_toolchain_on(
        kani_dir,
        use_local_toolchain,
        std::env::var_os("ATERM_STOCK_REASON").as_deref(),
    )
}

fn setup_rust_toolchain_on(
    kani_dir: &Path,
    use_local_toolchain: Option<OsString>,
    oracle_reason: Option<&OsStr>,
) -> Result<String> {
    let toolchain_version = get_rust_toolchain_version(kani_dir)?;
    let rustc_version = get_rustc_version_from_build(kani_dir)?.trim().to_string();
    let mode =
        setup_toolchain_policy(&toolchain_version, use_local_toolchain.is_some(), oracle_reason)?;
    let toolchain_path =
        PathBuf::from(use_local_toolchain.expect("policy requires a local toolchain"))
            .canonicalize()
            .context("local toolchain directory does not exist")?;
    // Validate before reading version metadata or changing an existing link.
    require_local_tools(&toolchain_path, mode)?;
    if mode == SetupToolchain::FrozenOracle {
        require_frozen_local_identity(&toolchain_path, &toolchain_version)?;
    }
    let local_version =
        get_rustc_version_from_local_toolchain(toolchain_path.clone().into_os_string())?;
    if rustc_version != local_version {
        bail!(
            "The local compiler version {:?} differs from the release bundle {:?}; \
             use the matching installed toolchain.",
            local_version,
            rustc_version
        );
    }
    symlink_rust_toolchain(&toolchain_path, kani_dir)?;
    println!("[3/5] Linking installed toolchain: {}", toolchain_path.display());
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
    Ok(local_compiler_output(Path::new(&path), &["--version"])?.trim().to_string())
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

    #[cfg(unix)]
    fn scratch(name: &str) -> PathBuf {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("target/tmp/setup-toolchain-tests").join(
                format!("{name}-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)),
            );
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).unwrap();
        path
    }

    #[cfg(unix)]
    fn fixture_bundle(root: &Path, channel: &str, version: &str) -> PathBuf {
        let bundle = root.join("bundle");
        std::fs::create_dir_all(&bundle).unwrap();
        std::fs::write(bundle.join("rust-toolchain-version"), channel).unwrap();
        std::fs::write(bundle.join("rustc-version"), version).unwrap();
        bundle
    }

    #[cfg(unix)]
    fn fake_rustc(path: &Path, version: &str, verbose: &str, sysroot: &Path) {
        use std::os::unix::fs::PermissionsExt;
        let quote = |value: &str| format!("'{}'", value.replace('\'', "'\\''"));
        let script = format!(
            "#!/bin/sh\ncase \"$1\" in\n\
             --version) printf '%s\\n' {} ;;\n\
             -vV) printf '%s\\n' {} ;;\n\
             --print) test \"$2\" = sysroot || exit 2; printf '%s\\n' {} ;;\n\
             *) exit 3 ;;\nesac\n",
            quote(version),
            quote(verbose),
            quote(sysroot.to_str().unwrap())
        );
        std::fs::write(path, script).unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
    }

    #[test]
    fn setup_requires_an_installed_local_toolchain_in_every_lane() {
        for channel in ["trust", "nightly-2025-12-03"] {
            let error = setup_toolchain_policy(channel, false, Some(OsStr::new("oracle check")))
                .unwrap_err()
                .to_string();
            assert!(error.contains("does not install compiler toolchains"), "{error}");
        }
        for channel in ["stable", "nightly-2025-12-04", "nightly-2025-12-03-wrong-host"] {
            let error = setup_toolchain_policy(channel, true, Some(OsStr::new("not an exemption")))
                .unwrap_err()
                .to_string();
            assert!(error.contains("not Trust"), "{error}");
        }
    }

    #[test]
    fn only_the_frozen_local_oracle_requires_a_nonblank_reason() {
        for reason in [None, Some(OsStr::new("")), Some(OsStr::new(" \n\t"))] {
            let error =
                setup_toolchain_policy("nightly-2025-12-03", true, reason).unwrap_err().to_string();
            assert!(error.contains("ATERM_STOCK_REASON"), "{error}");
        }
        assert_eq!(setup_toolchain_policy("trust", true, None).unwrap(), SetupToolchain::Trust);
        assert_eq!(
            setup_toolchain_policy("nightly-2025-12-03", true, Some(OsStr::new("oracle check")))
                .unwrap(),
            SetupToolchain::FrozenOracle
        );
    }

    #[cfg(unix)]
    #[test]
    fn trust_setup_checks_every_required_tool_before_replacing_the_link() {
        for missing in ["targo", "trustc", "rustc"] {
            let root = scratch(&format!("missing-{missing}"));
            let bundle = fixture_bundle(&root, "trust", "matching version");
            let old = root.join("old toolchain");
            std::fs::create_dir_all(&old).unwrap();
            std::os::unix::fs::symlink(&old, bundle.join("toolchain")).unwrap();
            let local = root.join("local toolchain");
            std::fs::create_dir_all(local.join("bin")).unwrap();
            for name in ["targo", "trustc", "rustc"] {
                if name != missing {
                    std::fs::write(local.join("bin").join(name), "must not be executed").unwrap();
                }
            }
            let error = setup_rust_toolchain_on(&bundle, Some(local.into_os_string()), None)
                .unwrap_err()
                .to_string();
            assert!(error.contains(&format!("bin/{missing}")), "{error}");
            assert_eq!(std::fs::read_link(bundle.join("toolchain")).unwrap(), old);
        }
    }

    #[cfg(unix)]
    #[test]
    fn trust_setup_keeps_the_legacy_version_probe_and_holds_a_canonical_local_path() {
        let root = scratch("matching-trust");
        let version = "rustc matching version without the trustc persona suffix";
        let bundle = fixture_bundle(&root, "trust", version);
        let local = root.join("local toolchain with spaces");
        std::fs::create_dir_all(local.join("bin")).unwrap();
        for name in ["targo", "trustc"] {
            std::fs::write(local.join("bin").join(name), "canonical tool presence").unwrap();
        }
        fake_rustc(&local.join("bin/rustc"), version, "unused", &local);
        let current = std::env::current_dir().unwrap();
        let relative = local.strip_prefix(&current).unwrap().to_path_buf();
        setup_rust_toolchain_on(&bundle, Some(relative.into_os_string()), None).unwrap();
        let linked = std::fs::read_link(bundle.join("toolchain")).unwrap();
        assert!(linked.is_absolute());
        assert_eq!(linked, local.canonicalize().unwrap());
    }

    #[cfg(unix)]
    fn frozen_fixture(name: &str, verbose: &str) -> (PathBuf, PathBuf) {
        let root = scratch(name);
        let version = "rustc 1.93.0-nightly (646a3f8c1 2025-12-02)";
        let bundle = fixture_bundle(&root, "nightly-2025-12-03", version);
        let local = root.join(format!("nightly-2025-12-03-{TARGET}"));
        std::fs::create_dir_all(local.join("bin")).unwrap();
        std::fs::write(local.join("bin/cargo"), "oracle frontend presence only").unwrap();
        fake_rustc(&local.join("bin/rustc"), version, verbose, &local.canonicalize().unwrap());
        (bundle, local)
    }

    #[cfg(unix)]
    fn frozen_verbose() -> String {
        format!(
            "binary: rustc\nrelease: 1.93.0-nightly\nhost: {TARGET}\n\
             commit-hash: 646a3f8c15baefb98dc6e0c1c1ba3356db702d2a\n"
        )
    }

    #[cfg(unix)]
    #[test]
    fn explicit_frozen_local_setup_checks_the_actual_identity() {
        let (bundle, local) = frozen_fixture("frozen-match", &frozen_verbose());
        setup_rust_toolchain_on(
            &bundle,
            Some(local.clone().into_os_string()),
            Some(OsStr::new("frozen oracle qualification")),
        )
        .unwrap();
        assert_eq!(
            std::fs::read_link(bundle.join("toolchain")).unwrap(),
            local.canonicalize().unwrap()
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_matching_banner_cannot_hide_wrong_frozen_compiler_facts() {
        for verbose in [
            frozen_verbose().replace("646a3f8c15baefb98dc6e0c1c1ba3356db702d2a", &"0".repeat(40)),
            frozen_verbose().replace(TARGET, "wrong-host"),
            format!("{}trust:\n", frozen_verbose()),
        ] {
            let (bundle, local) = frozen_fixture("frozen-mismatch", &verbose);
            let old = bundle.parent().unwrap().join("old toolchain");
            std::fs::create_dir_all(&old).unwrap();
            std::os::unix::fs::symlink(&old, bundle.join("toolchain")).unwrap();
            let error = setup_rust_toolchain_on(
                &bundle,
                Some(local.into_os_string()),
                Some(OsStr::new("frozen oracle qualification")),
            )
            .unwrap_err()
            .to_string();
            assert!(error.contains("not the exact frozen Kani oracle"), "{error}");
            assert_eq!(std::fs::read_link(bundle.join("toolchain")).unwrap(), old);
        }
    }

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
