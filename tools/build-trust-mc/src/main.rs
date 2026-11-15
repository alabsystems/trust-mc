// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This file is a glorified shell script for constructing a trust-mc release bundle.
//! We use Rust here just to aid in making the "script" more robust.
//!
//! Run with `<seal>/bin/targo --unverified bundle` (the `.cargo/config.toml`
//! alias for `targo --unverified run -p build-trust-mc -- bundle`) and this will
//! produce (e.g.) `trust-mc-1.0-aarch64-apple-darwin.tar.gz`, cut on that Trust
//! seal and refused on any other toolchain (`release.rs`). `targo --unverified
//! build-dev` builds the development sysroot; see `dev_std.rs` for where its
//! `-Z build-std` sources come from on a Trust seal that ships none.
//!
//! `build-keyed --trustc <path> --trust-checkout <path> --std build-std|prebuilt`
//! builds the Kani library with one Trust compiler into
//! `target/trust-mc/keyed/<KEY>/` (see `keyed.rs`).

mod dev_std;
mod keyed;
mod parser;
mod private_ay;
mod release;
mod sysroot;
mod watchdog;

use crate::dev_std::{
    CheckoutCandidates, DevCompiler, StdSource, checkout_holds_commit, choose_std_source,
    prepare_std_source, probe_compiler, require_driver_commit, require_rustc_dev,
};
use crate::release::ReleaseSeal;
use crate::sysroot::{
    ReleaseFlags, build_bin, build_lib, build_tools, launching_cargo, toolchain_rustc,
    trust_mc_no_core_lib, trust_mc_playback_lib, trust_mc_repo_root, trust_mc_sysroot,
    trust_mc_sysroot_lib,
};
use crate::watchdog::Watchdog;
use anyhow::{Context, Result, bail};
use clap::Parser;
use std::{
    ffi::OsString,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::Duration,
};

fn main() -> Result<()> {
    let args = parser::ArgParser::parse();

    match args.subcommand {
        parser::Commands::BuildDev(build_parser) => {
            // Decide everything the library build needs before the long binary
            // build, so a missing std source fails in seconds, not after it.
            let compiler = preflight_toolchain()?;
            let std_source = if build_parser.skip_libs {
                None
            } else {
                Some(select_std_source(&compiler, build_parser.trust_checkout.as_deref())?)
            };
            let bin_folder = &build_bin(&build_parser.args, None)?;
            if let Some(source) = std_source {
                build_lib_from(bin_folder, &compiler, &source)?;
            }
            Ok(())
        }
        parser::Commands::BuildKeyed(keyed_parser) => keyed::build_keyed(&keyed_parser),
        parser::Commands::Bundle(bundle_parser) => {
            let version_string = bundle_version(bundle_parser.version)?;
            let trust_mc_string = format!("trust-mc-{version_string}");
            let bundle_name = format!("{trust_mc_string}-{}.tar.gz", env!("TARGET"));
            let dir = Path::new(&trust_mc_string);

            // Check everything is ready before we start copying files
            println!("-- Build release bundle {bundle_name}");
            let (seal, std_source, ay) = prebundle(dir)?;

            std::fs::create_dir(dir)?;

            bundle_trust_mc(dir, &seal, std_source)?;
            private_ay::stage(&trust_mc_repo_root(), &seal, &ay, dir)?;

            create_release_bundle(dir, &bundle_name)?;

            std::fs::remove_dir_all(dir)?;

            println!("\nSuccessfully built release bundle: {bundle_name}");

            Ok(())
        }
    }
}

/// Preflight: trust-mc-compiler is a **rustc driver** (`#![feature(rustc_private)]`,
/// `extern crate rustc_driver`), so the build links the compiler's internal
/// crates, and `build_lib` rebuilds `std` with `-Z build-std`. Probe the compiler
/// of the launching toolchain (the seal's `trustc` under `targo`) and fail fast
/// when it carries no `librustc_driver`. When that is missing the build otherwise
/// dies deep inside cargo with "can't find crate for `rustc_driver`".
fn preflight_toolchain() -> Result<DevCompiler> {
    let compiler = probe_compiler(&toolchain_rustc())?;
    require_rustc_dev(&compiler)?;
    println!(
        "-- toolchain: {} ({}, sysroot {})",
        compiler.rustc.display(),
        compiler.version,
        compiler.sysroot.display()
    );
    Ok(compiler)
}

/// Where the library build's `-Z build-std` reads std from (see `dev_std.rs`).
fn select_std_source(compiler: &DevCompiler, trust_checkout: Option<&Path>) -> Result<StdSource> {
    let candidates = CheckoutCandidates::discover(trust_checkout);
    let source = choose_std_source(compiler, &candidates, &checkout_holds_commit)?;
    match &source {
        StdSource::Sysroot => println!("-- std sources: the toolchain sysroot's own"),
        StdSource::Checkout(checkout) => println!(
            "-- std sources: trust checkout {} at {}",
            checkout.display(),
            compiler.commit.as_deref().unwrap_or_default()
        ),
    }
    Ok(source)
}

/// Build the Kani libraries with the freshly built driver, against `source`.
fn build_lib_from(bin_folder: &Path, compiler: &DevCompiler, source: &StdSource) -> Result<()> {
    if let StdSource::Checkout(_) = source {
        require_driver_commit(compiler, &bin_folder.join("trust-mc-compiler"))?;
    }
    let std_src_root = prepare_std_source(source, compiler, &launching_cargo())?;
    build_lib(bin_folder, std_src_root.as_deref(), None)
}

/// Ensures everything is good to go before we begin to build the release bundle,
/// then builds it: the binaries in release mode and the libraries with the
/// release trust-mc-compiler. Returns the admitted seal and the std source label
/// the bundle records.
///
/// Everything that decides WHAT is built — the seal ([`release::admit`]), the std
/// sources, the remap flags — is settled before the long binary build, so a stock
/// toolchain or a missing source is refused in seconds.
fn prebundle(dir: &Path) -> Result<(ReleaseSeal, &'static str, PathBuf)> {
    if !Path::new("trust-mc-compiler").exists() {
        bail!("Run from project root directory. Couldn't find 'trust-mc-compiler'.");
    }

    if dir.exists() {
        bail!(
            "Directory {} already exists. Previous failed run? Delete it first.",
            dir.to_string_lossy()
        );
    }

    let root = trust_mc_repo_root();
    let seal = release::admit_this_launch(preflight_toolchain()?, &root)?;
    println!(
        "-- release seal: {} (commit {}, build {}, {} {})",
        seal.compiler.sysroot.display(),
        seal.commit,
        seal.build().as_deref().unwrap_or("none"),
        seal.identity.driver_name,
        seal.identity.driver_sha256
    );
    let source = select_std_source(&seal.compiler, None)?;
    let prepared = prepare_std_source(&source, &seal.compiler, &launching_cargo())?;
    let library = seal.std_library(&source, prepared.as_deref());
    let release = ReleaseFlags {
        rustflags: seal.remap_flags(&release::HostPaths::of_this_host(&root), &library)?,
        env: seal.cargo_env(),
    };
    println!("-- release std sources: {}", library.display());
    let ay = private_ay::prepare(&root, &seal)?;
    build_tools(&["--release"], Some(&release))?;

    // Before we begin, ensure trust-mc is built successfully in release mode,
    // and build the libraries with that very trust-mc-compiler. It carries only
    // the relative rpath an installed bundle uses, so link the seal where that
    // rpath looks first.
    let bin_folder = build_bin(&["--release"], Some(&release))?;
    seal.link_toolchain(&trust_mc_sysroot())?;
    require_driver_commit(&seal.compiler, &bin_folder.join("trust-mc-compiler"))?;
    build_lib(&bin_folder, Some(&library), Some(&release))?;
    let label = match source {
        StdSource::Sysroot => "seal-rust-src",
        StdSource::Checkout(_) => "trust-checkout-at-commit",
    };
    Ok((seal, label, ay))
}

/// Copy trust-mc files into `dir`
fn bundle_trust_mc(dir: &Path, seal: &ReleaseSeal, std_source: &str) -> Result<()> {
    let bin = dir.join("bin");
    std::fs::create_dir(&bin)?;

    // 1. trust-mc binaries
    let release = Path::new("./target/release");
    cp(&release.join("trust-mc-driver"), &bin)?;
    cp(&release.join("trust-mc-compiler"), &bin)?;
    cp(&release.join("trust-mc-cov"), &bin)?;

    // 2. trust-mc scripts
    let scripts = dir.join("scripts");
    std::fs::create_dir(scripts)?;

    // 3. trust-mc libraries
    let library = dir.join("library");
    std::fs::create_dir(&library)?;

    cp_dir(Path::new("./library/trust-mc"), &library)?;
    cp_dir(Path::new("./library/kani_macros"), &library)?;
    cp_dir(Path::new("./library/std"), &library)?;

    // 4. Pre-compiled library files
    cp_dir(&trust_mc_sysroot_lib(), dir)?;
    cp_dir(trust_mc_playback_lib().parent().expect("playback lib path must have parent"), dir)?;
    cp_dir(trust_mc_no_core_lib().parent().expect("no_core lib path must have parent"), dir)?;
    // librustc_codegen_trust_mc.dylib, which `build_bin` put there.
    cp_dir(&trust_mc_sysroot().join("codegen-backends"), dir)?;

    // 5. Record the exact toolchain: the channel consumers link (`trust`), the
    //    seal itself (commit, build, driver), and the version line of the seal
    //    compiler under the name an install runs and setup checks (`bin/rustc`).
    std::fs::write(dir.join("rust-toolchain-version"), bundle_toolchain_name()?)?;
    std::fs::write(dir.join(release::SEAL_RECORD), seal.record(std_source))?;
    std::fs::write(dir.join("rustc-version"), seal.installed_rustc_version()?)?;

    // 6. Include a licensing note
    cp(Path::new("tools/build-trust-mc/license-notes.txt"), dir)?;

    Ok(())
}

/// Create the release tarball from `./dir` named `bundle`.
/// This should include all files as `dir/<path>` in the tarball.
/// e.g. `trust-mc-1.0/bin/trust-mc-compiler` not just `bin/trust-mc-compiler`.
fn create_release_bundle(dir: &Path, bundle: &str) -> Result<()> {
    Command::new("tar")
        .args(["zcf", bundle])
        .arg(dir)
        .run_with_watchdog(Watchdog::fixed(TAR_TIMEOUT))
}

/// Timeout for tar operations (5 minutes).
const TAR_TIMEOUT: Duration = Duration::from_secs(300);
/// Timeout for bash operations (2 minutes).
const BASH_TIMEOUT: Duration = Duration::from_secs(120);

/// Helper trait to fallibly run commands
pub(crate) trait AutoRun {
    fn run_with_watchdog(&mut self, watchdog: Watchdog) -> Result<()>;
}

impl AutoRun for Command {
    /// Run under `watchdog`, which kills the command and its descendants on
    /// timeout (on Unix; elsewhere the process may not be killed).
    fn run_with_watchdog(&mut self, watchdog: Watchdog) -> Result<()> {
        let cmd_str = render_command(self);

        let child = self.stdout(Stdio::inherit()).stderr(Stdio::inherit()).spawn()?;
        let status = watchdog.wait(child, &format!("Command {}", cmd_str.to_string_lossy()))?;
        if !status.success() {
            bail!("Failed command: {}", cmd_str.to_string_lossy());
        }
        Ok(())
    }
}

fn expect_dir(path: &Path) -> Result<()> {
    if !path.is_dir() {
        bail!("{} isn't a directory", path.to_string_lossy());
    }
    Ok(())
}

/// Copy a single file to a directory
fn cp(src: &Path, dst: &Path) -> Result<()> {
    expect_dir(dst)?;
    let dst = dst.join(src.file_name().expect("source path must have a file name"));
    std::fs::copy(src, dst)?;
    Ok(())
}

/// The toolchain name a bundle records in `rust-toolchain-version`: `trust`, the
/// channel this repository pins, and nothing else. A `RUSTUP_TOOLCHAIN` naming
/// another toolchain is refused, not recorded (it once stamped
/// `nightly-2025-12-03`, sending consumers to a stock toolchain), and so is a
/// checkout pinned to another channel ([`release::toolchain_name`]).
fn bundle_toolchain_name() -> Result<String> {
    let pin = trust_mc_repo_root().join("rust-toolchain.toml");
    let text =
        std::fs::read_to_string(&pin).with_context(|| format!("cannot read {}", pin.display()))?;
    let selected = std::env::var("RUSTUP_TOOLCHAIN").ok();
    release::toolchain_name(selected.as_deref(), pinned_channel(&text).as_deref())
        .map(str::to_string)
}

/// The version a bundle is named for: `explicit`, else trust-mc's own
/// `[package] version`. It used to default to this tool's CARGO_PKG_VERSION
/// (`0.1.0`), naming a 0.7.0 bundle `trust-mc-0.1.0`.
fn bundle_version(explicit: Option<String>) -> Result<String> {
    if let Some(version) = explicit {
        return Ok(version);
    }
    let manifest = trust_mc_repo_root().join("Cargo.toml");
    let text = std::fs::read_to_string(&manifest)
        .with_context(|| format!("cannot read {}", manifest.display()))?;
    package_version(&text)
        .ok_or_else(|| anyhow::format_err!("{} has no [package] version", manifest.display()))
}

/// `version = "…"` of a manifest's `[package]` table.
fn package_version(manifest: &str) -> Option<String> {
    let mut in_package = false;
    manifest.lines().find_map(|line| {
        let line = line.trim();
        if line.starts_with('[') {
            in_package = line == "[package]";
            return None;
        }
        let value = in_package.then_some(line)?.strip_prefix("version")?.trim_start();
        let value = value.strip_prefix('=')?.trim().strip_prefix('"')?;
        value.split('"').next().filter(|v| !v.is_empty()).map(str::to_string)
    })
}

/// `channel = "trust"` from a `rust-toolchain.toml`.
fn pinned_channel(text: &str) -> Option<String> {
    text.lines().find_map(|line| {
        let value = line.trim().strip_prefix("channel")?.trim_start().strip_prefix('=')?;
        let value = value.trim().strip_prefix('"')?;
        value.split('"').next().filter(|channel| !channel.is_empty()).map(str::to_string)
    })
}

/// Invoke `cp -r`
fn cp_dir(src: &Path, dst: &Path) -> Result<()> {
    let mut cmd = OsString::from("cp -r ");
    cmd.push(src.as_os_str());
    cmd.push(" ");
    cmd.push(dst.as_os_str());

    Command::new("bash").arg("-c").arg(cmd).run_with_watchdog(Watchdog::fixed(BASH_TIMEOUT))
}

/// Render a Command as a string, to log it
pub(crate) fn render_command(cmd: &Command) -> OsString {
    let mut str = OsString::new();

    for (k, v) in cmd.get_envs() {
        if let Some(v) = v {
            str.push(k);
            str.push("=\"");
            str.push(v);
            str.push("\" ");
        }
    }

    str.push(cmd.get_program());

    for a in cmd.get_args() {
        str.push(" ");
        if a.to_string_lossy().contains(' ') {
            str.push("\"");
            str.push(a);
            str.push("\"");
        } else {
            str.push(a);
        }
    }

    str
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "a panicking assertion is the point in tests")]
mod tests {
    use super::*;

    #[test]
    fn pinned_channel_reads_rust_toolchain_toml() {
        assert_eq!(pinned_channel("[toolchain]\nchannel = \"trust\"\n").as_deref(), Some("trust"));
        assert_eq!(pinned_channel("# channel = x\n[toolchain]\n").as_deref(), None);
        assert_eq!(
            pinned_channel("[toolchain]\nchannel=\"nightly-2025-12-03\"").as_deref(),
            Some("nightly-2025-12-03")
        );
        let pin =
            std::fs::read_to_string(trust_mc_repo_root().join("rust-toolchain.toml")).unwrap();
        assert_eq!(pinned_channel(&pin).as_deref(), Some("trust"));
    }

    /// The default bundle version is trust-mc's own, not this tool's 0.1.0.
    #[test]
    fn a_bundle_is_named_for_trust_mc_s_own_version() {
        let manifest = "[workspace.package]\nversion = \"9.9.9\"\n[package]\nname = \"trust-mc\"\n\
                        version = \"0.7.0\"\n[dependencies]\nversion = \"1\"\n";
        assert_eq!(package_version(manifest).as_deref(), Some("0.7.0"));
        assert_eq!(package_version("[dependencies]\nversion = \"1\"\n"), None);
        let ours = std::fs::read_to_string(trust_mc_repo_root().join("Cargo.toml")).unwrap();
        let version = bundle_version(None).unwrap();
        assert_eq!(Some(version.as_str()), package_version(&ours).as_deref());
        assert_eq!(bundle_version(Some("2.0.0".to_string())).unwrap(), "2.0.0");
    }

    /// Regression (REL-C1): `bundle_toolchain_name` recorded `RUSTUP_TOOLCHAIN`
    /// verbatim, so a release bundle built with the frozen nightly selected
    /// stamped `nightly-2025-12-03` into `rust-toolchain-version` and sent every
    /// consumer to a stock toolchain. It must refuse instead; with nothing
    /// selected it stamps the Trust channel.
    #[test]
    fn a_release_bundle_never_stamps_a_stock_rustup_toolchain() {
        let saved = std::env::var_os("RUSTUP_TOOLCHAIN");
        // SAFETY: no other test in this binary reads or writes RUSTUP_TOOLCHAIN.
        unsafe { std::env::set_var("RUSTUP_TOOLCHAIN", "nightly-2025-12-03") };
        let stamped = bundle_toolchain_name();
        unsafe { std::env::remove_var("RUSTUP_TOOLCHAIN") };
        let unselected = bundle_toolchain_name();
        if let Some(saved) = saved {
            unsafe { std::env::set_var("RUSTUP_TOOLCHAIN", saved) };
        }
        let error = stamped.expect_err("a stock RUSTUP_TOOLCHAIN must be refused, not stamped");
        assert!(format!("{error:#}").contains("RUSTUP_TOOLCHAIN=nightly-2025-12-03"), "{error:#}");
        assert_eq!(unselected.unwrap(), "trust");
    }

    #[test]
    fn test_render_command_simple() {
        let cmd = Command::new("echo");
        let rendered = render_command(&cmd);
        assert_eq!(rendered.to_string_lossy(), "echo");
    }

    #[test]
    fn test_render_command_with_args() {
        let mut cmd = Command::new("cargo");
        cmd.arg("build").arg("--release");
        let rendered = render_command(&cmd);
        assert_eq!(rendered.to_string_lossy(), "cargo build --release");
    }

    #[test]
    fn test_render_command_with_space_in_arg() {
        let mut cmd = Command::new("echo");
        cmd.arg("hello world");
        let rendered = render_command(&cmd);
        assert_eq!(rendered.to_string_lossy(), "echo \"hello world\"");
    }

    #[test]
    fn test_render_command_with_env() {
        let mut cmd = Command::new("rustc");
        cmd.env("RUSTFLAGS", "-Dwarnings");
        let rendered = render_command(&cmd);
        // Verify exact format: ENV="value" program
        assert_eq!(rendered.to_string_lossy(), "RUSTFLAGS=\"-Dwarnings\" rustc");
    }

    #[test]
    fn test_render_command_with_multiple_env() {
        let mut cmd = Command::new("cargo");
        cmd.env("CARGO_TERM_COLOR", "always");
        cmd.env("RUSTFLAGS", "-Clink-dead-code");
        cmd.arg("build");
        let rendered = render_command(&cmd);
        let rendered_str = rendered.to_string_lossy();
        // Env vars may appear in any order, so check both are present
        assert!(rendered_str.contains("CARGO_TERM_COLOR=\"always\""));
        assert!(rendered_str.contains("RUSTFLAGS=\"-Clink-dead-code\""));
        assert!(rendered_str.ends_with("cargo build"));
    }
}
