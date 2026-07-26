// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This file is a glorified shell script for constructing a trust-mc release bundle.
//! We use Rust here just to aid in making the "script" more robust.
//!
//! Run with `cargo run -p build-trust-mc -- release` and this will produce
//! (e.g.) `trust-mc-1.0-x86_64-unknown-linux-gnu.tar.gz`.

mod parser;
mod sysroot;

use crate::sysroot::{
    build_bin, build_lib, build_tools, trust_mc_no_core_lib, trust_mc_playback_lib,
    trust_mc_sysroot_lib,
};
use anyhow::{Result, bail};
use clap::Parser;
use std::{
    ffi::OsString,
    path::Path,
    process::{Command, Stdio},
    sync::mpsc,
    time::Duration,
};

fn main() -> Result<()> {
    let args = parser::ArgParser::parse();

    match args.subcommand {
        parser::Commands::BuildDev(build_parser) => {
            preflight_toolchain_components()?;
            let bin_folder = &build_bin(&build_parser.args)?;
            if !build_parser.skip_libs {
                build_lib(bin_folder)?;
            }
            Ok(())
        }
        parser::Commands::Bundle(bundle_parser) => {
            let version_string = bundle_parser.version;
            let trust_mc_string = format!("trust-mc-{version_string}");
            let bundle_name = format!("{trust_mc_string}-{}.tar.gz", env!("TARGET"));
            let dir = Path::new(&trust_mc_string);

            // Check everything is ready before we start copying files
            println!("-- Build release bundle {bundle_name}");
            prebundle(dir)?;

            std::fs::create_dir(dir)?;

            bundle_trust_mc(dir)?;
            bundle_kissat(dir)?;

            create_release_bundle(dir, &bundle_name)?;

            std::fs::remove_dir_all(dir)?;

            println!("\nSuccessfully built release bundle: {bundle_name}");

            Ok(())
        }
    }
}

/// Preflight: trust-mc-compiler is a **rustc driver** (`#![feature(rustc_private)]`,
/// `extern crate rustc_driver`), so the build links the compiler's internal
/// crates and rebuilds `std` with `-Z build-std`. That requires the `rustc-dev`
/// and `rust-src` components of the pinned toolchain. When they are missing the
/// build otherwise dies deep inside cargo with a cryptic
/// "can't find crate for `rustc_driver`" / "can't find crate for `std`" — the
/// thing that trips people (and AI sessions) up. Fail fast with the exact fix.
///
/// Best-effort: if `rustup` is not on PATH (e.g. a `RUSTC_BOOTSTRAP` shell or a
/// vendored toolchain), skip silently rather than block a working environment.
fn preflight_toolchain_components() -> Result<()> {
    let output = match Command::new("rustup").args(["component", "list", "--installed"]).output() {
        Ok(o) if o.status.success() => o,
        _ => return Ok(()),
    };
    let installed = String::from_utf8_lossy(&output.stdout);
    let missing: Vec<&str> = ["rustc-dev", "rust-src"]
        .into_iter()
        .filter(|component| !installed.lines().any(|line| line.starts_with(component)))
        .collect();
    if !missing.is_empty() {
        let toolchain = rustup_toolchain();
        let toolchain = toolchain.trim();
        bail!(
            "missing toolchain component(s) required to build trust-mc: {missing}\n\
             \n\
             trust-mc-compiler is a rustc driver (it links rustc internals via\n\
             rustc_private and rebuilds std with -Z build-std), so these are required\n\
             — the same way Kani needs them. Install with:\n\
             \n    rustup component add {add} --toolchain {toolchain}\n",
            missing = missing.join(", "),
            add = missing.join(" "),
        );
    }
    Ok(())
}

/// Ensures everything is good to go before we begin to build the release bundle.
/// Notably, builds trust-mc in release mode.
fn prebundle(dir: &Path) -> Result<()> {
    if !Path::new("trust-mc-compiler").exists() {
        bail!("Run from project root directory. Couldn't find 'trust-mc-compiler'.");
    }

    if dir.exists() {
        bail!(
            "Directory {} already exists. Previous failed run? Delete it first.",
            dir.to_string_lossy()
        );
    }

    build_tools(&["--release"])?;

    // Before we begin, ensure trust-mc is built successfully in release mode.
    // And that libraries have been built too.
    build_lib(&build_bin(&["--release"])?)
}

/// Copy trust-mc files into `dir`
fn bundle_trust_mc(dir: &Path) -> Result<()> {
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

    // 5. Record the exact toolchain and rustc version we use
    std::fs::write(dir.join("rust-toolchain-version"), rustup_toolchain())?;
    std::fs::write(dir.join("rustc-version"), get_rustc_version()?)?;

    // 6. Include a licensing note
    cp(Path::new("tools/build-trust-mc/license-notes.txt"), dir)?;

    Ok(())
}

/// Copy Kissat binary into `dir`
fn bundle_kissat(dir: &Path) -> Result<()> {
    let bin = dir.join("bin");

    // We use these directly
    cp(&which::which("kissat")?, &bin)?;

    Ok(())
}

/// Create the release tarball from `./dir` named `bundle`.
/// This should include all files as `dir/<path>` in the tarball.
/// e.g. `trust-mc-1.0/bin/trust-mc-compiler` not just `bin/trust-mc-compiler`.
fn create_release_bundle(dir: &Path, bundle: &str) -> Result<()> {
    Command::new("tar").args(["zcf", bundle]).arg(dir).run_with_timeout(TAR_TIMEOUT)
}

/// Timeout for tar operations (5 minutes).
const TAR_TIMEOUT: Duration = Duration::from_secs(300);
/// Timeout for bash operations (2 minutes).
const BASH_TIMEOUT: Duration = Duration::from_secs(120);

/// Helper trait to fallibly run commands
pub(crate) trait AutoRun {
    fn run_with_timeout(&mut self, timeout: Duration) -> Result<()>;
}

impl AutoRun for Command {
    /// Run with timeout. On non-Unix, process may not be killed on timeout.
    fn run_with_timeout(&mut self, timeout: Duration) -> Result<()> {
        let cmd_str = render_command(self);

        let mut child = self.stdout(Stdio::inherit()).stderr(Stdio::inherit()).spawn()?;

        #[cfg(unix)]
        let child_pid = child.id();

        let (tx, rx) = mpsc::channel();

        // Use wait() since we inherit stdio and don't need output capture
        std::thread::spawn(move || {
            let result = child.wait();
            let _ = tx.send(result);
        });

        match rx.recv_timeout(timeout) {
            Ok(result) => {
                let status = result?;
                if !status.success() {
                    bail!("Failed command: {}", cmd_str.to_string_lossy());
                }
                Ok(())
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {
                #[cfg(unix)]
                {
                    unsafe {
                        libc::kill(child_pid as i32, libc::SIGKILL);
                    }
                }
                bail!(
                    "Command timed out after {:.0}s: {}",
                    timeout.as_secs_f64(),
                    cmd_str.to_string_lossy()
                )
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                bail!("Command thread panicked unexpectedly: {}", cmd_str.to_string_lossy())
            }
        }
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

/// Record version of rustc being used to build trust-mc
fn get_rustc_version() -> Result<String> {
    let output = Command::new("rustc").arg("--version").output();
    let rustc_version = String::from_utf8(output.expect("failed to run rustc --version").stdout)?;
    Ok(rustc_version)
}

/// The rustup toolchain this build was produced with. Prefers the value baked at
/// build time (set when built under rustup), then the runtime `RUSTUP_TOOLCHAIN`,
/// then `stable`. Using `option_env!` instead of `env!` lets this tool build
/// outside a rustup shell (e.g. under `RUSTC_BOOTSTRAP`) without a hard
/// compile-time failure — matching `trust-mc-driver`'s `rustup_toolchain()`.
fn rustup_toolchain() -> String {
    option_env!("RUSTUP_TOOLCHAIN")
        .map(str::to_string)
        .or_else(|| std::env::var("RUSTUP_TOOLCHAIN").ok())
        .unwrap_or_else(|| "stable".to_string())
}

/// Invoke `cp -r`
fn cp_dir(src: &Path, dst: &Path) -> Result<()> {
    let mut cmd = OsString::from("cp -r ");
    cmd.push(src.as_os_str());
    cmd.push(" ");
    cmd.push(dst.as_os_str());

    Command::new("bash").arg("-c").arg(cmd).run_with_timeout(BASH_TIMEOUT)
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
mod tests {
    use super::*;

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
