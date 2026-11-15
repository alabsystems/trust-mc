// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Cargo command construction and flamegraph setup.
//!
//! Builds `Command` instances for invoking cargo with the correct toolchain,
//! environment, and optional profiling configuration.
//!
//! Depends on `install.rs` for `InstallType` and the toolchain name.
//!
//! # Which cargo: the toolchain trust-mc-compiler links, never a rustup lookup
//!
//! trust-mc-compiler links one exact rustc, so every cargo subprocess must run
//! that toolchain's cargo. Kani did this with `cargo +<toolchain>`, which needs a
//! rustup proxy on PATH and a rustup channel name; a driver built by `targo`
//! has neither (no `RUSTUP_TOOLCHAIN` is set, measured on seal 9192), and the
//! old fallback to `stable` then ran a toolchain the compiler was never built
//! with.
//!
//! The driver's build script records the sysroot of the compiler that built it
//! (`MC_DRIVER_BUILD_SYSROOT`: `$RUSTC --print sysroot`), which `build-dev` makes
//! the same compiler that builds trust-mc-compiler. A development checkout (and
//! a sysroot override without a bundled toolchain) runs `<that sysroot>/bin/targo`
//! directly, with `RUSTC` pointing at its sibling trustc and its `bin` appended to
//! PATH; a release bundle runs its own `toolchain/bin/targo` the same way. There
//! is no fallback: without that cargo the driver refuses and names the rebuild.

use super::install::{InstallType, build_toolchain_sysroot, release_cargo_path, trust_mc_sysroot};
use anyhow::{Result, bail};
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

// Constants related to the option to create flamegraphs to debug compiler performance.
// See our mdbook's developer documentation for details.
const FLAMEGRAPH_ENV_VAR: &str = "FLAMEGRAPH";
const FLAMEGRAPH_DIR: &str = "flamegraphs";
const FLAMEGRAPH_SAMPLING_RATE: &str = "8000"; // in Hz

/// How a cargo subprocess reaches the toolchain trust-mc was built against.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CargoLauncher {
    /// A release bundle's own `toolchain/bin/targo`, using its sibling rustc.
    Bundled(PathBuf),
    /// `<sysroot>/bin/targo` of the toolchain that built this driver.
    Toolchain(PathBuf),
    /// Explicitly recorded frozen Kani oracle only; no Trust fallback.
    FrozenOracle(PathBuf),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CargoResolution {
    /// The cargo binary `cargo metadata` runs.
    pub(crate) metadata_path: PathBuf,
    /// How build, test and pkgid subprocesses launch cargo.
    pub(crate) launcher: CargoLauncher,
}

impl CargoResolution {
    fn cargo(&self) -> &Path {
        match &self.launcher {
            CargoLauncher::Bundled(cargo)
            | CargoLauncher::Toolchain(cargo)
            | CargoLauncher::FrozenOracle(cargo) => cargo,
        }
    }

    fn direct_build_command(&self) -> Command {
        let mut cmd = self.direct_query_command();
        if !matches!(self.launcher, CargoLauncher::FrozenOracle(_)) {
            cmd.arg("--unverified");
        }
        cmd
    }

    fn direct_query_command(&self) -> Command {
        let mut cmd = Command::new(self.cargo());
        self.apply_toolchain_env(&mut cmd);
        cmd
    }

    fn append_direct_build_invocation(&self, cmd: &mut Command) {
        cmd.arg(self.cargo());
        if !matches!(self.launcher, CargoLauncher::FrozenOracle(_)) {
            cmd.arg("--unverified");
        }
        self.apply_toolchain_env(cmd);
    }

    fn apply_toolchain_env(&self, cmd: &mut Command) {
        for (key, value) in self.toolchain_env() {
            cmd.env(key, value);
        }
    }

    /// Environment a cargo subprocess needs so that it — and the `rustc -vV`
    /// probes it runs before any `RUSTC` override applies — stays on the
    /// selected toolchain. Call sites that compile set `RUSTC` to
    /// trust-mc-compiler afterwards, which takes precedence.
    pub(crate) fn toolchain_env(&self) -> Vec<(&'static str, OsString)> {
        let mut env = Vec::new();
        if let Some(bin) = self.cargo().parent() {
            let name = if matches!(self.launcher, CargoLauncher::FrozenOracle(_)) {
                "rustc"
            } else {
                "trustc"
            };
            let rustc = bin.join(format!("{name}{}", std::env::consts::EXE_SUFFIX));
            // Retain the held path if it disappears after resolution: failing
            // to spawn it must never turn into a PATH/default compiler lookup.
            env.push(("RUSTC", rustc.into_os_string()));
            if let Some(path) = path_with_appended_dir(std::env::var_os("PATH"), bin) {
                env.push(("PATH", path));
            }
        }
        env
    }
}

/// Append `dir` to a PATH value unless it is already listed. Appending (not
/// prepending) keeps every ambient entry — e.g. the `ay` a corpus runner put
/// first — ahead of the toolchain's own binaries.
fn path_with_appended_dir(path: Option<OsString>, dir: &Path) -> Option<OsString> {
    let mut parts: Vec<PathBuf> =
        path.as_deref().map(|p| std::env::split_paths(p).collect()).unwrap_or_default();
    if parts.iter().any(|p| p == dir) {
        return path;
    }
    parts.push(dir.to_path_buf());
    std::env::join_paths(parts).ok()
}

pub(crate) fn setup_cargo_command() -> Result<Command> {
    let resolution = resolve_cargo_path()?;
    let mut cmd = resolution.direct_query_command();
    crate::util::apply_rust_min_stack(&mut cmd);
    Ok(cmd)
}

// Setup the default version of cargo being run, based on the type/mode of installation for trust_mc.
// Optionally takes a path to output compiler profiling info to.
// In developer mode (and for a sysroot override without a bundled toolchain) the cargo of the
// toolchain this driver was built with runs; see the module docs.
// For release versions of trust_mc, we use a version of cargo that's in the toolchain that's been symlinked during `cargo-trust-mc` setup.
pub(crate) fn setup_cargo_command_inner(profiling_out_path: Option<String>) -> Result<Command> {
    let has_sysroot_override = trust_mc_sysroot().is_some();
    let install_type = InstallType::new()?;
    let cargo_resolution = resolve_cargo_path_for_install(
        &install_type,
        has_sysroot_override,
        build_toolchain_sysroot().as_deref(),
    )?;

    let mut cmd = match install_type {
        InstallType::DevRepo(_) => {
            // check if we should instrument the compiler for a flamegraph
            let instrument_compiler = matches!(
                std::env::var(FLAMEGRAPH_ENV_VAR),
                Ok(ref s) if s == "compiler"
            );

            if let Some(profiler_out_path) = profiling_out_path
                && instrument_compiler
            {
                // create temporary flamegraph directory
                std::fs::create_dir_all(FLAMEGRAPH_DIR)?;
                let time_postfix = chrono::Local::now().format("%Y-%m-%dT%H:%M:%S");

                let mut cmd = Command::new("samply");
                cmd.arg("record");

                // adjust the sampling rate (in Hz)
                cmd.arg("-r").arg(FLAMEGRAPH_SAMPLING_RATE);
                cmd.arg("-o").arg(format!(
                    "{FLAMEGRAPH_DIR}/compiler-{profiler_out_path}-{time_postfix}.json.gz",
                ));

                // just save the output and don't open the interactive UI.
                cmd.arg("--save-only");
                cargo_resolution.append_direct_build_invocation(&mut cmd);
                cmd
            } else {
                cargo_resolution.direct_build_command()
            }
        }
        InstallType::Release(_) => cargo_resolution.direct_build_command(),
    };

    crate::util::apply_rust_min_stack(&mut cmd);

    Ok(cmd)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BuildFrontend {
    Trust,
    FrozenOracle,
    Unknown,
}

fn build_frontend() -> BuildFrontend {
    match option_env!("MC_DRIVER_BUILD_FRONTEND") {
        Some("trust") => BuildFrontend::Trust,
        Some("frozen-kani-oracle") => BuildFrontend::FrozenOracle,
        _ => BuildFrontend::Unknown,
    }
}

fn checked_resolution(launcher: CargoLauncher) -> Result<CargoResolution> {
    let resolution = CargoResolution {
        metadata_path: match &launcher {
            CargoLauncher::Bundled(path)
            | CargoLauncher::Toolchain(path)
            | CargoLauncher::FrozenOracle(path) => path.clone(),
        },
        launcher,
    };
    let compiler = if matches!(resolution.launcher, CargoLauncher::FrozenOracle(_)) {
        "rustc"
    } else {
        "trustc"
    };
    let path = resolution
        .cargo()
        .parent()
        .expect("frontend has a bin parent")
        .join(format!("{compiler}{}", std::env::consts::EXE_SUFFIX));
    if !path.is_file() {
        bail!(
            "{} does not exist beside the selected frontend; rebuild with targo --unverified build-dev",
            path.display()
        );
    }
    Ok(resolution)
}

fn resolve_cargo_path_for_install(
    install_type: &InstallType,
    has_sysroot_override: bool,
    build_sysroot: Option<&Path>,
) -> Result<CargoResolution> {
    resolve_cargo_path_for_install_on(
        install_type,
        has_sysroot_override,
        build_sysroot,
        build_frontend(),
        std::env::var_os("ATERM_STOCK_REASON").as_deref(),
    )
}

fn resolve_cargo_path_for_install_on(
    install_type: &InstallType,
    has_sysroot_override: bool,
    build_sysroot: Option<&Path>,
    frontend: BuildFrontend,
    oracle_reason: Option<&std::ffi::OsStr>,
) -> Result<CargoResolution> {
    if frontend == BuildFrontend::Unknown {
        bail!(
            "this driver records no recognized build frontend; rebuild with targo --unverified build-dev"
        );
    }
    if frontend == BuildFrontend::FrozenOracle
        && oracle_reason.is_none_or(|reason| reason.to_string_lossy().trim().is_empty())
    {
        bail!("the frozen Kani oracle requires a nonblank ATERM_STOCK_REASON");
    }
    let build_toolchain = || -> Result<CargoResolution> {
        let Some(sysroot) = build_sysroot else {
            bail!(
                "this trust-mc-driver records no build toolchain (its build script could not \
                 ask RUSTC for a sysroot). Rebuild it with the Trust toolchain: targo --unverified build-dev"
            );
        };
        let name = if frontend == BuildFrontend::FrozenOracle { "cargo" } else { "targo" };
        let cargo = sysroot.join("bin").join(format!("{name}{}", std::env::consts::EXE_SUFFIX));
        if !cargo.is_file() {
            bail!(
                "{} does not exist: the toolchain trust-mc was built with ({}) is incomplete. \
                 Check the Trust toolchain (`aterm pkg doctor`) and rebuild: \
                 targo --unverified build-dev",
                cargo.display(),
                sysroot.display()
            );
        }
        checked_resolution(if frontend == BuildFrontend::FrozenOracle {
            CargoLauncher::FrozenOracle(cargo)
        } else {
            CargoLauncher::Toolchain(cargo)
        })
    };
    match install_type {
        InstallType::Release(_)
            if frontend == BuildFrontend::FrozenOracle && !has_sysroot_override =>
        {
            bail!("the frozen Kani oracle cannot select a bundled release toolchain");
        }
        _ if frontend == BuildFrontend::FrozenOracle => build_toolchain(),
        InstallType::DevRepo(_) => build_toolchain(),
        InstallType::Release(kani_dir) => {
            let cargo_path = release_cargo_path(kani_dir);
            if cargo_path.is_file() {
                return checked_resolution(CargoLauncher::Bundled(cargo_path));
            }
            let unlinked = format!(
                "{} does not exist: this trust-mc install has no complete `toolchain` link to the Trust \
                 seal it was built on. Link it: trust-mc setup --use-local-toolchain <seal directory>, or \
                 ln -s <seal directory> {}",
                cargo_path.display(),
                kani_dir.join("toolchain").display()
            );
            if has_sysroot_override {
                return build_toolchain().map_err(|error| error.context(unlinked));
            }
            bail!(unlinked)
        }
    }
}

pub(crate) fn resolve_cargo_path() -> Result<CargoResolution> {
    let has_sysroot_override = trust_mc_sysroot().is_some();
    let install_type = InstallType::new()?;
    resolve_cargo_path_for_install(
        &install_type,
        has_sysroot_override,
        build_toolchain_sysroot().as_deref(),
    )
}

#[cfg(test)]
mod tests {
    mod frontend_policy {
        include!(concat!(env!("CARGO_MANIFEST_DIR"), "/../src/build_frontend.rs"));
    }

    use super::{
        BuildFrontend, CargoLauncher, CargoResolution, path_with_appended_dir,
        resolve_cargo_path_for_install_on,
    };
    use crate::session::InstallType;
    use std::ffi::OsString;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use tempfile::TempDir;

    fn resolve_cargo_path_for_install(
        install: &InstallType,
        override_sysroot: bool,
        build: Option<&Path>,
    ) -> anyhow::Result<CargoResolution> {
        resolve_cargo_path_for_install_on(
            install,
            override_sysroot,
            build,
            BuildFrontend::Trust,
            None,
        )
    }

    /// A fake toolchain sysroot whose `bin` holds `cargo` and `rustc` stubs.
    fn fake_sysroot(root: &Path) -> PathBuf {
        let sysroot = root.join("store/trust/9192");
        let bin = sysroot.join("bin");
        std::fs::create_dir_all(&bin).expect("toolchain bin should be created");
        for tool in ["targo", "trustc"] {
            std::fs::write(bin.join(tool), "").expect("tool stub should be written");
        }
        sysroot
    }

    fn resolution_for_release(
        create_toolchain_cargo: bool,
        has_sysroot_override: bool,
        build_sysroot: Option<&Path>,
    ) -> (TempDir, anyhow::Result<CargoResolution>) {
        let temp = TempDir::new().expect("temp dir should be created");
        if create_toolchain_cargo {
            let cargo_path = temp.path().join("toolchain/bin");
            std::fs::create_dir_all(&cargo_path).expect("toolchain/bin should be created");
            std::fs::write(cargo_path.join("targo"), "").expect("cargo stub should be written");
            std::fs::write(cargo_path.join("trustc"), "").expect("rustc stub should be written");
        }
        let resolution = resolve_cargo_path_for_install(
            &InstallType::Release(temp.path().to_path_buf()),
            has_sysroot_override,
            build_sysroot,
        );
        (temp, resolution)
    }

    fn command_program_and_args(cmd: &Command) -> (String, Vec<String>) {
        (
            cmd.get_program().to_string_lossy().into_owned(),
            cmd.get_args().map(|arg| arg.to_string_lossy().into_owned()).collect(),
        )
    }

    fn command_env(cmd: &Command, key: &str) -> Option<OsString> {
        cmd.get_envs().find(|(k, _)| *k == key).and_then(|(_, v)| v.map(OsString::from))
    }

    /// The defect this replaces: a targo-built driver has no `RUSTUP_TOOLCHAIN`,
    /// so the dev-repo path fell back to `stable` and ran `cargo +stable`, a
    /// toolchain trust-mc-compiler was never built with. It now runs the cargo
    /// of the toolchain that built it, directly.
    #[test]
    fn dev_repo_runs_the_build_toolchain_cargo_directly() {
        let temp = TempDir::new().expect("temp dir should be created");
        let sysroot = fake_sysroot(temp.path());
        let bin = sysroot.join("bin");
        let resolution = resolve_cargo_path_for_install(
            &InstallType::DevRepo("/repo/trust_mc".into()),
            false,
            Some(&sysroot),
        )
        .expect("the build toolchain's cargo exists");
        let cargo = bin.join("targo");
        assert_eq!(resolution.metadata_path, cargo);
        assert_eq!(resolution.launcher, CargoLauncher::Toolchain(cargo.clone()));

        let cmd = resolution.direct_build_command();
        let (program, args) = command_program_and_args(&cmd);
        assert_eq!(program, cargo.display().to_string());
        assert_eq!(args, ["--unverified"], "explicit build lane: {args:?}");
        assert_eq!(command_env(&cmd, "RUSTUP_TOOLCHAIN"), None, "no rustup channel is named");
        assert_eq!(command_env(&cmd, "RUSTC"), Some(bin.join("trustc").into_os_string()));
        let path = command_env(&cmd, "PATH").expect("PATH should carry the toolchain bin");
        assert_eq!(std::env::split_paths(&path).last(), Some(bin));
    }

    /// No stock fallback: without the build toolchain's cargo the driver refuses
    /// and names the Trust rebuild.
    #[test]
    fn dev_repo_without_the_build_toolchain_refuses() {
        let temp = TempDir::new().expect("temp dir should be created");
        let dev = InstallType::DevRepo("/repo/trust_mc".into());
        let gone = resolve_cargo_path_for_install(&dev, false, Some(&temp.path().join("gone")))
            .expect_err("a missing toolchain cargo is refused");
        assert!(gone.to_string().contains("targo --unverified build-dev"), "{gone}");
        let unknown = resolve_cargo_path_for_install(&dev, false, None)
            .expect_err("an unrecorded toolchain is refused");
        assert!(unknown.to_string().contains("targo --unverified build-dev"), "{unknown}");
        for error in [gone, unknown] {
            assert!(!error.to_string().contains("rustup"), "no stock remedy: {error}");
        }
    }

    #[test]
    fn release_resolution_prefers_bundled_cargo_when_present() {
        let (temp, resolution) = resolution_for_release(true, true, None);
        let resolution = resolution.expect("the bundled cargo exists");
        assert_eq!(resolution.metadata_path, temp.path().join("toolchain/bin/targo"));
        assert!(matches!(resolution.launcher, CargoLauncher::Bundled(_)));

        let cmd = resolution.direct_build_command();
        let (program, args) = command_program_and_args(&cmd);
        assert_eq!(program, temp.path().join("toolchain/bin/targo").display().to_string());
        assert_eq!(args, ["--unverified"]);
        assert_eq!(command_env(&cmd, "RUSTUP_TOOLCHAIN"), None);
        let bin = temp.path().join("toolchain/bin");
        assert_eq!(command_env(&cmd, "RUSTC"), Some(bin.join("trustc").into_os_string()));
        let path = command_env(&cmd, "PATH").expect("PATH should carry the bundled toolchain bin");
        let mut expected: Vec<PathBuf> = std::env::var_os("PATH")
            .as_deref()
            .map(|value| std::env::split_paths(value).collect())
            .unwrap_or_default();
        expected.push(bin);
        assert_eq!(std::env::split_paths(&path).collect::<Vec<_>>(), expected);
        let metadata_env = resolution.toolchain_env();
        assert_eq!(
            metadata_env.iter().find(|(key, _)| *key == "RUSTC").map(|(_, value)| value),
            command_env(&cmd, "RUSTC").as_ref()
        );
    }

    #[test]
    fn bundled_cargo_keeps_the_verification_compiler_override() {
        let (_temp, resolution) = resolution_for_release(true, false, None);
        let mut cmd = resolution.expect("the bundled cargo exists").direct_build_command();
        cmd.env("RUSTC", "/bundle/bin/trust-mc-compiler");
        assert_eq!(command_env(&cmd, "RUSTC"), Some("/bundle/bin/trust-mc-compiler".into()));
    }

    #[test]
    fn sysroot_override_release_resolution_uses_the_build_toolchain_cargo() {
        let toolchain = TempDir::new().expect("temp dir should be created");
        let sysroot = fake_sysroot(toolchain.path());
        let (_temp, resolution) = resolution_for_release(false, true, Some(&sysroot));
        let expected = sysroot.join("bin/targo");
        let resolution = resolution.expect("the build toolchain's cargo exists");
        assert_eq!(resolution.metadata_path, expected);
        assert_eq!(resolution.launcher, CargoLauncher::Toolchain(expected));

        let (_temp, refused) = resolution_for_release(false, true, None);
        let refused = refused.expect_err("no bundled cargo and no build toolchain: refused");
        assert!(format!("{refused:#}").contains("no complete `toolchain` link"), "{refused:#}");
    }

    /// A release bundle bakes no build toolchain (MC_RELEASE_BUNDLE): without
    /// its `toolchain` link it is refused up front, naming the link, and never
    /// pointed at a stock remedy.
    #[test]
    fn release_install_without_its_toolchain_link_names_the_link() {
        for build_sysroot in [None, Some(Path::new("/nonexistent/store/trust/9192"))] {
            let (temp, refused) = resolution_for_release(false, false, build_sysroot);
            let message = format!("{:#}", refused.expect_err("no toolchain link: refused"));
            assert!(message.contains("trust-mc setup --use-local-toolchain"), "{message}");
            assert!(
                message.contains(&temp.path().join("toolchain").display().to_string()),
                "{message}"
            );
            assert!(!message.contains("rustup"), "no stock remedy: {message}");
        }
    }

    #[test]
    fn append_direct_build_invocation_uses_the_same_launcher() {
        let cargo = PathBuf::from("/store/trust/9192/bin/targo");
        let direct = CargoResolution {
            metadata_path: cargo.clone(),
            launcher: CargoLauncher::Toolchain(cargo.clone()),
        };
        let mut cmd = Command::new("samply");
        direct.append_direct_build_invocation(&mut cmd);
        let (program, args) = command_program_and_args(&cmd);
        assert_eq!(program, "samply");
        assert_eq!(args, vec![cargo.display().to_string(), "--unverified".to_string()]);
        assert_eq!(command_env(&cmd, "RUSTUP_TOOLCHAIN"), None);
    }

    #[test]
    fn query_has_no_lane_and_keeps_a_removed_compiler_pinned() {
        let temp = TempDir::new().unwrap();
        let sysroot = fake_sysroot(temp.path());
        let resolution = resolve_cargo_path_for_install(
            &InstallType::DevRepo("/repo".into()),
            false,
            Some(&sysroot),
        )
        .unwrap();
        std::fs::remove_file(sysroot.join("bin/trustc")).unwrap();
        let query = resolution.direct_query_command();
        assert!(query.get_args().next().is_none());
        assert_eq!(command_env(&query, "RUSTC"), Some(sysroot.join("bin/trustc").into_os_string()));
        assert_eq!(
            resolution.direct_build_command().get_args().collect::<Vec<_>>(),
            ["--unverified"]
        );
    }

    #[test]
    fn missing_trust_frontend_never_uses_a_compatibility_cargo() {
        let temp = TempDir::new().unwrap();
        let sysroot = fake_sysroot(temp.path());
        std::fs::remove_file(sysroot.join("bin/targo")).unwrap();
        std::fs::write(sysroot.join("bin/cargo"), "compatibility persona").unwrap();
        let error = resolve_cargo_path_for_install(
            &InstallType::DevRepo("/repo".into()),
            false,
            Some(&sysroot),
        )
        .unwrap_err();
        assert!(error.to_string().contains("bin/targo"), "{error}");
    }

    #[test]
    fn frozen_oracle_is_explicit_and_cannot_select_a_bundled_trust_toolchain() {
        let temp = TempDir::new().unwrap();
        let sysroot = fake_sysroot(temp.path());
        for tool in ["cargo", "rustc"] {
            std::fs::write(sysroot.join("bin").join(tool), "frozen oracle").unwrap();
        }
        let install = InstallType::DevRepo("/repo".into());
        for reason in [None, Some(std::ffi::OsStr::new("")), Some(std::ffi::OsStr::new(" \n"))] {
            assert!(
                resolve_cargo_path_for_install_on(
                    &install,
                    false,
                    Some(&sysroot),
                    BuildFrontend::FrozenOracle,
                    reason
                )
                .is_err()
            );
        }
        let resolution = resolve_cargo_path_for_install_on(
            &install,
            false,
            Some(&sysroot),
            BuildFrontend::FrozenOracle,
            Some(std::ffi::OsStr::new("frozen comparison")),
        )
        .unwrap();
        assert!(matches!(resolution.launcher, CargoLauncher::FrozenOracle(_)));
        assert!(resolution.direct_build_command().get_args().next().is_none());
        assert_eq!(
            command_env(&resolution.direct_query_command(), "RUSTC"),
            Some(sysroot.join("bin/rustc").into_os_string())
        );
        assert!(
            resolve_cargo_path_for_install_on(
                &InstallType::Release(temp.path().to_owned()),
                false,
                Some(&sysroot),
                BuildFrontend::FrozenOracle,
                Some(std::ffi::OsStr::new("comparison"))
            )
            .is_err()
        );
        assert!(
            resolve_cargo_path_for_install_on(
                &install,
                false,
                Some(&sysroot),
                BuildFrontend::Unknown,
                None
            )
            .is_err()
        );
    }

    #[test]
    fn toolchain_bin_is_appended_once() {
        let dir = Path::new("/toolchains/nightly/bin");
        let joined = path_with_appended_dir(Some("/a:/b".into()), dir).unwrap();
        assert_eq!(
            std::env::split_paths(&joined).collect::<Vec<_>>(),
            vec![PathBuf::from("/a"), PathBuf::from("/b"), dir.to_path_buf()]
        );
        let again = path_with_appended_dir(Some(joined.clone()), dir).unwrap();
        assert_eq!(again, joined);
    }
}
