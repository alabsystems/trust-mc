// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Cargo command construction and flamegraph setup.
//!
//! Builds `Command` instances for invoking cargo with the correct toolchain,
//! environment, and optional profiling configuration.
//!
//! Depends on `install.rs` for `InstallType` and `toolchain_shorthand`.

use super::install::{InstallType, release_cargo_path, toolchain_shorthand, trust_mc_sysroot};
use anyhow::Result;
use std::path::PathBuf;
use std::process::Command;

// Constants related to the option to create flamegraphs to debug compiler performance.
// See our mdbook's developer documentation for details.
const FLAMEGRAPH_ENV_VAR: &str = "FLAMEGRAPH";
const FLAMEGRAPH_DIR: &str = "flamegraphs";
const FLAMEGRAPH_SAMPLING_RATE: &str = "8000"; // in Hz

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CargoResolution {
    pub(crate) metadata_path: PathBuf,
    pub(crate) direct_build_uses_rustup_shim: bool,
}

impl CargoResolution {
    fn direct_build_command(&self) -> Command {
        if self.direct_build_uses_rustup_shim {
            let mut cmd = Command::new("cargo");
            cmd.arg(toolchain_shorthand());
            cmd
        } else {
            Command::new(&self.metadata_path)
        }
    }

    fn append_direct_build_invocation(&self, cmd: &mut Command) {
        if self.direct_build_uses_rustup_shim {
            cmd.arg("cargo").arg(toolchain_shorthand());
        } else {
            cmd.arg(&self.metadata_path);
        }
    }
}

pub(crate) fn setup_cargo_command() -> Result<Command> {
    setup_cargo_command_inner(None)
}

// Setup the default version of cargo being run, based on the type/mode of installation for trust_mc.
// Optionally takes a path to output compiler profiling info to.
// If trust-mc is being run in developer mode, then we use the one provided by rustup as we can assume that the developer will have rustup installed.
// For release versions of trust_mc, we use a version of cargo that's in the toolchain that's been symlinked during `cargo-trust-mc` setup. This will allow
// trust-mc to remove the runtime dependency on rustup later on.
pub(crate) fn setup_cargo_command_inner(profiling_out_path: Option<String>) -> Result<Command> {
    let has_sysroot_override = trust_mc_sysroot().is_some();
    let install_type = InstallType::new()?;
    let cargo_resolution = resolve_cargo_path_for_install(&install_type, has_sysroot_override);

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

fn resolve_cargo_path_for_install(
    install_type: &InstallType,
    has_sysroot_override: bool,
) -> CargoResolution {
    match install_type {
        InstallType::DevRepo(_) => CargoResolution {
            metadata_path: env!("CARGO").into(),
            direct_build_uses_rustup_shim: true,
        },
        InstallType::Release(kani_dir) => {
            let cargo_path = release_cargo_path(kani_dir);
            if has_sysroot_override && !cargo_path.exists() {
                CargoResolution {
                    metadata_path: env!("CARGO").into(),
                    direct_build_uses_rustup_shim: true,
                }
            } else {
                CargoResolution { metadata_path: cargo_path, direct_build_uses_rustup_shim: false }
            }
        }
    }
}

pub(crate) fn resolve_cargo_path() -> Result<CargoResolution> {
    let has_sysroot_override = trust_mc_sysroot().is_some();
    let install_type = InstallType::new()?;
    Ok(resolve_cargo_path_for_install(&install_type, has_sysroot_override))
}

#[cfg(test)]
mod tests {
    use super::{CargoResolution, resolve_cargo_path_for_install, toolchain_shorthand};
    use crate::session::InstallType;
    use std::path::PathBuf;
    use std::process::Command;
    use tempfile::TempDir;

    fn resolution_for_release(
        create_toolchain_cargo: bool,
        has_sysroot_override: bool,
    ) -> (TempDir, CargoResolution) {
        let temp = TempDir::new().expect("temp dir should be created");
        if create_toolchain_cargo {
            let cargo_path = temp.path().join("toolchain/bin");
            std::fs::create_dir_all(&cargo_path).expect("toolchain/bin should be created");
            std::fs::write(cargo_path.join("cargo"), "").expect("cargo stub should be written");
        }
        let resolution = resolve_cargo_path_for_install(
            &InstallType::Release(temp.path().to_path_buf()),
            has_sysroot_override,
        );
        (temp, resolution)
    }

    fn command_program_and_args(cmd: &Command) -> (String, Vec<String>) {
        (
            cmd.get_program().to_string_lossy().into_owned(),
            cmd.get_args().map(|arg| arg.to_string_lossy().into_owned()).collect(),
        )
    }

    #[test]
    fn dev_repo_resolution_uses_build_time_cargo_for_metadata_and_rustup_shim_for_build() {
        let resolution =
            resolve_cargo_path_for_install(&InstallType::DevRepo("/repo/trust_mc".into()), false);
        assert_eq!(resolution.metadata_path, PathBuf::from(env!("CARGO")));
        assert!(resolution.direct_build_uses_rustup_shim);

        let cmd = resolution.direct_build_command();
        let (program, args) = command_program_and_args(&cmd);
        assert_eq!(program, "cargo");
        assert_eq!(args, vec![toolchain_shorthand()]);
    }

    #[test]
    fn release_resolution_prefers_bundled_cargo_when_present() {
        let (temp, resolution) = resolution_for_release(true, true);
        assert_eq!(resolution.metadata_path, temp.path().join("toolchain/bin/cargo"));
        assert!(!resolution.direct_build_uses_rustup_shim);

        let cmd = resolution.direct_build_command();
        let (program, args) = command_program_and_args(&cmd);
        assert_eq!(program, temp.path().join("toolchain/bin/cargo").display().to_string());
        assert!(args.is_empty());
    }

    #[test]
    fn sysroot_override_release_resolution_falls_back_to_build_time_cargo_for_metadata_and_rustup_shim_for_build()
     {
        let (_temp, resolution) = resolution_for_release(false, true);
        assert_eq!(resolution.metadata_path, PathBuf::from(env!("CARGO")));
        assert!(resolution.direct_build_uses_rustup_shim);

        let cmd = resolution.direct_build_command();
        let (program, args) = command_program_and_args(&cmd);
        assert_eq!(program, "cargo");
        assert_eq!(args, vec![toolchain_shorthand()]);
    }

    #[test]
    fn append_direct_build_invocation_uses_rustup_shim_contract() {
        let resolution = CargoResolution {
            metadata_path: PathBuf::from(env!("CARGO")),
            direct_build_uses_rustup_shim: true,
        };
        let mut cmd = Command::new("samply");
        resolution.append_direct_build_invocation(&mut cmd);
        let (program, args) = command_program_and_args(&cmd);
        assert_eq!(program, "samply");
        assert_eq!(args, vec!["cargo".to_string(), toolchain_shorthand()]);
    }
}
