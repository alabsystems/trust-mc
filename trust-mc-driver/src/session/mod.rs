// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Session management for trust-mc driver.
//!
//! Submodules:
//! - `memory`: Memory pressure monitoring
//! - `process`: Process execution with timeout protection
//! - `install`: Installation type detection and path resolution
//! - `cargo`: Cargo command construction and flamegraph setup

mod cargo;
pub(crate) mod install;
mod memory;
mod process;

// Re-export crate-internal API — all callers use `crate::session::*`
pub(crate) use cargo::{resolve_cargo_path, setup_cargo_command, setup_cargo_command_inner};
pub(crate) use install::{InstallType, lib_folder, lib_no_core_folder, lib_playback_folder};
pub(crate) use process::{
    DEFAULT_TOOL_TIMEOUT_SECS, run_piped_with_timeout, run_terminal_with_default_timeout,
    wait_with_timeout,
};
use process::{RunLimits, RunMode};

use crate::args::VerificationArgs;
use anyhow::{Context, Result, bail};
use std::io::IsTerminal;
use std::path::PathBuf;
use std::process::Command;
use std::sync::Mutex;
use std::time::Duration;
use strum_macros::Display;
use tracing::level_filters::LevelFilter;
use tracing_subscriber::{EnvFilter, Registry, layer::SubscriberExt};

pub(crate) const BUG_REPORT_URL: &str =
    "https://github.com/alabsystems/trust-mc/issues/new?labels=bug";

/// Environment variable used to control this session log tracing.
/// This is the same variable used to control `trust-mc-compiler` logs. Note that you can still control
/// the driver logs separately, by using the logger directives to select the trust-mc-driver crate.
/// `export TRUST_MC_LOG=trust_mc_driver=debug`.
const LOG_ENV_VAR: &str = "TRUST_MC_LOG";
const LOG_ENV_VAR_LEGACY: &str = "KANI_LOG";

/// Contains information about the execution environment and arguments that affect operations
pub(crate) struct KaniSession {
    /// The common command-line arguments
    pub args: VerificationArgs,

    /// The autoharness-specific compiler arguments.
    /// Invariant: this field is_some() iff the autoharness subcommand is enabled.
    pub autoharness_compiler_flags: Option<Vec<String>>,

    /// The location we found the 'kani_rustc' command
    pub kani_compiler: PathBuf,

    /// The temporary files we littered that need to be cleaned up at the end of execution
    pub temporaries: Mutex<Vec<PathBuf>>,
}

impl KaniSession {
    fn run_mode(
        &self,
        cmd: Command,
        mode: RunMode,
        limits: RunLimits,
    ) -> Result<Option<std::process::Child>> {
        process::execute_with_limits(&self.args.common_args, cmd, mode, limits)
    }

    pub(crate) fn new(args: VerificationArgs) -> Result<Self> {
        Self::new_inner(args, true)
    }

    pub(crate) fn new_for_listing(args: VerificationArgs) -> Result<Self> {
        Self::new_inner(args, false)
    }

    fn new_inner(mut args: VerificationArgs, require_solver: bool) -> Result<Self> {
        init_logger(&args)?;

        // Re-arm the wall-clock watchdog with the authoritative
        // `--harness-timeout`. The early argv-based install in `main()`
        // misses timeouts injected from Cargo.toml config
        // (`args_toml::join_args`); by the time a session is constructed,
        // clap has parsed the fully merged argument list, so this value is
        // final (autoharness defaults are applied later and re-arm again in
        // `add_default_bounds`).
        crate::wall_clock_watchdog::rearm(args.harness_timeout.map(Duration::from));

        let install = InstallType::new()?;

        // Pre-flight check: verify sysroot exists (#903)
        // The sysroot contains pre-compiled standard libraries needed for compilation.
        // Without it, users get confusing "can't find crate for `core`" errors.
        let sysroot_lib = lib_folder()?;
        if !sysroot_lib.exists() {
            bail!(
                "trust_mc sysroot not found at {}\n\n\
                 The trust-mc sysroot contains pre-compiled standard libraries required for verification.\n\n\
                 To build the sysroot, run:\n\
                 \n  cargo build-dev\n\n\
                 This only needs to be done once after cloning the repository or updating the toolchain.",
                sysroot_lib.display()
            );
        }

        resolve_backend_for_session(&mut args, require_solver)?;

        Ok(KaniSession {
            args,
            autoharness_compiler_flags: None,
            kani_compiler: install.kani_compiler()?,
            temporaries: Mutex::new(vec![]),
        })
    }

    /// Record a temporary file so we can cleanup after ourselves at the end.
    /// Note that there will be no failure if the file does not exist.
    pub(crate) fn record_temporary_file<T: AsRef<std::path::Path>>(&self, temp: &T) {
        self.record_temporary_files(&[temp])
    }

    /// Record temporary files so we can cleanup after ourselves at the end.
    /// Note that there will be no failure if the file does not exist.
    pub(crate) fn record_temporary_files<T: AsRef<std::path::Path>>(&self, temps: &[T]) {
        let mut t = self.temporaries.lock().expect("temporaries mutex poisoned");
        t.extend(temps.iter().map(|p| p.as_ref().to_owned()));
    }

    /// Determine which symbols trust-mc should codegen (i.e. by slicing away symbols
    /// that are considered unreachable.)
    pub(crate) fn reachability_mode(&self) -> ReachabilityMode {
        if self.autoharness_compiler_flags.is_some() {
            ReachabilityMode::AllFns
        } else {
            ReachabilityMode::ProofHarnesses
        }
    }
}

fn resolve_backend_for_session(args: &mut VerificationArgs, require_solver: bool) -> Result<()> {
    use crate::args::Backend;

    // If CHC mode is requested, force AY backend (CHC is AY-only).
    // Part of #1755: --ay-chc should imply --backend=ay and a compatible solver.
    if args.ay_chc && args.backend == Backend::Auto {
        args.backend = Backend::AY;
    }

    let original_backend = args.backend;
    if require_solver {
        args.backend =
            args.backend.resolve(args.ay_solver).map_err(|e| anyhow::anyhow!("{}", e))?;
    } else if args.backend == Backend::Auto {
        // `list` needs the compiler/sysroot but does not solve obligations, so
        // do not require the external ay binary just to enumerate metadata.
        args.backend = Backend::AY;
    }

    if original_backend.is_auto() {
        tracing::info!("Auto-selected backend: AY (SMT)");
    }

    Ok(())
}

#[derive(Debug, Copy, Clone, Display)]
#[strum(serialize_all = "snake_case")]
pub(crate) enum ReachabilityMode {
    AllFns,
    #[strum(to_string = "harnesses")]
    ProofHarnesses,
}

impl Drop for KaniSession {
    fn drop(&mut self) {
        if !self.args.keep_temps
            && let Ok(temporaries) = self.temporaries.lock()
        {
            for file in temporaries.iter() {
                let _result = std::fs::remove_file(file);
            }
        }
    }
}

impl KaniSession {
    /// Get the tool timeout duration.
    ///
    /// Returns the user-configured timeout or the default (10 minutes).
    /// Returns None if timeout is explicitly disabled (set to 0).
    pub(crate) fn tool_timeout(&self) -> Option<Duration> {
        match &self.args.tool_timeout {
            Some(timeout) => {
                let duration: Duration = (*timeout).into();
                if duration.is_zero() {
                    None // Explicitly disabled
                } else {
                    Some(duration)
                }
            }
            None => Some(Duration::from_secs(DEFAULT_TOOL_TIMEOUT_SECS)),
        }
    }

    /// Run a command in terminal mode with timeout protection.
    pub(crate) fn run_terminal_with_tool_timeout(&self, cmd: Command) -> Result<()> {
        let limits = RunLimits::timeout_only(self.tool_timeout());
        match self.run_mode(cmd, RunMode::Terminal, limits)? {
            None => Ok(()),
            Some(_) => bail!("Internal error: expected terminal execution to complete"),
        }
    }

    /// Run a command in suppress mode with timeout protection.
    pub(crate) fn run_suppress_with_tool_timeout(&self, cmd: Command) -> Result<()> {
        let limits = RunLimits::timeout_only(self.tool_timeout());
        match self.run_mode(cmd, RunMode::Suppress, limits)? {
            None => Ok(()),
            Some(_) => bail!("Internal error: expected suppress execution to complete"),
        }
    }

    /// Run a command in piped mode with the verbosity configured by the user.
    pub(crate) fn run_piped(&self, cmd: Command) -> Result<std::process::Child> {
        let limits = RunLimits::no_limits();
        match self.run_mode(cmd, RunMode::Piped, limits)? {
            Some(child) => Ok(child),
            None => bail!("Internal error: expected piped execution to return child"),
        }
    }

    /// Call [with_timer] with the verbosity configured by the user.
    pub(crate) fn with_timer<T, F>(&self, func: F, description: &str) -> T
    where
        F: FnOnce() -> T,
    {
        process::with_timer(&self.args.common_args, func, description)
    }
}

/// Resolve which environment variable to use for log filtering.
/// Prefers TRUST_MC_LOG; falls back to the deprecated KANI_LOG.
/// Returns `(env_var_name, is_legacy)`.
fn resolve_log_env_var() -> (&'static str, bool) {
    if std::env::var(LOG_ENV_VAR).is_ok() {
        return (LOG_ENV_VAR, false);
    }
    if std::env::var(LOG_ENV_VAR_LEGACY).is_ok() {
        return (LOG_ENV_VAR_LEGACY, true);
    }
    (LOG_ENV_VAR, false)
}

/// Initialize the logger using the TRUST_MC_LOG environment variable and `--debug` argument.
/// Falls back to the deprecated KANI_LOG if TRUST_MC_LOG is not set.
fn init_logger(args: &VerificationArgs) -> Result<()> {
    let (log_var, is_legacy) = resolve_log_env_var();
    let filter = EnvFilter::from_env(log_var);
    let filter = if args.common_args.debug {
        filter.add_directive(LevelFilter::DEBUG.into())
    } else {
        filter
    };

    // Use a hierarchical view for now.
    let use_colors = std::io::stdout().is_terminal();
    let subscriber = Registry::default().with(filter);
    let subscriber = subscriber.with(
        tracing_subscriber::fmt::layer()
            .with_writer(std::io::stderr)
            .with_ansi(use_colors)
            .with_target(true),
    );
    tracing::subscriber::set_global_default(subscriber)
        .context("global tracing subscriber already set")?;
    if is_legacy {
        tracing::warn!("{} is deprecated, use {} instead", LOG_ENV_VAR_LEGACY, LOG_ENV_VAR);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::args::{Backend, CargoKaniArgs};
    use clap::Parser;

    fn default_verify_opts() -> VerificationArgs {
        CargoKaniArgs::try_parse_from(["cargo-trust-mc"]).unwrap().verify_opts
    }

    #[test]
    fn list_session_backend_resolution_does_not_probe_solver_path() {
        let mut args = default_verify_opts();
        args.backend = Backend::Auto;

        resolve_backend_for_session(&mut args, false).unwrap();

        assert_eq!(args.backend, Backend::AY);
    }

    #[test]
    fn verification_session_backend_resolution_still_rejects_missing_solver() {
        if which::which("ay").is_ok() {
            return;
        }

        let mut args = default_verify_opts();
        args.backend = Backend::Auto;

        assert!(resolve_backend_for_session(&mut args, true).is_err());
    }
}
