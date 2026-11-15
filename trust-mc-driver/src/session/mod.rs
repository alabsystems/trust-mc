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
pub(crate) mod trustc_route;

// Re-export crate-internal API — all callers use `crate::session::*`
pub(crate) use cargo::{resolve_cargo_path, setup_cargo_command, setup_cargo_command_inner};
pub(crate) use install::{CompilerRoute, InstallType, PlaybackRoute, lib_folder};
pub(crate) use process::{
    BUDGET_EXHAUSTED_BEFORE_SPAWN, DEFAULT_TOOL_TIMEOUT_SECS, run_piped_with_timeout,
    run_terminal_with_default_timeout, wait_with_timeout,
};
use process::{RunLimits, RunMode};

use crate::args::VerificationArgs;
use crate::util::args::{KaniArg, RustcArg, encode_as_pct1_rustc_arg, encode_as_rustc_arg};
use anyhow::{Context, Result, bail};
use std::ffi::OsString;
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};
use std::time::Duration;
use strum_macros::Display;
use tracing::level_filters::LevelFilter;
use tracing_subscriber::{EnvFilter, Registry, layer::SubscriberExt};
use trustc_route::{TRUST_VERIFY_OFF, TrustcIdentity, TrustcRouteError};

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

    /// Where trust-mc was detected. The Kani-compatibility compiler binary is
    /// resolved from this ON DEMAND -- see [`KaniSession::kani_compiler`].
    ///
    /// It used to be an eagerly-resolved `PathBuf`, which coupled the two lanes
    /// this driver serves. `trust-mc-compiler` is the RUST-SOURCE frontend (the
    /// Kani-compatibility path: Rust -> rustc internals -> AY). The TRUST-native
    /// path does not use it at all -- `--trust-vc-bundle` goes straight to
    /// `trust_mc_trust_vc_ingest` -- yet resolving it in the constructor made
    /// EVERY invocation fail closed when it was absent, including that one.
    /// Trust's own bootstrap builds this driver and never builds that compiler,
    /// so the Trust engine lane could not run without the Kani lane installed.
    pub install: InstallType,

    /// Which compiler builds the crates (T1-D1). Resolved from flags and
    /// environment in the constructor; the Trustc identity preflight runs at the
    /// first compile, so lanes that never compile never pay for it.
    pub route: CompilerRoute,

    /// What the Trustc route's preflight established, once it has run.
    pub(crate) trustc_identity: OnceLock<TrustcIdentity>,

    /// The temporary files we littered that need to be cleaned up at the end of execution
    pub temporaries: Mutex<Vec<PathBuf>>,
}

impl KaniSession {
    /// The program that compiles crates on this session's route.
    ///
    /// DevCli: the Kani-compatibility compiler binary, checking the sysroot first.
    /// Both checks were previously done eagerly in the constructor; the messages
    /// are preserved verbatim so anything that genuinely needs the Rust-source
    /// lane still fails closed exactly as before.
    ///
    /// Trustc: the canonical trustc, after the identity preflight (cached) has
    /// accepted it; prints the `[AY:COMPILER_ROUTE ...]` marker once per compile.
    pub(crate) fn compiler_program(&self) -> Result<PathBuf> {
        if matches!(self.route, CompilerRoute::Trustc { .. }) {
            let identity = self.trustc_identity()?;
            println!("{}", identity.marker());
            return Ok(identity.trustc.clone());
        }
        // Pre-flight check: verify sysroot exists (#903)
        // The sysroot contains pre-compiled standard libraries needed for compilation.
        // Without it, users get confusing "can't find crate for `core`" errors.
        let sysroot_lib = lib_folder()?;
        if !sysroot_lib.exists() {
            bail!(
                "trust_mc sysroot not found at {}\n\n\
                 The trust-mc sysroot contains pre-compiled standard libraries required for verification.\n\n\
                 To build the sysroot, run:\n\
                 \n  targo --unverified build-dev\n\n\
                 This only needs to be done once after cloning the repository or updating the toolchain.",
                sysroot_lib.display()
            );
        }
        self.install.kani_compiler()
    }

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

        // Only the route's flags and environment are resolved here; its identity
        // preflight runs at the first compile (see `compiler_program`).
        let route = CompilerRoute::resolve(&args.compiler_route)?;
        if matches!(route, CompilerRoute::Trustc { .. }) && args.no_codegen {
            return Err(TrustcRouteError::NoCodegen.into());
        }

        // The sysroot and compiler-binary checks that used to live here are now in
        // `compiler_program()`, at the point of use. Both are RUST-SOURCE lane
        // requirements; running them in the constructor made them requirements of
        // every lane. They still fail closed, with the same messages, for anything
        // that actually needs them.
        resolve_backend_for_session(&mut args, require_solver)?;

        Ok(KaniSession {
            args,
            autoharness_compiler_flags: None,
            install,
            route,
            trustc_identity: OnceLock::new(),
            temporaries: Mutex::new(vec![]),
        })
    }

    /// The Trustc route's identity, establishing it on first use.
    pub(crate) fn trustc_identity(&self) -> Result<&TrustcIdentity> {
        if let Some(identity) = self.trustc_identity.get() {
            return Ok(identity);
        }
        let CompilerRoute::Trustc { trustc, backend, key_dir } = &self.route else {
            bail!("internal error: the dev-cli compiler route has no trustc identity");
        };
        if self.args.no_codegen {
            return Err(TrustcRouteError::NoCodegen.into());
        }
        let identity = trustc_route::establish_identity(trustc, backend, key_dir)?;
        Ok(self.trustc_identity.get_or_init(|| identity))
    }

    /// Refuse when the Trustc route's backend dylib changed since the preflight
    /// (trustc dlopens the path per compile). Nothing to check when no identity has
    /// been established, which includes the DevCli route.
    pub(crate) fn recheck_trustc_backend(&self) -> Result<()> {
        match self.trustc_identity.get() {
            Some(identity) => Ok(identity.recheck_backend()?),
            None => Ok(()),
        }
    }

    /// Run `compile`, then [`Self::recheck_trustc_backend`]. A changed backend wins
    /// over the compile's own result, so no artifact of that compile is used.
    pub(crate) fn with_backend_recheck<T>(&self, compile: impl FnOnce() -> Result<T>) -> Result<T> {
        let result = compile();
        self.recheck_trustc_backend()?;
        result
    }

    /// Encode engine arguments into one `-Cllvm-args` for this route: the legacy
    /// space join on DevCli, the whitespace-safe `pct1` channel on Trustc.
    pub(crate) fn encode_kani_args(&self, kani_args: &[KaniArg]) -> RustcArg {
        match self.route {
            CompilerRoute::DevCli => encode_as_rustc_arg(kani_args),
            CompilerRoute::Trustc { .. } => encode_as_pct1_rustc_arg(kani_args),
        }
    }

    /// Route-specific environment for a compile command (a trustc child, or a
    /// cargo whose `RUSTC` is trustc).
    pub(crate) fn apply_route_env(&self, cmd: &mut Command) {
        apply_route_env_for(&self.route, cmd);
    }

    /// An explicitly unverified compilation command for this session's route.
    ///
    /// DevCli uses [`setup_cargo_command_inner`]. Trustc uses the held seal's
    /// Targo with `RUSTC=<trustc>` and every rustc wrapper disabled. Flamegraph
    /// profiling applies only to DevCli.
    pub(crate) fn cargo_command(&self, profiling_out_path: Option<String>) -> Result<Command> {
        match self.route {
            CompilerRoute::DevCli => setup_cargo_command_inner(profiling_out_path),
            CompilerRoute::Trustc { .. } => {
                self.trustc_cargo_build_command_on(std::env::vars_os().collect())
            }
        }
    }

    /// A project-context query, which must not carry a compilation lane flag.
    pub(crate) fn cargo_query_command(&self) -> Result<Command> {
        match self.route {
            CompilerRoute::DevCli => setup_cargo_command(),
            CompilerRoute::Trustc { .. } => {
                self.trustc_cargo_command_on(std::env::vars_os().collect())
            }
        }
    }

    /// A Trustc query with injectable parent context for refusal tests.
    pub(crate) fn trustc_cargo_command_on(
        &self,
        env: Vec<(OsString, OsString)>,
    ) -> Result<Command> {
        self.trustc_cargo_command_for(env, trustc_route::CargoInvocation::Query)
    }

    /// A Trustc compilation with injectable parent context for refusal tests.
    pub(crate) fn trustc_cargo_build_command_on(
        &self,
        env: Vec<(OsString, OsString)>,
    ) -> Result<Command> {
        self.trustc_cargo_command_for(env, trustc_route::CargoInvocation::Build)
    }

    /// Both invocation kinds preserve the same wrapper, flag and engine-knob
    /// refusals before any identity probe, then the same held-toolchain edits.
    fn trustc_cargo_command_for(
        &self,
        env: Vec<(OsString, OsString)>,
        invocation: trustc_route::CargoInvocation,
    ) -> Result<Command> {
        trustc_route::refuse_cargo_route_env(&env)?;
        let identity = self.trustc_identity()?;
        let mut cmd = trustc_route::trustc_cargo_command(identity, env, invocation)?;
        crate::util::apply_rust_min_stack(&mut cmd);
        Ok(cmd)
    }

    /// Refuse when the effective cargo `[env]` table, read with the seal's cargo
    /// from `cwd` (the directory the verification cargo runs in), sets a
    /// `TRUST_MC_*` / `AY_*` variable: cargo applies the table to every rustc it
    /// runs after the launcher's environment edits, so an engine knob there would
    /// reach the trustc child unseen (`trustc_route::probe_cargo_env_table`).
    /// Nothing to probe on DevCli.
    pub(crate) fn refuse_cargo_env_table(&self, cwd: Option<&Path>) -> Result<()> {
        if !matches!(self.route, CompilerRoute::Trustc { .. }) {
            return Ok(());
        }
        let mut cargo = self.cargo_query_command()?;
        if let Some(cwd) = cwd {
            cargo.current_dir(cwd);
        }
        Ok(trustc_route::probe_cargo_env_table(cargo)?)
    }

    /// The cargo target-dir namespace: `kani` on DevCli,
    /// `kani-trustc-<commit12>-<backend sha256[:12]>-<KEY content sha256[:12]>` on
    /// Trustc, so fingerprints never mix across compilers, across rebuilds of the
    /// backend dylib, or across rebuilds of the KEY's libraries at one path.
    pub(crate) fn kani_target_namespace(&self) -> Result<String> {
        match self.route {
            CompilerRoute::DevCli => Ok("kani".to_string()),
            CompilerRoute::Trustc { .. } => Ok(self.trustc_identity()?.target_namespace()),
        }
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

#[cfg(test)]
impl KaniSession {
    /// A session for argv-composition tests: no logger, no solver resolution and
    /// an install location that composition never reads.
    pub(crate) fn for_argv_tests(args: VerificationArgs) -> Self {
        KaniSession {
            args,
            autoharness_compiler_flags: None,
            install: InstallType::Release(PathBuf::from("/nonexistent/trust-mc-install")),
            route: CompilerRoute::DevCli,
            trustc_identity: OnceLock::new(),
            temporaries: Mutex::new(vec![]),
        }
    }

    /// [`Self::for_argv_tests`] on an explicit compiler route.
    pub(crate) fn for_argv_tests_with_route(args: VerificationArgs, route: CompilerRoute) -> Self {
        let mut session = Self::for_argv_tests(args);
        session.route = route;
        session
    }
}

/// Route-specific environment for a compile command: on Trustc, no `TRUST_MC_*`
/// or `AY_*` variable reaches the child. DevCli commands are left untouched.
pub(crate) fn apply_route_env_for(route: &CompilerRoute, cmd: &mut Command) {
    apply_route_env_with(route, cmd, std::env::vars_os().map(|(key, _)| key));
}

/// [`apply_route_env_for`] with the keys of the environment the child would
/// inherit given explicitly.
pub(crate) fn apply_route_env_with<I>(route: &CompilerRoute, cmd: &mut Command, parent_keys: I)
where
    I: IntoIterator<Item = std::ffi::OsString>,
{
    if matches!(route, CompilerRoute::Trustc { .. }) {
        trustc_route::scrub_engine_env(cmd, parent_keys);
    }
}

/// [`apply_route_env_for`] for a concrete-playback compile.
pub(crate) fn apply_playback_route_env(route: &PlaybackRoute, cmd: &mut Command) {
    if matches!(route, PlaybackRoute::Trustc { .. }) {
        trustc_route::scrub_engine_env(cmd, std::env::vars_os().map(|(key, _)| key));
    }
}

/// Rustc arguments a route adds to compiles that select no engine backend
/// (concrete playback): the Trustc harness posture (T1-D6), nothing on DevCli.
pub(crate) fn route_posture_rustc_args(route: &PlaybackRoute) -> Vec<RustcArg> {
    match route {
        PlaybackRoute::DevCli => vec![],
        PlaybackRoute::Trustc { .. } => vec![RustcArg::from(TRUST_VERIFY_OFF)],
    }
}

/// The compiler program for concrete playback, which runs outside a session.
///
/// Playback builds a real test executable, so it never selects the engine
/// backend: DevCli runs trust-mc-compiler without `--kani-compiler`, and Trustc
/// runs trustc with its ordinary codegen backend after the trustc, PROVENANCE and
/// KEY checks. It neither requires a backend dylib nor names one: its route
/// marker says `backend=unused`.
pub(crate) fn playback_compiler(install: &InstallType, route: &PlaybackRoute) -> Result<PathBuf> {
    Ok(playback_compiler_and_identity(install, route)?.0)
}

/// [`playback_compiler`] with the Trustc identity it established (`None` on DevCli),
/// for the cargo playback, which runs the seal's cargo on that route.
pub(crate) fn playback_compiler_and_identity(
    install: &InstallType,
    route: &PlaybackRoute,
) -> Result<(PathBuf, Option<TrustcIdentity>)> {
    match route {
        PlaybackRoute::DevCli => Ok((install.kani_compiler()?, None)),
        PlaybackRoute::Trustc { trustc, key_dir } => {
            let identity = trustc_route::establish_playback_identity(trustc, key_dir)?;
            println!("{}", identity.marker());
            Ok((identity.trustc.clone(), Some(identity)))
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

    crate::ay_binary::set_allow_unpinned(args.allow_unpinned_ay);

    let original_backend = args.backend;
    if require_solver {
        args.backend =
            args.backend.resolve(args.ay_solver).map_err(|e| anyhow::anyhow!("{}", e))?;
        // Resolve and pin-check the external `ay` now, before anything is
        // compiled: an off-pin binary is refused up front rather than after a
        // build, and an allowed one is announced before any verdict. Direct
        // solving spawns no subprocess for the main query; the cover-check and
        // fallback sites it can still reach check lazily through the same cache.
        if args.ay_solver.requires_ay_binary() {
            crate::ay_binary::pinned_ay()?;
        }
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
