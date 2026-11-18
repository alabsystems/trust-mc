// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Engine discovery and hand-off: where `trust-mc-driver` may live, what must
//! sit beside it, and how it is `exec`'d. Also the cheap probes (`--version`,
//! `--version-authority`, `ay --version`) that `doctor` and `version` report.

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::sync::OnceLock;
use std::{env, fs};

use super::{BUILD_CMD, COMPILER, DRIVER, EXIT_NOT_READY, Fail, Front, VERSION};
use crate::setup;

/// A located engine: the sysroot that holds it and the driver binary itself.
pub(crate) struct Engine {
    pub(crate) sysroot: PathBuf,
    pub(crate) driver: PathBuf,
    pub(crate) source: &'static str,
    authority: OnceLock<Result<Authority, String>>,
}

impl Engine {
    /// The rustc driver the engine runs; it must sit beside the engine.
    pub(crate) fn compiler(&self) -> PathBuf {
        self.sysroot.join("bin").join(COMPILER)
    }
}

/// One place the engine may live.
pub(crate) struct Candidate {
    pub(crate) source: &'static str,
    /// The sysroot to use, when we can name one.
    pub(crate) sysroot: Option<PathBuf>,
    /// Always printable, even when nothing is configured.
    pub(crate) display: String,
}

impl Candidate {
    pub(crate) fn driver(&self) -> Option<PathBuf> {
        self.sysroot.as_ref().map(|s| s.join("bin").join(DRIVER))
    }

    pub(crate) fn found(&self) -> bool {
        self.driver().is_some_and(|d| d.is_file())
    }
}

/// Where the engine may live, in resolution order.
pub(crate) fn candidates() -> Vec<Candidate> {
    let env_sysroot = env::var_os("TRUST_MC_SYSROOT").map(PathBuf::from);
    let env_display = env_sysroot.as_ref().map_or_else(
        || "$TRUST_MC_SYSROOT is not set".to_string(),
        |dir| format!("{}/bin/{DRIVER}", dir.display()),
    );

    // When no local build exists yet, still name where one would go, so the
    // build command we print lands somewhere the reader can see.
    let dev = dev_sysroot();
    let dev_display = dev
        .clone()
        .or_else(|| env::current_dir().ok().map(|cwd| cwd.join("target").join("trust-mc")));

    let bundle = setup::kani_dir().ok();
    let bundle_display = bundle.as_ref().map_or_else(
        || format!("${{KANI_HOME:-~/.kani}}/kani-{VERSION}/bin/{DRIVER}"),
        |dir| format!("{}/bin/{DRIVER}", dir.display()),
    );

    // A package manager may install the complete bundle at any prefix. Resolve
    // it from the executable, so a PATH symlink works without a global
    // TRUST_MC_SYSROOT override or a checkout in the working directory.
    let colocated = env::current_exe().ok().and_then(|exe| colocated_sysroot(&exe));
    let colocated_display = colocated.as_ref().map_or_else(
        || format!("<executable bundle>/bin/{DRIVER}"),
        |dir| format!("{}/bin/{DRIVER}", dir.display()),
    );

    vec![
        Candidate { source: "TRUST_MC_SYSROOT", sysroot: env_sysroot, display: env_display },
        Candidate { source: "executable bundle", sysroot: colocated, display: colocated_display },
        Candidate {
            source: "local build",
            sysroot: dev,
            display: dev_display.map_or_else(
                || format!("<repo>/target/trust-mc/bin/{DRIVER}"),
                |dir| format!("{}/bin/{DRIVER}", dir.display()),
            ),
        },
        Candidate { source: "release bundle", sysroot: bundle, display: bundle_display },
    ]
}

fn colocated_sysroot(executable: &Path) -> Option<PathBuf> {
    let bin = executable.parent()?;
    if bin.file_name()? != "bin" || !bin.join(DRIVER).is_file() {
        return None;
    }
    Some(bin.parent()?.to_path_buf())
}

/// A sysroot produced by `build-trust-mc build-dev`, at `<repo>/target/trust-mc`.
///
/// Searched from the working directory upwards, then from the directory holding
/// this executable upwards, so both `trust-mc demo.rs` inside a checkout and
/// `target/release/trust-mc demo.rs` from anywhere find the build you just made.
fn dev_sysroot() -> Option<PathBuf> {
    let mut roots: Vec<PathBuf> = Vec::new();
    if let Ok(cwd) = env::current_dir() {
        roots.extend(cwd.ancestors().map(Path::to_path_buf));
    }
    if let Ok(exe) = env::current_exe()
        && let Some(dir) = exe.parent()
    {
        roots.extend(dir.ancestors().map(Path::to_path_buf));
    }
    roots
        .into_iter()
        .map(|root| root.join("target").join("trust-mc"))
        .find(|sysroot| sysroot.join("bin").join(DRIVER).is_file())
}

pub(crate) fn resolve_engine() -> Option<Engine> {
    for candidate in candidates() {
        if candidate.found() {
            let driver = candidate.driver()?;
            return Some(Engine {
                sysroot: candidate.sysroot?,
                driver,
                source: candidate.source,
                authority: OnceLock::new(),
            });
        }
    }
    None
}

/// The library sysroot directories the engine fails closed without, with the
/// feature each one serves.
pub(crate) fn library_dirs(sysroot: &Path) -> [(&'static str, &'static str, PathBuf); 3] {
    [
        ("lib", "verification (std + kani crate compiled for proofs)", sysroot.join("lib")),
        ("no_core/lib", "verify-std", sysroot.join("no_core").join("lib")),
        ("playback/lib", "concrete playback", sysroot.join("playback").join("lib")),
    ]
}

/// Is `name` runnable from `PATH` (or from an extra directory we prepend)?
pub(crate) fn find_on_path(name: &str, extra: &[PathBuf]) -> Option<PathBuf> {
    let mut dirs: Vec<PathBuf> = extra.to_vec();
    if let Some(path) = env::var_os("PATH") {
        dirs.extend(env::split_paths(&path));
    }
    dirs.into_iter().map(|dir| dir.join(name)).find(|candidate| is_executable(candidate))
}

pub(crate) fn is_executable(path: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::metadata(path).is_ok_and(|m| m.is_file() && m.permissions().mode() & 0o111 != 0)
    }
    #[cfg(not(unix))]
    {
        path.is_file()
    }
}

/// Names the `ay` binary the engine runs, in preference to `PATH`.
pub(crate) const AY_BIN_ENV: &str = "TRUST_MC_AY_BIN";
/// `1` lets the engine run an off-pin `ay`, with every success UNVALIDATED.
pub(crate) const ALLOW_UNPINNED_ENV: &str = "TRUST_MC_ALLOW_UNPINNED_AY";

/// `$TRUST_MC_AY_BIN`, when set to something non-empty. The engine runs that
/// binary and does not fall back to `PATH` while it is set.
pub(crate) fn solver_override() -> Option<PathBuf> {
    env::var_os(AY_BIN_ENV).filter(|value| !value.is_empty()).map(PathBuf::from)
}

/// The `ay` solver binary the engine will pick: `$TRUST_MC_AY_BIN` when set
/// (and nothing else, even when unusable), otherwise the release engine's
/// private helper, or development `bin`/PATH. The engine reports its default
/// through its existing authority probe; the probe is cached per invocation.
pub(crate) fn solver_path(engine: Option<&Engine>) -> Option<PathBuf> {
    if let Some(path) = solver_override() {
        return is_executable(&path).then_some(path);
    }
    if let Some(engine) = engine
        && bundled_solver_required(Some(engine))
    {
        return private_solver_path(&engine.driver);
    }
    let extra = engine.map(|e| vec![e.sysroot.join("bin")]).unwrap_or_default();
    find_on_path("ay", &extra)
}

pub(crate) fn bundled_solver_required(engine: Option<&Engine>) -> bool {
    engine
        .and_then(|e| engine_authority(e).ok())
        .is_some_and(|a| a.ay_runtime_default.as_deref() == Some("bundled"))
}

/// Mirror the release driver's private-file boundary before doctor executes a
/// version probe. Resolve relative to the actual driver, including a PATH link.
fn private_solver_path(driver: &Path) -> Option<PathBuf> {
    let driver = driver.canonicalize().ok()?;
    let bin = driver.parent().filter(|p| p.file_name().is_some_and(|n| n == "bin"))?;
    let directory = bin.parent()?.join("libexec");
    let metadata = fs::symlink_metadata(&directory).ok()?;
    if !metadata.is_dir() || metadata.file_type().is_symlink() {
        return None;
    }
    let helper = directory.join("ay");
    let metadata = fs::symlink_metadata(&helper).ok()?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || !is_executable(&helper)
        || helper.canonicalize().ok()? != helper
    {
        return None;
    }
    Some(helper)
}

/// The root manifest of the workspace this front door was built in.
const ROOT_MANIFEST: &str = include_str!("../../Cargo.toml");

/// The AY commit this front door's workspace pins: the `rev` of `ay` in the
/// root `Cargo.toml`'s `[workspace.dependencies]`, the same declaration the
/// engine checks its `ay` against. Doctor falls back to it when the engine is
/// missing or will not attest its own pin, so it can still call a binary
/// off-pin.
pub(crate) fn declared_ay_pin() -> Option<String> {
    parse_declared_ay_pin(ROOT_MANIFEST)
}

pub(crate) fn parse_declared_ay_pin(manifest: &str) -> Option<String> {
    let mut in_workspace_dependencies = false;
    for line in manifest.lines() {
        let line = line.trim();
        if line.starts_with('[') {
            in_workspace_dependencies = line == "[workspace.dependencies]";
            continue;
        }
        if !in_workspace_dependencies {
            continue;
        }
        // `ay = {...}`, not `ay-dpll = {...}` or `ay_bindings = {...}`.
        let Some(table) =
            line.strip_prefix("ay").and_then(|rest| rest.trim_start().strip_prefix('='))
        else {
            continue;
        };
        let (_, after_rev) = table.split_once("rev")?;
        let value = after_rev.trim_start().strip_prefix('=')?.trim_start().strip_prefix('"')?;
        let sha = value.split('"').next()?;
        return is_full_commit(sha).then(|| sha.to_string());
    }
    None
}

fn is_full_commit(value: &str) -> bool {
    value.len() == 40 && value.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// How an `ay` binary relates to the pinned AY commit. Mirrors the engine's
/// `PinStatus` (`trust-mc-driver/src/ay_binary.rs`); the engine is what
/// refuses, doctor only reports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SolverPin {
    Matched,
    OtherCommit(String),
    DirtyBuild(String),
    Unstamped,
    NoVersion,
}

pub(crate) fn solver_pin(version: Option<&str>, pin: &str) -> SolverPin {
    let Some(version) = version else {
        return SolverPin::NoVersion;
    };
    match solver_build_stamp(version) {
        None => SolverPin::Unstamped,
        Some((commit, true)) => SolverPin::DirtyBuild(commit),
        Some((commit, false)) if commit == pin => SolverPin::Matched,
        Some((commit, false)) => SolverPin::OtherCommit(commit),
    }
}

impl SolverPin {
    /// The same wording the engine's refusal uses.
    pub(crate) fn problem(&self) -> String {
        match self {
            SolverPin::Matched => "none: it is the pinned commit".to_string(),
            SolverPin::OtherCommit(commit) => {
                format!("it was built from AY commit {commit}, not the pinned commit")
            }
            SolverPin::DirtyBuild(commit) => format!(
                "it was built from a dirty AY tree at {commit}, so it is not the pinned commit"
            ),
            SolverPin::Unstamped => "its version line carries no `+build.<n>.<commit>` stamp, \
                                     so its commit cannot be checked"
                .to_string(),
            SolverPin::NoVersion => {
                "it did not answer `ay --version`, so its commit cannot be checked".to_string()
            }
        }
    }
}

/// The fix for an off-pin `ay`, word for word what the engine prints when it
/// refuses one (`trust-mc-driver/src/ay_binary.rs`, `unpinned_ay_fix`);
/// `tests/cli.rs` compares the two binaries' output.
pub(crate) fn unpinned_ay_fix(pin: &str) -> String {
    format!(
        "build `ay` at the pinned AY commit and point trust-mc at it:\n    \
         git -C <ay checkout> checkout {pin}\n    \
         targo --unverified build --release --manifest-path <ay checkout>/Cargo.toml -p ay --features cli\n    \
         export {AY_BIN_ENV}=<ay checkout>/target/release/ay\n  \
         ...or run anyway, with every success reported as SUCCESSFUL (UNVALIDATED):\n    \
         pass --allow-unpinned-ay, or set {ALLOW_UNPINNED_ENV}=1"
    )
}

/// A sibling `ay` checkout whose solver binary is already built, if there is one.
fn nearby_ay_binary() -> Option<PathBuf> {
    let cwd = env::current_dir().ok()?;
    for ancestor in cwd.ancestors() {
        for profile in ["release", "debug"] {
            let candidate = ancestor.join("ay").join("target").join(profile).join("ay");
            if is_executable(&candidate) {
                return Some(candidate);
            }
        }
    }
    None
}

pub(crate) fn solver_hint() -> String {
    match nearby_ay_binary() {
        Some(binary) => {
            let dir = binary.parent().map(Path::to_path_buf).unwrap_or_default();
            format!("export PATH=\"{}:$PATH\"", dir.display())
        }
        None => "build the AY solver in a sibling checkout of alabsystems/ay\n    \
                 (cd ../ay && targo --unverified build --release -p ay --features cli),\n    \
                 then put its target/release directory on PATH"
            .to_string(),
    }
}

// ---------------------------------------------------------------------------
// Running the engine
// ---------------------------------------------------------------------------

/// Check the environment, then hand off to the engine as `trust-mc`.
pub(crate) fn drive(args: Vec<OsString>, needs_solver: bool, verbose: bool) -> Front<ExitCode> {
    drive_as("trust-mc", args, needs_solver, verbose)
}

/// Check the environment, then hand off to the engine under the given
/// invocation identity (`trust-mc` or `cargo-trust-mc`).
pub(crate) fn drive_as(
    arg0: &str,
    args: Vec<OsString>,
    needs_solver: bool,
    verbose: bool,
) -> Front<ExitCode> {
    let Some(engine) = resolve_engine() else {
        return Err(Fail::not_ready(engine_missing_report()));
    };

    let missing: Vec<&str> = library_dirs(&engine.sysroot)
        .iter()
        .filter(|(_, _, dir)| !dir.is_dir())
        .map(|(label, _, _)| *label)
        .collect();
    if !missing.is_empty() {
        return Err(Fail::not_ready(format!(
            "error: the trust-mc library sysroot is incomplete\n\n  \
             found the engine:   {}\n  \
             but missing:        {}\n\n\
             The engine fails closed without its pre-compiled libraries. Rebuild them with:\n\n    \
             {BUILD_CMD}\n",
            engine.driver.display(),
            missing.join(", ")
        )));
    }

    let solver = needs_solver.then(|| solver_path(Some(&engine))).flatten();
    if needs_solver
        && solver.is_none()
        && let Some(path) = solver_override()
    {
        return Err(Fail::not_ready(format!(
            "error: {AY_BIN_ENV}={} is not an executable file\n\n\
             trust-mc runs the `ay` solver {AY_BIN_ENV} names in preference to PATH, and\n\
             does not fall back to PATH while it is set.\n\n\
             To fix, point it at a built `ay` binary, or unset it:\n\n    unset {AY_BIN_ENV}\n",
            path.display()
        )));
    }

    if needs_solver && solver.is_none() && bundled_solver_required(Some(&engine)) {
        return Err(Fail::not_ready(
            "error: this engine's private libexec/ay is unavailable\n       \
             Reinstall the complete trust-mc bundle. No PATH fallback is allowed.\n"
                .to_string(),
        ));
    }
    if needs_solver && solver.is_none() {
        return Err(Fail::not_ready(format!(
            "error: the `ay` SMT solver is not on PATH\n\n\
             trust-mc discharges bounded (BMC) proof obligations by running `ay`, and the\n\
             engine checks for it before every verification run. `trust-mc --version`,\n\
             `--help`, `explain`, `example`, `doctor` and `trust-mc list <FILE.rs>` do not\n\
             need it.\n\n\
             To fix:\n\n    {}\n",
            solver_hint()
        )));
    }

    exec_engine(&engine, arg0, &args, verbose)
}

/// `exec` the engine with our environment fixups, and adopt its exit code.
pub(crate) fn exec_engine(
    engine: &Engine,
    arg0: &str,
    args: &[OsString],
    verbose: bool,
) -> Front<ExitCode> {
    let bin_dir = engine.sysroot.join("bin");
    let pyroot = engine.sysroot.join("pyroot");

    // Same environment preparation the historical proxy did: let the bundle's
    // own binaries and python packages win, and strip rustup's toolchain
    // library paths so the engine loads the rustc it was linked against.
    let pythonpath =
        crate::prepend_search_path(std::slice::from_ref(&pyroot), env::var_os("PYTHONPATH"))
            .map_err(|e| Fail::other(format!("error: {e}")))?;
    let path = crate::prepend_search_path(&[bin_dir, pyroot.join("bin")], env::var_os("PATH"))
        .map_err(|e| Fail::other(format!("error: {e}")))?;
    crate::fixup_dynamic_linking_environment();

    // Release bundles record the toolchain they link against; local builds do
    // not ship that file and must keep the caller's toolchain selection.
    let version_file = engine.sysroot.join("rust-toolchain-version");
    if let Ok(toolchain) = fs::read_to_string(&version_file) {
        crate::set_process_env_var("RUSTUP_TOOLCHAIN", toolchain.trim());
    }

    if verbose {
        eprintln!("[trust-mc] engine ({}): {}", engine.source, engine.driver.display());
        eprintln!(
            "[trust-mc] running: {} {}",
            arg0,
            args.iter().map(|a| a.to_string_lossy().into_owned()).collect::<Vec<_>>().join(" ")
        );
    }

    let mut cmd = Command::new(&engine.driver);
    cmd.args(args).env("PYTHONPATH", pythonpath).env("PATH", path);
    // The engine reads its invocation identity from argv[0].
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.arg0(arg0);
    }
    #[cfg(not(unix))]
    let _ = arg0;

    // Spawn rather than `status()` so a termination aimed at the front-door
    // PID can be forwarded to the engine. Without this the engine outlives us
    // as an orphan and keeps its solver subtree running (see `super::cancel`).
    let mut child = match cmd.spawn() {
        Ok(child) => child,
        Err(e) => {
            return Err(Fail {
                msg: format!(
                    "error: could not run the verification engine\n  {}\n  {e}",
                    engine.driver.display()
                ),
                code: EXIT_NOT_READY,
            });
        }
    };
    super::cancel::watch_engine(child.id());

    let waited = child.wait();
    super::cancel::forget_engine();

    match waited {
        // A signal-terminated engine has no exit code; that stays FAILURE, as
        // it did when this was a `status()` call.
        Ok(status) => Ok(status
            .code()
            .and_then(|c| u8::try_from(c).ok())
            .map_or(ExitCode::FAILURE, ExitCode::from)),
        Err(e) => Err(Fail {
            msg: format!(
                "error: could not run the verification engine\n  {}\n  {e}",
                engine.driver.display()
            ),
            code: EXIT_NOT_READY,
        }),
    }
}

/// `trust-mc flags [--all]`: the engine's own flag reference.
///
/// The engine's fast path answers a bare `--help` with the short help (the
/// flags marked `hide_short_help` are omitted); any extra argument makes clap
/// render the long help, which `--all` requests.
pub(crate) fn show_engine_flags(rest: &[OsString]) -> Front<ExitCode> {
    let mut all = false;
    for arg in rest {
        match arg.to_str() {
            Some("--all" | "-a") => all = true,
            Some(other) => {
                return Err(Fail::usage(format!(
                    "error: `flags` takes no arguments other than --all, got {other}\n       \
                     Usage: trust-mc flags [--all]"
                )));
            }
            None => return Err(Fail::usage("error: `flags` takes no arguments other than --all")),
        }
    }
    let Some(engine) = resolve_engine() else {
        return Err(Fail::not_ready(format!(
            "{}\n  The engine's flag families are summarized without it: trust-mc explain flags\n",
            engine_missing_report()
        )));
    };
    println!(
        "# Flags accepted by the verification engine ({}).\n\
         # `trust-mc` forwards every flag it does not translate (see `trust-mc explain flags`).\n",
        engine.driver.display()
    );
    let args: Vec<OsString> = if all {
        vec![OsString::from("--help"), OsString::from("--quiet")]
    } else {
        vec![OsString::from("-h")]
    };
    exec_engine(&engine, "trust-mc", &args, false)
}

// ---------------------------------------------------------------------------
// Probes (used by doctor / version)
// ---------------------------------------------------------------------------

/// Run `program args...` and return its combined stdout+stderr when it exits
/// successfully; `None` if it could not be run or failed.
pub(crate) fn capture(program: &Path, args: &[&str]) -> Option<String> {
    capture_with_env(program, args, &[])
}

pub(crate) fn capture_with_env(
    program: &Path,
    args: &[&str],
    envs: &[(&str, &OsStr)],
) -> Option<String> {
    let mut cmd = Command::new(program);
    cmd.args(args).stdin(Stdio::null());
    for (k, v) in envs {
        cmd.env(k, v);
    }
    let out = cmd.output().ok()?;
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    if out.status.success() { Some(text) } else { None }
}

/// Like [`capture`], but also return the status on failure so a caller can
/// show the failure text.
pub(crate) fn capture_either(program: &Path, args: &[&str]) -> Result<String, String> {
    let out = Command::new(program)
        .args(args)
        .stdin(Stdio::null())
        .output()
        .map_err(|e| format!("could not run {}: {e}", program.display()))?;
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    let text = text.trim().to_string();
    if out.status.success() { Ok(text) } else { Err(text) }
}

/// The driver reports its own package version. Older drivers can answer
/// `--version` even when they cannot provide authority metadata.
pub(crate) fn engine_version(engine: &Engine, authority: Option<&Authority>) -> Option<String> {
    if let Some(version) = authority.and_then(|a| a.version.as_deref()) {
        return Some(format!("trust-mc {version}"));
    }
    let output = capture(&engine.driver, &["--version"])?;
    output.lines().map(str::trim).find(|line| !line.is_empty()).map(str::to_owned)
}

/// What `--version-authority` tells us about the linked AY build.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Authority {
    pub(crate) version: Option<String>,
    pub(crate) trust_mc_sha: String,
    pub(crate) trust_mc_dirty: bool,
    pub(crate) ay_version: String,
    pub(crate) ay_pin: String,
    pub(crate) ay_linked_sha: String,
    pub(crate) linked_at_pin: bool,
    pub(crate) ay_runtime_default: Option<String>,
}

/// `trust-mc-driver --version-authority`. The engine fails closed (non-zero)
/// when the linked AY is dirty or off-pin; the error text is returned as-is.
pub(crate) fn engine_authority(engine: &Engine) -> Result<Authority, String> {
    engine
        .authority
        .get_or_init(|| {
            let line = capture_either(&engine.driver, &["--version-authority"])?;
            parse_authority(&line)
                .ok_or_else(|| format!("unexpected --version-authority output: {line}"))
        })
        .clone()
}

/// Parse the single `trust_mc-version-authority key=value ...` line.
pub(crate) fn parse_authority(line: &str) -> Option<Authority> {
    let line = line.lines().find(|l| l.contains("trust_mc-version-authority"))?;
    let field = |key: &str| -> Option<String> {
        line.split_whitespace()
            .find_map(|kv| kv.strip_prefix(key).and_then(|rest| rest.strip_prefix('=')))
            .map(str::to_string)
    };
    let ay_runtime_default = field("ay_runtime_default");
    if ay_runtime_default.as_deref().is_some_and(|mode| !matches!(mode, "bundled" | "path")) {
        return None;
    }
    let ay_pin = field("ay_pin")?;
    let ay_linked_sha = field("ay_linked_sha")?;
    let linked_at_pin = ay_linked_sha == ay_pin;
    Some(Authority {
        version: field("version").filter(|version| !version.is_empty()),
        trust_mc_sha: field("trust_mc_sha")?,
        trust_mc_dirty: field("trust_mc_dirty").as_deref() == Some("1"),
        ay_version: field("ay_version")?,
        ay_pin,
        ay_linked_sha,
        linked_at_pin,
        ay_runtime_default,
    })
}

/// `ay --version` first line, e.g.
/// `ay 0.13.0+build.8212.5bd74669349190eae57027c91c0430b4980046ac@2026-08-20T15:54:57Z`.
pub(crate) fn solver_version(ay: &Path) -> Option<String> {
    capture(ay, &["--version"]).and_then(|s| s.lines().next().map(|l| l.trim().to_string()))
}

/// The build stamp of an `ay --version` line, `+build.<n>.<commit>[-dirty]`:
/// the 40-hex commit and whether the build was dirty. Strict in the same way
/// the engine is — a decimal increment, exactly 40 lowercase hex digits, then
/// `-dirty`, `@`, whitespace or the end.
pub(crate) fn solver_build_stamp(version_line: &str) -> Option<(String, bool)> {
    let (_, after) = version_line.split_once("+build.")?;
    let (increment, rest) = after.split_once('.')?;
    if increment.is_empty() || !increment.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    if rest.bytes().take_while(u8::is_ascii_hexdigit).count() != 40 {
        return None;
    }
    let (commit, tail) = rest.split_at(40);
    if !is_full_commit(commit) {
        return None;
    }
    let (dirty, tail) = match tail.strip_prefix("-dirty") {
        Some(tail) => (true, tail),
        None => (false, tail),
    };
    if !(tail.is_empty() || tail.starts_with('@') || tail.starts_with(char::is_whitespace)) {
        return None;
    }
    Some((commit.to_string(), dirty))
}

// ---------------------------------------------------------------------------
// Reports
// ---------------------------------------------------------------------------

pub(crate) fn engine_missing_report() -> String {
    let mut report = format!(
        "error: the trust-mc verification engine is not installed\n\n  \
         looked for `{DRIVER}`, in order:\n"
    );
    for candidate in candidates() {
        report.push_str(&format!(
            "    [{}] {}  ({})\n",
            mark(candidate.found()),
            candidate.display,
            candidate.source
        ));
    }
    report.push_str(&format!(
        "\n  `trust-mc --version`, `--help`, `explain`, `example` and `doctor` work without it;\n  \
         verification needs the engine and its pre-compiled library sysroot.\n\n  \
         If you have already built one, point at it:\n\n      \
         export TRUST_MC_SYSROOT=<checkout>/target/trust-mc\n\n  \
         To build it from a trust-mc checkout (no network):\n\n      {BUILD_CMD}\n\n  \
         Or install a published release bundle:\n\n      trust-mc setup\n"
    ));
    report
}

pub(crate) fn mark(present: bool) -> char {
    if present { 'x' } else { ' ' }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "a panicking assertion is the point in tests")]
mod tests {
    use super::*;

    #[test]
    fn installed_front_door_finds_its_own_bundle_without_a_checkout() {
        let unique =
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let root = env::temp_dir().join(format!("trust-mc-bundle-{}-{unique}", std::process::id()));
        let bin = root.join("bin");
        fs::create_dir_all(&bin).unwrap();
        let executable = bin.join("trust-mc");
        // A front door on its own must not claim an installed engine.
        assert_eq!(colocated_sysroot(&executable), None);
        fs::write(bin.join(DRIVER), b"fixture").unwrap();
        assert_eq!(colocated_sysroot(&executable), Some(root.clone()));
        // A conventional cargo output remains the existing local-build lane.
        let release = root.join("target/release");
        fs::create_dir_all(&release).unwrap();
        fs::write(release.join(DRIVER), b"fixture").unwrap();
        assert_eq!(colocated_sysroot(&release.join("trust-mc")), None);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn the_authority_line_parses() {
        let line = "trust_mc-version-authority version=0.2.0 invocation=standalone \
                    trust_mc_sha=fcdc0472e27fd131167fd7508d428af9a9c6c69f trust_mc_dirty=1 \
                    ay_version=0.13.0 ay_pin=5bd74669349190eae57027c91c0430b4980046ac \
                    ay_linked_sha=5bd74669349190eae57027c91c0430b4980046ac ay_linked_dirty=0 \
                    ay_authority=matched";
        let a = parse_authority(line).unwrap();
        assert_eq!(a.version.as_deref(), Some("0.2.0"));
        assert_eq!(a.ay_version, "0.13.0");
        assert_eq!(a.ay_pin, "5bd74669349190eae57027c91c0430b4980046ac");
        assert_eq!(a.ay_linked_sha, a.ay_pin);
        assert!(a.linked_at_pin);
        assert!(a.trust_mc_dirty);
        assert_eq!(a.ay_runtime_default, None, "older driver output remains supported");
        assert_eq!(
            parse_authority(&format!("{line} ay_runtime_default=bundled"))
                .unwrap()
                .ay_runtime_default
                .as_deref(),
            Some("bundled")
        );
        assert!(parse_authority(&format!("{line} ay_runtime_default=unknown")).is_none());
        assert!(parse_authority("error: linked AY build is dirty").is_none());
        let bundled = line.replace("ay_authority=matched", "ay_authority=contains-pin");
        assert!(parse_authority(&bundled).unwrap().linked_at_pin);
        let descendant = bundled.replace(
            "ay_linked_sha=5bd74669349190eae57027c91c0430b4980046ac",
            "ay_linked_sha=fcdc0472e27fd131167fd7508d428af9a9c6c69f",
        );
        assert!(!parse_authority(&descendant).unwrap().linked_at_pin);
    }

    #[cfg(unix)]
    #[test]
    fn package_private_solver_follows_the_actual_driver_and_refuses_escaped_files() {
        use std::os::unix::fs::{PermissionsExt, symlink};
        let unique =
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let root =
            env::temp_dir().join(format!("trust-mc-private-ay-{}-{unique}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let root = root.canonicalize().unwrap();
        let bundle = root.join("bundle");
        fs::create_dir_all(bundle.join("bin")).unwrap();
        fs::create_dir(bundle.join("libexec")).unwrap();
        let driver = bundle.join("bin/trust-mc-driver");
        fs::write(&driver, []).unwrap();
        let helper = bundle.join("libexec/ay");
        fs::write(&helper, []).unwrap();
        fs::set_permissions(&helper, fs::Permissions::from_mode(0o755)).unwrap();
        let driver_link = root.join("driver-link");
        symlink(&driver, &driver_link).unwrap();
        // The global PATH is irrelevant to a valid private helper.
        assert_eq!(private_solver_path(&driver_link), Some(helper.clone()));
        fs::remove_file(&helper).unwrap();
        assert_eq!(private_solver_path(&driver_link), None);
        let outside = root.join("outside-ay");
        fs::write(&outside, []).unwrap();
        fs::set_permissions(&outside, fs::Permissions::from_mode(0o755)).unwrap();
        symlink(&outside, &helper).unwrap();
        assert_eq!(private_solver_path(&driver_link), None);
        fs::remove_file(&helper).unwrap();
        fs::remove_dir(bundle.join("libexec")).unwrap();
        symlink(&root, bundle.join("libexec")).unwrap();
        assert_eq!(private_solver_path(&driver_link), None);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn the_solver_build_stamp_is_extracted_strictly() {
        let pin = "94bf24d0f07fbcbfceea7ca3c509f8f35e9a8322";
        assert_eq!(
            solver_build_stamp(&format!("ay 0.26.0+build.9281.{pin}@2026-09-11T02:47:31Z")),
            Some((pin.to_string(), false))
        );
        assert_eq!(
            solver_build_stamp(&format!("ay 0.26.0+build.1.{pin}-dirty@now")),
            Some((pin.to_string(), true))
        );
        assert_eq!(solver_build_stamp("ay 0.5.0"), None);
        assert_eq!(solver_build_stamp("ay 0.5.0+build.1.abcdef@now"), None);
        assert_eq!(solver_build_stamp(&format!("ay 0.26.0+build.1.{pin}0@now")), None);
        assert_eq!(solver_build_stamp(&format!("ay 0.26.0+build.x.{pin}@now")), None);
        assert_eq!(
            solver_build_stamp(&format!("ay 0.26.0+build.1.{}@now", pin.to_ascii_uppercase())),
            None
        );
    }

    #[test]
    fn solver_pin_names_every_off_pin_shape() {
        let pin = "94bf24d0f07fbcbfceea7ca3c509f8f35e9a8322";
        let old = "dd4de9e94e0bb94a458641c7e5aa814c8aeadf59";
        let line = |commit: &str| format!("ay 0.26.0+build.9281.{commit}@2026-09-11T02:47:31Z");
        assert_eq!(solver_pin(Some(&line(pin)), pin), SolverPin::Matched);
        assert_eq!(solver_pin(Some(&line(old)), pin), SolverPin::OtherCommit(old.to_string()));
        assert_eq!(
            solver_pin(Some(&format!("ay 0.26.0+build.1.{pin}-dirty")), pin),
            SolverPin::DirtyBuild(pin.to_string())
        );
        assert_eq!(solver_pin(Some("ay 0.26.0"), pin), SolverPin::Unstamped);
        assert_eq!(solver_pin(None, pin), SolverPin::NoVersion);
        assert!(SolverPin::OtherCommit(old.to_string()).problem().contains(old));
    }

    #[test]
    fn the_declared_ay_pin_comes_from_workspace_dependencies_only() {
        let pin = "94bf24d0f07fbcbfceea7ca3c509f8f35e9a8322";
        let manifest = format!(
            "[workspace.dependencies]\n\
             ay-dpll = {{ git = \"https://github.com/alabsystems/ay.git\", rev = \"{}\" }}\n\
             ay_bindings = {{ rev = \"{}\", package = \"ay-bindings\" }}\n\
             ay = {{ version = \"0.26.0\", git = \"https://github.com/alabsystems/ay.git\", rev = \"{pin}\", default-features = false }}\n\
             \n[patch.\"https://github.com/alabsystems/ay.git\"]\nay = {{ path = \"../ay/crates/ay\" }}\n",
            "a".repeat(40),
            "b".repeat(40),
        );
        assert_eq!(parse_declared_ay_pin(&manifest).as_deref(), Some(pin));
        assert_eq!(
            parse_declared_ay_pin(&format!("[patch.x]\nay = {{ rev = \"{pin}\" }}\n")),
            None
        );
        assert_eq!(
            parse_declared_ay_pin("[workspace.dependencies]\nay = { path = \"../ay\" }\n"),
            None
        );
        assert_eq!(
            parse_declared_ay_pin("[workspace.dependencies]\nay = { rev = \"abc\" }\n"),
            None
        );

        let real = declared_ay_pin().expect("this workspace pins ay by rev");
        assert!(is_full_commit(&real), "{real}");
    }

    #[test]
    fn the_unpinned_fix_names_the_pin_the_override_and_the_escape_hatch() {
        let fix = unpinned_ay_fix("94bf24d0f07fbcbfceea7ca3c509f8f35e9a8322");
        assert!(
            fix.contains("git -C <ay checkout> checkout 94bf24d0f07fbcbfceea7ca3c509f8f35e9a8322")
        );
        assert!(fix.contains("export TRUST_MC_AY_BIN=<ay checkout>/target/release/ay"));
        assert!(fix.contains("--allow-unpinned-ay"));
        assert!(fix.contains("TRUST_MC_ALLOW_UNPINNED_AY=1"));
    }

    #[test]
    fn library_dirs_name_the_three_trees_the_engine_needs() {
        let dirs = library_dirs(Path::new("/sysroot"));
        let labels: Vec<&str> = dirs.iter().map(|(l, _, _)| *l).collect();
        assert_eq!(labels, ["lib", "no_core/lib", "playback/lib"]);
        assert_eq!(dirs[1].2, PathBuf::from("/sysroot/no_core/lib"));
    }

    #[test]
    fn the_missing_engine_report_names_every_candidate_and_the_build_command() {
        let report = engine_missing_report();
        assert!(report.contains("TRUST_MC_SYSROOT"));
        assert!(report.contains("local build"));
        assert!(report.contains("release bundle"));
        assert!(report.contains(BUILD_CMD));
    }
}
