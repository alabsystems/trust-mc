// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Engine discovery and hand-off: where `trust-mc-driver` may live, what must
//! sit beside it, and how it is `exec`'d. Also the cheap probes (`--version`,
//! `--version-authority`, `ay --version`) that `doctor` and `version` report.

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::{env, fs};

use super::{BUILD_CMD, COMPILER, DRIVER, EXIT_NOT_READY, Fail, Front, VERSION};
use crate::setup;

/// A located engine: the sysroot that holds it and the driver binary itself.
pub(crate) struct Engine {
    pub(crate) sysroot: PathBuf,
    pub(crate) driver: PathBuf,
    pub(crate) source: &'static str,
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

    vec![
        Candidate { source: "TRUST_MC_SYSROOT", sysroot: env_sysroot, display: env_display },
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
            return Some(Engine { sysroot: candidate.sysroot?, driver, source: candidate.source });
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

/// The `ay` solver binary the engine will pick: first in the sysroot's `bin`,
/// then on `PATH` — the same order the engine's `PATH` sees after
/// [`exec_engine`] prepends `<sysroot>/bin`.
pub(crate) fn solver_path(engine: Option<&Engine>) -> Option<PathBuf> {
    let extra = engine.map(|e| vec![e.sysroot.join("bin")]).unwrap_or_default();
    find_on_path("ay", &extra)
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
                 (cd ../ay && cargo build --release -p ay --features cli),\n    \
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

    if needs_solver && solver_path(Some(&engine)).is_none() {
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

/// `trust-mc-driver --version` → e.g. `trust-mc 0.2.0`.
pub(crate) fn engine_version(engine: &Engine) -> Option<String> {
    capture(&engine.driver, &["--version"]).map(|s| s.trim().to_string())
}

/// What `--version-authority` tells us about the linked AY build.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Authority {
    pub(crate) trust_mc_sha: String,
    pub(crate) trust_mc_dirty: bool,
    pub(crate) ay_version: String,
    pub(crate) ay_pin: String,
    pub(crate) ay_linked_sha: String,
    pub(crate) matched: bool,
}

/// `trust-mc-driver --version-authority`. The engine fails closed (non-zero)
/// when the linked AY is dirty or off-pin; the error text is returned as-is.
pub(crate) fn engine_authority(engine: &Engine) -> Result<Authority, String> {
    let line = capture_either(&engine.driver, &["--version-authority"])?;
    parse_authority(&line).ok_or_else(|| format!("unexpected --version-authority output: {line}"))
}

/// Parse the single `trust_mc-version-authority key=value ...` line.
pub(crate) fn parse_authority(line: &str) -> Option<Authority> {
    let line = line.lines().find(|l| l.contains("trust_mc-version-authority"))?;
    let field = |key: &str| -> Option<String> {
        line.split_whitespace()
            .find_map(|kv| kv.strip_prefix(key).and_then(|rest| rest.strip_prefix('=')))
            .map(str::to_string)
    };
    Some(Authority {
        trust_mc_sha: field("trust_mc_sha")?,
        trust_mc_dirty: field("trust_mc_dirty").as_deref() == Some("1"),
        ay_version: field("ay_version")?,
        ay_pin: field("ay_pin")?,
        ay_linked_sha: field("ay_linked_sha")?,
        matched: field("ay_authority").as_deref() == Some("matched"),
    })
}

/// `ay --version` first line, e.g.
/// `ay 0.13.0+build.8212.5bd74669349190eae57027c91c0430b4980046ac@2026-08-20T15:54:57Z`.
pub(crate) fn solver_version(ay: &Path) -> Option<String> {
    capture(ay, &["--version"]).and_then(|s| s.lines().next().map(|l| l.trim().to_string()))
}

/// The 40-hex commit embedded in an `ay --version` line (`+build.<n>.<sha>`),
/// when the solver stamps one.
pub(crate) fn solver_build_sha(version_line: &str) -> Option<String> {
    let (_, after) = version_line.split_once("+build.")?;
    let (_, rest) = after.split_once('.')?;
    let sha: String = rest.chars().take_while(|c| c.is_ascii_hexdigit()).collect();
    if sha.len() == 40 { Some(sha) } else { None }
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
    fn the_authority_line_parses() {
        let line = "trust_mc-version-authority version=0.2.0 invocation=standalone \
                    trust_mc_sha=fcdc0472e27fd131167fd7508d428af9a9c6c69f trust_mc_dirty=1 \
                    ay_version=0.13.0 ay_pin=5bd74669349190eae57027c91c0430b4980046ac \
                    ay_linked_sha=5bd74669349190eae57027c91c0430b4980046ac ay_linked_dirty=0 \
                    ay_authority=matched";
        let a = parse_authority(line).unwrap();
        assert_eq!(a.ay_version, "0.13.0");
        assert_eq!(a.ay_pin, "5bd74669349190eae57027c91c0430b4980046ac");
        assert_eq!(a.ay_linked_sha, a.ay_pin);
        assert!(a.matched);
        assert!(a.trust_mc_dirty);
        assert!(parse_authority("error: linked AY build is dirty").is_none());
    }

    #[test]
    fn the_solver_build_sha_is_extracted_from_the_version_stamp() {
        let line =
            "ay 0.13.0+build.8212.5bd74669349190eae57027c91c0430b4980046ac@2026-08-20T15:54:57Z";
        assert_eq!(
            solver_build_sha(line).as_deref(),
            Some("5bd74669349190eae57027c91c0430b4980046ac")
        );
        assert_eq!(solver_build_sha("ay 0.5.0"), None);
        assert_eq!(solver_build_sha("ay 0.5.0+build.1.abcdef@now"), None);
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
