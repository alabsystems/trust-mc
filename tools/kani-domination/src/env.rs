// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Environment discovery: trust-mc repo root, the verifier binary + sysroot,
//! the `ay` SMT binary, the Kani corpus checkout, and the provenance authority
//! tuple (including the runner attestation that names the exact binaries).
//!
//! # Where the Kani corpus lives, and why
//!
//! Cargo discovers configuration from the directory it runs in upwards, so a
//! Kani checkout under `<trust-mc>/target` made every cargo-unit row inherit
//! trust-mc's own `.cargo/config.toml` (then its rustc-wrapper and a Trust-only
//! `-Ztrust-verify=off`, since removed) and die before measuring anything. The corpus
//! therefore defaults to the user cache — `~/Library/Caches` on macOS,
//! `$XDG_CACHE_HOME` or `~/.cache` elsewhere — at
//! `trust-mc/kani-domination/<kani-rev>`, outside every cargo workspace.
//! `--kani-dir` or `KANI_DOMINATION_CORPUS_DIR` names another checkout, and a
//! run with cargo units refuses any location that would inherit an ancestor's
//! cargo configuration. Reports and per-test build dirs stay under
//! `<trust-mc>/target/kani-domination/`.

use anyhow::{Context, Result, bail};
use sha2::{Digest, Sha256};
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::model::{Engine, HostLoad, KaniAttestation, Provenance, RunnerAttestation, SCORER_VERSION, iso8601_utc};

/// Names the `kani` launcher for `--engine kani` (else `~/.cargo/bin/kani`).
pub const KANI_BIN_ENV: &str = "KANI_BIN";

/// STOCK-AS-ORACLE (owner ruling 2026-09-29: kept, pinned, never a blocker):
/// the one upstream Kani release `--engine kani` runs. The 0.67.0 release and
/// the corpus-rev source build (`kani-src`) both report it.
pub const KANI_ORACLE: &str = "0.67.0";

/// Environment variable naming the Kani corpus checkout (same as `--kani-dir`).
pub const CORPUS_DIR_ENV: &str = "KANI_DOMINATION_CORPUS_DIR";

/// Holds one Trust build for every tool `scripts/resolve-trust-tool.sh` resolves
/// (a numbered seal directory, or a rustup toolchain linked to one).
pub const TRUST_TOOLCHAIN_OVERRIDE_ENV: &str = "TRUST_MC_TRUST_TOOLCHAIN";

/// Toolchain and cargo-build selectors (and the driver's off-pin-solver switch)
/// the runner removes from every verifier child. They describe how the
/// *runner* was launched (for example `cargo run` under trust-mc's workspace
/// config, or a shell that exported `RUSTFLAGS` for the frozen lane), not the
/// corpus, and each one silently changes what a cargo unit builds with.
/// `RUSTFLAGS` is set again per test from Kani's own `kani-rustflags` header
/// when the test declares one.
pub const SCRUBBED_CHILD_ENV: &[&str] = &[
    "RUSTUP_TOOLCHAIN",
    "RUSTC",
    "RUSTDOC",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_TARGET",
    "CARGO_TARGET_DIR",
    "CARGO_BUILD_TARGET_DIR",
    "RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
    "CARGO_BUILD_RUSTFLAGS",
    "RUSTDOCFLAGS",
    "CARGO_ENCODED_RUSTDOCFLAGS",
    "TRUST_PRIVATE_DRIVER_CRATES",
    "TRUST_PRIVATE_SYSROOTS",
    // Not a toolchain selector: the driver's escape hatch for an off-pin `ay`.
    // A ledger row must come from the pinned solver, so a child never inherits
    // it; without it the driver refuses an off-pin binary and the row is an
    // error, never a demoted "success" (`runner.rs` drops the flag spelling).
    "TRUST_MC_ALLOW_UNPINNED_AY",
];

/// Cargo reads any `CARGO_<SECTION>_<KEY>` variable as configuration, so the
/// named list above cannot be complete: `CARGO_TARGET_<triple>_RUSTFLAGS`,
/// `CARGO_TARGET_<triple>_LINKER`, `CARGO_PROFILE_*`, `CARGO_UNSTABLE_*` and
/// `CARGO_HOST_<triple>_RUSTFLAGS` (the `[host]` tables, which reach build
/// scripts and proc-macros on the Trustc route) each change what a cargo unit
/// builds with just as silently. Every variable with one of these prefixes is
/// removed too.
pub const SCRUBBED_CHILD_ENV_PREFIXES: &[&str] =
    &["CARGO_BUILD_", "CARGO_TARGET_", "CARGO_PROFILE_", "CARGO_UNSTABLE_", "CARGO_HOST_"];

/// The variables among `keys` that the runner removes from verifier children:
/// the exact names in [`SCRUBBED_CHILD_ENV`] plus every
/// [`SCRUBBED_CHILD_ENV_PREFIXES`] match, sorted.
pub fn scrubbed_child_env_keys<I, K>(keys: I) -> Vec<String>
where
    I: IntoIterator<Item = K>,
    K: AsRef<std::ffi::OsStr>,
{
    let mut out: Vec<String> = keys
        .into_iter()
        .filter_map(|k| k.as_ref().to_str().map(str::to_string))
        .filter(|k| {
            SCRUBBED_CHILD_ENV.contains(&k.as_str())
                || SCRUBBED_CHILD_ENV_PREFIXES.iter().any(|p| k.starts_with(p))
        })
        .collect();
    out.sort();
    out.dedup();
    out
}

/// [`scrubbed_child_env_keys`] over the runner's own environment.
pub fn scrubbed_child_env_present() -> Vec<String> {
    scrubbed_child_env_keys(std::env::vars_os().map(|(k, _)| k))
}

/// Resolved paths and binaries for a domination run.
pub struct Env {
    /// trust-mc repository root (the tool's home: reports and per-unit build
    /// dirs live under its `target/`, whichever engine runs).
    pub repo: PathBuf,
    /// The engine every unit runs on, with its resolved binaries.
    pub engine: EngineEnv,
    /// The `cargo` binary for cargo-project test units (its directory is
    /// prepended to PATH so the driver's / Kani's internal `cargo` calls resolve).
    pub cargo: Option<PathBuf>,
    /// Cache root for per-test build artifacts and run reports.
    pub cache: PathBuf,
    /// The Kani corpus checkout.
    pub kani: PathBuf,
}

/// The engine-specific half of [`Env`].
pub enum EngineEnv {
    TrustMc(TrustMcEnv),
    Kani(KaniEnv),
}

/// The trust-mc verifier: driver, sysroot, pinned solver and attested toolchain.
pub struct TrustMcEnv {
    /// The `trust-mc-driver` verifier binary.
    pub verifier: PathBuf,
    /// `TRUST_MC_SYSROOT` to export for the verifier.
    pub sysroot: PathBuf,
    /// The `ay` SMT binary (its directory is prepended to PATH for the verifier).
    pub ay: PathBuf,
    /// How `ay` was found: `AY_BIN`, `TRUST_MC_AY_BIN`, `pinned-cache`, `sibling`, or `PATH`.
    pub ay_source: &'static str,
    /// The Trust toolchain the run attests, resolved once at discovery.
    pub trust: TrustToolchain,
}

/// An upstream Kani install: the `kani` launcher, `cargo-kani` beside it, and
/// the home the launcher dispatches into. Kani picks its own toolchain
/// (`<home>/rust-toolchain-version`); the runner never forces one.
pub struct KaniEnv {
    pub kani: PathBuf,
    pub cargo_kani: PathBuf,
    /// `KANI_BIN` or `~/.cargo/bin`.
    pub source: &'static str,
    /// First line of `kani --version`, e.g. `kani 0.67.0`.
    pub version: String,
    pub home: Option<PathBuf>,
    pub toolchain: Option<String>,
    /// For the default `~/.cargo/bin` launcher: the set-up home every Kani
    /// child gets as `KANI_HOME`, so the launcher never sets itself up.
    pub launcher_home: Option<PathBuf>,
}

/// The Trust toolchain a run attests, as `scripts/resolve-trust-tool.sh` resolves
/// it: rust-toolchain.toml's channel, or `TRUST_MC_TRUST_TOOLCHAIN` when set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustToolchain {
    /// `rust-toolchain.toml`'s channel.
    pub channel: String,
    /// `TRUST_MC_TRUST_TOOLCHAIN`, when set.
    pub override_value: Option<String>,
    /// `commit-hash` of the resolved trustc (`<unknown>` only without an override).
    pub commit: String,
    /// The resolved sysroot.
    pub sysroot: Option<PathBuf>,
    /// The sysroot's directory name when it is a numbered seal (`store/trust/8571`).
    pub seal_build: Option<String>,
    /// `artifact_driver_sha256` from the sysroot's PROVENANCE.
    pub artifact_driver_sha256: Option<String>,
}

/// Run `scripts/resolve-trust-tool.sh <what>` with the override set exactly as
/// given (or removed), returning its one line of stdout.
fn run_resolver(repo: &Path, what: &str, override_value: Option<&OsString>) -> Result<String> {
    let resolver = repo.join("scripts/resolve-trust-tool.sh");
    let mut cmd = Command::new(&resolver);
    cmd.arg(what);
    match override_value {
        Some(value) => cmd.env(TRUST_TOOLCHAIN_OVERRIDE_ENV, value),
        None => cmd.env_remove(TRUST_TOOLCHAIN_OVERRIDE_ENV),
    };
    let out = cmd.output().with_context(|| format!("cannot run {}", resolver.display()))?;
    let stdout = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if !out.status.success() || stdout.is_empty() || stdout.contains('\n') {
        bail!(
            "`{} {what}` exited with {}: {}",
            resolver.display(),
            out.status,
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    Ok(stdout)
}

/// The `commit-hash:` line of `<trustc> -Vv`.
fn compiler_commit(trustc: &Path) -> Option<String> {
    let out = Command::new(trustc).arg("-Vv").output().ok()?;
    if !out.status.success() {
        return None;
    }
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .find_map(|l| l.strip_prefix("commit-hash:").map(|h| h.trim().to_string()))
        .filter(|h| !h.is_empty() && h != "unknown")
}

/// `artifact_driver_sha256=` from a seal PROVENANCE text.
fn provenance_driver_sha256(text: &str) -> Option<String> {
    text.lines()
        .find_map(|l| l.trim().strip_prefix("artifact_driver_sha256="))
        .map(|v| v.trim().to_string())
        .filter(|v| !v.is_empty())
}

/// Resolve the Trust toolchain a run attests through `scripts/resolve-trust-tool.sh`.
///
/// With `override_value` set (the `TRUST_MC_TRUST_TOOLCHAIN` of the runner), a value
/// that does not resolve, or whose trustc reports no commit, is an error: a run held
/// on one seal must never start attesting another. Without it, an unresolvable
/// toolchain is recorded as `<unknown>`, as before.
pub fn resolve_trust_toolchain(repo: &Path, override_value: Option<OsString>) -> Result<TrustToolchain> {
    let channel = toolchain_channel(repo);
    let Some(value) = override_value else {
        let resolved = run_resolver(repo, "trustc", None)
            .and_then(|trustc| Ok((trustc, run_resolver(repo, "sysroot", None)?)));
        return Ok(match resolved {
            Ok((trustc, sysroot)) => describe_toolchain(channel, None, &trustc, &sysroot),
            Err(error) => {
                eprintln!("[kani-domination] WARNING: Trust toolchain unresolved: {error:#}");
                TrustToolchain {
                    channel,
                    override_value: None,
                    commit: "<unknown>".into(),
                    sysroot: None,
                    seal_build: None,
                    artifact_driver_sha256: None,
                }
            }
        });
    };
    let shown = value.to_str().map(str::to_string).with_context(|| {
        format!("{TRUST_TOOLCHAIN_OVERRIDE_ENV} is not UTF-8; refusing to start a run it cannot attest")
    })?;
    let refuse = |error: anyhow::Error| {
        error.context(format!(
            "{TRUST_TOOLCHAIN_OVERRIDE_ENV}={shown:?} does not resolve through \
             scripts/resolve-trust-tool.sh; refusing to start a run that would attest another \
             Trust toolchain (unset it to use rust-toolchain.toml's channel)"
        ))
    };
    let trustc = run_resolver(repo, "trustc", Some(&value)).map_err(refuse)?;
    let sysroot = run_resolver(repo, "sysroot", Some(&value)).map_err(refuse)?;
    let toolchain = describe_toolchain(channel, Some(shown.clone()), &trustc, &sysroot);
    if toolchain.commit == "<unknown>" {
        return Err(refuse(anyhow::anyhow!("{trustc} -Vv reports no commit-hash")));
    }
    Ok(toolchain)
}

fn describe_toolchain(
    channel: String,
    override_value: Option<String>,
    trustc: &str,
    sysroot: &str,
) -> TrustToolchain {
    let sysroot = PathBuf::from(sysroot);
    let seal_build = sysroot
        .file_name()
        .and_then(|n| n.to_str())
        .filter(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
        .map(str::to_string);
    let artifact_driver_sha256 = std::fs::read_to_string(sysroot.join("PROVENANCE"))
        .ok()
        .as_deref()
        .and_then(provenance_driver_sha256);
    TrustToolchain {
        channel,
        override_value,
        commit: compiler_commit(Path::new(trustc)).unwrap_or_else(|| "<unknown>".into()),
        sysroot: Some(sysroot),
        seal_build,
        artifact_driver_sha256,
    }
}

impl Env {
    /// Resolve everything a run on `engine` needs. Only the trust-mc engine
    /// requires a built verifier and a pinned `ay`; the Kani engine requires
    /// a Kani install and nothing of trust-mc's beyond the repo root.
    pub fn discover(kani: PathBuf, engine: Engine) -> Result<Self> {
        let repo = find_repo_root().context("could not locate the trust-mc repo root")?;
        let engine = match engine {
            Engine::TrustMc => EngineEnv::TrustMc(resolve_trust_mc(&repo)?),
            Engine::Kani => EngineEnv::Kani(resolve_kani()?),
        };
        let cargo = resolve_cargo(&engine);
        let cache = repo.join("target/kani-domination");
        std::fs::create_dir_all(&cache).ok();

        Ok(Env { repo, engine, cargo, cache, kani })
    }

    pub fn engine_kind(&self) -> Engine {
        match self.engine {
            EngineEnv::TrustMc(_) => Engine::TrustMc,
            EngineEnv::Kani(_) => Engine::Kani,
        }
    }

    /// The trust-mc half, for callers that only make sense there (`build`).
    pub fn trust_mc(&self) -> Option<&TrustMcEnv> {
        match &self.engine {
            EngineEnv::TrustMc(t) => Some(t),
            EngineEnv::Kani(_) => None,
        }
    }

    pub fn kani_dir(&self) -> PathBuf {
        self.kani.clone()
    }
    pub fn build_base(&self) -> PathBuf {
        self.cache.join("build")
    }
    pub fn reports_dir(&self) -> PathBuf {
        self.cache.join("reports")
    }
    /// Per-test build directories for `route`. DevCli keeps [`Self::build_base`].
    /// Trustc units build under `<user cache>/trust-mc/kani-domination/build/trustc-<backend>`:
    /// never under /tmp (trustc and the route preflight refuse world-writable
    /// directories, P14), and apart from DevCli and the other lane, so runs can
    /// go side by side without sharing a unit's target directory.
    pub fn build_base_for(&self, route: crate::route::Route, backend: &str) -> PathBuf {
        match route {
            crate::route::Route::DevCli => self.build_base(),
            crate::route::Route::Trustc => user_cache_root()
                .map(|c| c.join("trust-mc").join("kani-domination").join("build"))
                .unwrap_or_else(|| self.build_base())
                .join(format!("trustc-{backend}")),
        }
    }

    /// Assemble the full provenance authority tuple for a run, including the
    /// runner attestation and the load average at the start of the run.
    ///
    /// Under `--engine kani` the trust-mc half of the tuple still names the
    /// tool's own repo and the `ay` pin (they identify the runner and the
    /// comparison target) but no solver ran, so `ay_binary_version` is
    /// `<n/a>`, `backend` is `cbmc`, and the Kani install is attested in
    /// `kani_attestation` instead of `attestation`.
    pub fn provenance(
        &self,
        backend: &str,
        harness_timeout_s: u64,
        jobs: usize,
        scopes: &[String],
    ) -> Provenance {
        let now = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0);
        let (head, dirty) = git_head(&self.repo);
        let pin = ay_pin(&self.repo).unwrap_or_else(|| "<unknown>".into());
        let (kani_rev, kani_repo) = kani_provenance(&self.kani_dir());
        let tm = match &self.engine {
            EngineEnv::TrustMc(tm) => tm,
            EngineEnv::Kani(k) => {
                let att = KaniAttestation {
                    kani_path: display(&k.kani),
                    kani_sha256: sha256_file(&k.kani).unwrap_or_else(|| "<unreadable>".into()),
                    kani_version: k.version.clone(),
                    kani_source: k.source.to_string(),
                    cargo_kani_path: display(&k.cargo_kani),
                    cargo_kani_sha256: sha256_file(&k.cargo_kani)
                        .unwrap_or_else(|| "<unreadable>".into()),
                    kani_home: k.home.as_deref().map(display),
                    kani_toolchain: k.toolchain.clone(),
                    kani_dir: display(&self.kani_dir()),
                    load_average_start: load_average(),
                    load_average_end: None,
                    load_start: Some(host_load()),
                    load_end: None,
                    trust_mc_jobs: Some(jobs),
                    child_env_scrubbed: scrubbed_child_env_present(),
                };
                return Provenance {
                    generated_unix: now,
                    generated_iso: iso8601_utc(now),
                    trust_mc_head: head,
                    trust_mc_dirty: dirty,
                    ay_pin: pin,
                    ay_binary_version: "<n/a>".into(),
                    ay_rev_matches_pin: false,
                    kani_rev,
                    kani_repo,
                    backend: "cbmc".into(),
                    harness_timeout_s,
                    jobs,
                    scopes: scopes.to_vec(),
                    surface: None,
                    attestation: None,
                    engine: Some(Engine::Kani),
                    engine_version: Some(k.version.clone()),
                    engine_path: Some(att.kani_path.clone()),
                    engine_sha256: Some(att.kani_sha256.clone()),
                    kani_attestation: Some(att),
                    scorer_version: SCORER_VERSION,
                    log_root: None,
                    rescored_from: None,
                    route: None,
                    route_attestation: None,
                };
            }
        };
        let ay_ver = ay_version(&tm.ay).unwrap_or_else(|| "<unknown>".into());
        let ay_matches = pin != "<unknown>" && ay_ver.contains(&pin[..pin.len().min(12)]);
        let ay_tree = ay_tree(&self.repo);
        let (ay_tree_head, ay_tree_dirty) = match &ay_tree {
            Some(tree) => {
                let (h, d) = git_head(tree);
                (h, Some(d))
            }
            None => ("<unknown>".to_string(), None),
        };
        // The driver runs its sibling `trust-mc-compiler` (dev layout) or
        // `<release>/bin/trust-mc-compiler`; a bundle has both in one place.
        let compiler = [
            tm.verifier.parent().map(|d| d.join("trust-mc-compiler")),
            Some(tm.sysroot.join("bin").join("trust-mc-compiler")),
        ]
        .into_iter()
        .flatten()
        .find(|c| c.is_file());
        let attestation = RunnerAttestation {
            driver_path: display(&tm.verifier),
            driver_sha256: sha256_file(&tm.verifier).unwrap_or_else(|| "<unreadable>".into()),
            driver_version: driver_version(&tm.verifier, &tm.sysroot)
                .unwrap_or_else(|| "<unknown>".into()),
            compiler_path: compiler.as_deref().map(display),
            compiler_sha256: compiler.as_deref().map(|c| sha256_file(c).unwrap_or_else(|| "<unreadable>".into())),
            sysroot: display(&tm.sysroot),
            ay_binary_path: display(&tm.ay),
            ay_binary_source: tm.ay_source.to_string(),
            trust_toolchain: tm.trust.channel.clone(),
            trust_toolchain_commit: tm.trust.commit.clone(),
            trust_toolchain_override: tm.trust.override_value.clone(),
            trust_sysroot: tm.trust.sysroot.as_deref().map(display),
            trust_seal_build: tm.trust.seal_build.clone(),
            trust_artifact_driver_sha256: tm.trust.artifact_driver_sha256.clone(),
            ay_tree: ay_tree.as_deref().map(display).unwrap_or_else(|| "<unknown>".into()),
            ay_tree_head,
            ay_tree_dirty,
            kani_dir: display(&self.kani_dir()),
            load_average_start: load_average(),
            load_average_end: None,
            load_start: Some(host_load()),
            load_end: None,
            trust_mc_jobs: Some(jobs),
            child_env_scrubbed: scrubbed_child_env_present(),
        };
        Provenance {
            generated_unix: now,
            generated_iso: iso8601_utc(now),
            trust_mc_head: head,
            trust_mc_dirty: dirty,
            ay_pin: pin,
            ay_binary_version: ay_ver,
            ay_rev_matches_pin: ay_matches,
            kani_rev,
            kani_repo,
            backend: backend.to_string(),
            harness_timeout_s,
            jobs,
            scopes: scopes.to_vec(),
            surface: None,
            engine: Some(Engine::TrustMc),
            engine_version: Some(attestation.driver_version.clone()),
            engine_path: Some(attestation.driver_path.clone()),
            engine_sha256: Some(attestation.driver_sha256.clone()),
            kani_attestation: None,
            attestation: Some(attestation),
            scorer_version: SCORER_VERSION,
            log_root: None,
            rescored_from: None,
            route: None,
            route_attestation: None,
        }
    }
}

fn display(p: &Path) -> String {
    p.display().to_string()
}

/// The trust-mc verifier: `$TRUST_MC_TEST_BIN`, else the build-dev sysroot
/// driver; the pinned `ay`; and the attested Trust toolchain.
fn resolve_trust_mc(repo: &Path) -> Result<TrustMcEnv> {
    let (verifier, sysroot) = if let Some(bin) = std::env::var_os("TRUST_MC_TEST_BIN") {
        let bin = PathBuf::from(bin);
        let sysroot = std::env::var_os("TRUST_MC_SYSROOT")
            .map(PathBuf::from)
            .unwrap_or_else(|| repo.join("target/trust-mc"));
        (bin, sysroot)
    } else {
        let sysroot = repo.join("target/trust-mc");
        let bin = sysroot.join("bin/trust-mc-driver");
        (bin, sysroot)
    };
    if !verifier.exists() {
        bail!(
            "verifier not found at {}\n  build it first: `kani-domination build`, i.e. \
             `targo --unverified build-dev` in the trust-mc checkout (or set TRUST_MC_TEST_BIN)",
            verifier.display()
        );
    }
    let (ay, ay_source) = resolve_ay(repo)?;
    // Before anything is built or run: an override that does not resolve refuses.
    let trust = resolve_trust_toolchain(repo, std::env::var_os(TRUST_TOOLCHAIN_OVERRIDE_ENV))?;
    Ok(TrustMcEnv { verifier, sysroot, ay, ay_source, trust })
}

/// The Kani install for `--engine kani`: `$KANI_BIN`, else `~/.cargo/bin/kani`
/// (where `cargo install kani-verifier` puts the launcher), with `cargo-kani`
/// beside it. A set-but-missing `KANI_BIN` is an error, never a fall-through,
/// and `kani --version` must succeed and name [`KANI_ORACLE`]: a row must name
/// the Kani that ran it. Nothing here installs Kani: an unset-up launcher
/// downloads a bundle and installs a toolchain the first time it runs, so the
/// default launcher runs only over an existing home ([`launcher_home`]).
fn resolve_kani() -> Result<KaniEnv> {
    let not_installed = |why: String| {
        anyhow::anyhow!(
            "NOT RUN: oracle kani {KANI_ORACLE} not installed: {why} (set up Kani {KANI_ORACLE} yourself, or set {KANI_BIN_ENV})"
        )
    };
    let (kani, source, launcher_home): (PathBuf, &'static str, Option<PathBuf>) =
        match std::env::var_os(KANI_BIN_ENV).filter(|v| !v.is_empty()) {
            Some(bin) => {
                let p = PathBuf::from(bin);
                if !p.is_file() {
                    bail!("{KANI_BIN_ENV} is set to {} but no file exists there", p.display());
                }
                (p, KANI_BIN_ENV, None)
            }
            None => {
                let home = std::env::var_os("HOME").filter(|h| !h.is_empty()).map(PathBuf::from);
                let p = home
                    .map(|h| h.join(".cargo/bin/kani"))
                    .with_context(|| format!("HOME is unset; set {KANI_BIN_ENV}"))?;
                if !p.is_file() {
                    return Err(not_installed(format!("no launcher at {}", p.display())));
                }
                let home = launcher_home(std::env::var_os("KANI_HOME"), std::env::var_os("HOME"))
                    .map_err(not_installed)?;
                (p, "~/.cargo/bin", Some(home))
            }
        };
    let cargo_kani = kani.with_file_name("cargo-kani");
    if !cargo_kani.is_file() {
        bail!(
            "found {} but no cargo-kani beside it at {} (cargo units need it)",
            kani.display(),
            cargo_kani.display()
        );
    }
    let version = kani_version(&kani, launcher_home.as_deref())?;
    if version != format!("kani {KANI_ORACLE}") {
        bail!("{} reports `{version}`, not the pinned oracle kani {KANI_ORACLE}", kani.display());
    }
    let home = launcher_home.clone().or_else(|| kani_home(&version));
    let toolchain = home
        .as_deref()
        .and_then(|h| std::fs::read_to_string(h.join("rust-toolchain-version")).ok())
        .map(|t| t.trim().to_string())
        .filter(|t| !t.is_empty());
    Ok(KaniEnv { kani, cargo_kani, source, version, home, toolchain, launcher_home })
}

/// The home the default launcher must find already set up: `$KANI_HOME`, else
/// `~/.kani/kani-<KANI_ORACLE>`. Its existence is all the launcher checks
/// before it would set itself up, so a missing one is refused, not run.
fn launcher_home(kani_home_env: Option<OsString>, home_env: Option<OsString>) -> Result<PathBuf, String> {
    let home = match kani_home_env.filter(|v| !v.is_empty()) {
        Some(h) => PathBuf::from(h),
        None => home_env
            .filter(|h| !h.is_empty())
            .map(|h| PathBuf::from(h).join(".kani").join(format!("kani-{KANI_ORACLE}")))
            .ok_or_else(|| "HOME is unset".to_string())?,
    };
    if home.is_dir() { Ok(home) } else { Err(format!("no Kani home at {}", home.display())) }
}

/// First line of `kani --version`, run without the runner's toolchain
/// selectors so the launcher resolves exactly as it will for every unit, and
/// with the same [`kani_child_env`].
fn kani_version(kani: &Path, launcher_home: Option<&Path>) -> Result<String> {
    let mut cmd = Command::new(kani);
    cmd.arg("--version");
    for key in scrubbed_child_env_present() {
        cmd.env_remove(key);
    }
    kani_child_env(&mut cmd, launcher_home);
    let out = cmd.output().with_context(|| format!("cannot run {} --version", kani.display()))?;
    let first = String::from_utf8_lossy(&out.stdout).lines().next().map(|l| l.trim().to_string());
    match first {
        Some(v) if out.status.success() && !v.is_empty() => Ok(v),
        _ => bail!(
            "`{} --version` failed ({}): {}",
            kani.display(),
            out.status,
            String::from_utf8_lossy(&out.stderr).trim()
        ),
    }
}

/// What every Kani child carries: the default launcher's set-up home as
/// `KANI_HOME` (so it never sets itself up), and `RUSTUP_AUTO_INSTALL=0` (so
/// the toolchain Kani selects is never downloaded).
pub fn kani_child_env(cmd: &mut Command, launcher_home: Option<&Path>) {
    cmd.env("RUSTUP_AUTO_INSTALL", "0");
    if let Some(home) = launcher_home {
        cmd.env("KANI_HOME", home);
    }
}

/// Where the launcher dispatches: `$KANI_HOME`, else `~/.kani/kani-<version>`
/// with the version taken from the `--version` line (`kani 0.67.0`).
fn kani_home(version_line: &str) -> Option<PathBuf> {
    if let Some(h) = std::env::var_os("KANI_HOME").filter(|v| !v.is_empty()) {
        let p = PathBuf::from(h);
        return p.is_dir().then_some(p);
    }
    let ver = version_line.split_whitespace().nth(1)?;
    let home = std::env::var_os("HOME").filter(|h| !h.is_empty()).map(PathBuf::from)?;
    let p = home.join(".kani").join(format!("kani-{ver}"));
    p.is_dir().then_some(p)
}

/// The Kani corpus checkout for `rev`: `--kani-dir`, then
/// `KANI_DOMINATION_CORPUS_DIR`, then the per-rev user cache.
pub fn corpus_dir(flag: Option<&Path>, rev: &str) -> Result<PathBuf> {
    let env_override = std::env::var_os(CORPUS_DIR_ENV).filter(|v| !v.is_empty()).map(PathBuf::from);
    let chosen = match flag.map(Path::to_path_buf).or(env_override) {
        Some(dir) => dir,
        None => default_corpus_dir(rev).context(
            "cannot place the Kani corpus: HOME is unset; pass --kani-dir or set KANI_DOMINATION_CORPUS_DIR",
        )?,
    };
    Ok(absolute(&chosen))
}

/// `<user cache>/trust-mc/kani-domination/<rev>`.
pub fn default_corpus_dir(rev: &str) -> Option<PathBuf> {
    user_cache_root().map(|c| c.join("trust-mc").join("kani-domination").join(rev))
}

pub fn user_cache_root() -> Option<PathBuf> {
    let home = std::env::var_os("HOME").filter(|h| !h.is_empty()).map(PathBuf::from);
    if cfg!(target_os = "macos") {
        return home.map(|h| h.join("Library").join("Caches"));
    }
    std::env::var_os("XDG_CACHE_HOME")
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
        .or_else(|| home.map(|h| h.join(".cache")))
}

fn absolute(p: &Path) -> PathBuf {
    if p.is_absolute() {
        p.to_path_buf()
    } else {
        std::env::current_dir().map(|cwd| cwd.join(p)).unwrap_or_else(|_| p.to_path_buf())
    }
}

/// Cargo context a cargo unit inside `kani_dir` would inherit from directories
/// ABOVE the checkout: `.cargo/config.toml` (or legacy `.cargo/config`) files,
/// and `Cargo.toml` manifests declaring `[workspace]` (measured: a corpus under
/// `<trust-mc>/target` also fails `cargo metadata` with "current package
/// believes it's in a workspace when it's not"). Kani's own config and
/// workspace at the checkout root are upstream's and belong to the corpus;
/// `cargo_home`'s config applies to every project wherever it lives, so
/// neither is reported.
pub fn inherited_cargo_configs(kani_dir: &Path, cargo_home: Option<&Path>) -> Vec<PathBuf> {
    let start = std::fs::canonicalize(kani_dir).unwrap_or_else(|_| absolute(kani_dir));
    let cargo_home = cargo_home.map(|h| std::fs::canonicalize(h).unwrap_or_else(|_| h.to_path_buf()));
    let mut found = Vec::new();
    let mut dir = start.parent();
    while let Some(d) = dir {
        let dot_cargo = d.join(".cargo");
        let is_cargo_home = cargo_home.as_deref().is_some_and(|h| {
            std::fs::canonicalize(&dot_cargo).map(|c| c == h).unwrap_or(false) || dot_cargo == h
        });
        if !is_cargo_home {
            for name in ["config.toml", "config"] {
                let cfg = dot_cargo.join(name);
                if cfg.is_file() {
                    found.push(cfg);
                }
            }
        }
        let manifest = d.join("Cargo.toml");
        if std::fs::read_to_string(&manifest)
            .is_ok_and(|txt| {
                // `[workspace.package]` / `[workspace.dependencies]` alone also
                // define the `workspace` table, so they make a workspace root too.
                txt.lines().any(|l| {
                    let l = l.trim();
                    l == "[workspace]" || l.starts_with("[workspace.")
                })
            })
        {
            found.push(manifest);
        }
        dir = d.parent();
    }
    found
}

/// `$CARGO_HOME`, else `~/.cargo`.
pub fn cargo_home() -> Option<PathBuf> {
    std::env::var_os("CARGO_HOME")
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cargo")))
}

/// Locate just the trust-mc repo root — no verifier / ay binaries required.
/// For text-only commands (`rekey-dry-run`) that never run a verification.
pub fn repo_root_lax() -> Result<PathBuf> {
    find_repo_root().context("could not locate the trust-mc repo root")
}

/// Walk up from the runtime override, configured build root, CWD, or compiled
/// manifest directory looking for the workspace root.
pub fn find_repo_root() -> Option<PathBuf> {
    let mut candidates: Vec<PathBuf> = Vec::new();
    if let Some(r) = std::env::var_os("TRUST_MC_REPO_ROOT") {
        let p = PathBuf::from(r);
        if !p.as_os_str().is_empty() {
            candidates.push(p);
        }
    }
    if let Some(r) = option_env!("MC_REPO_ROOT") {
        let p = PathBuf::from(r);
        if !p.as_os_str().is_empty() {
            candidates.push(p);
        }
    }
    if let Ok(cwd) = std::env::current_dir() {
        candidates.push(cwd);
    }
    // tools/kani-domination -> repo root
    candidates.push(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../.."));

    for start in candidates {
        let mut dir = start.as_path();
        loop {
            let cargo = dir.join("Cargo.toml");
            if cargo.is_file() {
                if let Ok(txt) = std::fs::read_to_string(&cargo) {
                    if txt.contains("[workspace]") && txt.contains("trust-mc-driver") {
                        return Some(dir.to_path_buf());
                    }
                }
            }
            match dir.parent() {
                Some(p) => dir = p,
                None => break,
            }
        }
    }
    None
}

/// Locate an `ay` binary: $AY_BIN, then $TRUST_MC_AY_BIN, then the pin-keyed
/// cache `scripts/build-pinned-ay-cli.sh` builds (`pinned_ay_cli`, keyed by the
/// root Cargo.toml AY pin), then sibling `../ay` release/debug, then PATH.
///
/// A set-but-missing `AY_BIN` or `TRUST_MC_AY_BIN` is an error, not a
/// fall-through: silently dropping to whatever `ay` is on PATH is how a corpus
/// run once measured a months-old ay instead of the pinned one. (The driver
/// treats a set-but-unusable `TRUST_MC_AY_BIN` the same way.)
///
/// The runner hands the result to the driver as `TRUST_MC_AY_BIN`
/// (`runner.rs`), which the driver prefers to PATH and pin-checks. Without
/// that, an operator's exported `TRUST_MC_AY_BIN` would be the binary the
/// driver ran while the ledger's `ay_binary_version` described this one.
fn resolve_ay(repo: &Path) -> Result<(PathBuf, &'static str)> {
    for var in ["AY_BIN", "TRUST_MC_AY_BIN"] {
        if let Some(b) = std::env::var_os(var).filter(|b| !b.is_empty()) {
            let p = PathBuf::from(b);
            if p.is_file() {
                return Ok((p, var));
            }
            bail!("{var} is set to {} but no file exists there", p.display());
        }
    }
    // The CLI built at the Cargo.toml pin, where scripts/build-pinned-ay-cli.sh
    // puts it. Keyed by the pin, so a bump never finds the previous pin's build
    // here the way an unkeyed cache or the sibling's own target dir can.
    if let (Some(root), Some(pin)) = (ay_cli_cache_root(), ay_pin(repo)) {
        if let Some(p) = pinned_ay_cli(&root, &pin).filter(|p| p.is_file()) {
            return Ok((p, "pinned-cache"));
        }
    }
    for rel in ["../ay/target/release/ay", "../ay/target/debug/ay"] {
        let p = repo.join(rel);
        if p.exists() {
            return Ok((p, "sibling"));
        }
    }
    if let Ok(p) = which::which("ay") {
        return Ok((p, "PATH"));
    }
    bail!(
        "no `ay` binary found (needed for the SMT/BMC path).\n  \
         set AY_BIN (or TRUST_MC_AY_BIN), run scripts/build-pinned-ay-cli.sh (it builds the Cargo.toml AY pin), \
         build it in the sibling ../ay checkout (`targo --unverified build --release -p ay --features cli`), \
         or put `ay` on PATH."
    )
}

/// The `cargo` whose directory cargo-project test units get on PATH.
///
/// trust-mc: the attested Trust toolchain's own `bin/cargo` (the sysroot
/// `scripts/resolve-trust-tool.sh` resolved), never a PATH lookup -- on an ALab
/// host a bare `cargo` is not the Trust toolchain.
///
/// Kani: STOCK-AS-ORACLE -- upstream Kani is the external
/// comparison oracle and drives its own rustup-proxy `cargo`/`rustc`, so its
/// cargo is PATH's, else `~/.cargo/bin/cargo`, as a Kani install expects.
fn resolve_cargo(engine: &EngineEnv) -> Option<PathBuf> {
    match engine {
        EngineEnv::TrustMc(tm) => {
            // Targo acting as upstream cargo, as the driver's own routes run it
            // (trust-mc-driver/src/session/cargo.rs says why).
            let cargo = tm.trust.sysroot.as_ref()?.join("bin/cargo");
            cargo.is_file().then_some(cargo)
        }
        EngineEnv::Kani(_) => {
            if let Ok(p) = which::which("cargo") {
                return Some(p);
            }
            let home = std::env::var_os("HOME").map(PathBuf::from)?;
            let p = home.join(".cargo/bin/cargo");
            p.exists().then_some(p)
        }
    }
}

/// The Targo `scripts/resolve-trust-tool.sh targo` resolves for `repo`, honouring
/// `TRUST_MC_TRUST_TOOLCHAIN` exactly as a run's attestation does.
pub fn resolve_targo(repo: &Path) -> Result<PathBuf> {
    let value = std::env::var_os(TRUST_TOOLCHAIN_OVERRIDE_ENV);
    run_resolver(repo, "targo", value.as_ref()).map(PathBuf::from)
}

fn ay_version(ay: &Path) -> Option<String> {
    let out = Command::new(ay).arg("--version").output().ok()?;
    let s = String::from_utf8_lossy(&out.stdout);
    s.lines().next().map(|l| l.trim().to_string())
}

/// First line of `trust-mc-driver --version`, run against the same sysroot
/// the corpus run uses.
fn driver_version(driver: &Path, sysroot: &Path) -> Option<String> {
    let out = Command::new(driver)
        .arg("--version")
        .env("TRUST_MC_SYSROOT", sysroot)
        .output()
        .ok()?;
    let s = String::from_utf8_lossy(&out.stdout);
    s.lines().next().map(|l| l.trim().to_string()).filter(|l| !l.is_empty())
}

pub fn sha256_file(path: &Path) -> Option<String> {
    let mut file = std::fs::File::open(path).ok()?;
    let mut hasher = Sha256::new();
    std::io::copy(&mut file, &mut hasher).ok()?;
    Some(hasher.finalize().iter().map(|b| format!("{b:02x}")).collect())
}

/// The 1/5/15-minute load average (`sysctl -n vm.loadavg` on macOS,
/// `/proc/loadavg` elsewhere).
pub fn load_average() -> Option<[f64; 3]> {
    let text = if cfg!(target_os = "macos") {
        let out = Command::new("sysctl").args(["-n", "vm.loadavg"]).output().ok()?;
        String::from_utf8_lossy(&out.stdout).into_owned()
    } else {
        std::fs::read_to_string("/proc/loadavg").ok()?
    };
    parse_load_average(&text)
}

/// The processes a host-load sample counts: the host's other builds and
/// verifiers, whose CPU and memory a measured unit competes with.
pub const COMPETING_PROCESS_NAMES: &[&str] = &["cargo", "rustc", "trust-mc-driver", "kani-driver"];

/// One `/proc` process: its pid, parent pid and name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProcEntry {
    pub pid: u32,
    pub ppid: u32,
    pub name: String,
}

/// A process's name: the basename of `argv[0]` from `/proc/<pid>/cmdline`,
/// else its `comm` (which the kernel truncates to 15 bytes, and which a
/// kernel thread or a zombie has alone).
pub fn process_name(comm: &str, cmdline: &[u8]) -> String {
    let argv0 = cmdline.split(|b| *b == 0).next().unwrap_or_default();
    let argv0 = String::from_utf8_lossy(argv0);
    let base = argv0.rsplit('/').next().unwrap_or_default().trim();
    if base.is_empty() { comm.trim().to_string() } else { base.to_string() }
}

/// Count the competing processes of a `/proc` snapshot: every entry named in
/// [`COMPETING_PROCESS_NAMES`] that is neither `own_pid` nor one of its
/// descendants (walked through the snapshot's parent links), and separately
/// how many matching entries were the run's own.
pub fn count_competing(procs: &[ProcEntry], own_pid: u32) -> (std::collections::BTreeMap<String, u64>, u64) {
    let mut own = std::collections::BTreeSet::from([own_pid]);
    loop {
        let before = own.len();
        for p in procs {
            if own.contains(&p.ppid) {
                own.insert(p.pid);
            }
        }
        if own.len() == before {
            break;
        }
    }
    let mut competing: std::collections::BTreeMap<String, u64> =
        COMPETING_PROCESS_NAMES.iter().map(|n| (n.to_string(), 0)).collect();
    let mut own_excluded = 0u64;
    for p in procs.iter().filter(|p| COMPETING_PROCESS_NAMES.contains(&p.name.as_str())) {
        if own.contains(&p.pid) {
            own_excluded += 1;
        } else {
            *competing.entry(p.name.clone()).or_default() += 1;
        }
    }
    (competing, own_excluded)
}

/// `(pid, ppid, comm)` of one `/proc/<pid>/stat` line: the command name is
/// parenthesized and may contain spaces or parentheses, so it spans to the
/// LAST `)`.
pub fn parse_stat_comm_ppid(stat: &str) -> Option<(u32, String, u32)> {
    let open = stat.find('(')?;
    let close = stat.rfind(')')?;
    let pid = stat[..open].trim().parse().ok()?;
    let comm = stat[open + 1..close].to_string();
    let ppid = stat[close + 1..].split_whitespace().nth(1)?.parse().ok()?;
    Some((pid, comm, ppid))
}

/// Sample the host's load now (plan D18). On Linux: `/proc/loadavg` and a
/// `/proc` scan of the competing processes outside this runner's own process
/// tree. Elsewhere: the load average only, `competing` unknown.
pub fn host_load() -> HostLoad {
    #[cfg(target_os = "linux")]
    {
        let mut procs = Vec::new();
        if let Ok(dir) = std::fs::read_dir("/proc") {
            for entry in dir.flatten() {
                if entry.file_name().to_str().and_then(|n| n.parse::<u32>().ok()).is_none() {
                    continue;
                }
                let Ok(stat) = std::fs::read_to_string(entry.path().join("stat")) else { continue };
                let Some((pid, comm, ppid)) = parse_stat_comm_ppid(&stat) else { continue };
                let cmdline = std::fs::read(entry.path().join("cmdline")).unwrap_or_default();
                procs.push(ProcEntry { pid, ppid, name: process_name(&comm, &cmdline) });
            }
        }
        let (competing, own_excluded) = count_competing(&procs, std::process::id());
        HostLoad {
            loadavg: load_average(),
            competing: (!procs.is_empty()).then_some(competing),
            own_excluded,
            source: "/proc".into(),
        }
    }
    #[cfg(not(target_os = "linux"))]
    {
        HostLoad { loadavg: load_average(), competing: None, own_excluded: 0, source: "sysctl".into() }
    }
}

/// `1.0/2.0/3.0 cargo=0 kani-driver=0 rustc=2 trust-mc-driver=1 (own 3)`.
pub fn host_load_line(l: &HostLoad) -> String {
    let avg = l.loadavg.map(|a| format!("{:.2}/{:.2}/{:.2}", a[0], a[1], a[2])).unwrap_or_else(|| "?".into());
    match &l.competing {
        Some(c) => {
            let parts: Vec<String> = c.iter().map(|(k, v)| format!("{k}={v}")).collect();
            format!("{avg} {} (own {})", parts.join(" "), l.own_excluded)
        }
        None => format!("{avg} (processes unknown)"),
    }
}

fn parse_load_average(text: &str) -> Option<[f64; 3]> {
    let mut values = text
        .split(|c: char| c.is_whitespace() || c == '{' || c == '}')
        .filter(|t| !t.is_empty())
        .map(|t| t.parse::<f64>());
    let mut out = [0.0; 3];
    for slot in &mut out {
        *slot = values.next()?.ok()?;
    }
    Some(out)
}

fn git_head(repo: &Path) -> (String, bool) {
    let head = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(repo)
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "<unknown>".into());
    let dirty = Command::new("git")
        .args(["status", "--porcelain"])
        .current_dir(repo)
        .output()
        .ok()
        .map(|o| !o.stdout.is_empty())
        .unwrap_or(false);
    (head, dirty)
}

/// Where `scripts/build-pinned-ay-cli.sh` puts the `ay` CLI built at `pin`:
/// `<cache root>/trust-mc-ay-cli-<first 9 characters of pin>/release/ay`.
/// `None` unless `pin` is a full 40-character lowercase sha.
fn pinned_ay_cli(cache_root: &Path, pin: &str) -> Option<PathBuf> {
    let full = pin.len() == 40 && pin.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'));
    full.then(|| {
        cache_root.join(format!("trust-mc-ay-cli-{}", &pin[..9])).join("release").join("ay")
    })
}

/// The directory holding the pin-keyed CLI caches, chosen as the script chooses
/// it: `TRUST_MC_AY_CLI_CACHE_ROOT`, else the user cache root.
fn ay_cli_cache_root() -> Option<PathBuf> {
    std::env::var_os("TRUST_MC_AY_CLI_CACHE_ROOT")
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
        .or_else(user_cache_root)
}

/// Parse the pinned `ay` rev out of trust-mc's root `Cargo.toml`.
fn ay_pin(repo: &Path) -> Option<String> {
    let txt = std::fs::read_to_string(repo.join("Cargo.toml")).ok()?;
    for line in txt.lines() {
        if line.contains("alabsystems/ay.git") {
            if let Some(idx) = line.find("rev = \"") {
                let rest = &line[idx + 7..];
                if let Some(end) = rest.find('"') {
                    return Some(rest[..end].to_string());
                }
            }
        }
    }
    None
}

/// The ay checkout trust-mc's `[patch]` links (`ay = { path = "<tree>/crates/ay" }`),
/// else the conventional sibling `../ay`.
fn ay_tree(repo: &Path) -> Option<PathBuf> {
    let txt = std::fs::read_to_string(repo.join("Cargo.toml")).unwrap_or_default();
    let patched = txt.lines().find_map(|line| {
        let line = line.trim();
        if !line.starts_with("ay = {") {
            return None;
        }
        let rest = &line[line.find("path = \"")? + 8..];
        let path = &rest[..rest.find('"')?];
        Some(path.strip_suffix("/crates/ay").unwrap_or(path).to_string())
    });
    let tree = repo.join(patched.unwrap_or_else(|| "../ay".to_string()));
    let tree = std::fs::canonicalize(&tree).unwrap_or(tree);
    tree.is_dir().then_some(tree)
}

/// The repo's pinned toolchain channel (`rust-toolchain.toml`).
fn toolchain_channel(repo: &Path) -> String {
    std::fs::read_to_string(repo.join("rust-toolchain.toml"))
        .ok()
        .and_then(|txt| {
            txt.lines().find_map(|l| {
                let l = l.trim();
                let rest = l.strip_prefix("channel")?.trim_start().strip_prefix('=')?.trim();
                Some(rest.trim_matches('"').to_string())
            })
        })
        .unwrap_or_else(|| "<unknown>".into())
}

/// The corpus checkout's `HEAD` rev (`<not-cloned>` when it has none), the
/// key the generated spec is filed under.
pub fn kani_rev_of(kani_dir: &Path) -> String {
    kani_provenance(kani_dir).0
}

fn kani_provenance(kani_dir: &Path) -> (String, String) {
    let rev = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(kani_dir)
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "<not-cloned>".into());
    let repo = Command::new("git")
        .args(["config", "--get", "remote.origin.url"])
        .current_dir(kani_dir)
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "https://github.com/model-checking/kani".into());
    (rev, repo)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pinned_ay_cli_is_keyed_by_the_full_pin() {
        let root = Path::new("/cache");
        assert_eq!(
            pinned_ay_cli(root, "501caafdf3b25a99289e0c87a71ba619a2a6884c"),
            Some(PathBuf::from("/cache/trust-mc-ay-cli-501caafdf/release/ay"))
        );
        assert_eq!(pinned_ay_cli(root, "501caafdf"), None);
        assert_eq!(pinned_ay_cli(root, "501CAAFDF3B25A99289E0C87A71BA619A2A6884C"), None);
        assert_eq!(pinned_ay_cli(root, "501caafdf3b25a99289e0c87a71ba619a2a6884g"), None);
    }

    fn temp_root(tag: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "kani-domination-env-{tag}-{}-{}",
            std::process::id(),
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()
        ));
        std::fs::create_dir_all(&root).unwrap();
        root
    }

    #[test]
    fn the_default_launcher_runs_only_over_a_set_up_home() {
        let root = temp_root("launcher-home");
        let pinned = root.join(".kani").join(format!("kani-{KANI_ORACLE}"));
        let missing = launcher_home(None, Some(root.clone().into())).unwrap_err();
        assert_eq!(missing, format!("no Kani home at {}", pinned.display()));
        std::fs::create_dir_all(&pinned).unwrap();
        assert_eq!(launcher_home(None, Some(root.clone().into())).unwrap(), pinned);
        let explicit = root.join("elsewhere");
        assert!(launcher_home(Some(explicit.clone().into()), Some(root.clone().into())).is_err());
        std::fs::create_dir_all(&explicit).unwrap();
        assert_eq!(launcher_home(Some(explicit.clone().into()), None).unwrap(), explicit);
        assert_eq!(launcher_home(None, None).unwrap_err(), "HOME is unset");

        let mut cmd = Command::new("kani");
        kani_child_env(&mut cmd, Some(&pinned));
        let envs: Vec<_> = cmd.get_envs().collect();
        assert!(envs.contains(&(std::ffi::OsStr::new("RUSTUP_AUTO_INSTALL"), Some(std::ffi::OsStr::new("0")))));
        assert!(envs.contains(&(std::ffi::OsStr::new("KANI_HOME"), Some(pinned.as_os_str()))));
        std::fs::remove_dir_all(&root).ok();
    }

    #[test]
    fn default_corpus_dir_is_keyed_by_rev_under_the_user_cache() {
        let Some(dir) = default_corpus_dir("abc123") else { return };
        assert!(dir.ends_with("trust-mc/kani-domination/abc123"), "{}", dir.display());
    }

    #[test]
    fn flag_overrides_the_default_corpus_dir() {
        let dir = corpus_dir(Some(Path::new("/elsewhere/kani")), "abc123").unwrap();
        assert_eq!(dir, PathBuf::from("/elsewhere/kani"));
    }

    /// The measured defect: a corpus under trust-mc/target inherited
    /// trust-mc/.cargo/config.toml. The checkout's own config (Kani's) and
    /// CARGO_HOME's are not inheritance from a foreign workspace.
    #[test]
    fn ancestor_cargo_config_is_reported_but_the_checkouts_own_is_not() {
        let root = temp_root("configs");
        let workspace = root.join("trust-mc");
        let kani = workspace.join("target/kani-domination/kani");
        std::fs::create_dir_all(kani.join(".cargo")).unwrap();
        std::fs::write(kani.join(".cargo/config.toml"), "").unwrap();
        std::fs::create_dir_all(workspace.join(".cargo")).unwrap();
        std::fs::write(workspace.join(".cargo/config.toml"), "").unwrap();

        let found = inherited_cargo_configs(&kani, None);
        let canonical_ws = std::fs::canonicalize(&workspace).unwrap();
        assert_eq!(found, vec![canonical_ws.join(".cargo/config.toml")]);

        // The same config is not reported when it IS CARGO_HOME.
        let found = inherited_cargo_configs(&kani, Some(&workspace.join(".cargo")));
        assert!(found.is_empty(), "{found:?}");

        // An ancestor workspace manifest is inherited context too; a plain
        // package manifest is not.
        std::fs::write(workspace.join("Cargo.toml"), "[workspace]\nmembers = []\n").unwrap();
        std::fs::write(workspace.join("target/Cargo.toml"), "[package]\nname = \"x\"\n").unwrap();
        let found = inherited_cargo_configs(&kani, Some(&workspace.join(".cargo")));
        assert_eq!(found, vec![canonical_ws.join("Cargo.toml")]);
        // A workspace declared only through a dotted `[workspace.*]` table.
        std::fs::write(workspace.join("Cargo.toml"), "[workspace.package]\nversion = \"1.0.0\"\n").unwrap();
        let found = inherited_cargo_configs(&kani, Some(&workspace.join(".cargo")));
        assert_eq!(found, vec![canonical_ws.join("Cargo.toml")]);

        // A checkout outside any workspace inherits nothing.
        let clean = root.join("cache/kani-domination/rev");
        std::fs::create_dir_all(&clean).unwrap();
        assert!(inherited_cargo_configs(&clean, None).is_empty());
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn scrubbed_keys_cover_named_selectors_and_cargo_config_prefixes() {
        let keys = [
            "RUSTFLAGS",
            "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS",
            "CARGO_PROFILE_DEV_OPT_LEVEL",
            "CARGO_UNSTABLE_BUILD_STD",
            "CARGO_BUILD_RUSTFLAGS",
            "CARGO_HOST_AARCH64_APPLE_DARWIN_RUSTFLAGS",
            "CARGO_HOST_RUSTFLAGS",
            "CARGO_TARGET_DIR",
            "CARGO_HOME",
            "CARGO_NET_OFFLINE",
            "AY_BIN",
            "TRUST_MC_AY_BIN",
            "TRUST_MC_ALLOW_UNPINNED_AY",
            "RUSTFLAGS",
        ];
        assert_eq!(
            scrubbed_child_env_keys(keys),
            vec![
                "CARGO_BUILD_RUSTFLAGS",
                "CARGO_HOST_AARCH64_APPLE_DARWIN_RUSTFLAGS",
                "CARGO_HOST_RUSTFLAGS",
                "CARGO_PROFILE_DEV_OPT_LEVEL",
                "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS",
                "CARGO_TARGET_DIR",
                "CARGO_UNSTABLE_BUILD_STD",
                "RUSTFLAGS",
                "TRUST_MC_ALLOW_UNPINNED_AY",
            ]
        );
    }

    #[test]
    fn competing_processes_exclude_the_runs_own_tree() {
        let e = |pid, ppid, name: &str| ProcEntry { pid, ppid, name: name.into() };
        let procs = vec![
            e(100, 1, "kani-domination"),
            e(101, 100, "trust-mc-driver"),
            e(102, 101, "rustc"),
            e(103, 102, "cargo"),
            e(200, 1, "rustc"),
            e(201, 1, "trust-mc-driver"),
            e(202, 1, "bash"),
            e(203, 202, "cargo"),
            e(204, 203, "kani-driver"),
        ];
        let (competing, own) = count_competing(&procs, 100);
        assert_eq!(own, 3);
        let want: std::collections::BTreeMap<String, u64> =
            [("cargo", 1), ("kani-driver", 1), ("rustc", 1), ("trust-mc-driver", 1)].map(|(k, v)| (k.to_string(), v)).into();
        assert_eq!(competing, want);
        assert_eq!(process_name("cargo", b"/home/u/.cargo/bin/cargo\0build\0"), "cargo");
        assert_eq!(process_name("trust-mc-driver", b""), "trust-mc-driver", "no cmdline: comm");
        assert_eq!(parse_stat_comm_ppid("4242 (my (odd) name) S 17 4242 0"), Some((4242, "my (odd) name".to_string(), 17)));
        let line = host_load_line(&HostLoad { loadavg: Some([1.0, 2.0, 3.0]), competing: Some(competing), own_excluded: 3, source: "/proc".into() });
        assert_eq!(line, "1.00/2.00/3.00 cargo=1 kani-driver=1 rustc=1 trust-mc-driver=1 (own 3)");
    }

    /// A live sample on Linux: a child of this test process named `rustc` is
    /// the run's own and never counted as competing load.
    #[cfg(target_os = "linux")]
    #[test]
    fn host_load_counts_the_host_but_not_the_runs_own_children() {
        let dir = std::env::temp_dir().join(format!("kd-hostload-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let fake = dir.join("rustc");
        let Some(sleep) = ["/bin/sleep", "/usr/bin/sleep"].into_iter().map(Path::new).find(|p| p.is_file()) else { return };
        std::fs::copy(sleep, &fake).unwrap();
        let before = host_load();
        let mut child = Command::new(&fake).arg("30").spawn().unwrap();
        std::thread::sleep(std::time::Duration::from_millis(200));
        let during = host_load();
        let _ = child.kill();
        let _ = child.wait();
        let _ = std::fs::remove_dir_all(&dir);
        assert_eq!(during.source, "/proc");
        assert!(during.loadavg.is_some());
        assert!(during.own_excluded >= before.own_excluded + 1, "{before:?} -> {during:?}");
        // Other processes on the host may come and go; ours is never counted.
        assert!(during.competing.is_some());
    }

    #[test]
    fn load_average_parses_macos_and_linux_shapes() {
        assert_eq!(parse_load_average("{ 10.14 13.93 10.86 }\n"), Some([10.14, 13.93, 10.86]));
        assert_eq!(parse_load_average("0.52 0.58 0.59 1/467 12345\n"), Some([0.52, 0.58, 0.59]));
        assert_eq!(parse_load_average("{ 1.0 }"), None);
    }

    #[test]
    fn sha256_of_a_known_file() {
        let root = temp_root("sha");
        let f = root.join("abc");
        std::fs::write(&f, "abc").unwrap();
        assert_eq!(
            sha256_file(&f).unwrap(),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        let _ = std::fs::remove_dir_all(&root);
    }

    /// A repo whose `scripts/resolve-trust-tool.sh` resolves unset to seal 8571 and
    /// the 8560 seal directory to itself, and refuses anything else, like the real
    /// resolver; both seals have a `bin/trustc` and a PROVENANCE.
    #[cfg(unix)]
    fn fake_resolver_repo(tag: &str) -> (PathBuf, PathBuf, PathBuf) {
        use std::os::unix::fs::PermissionsExt;
        let root = temp_root(tag);
        let repo = root.join("trust-mc");
        let store = root.join("Application Support/aterm/pkg/store/trust");
        let executable = |path: &Path, text: &str| {
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
            std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
        };
        for (build, commit, sha) in [
            ("8571", "45dc60873c4fef21649ae277a93cc8cc9cf39191", "948b36c6"),
            ("8560", "25ccaf01f102fe3b4127dabeffbeba7f55516b5a", "c2e8f179"),
        ] {
            let seal = store.join(build);
            executable(
                &seal.join("bin/trustc"),
                &format!("#!/bin/sh\nprintf 'rustc 1.99.0-dev\\ncommit-hash: {commit}\\nhost: x\\n'\n"),
            );
            std::fs::write(
                seal.join("PROVENANCE"),
                format!("# seal\nreported_commit={commit}\nartifact_driver_sha256={}\n", sha.repeat(8)),
            )
            .unwrap();
        }
        let (s8571, s8560) = (store.join("8571"), store.join("8560"));
        std::fs::create_dir_all(&repo).unwrap();
        std::fs::write(repo.join("rust-toolchain.toml"), "[toolchain]\nchannel = \"trust\"\n").unwrap();
        executable(
            &repo.join("scripts/resolve-trust-tool.sh"),
            &format!(
                "#!/bin/sh\n\
                 if [ -z \"${{TRUST_MC_TRUST_TOOLCHAIN+set}}\" ]; then seal='{}'\n\
                 elif [ \"$TRUST_MC_TRUST_TOOLCHAIN\" = '{}' ]; then seal=\"$TRUST_MC_TRUST_TOOLCHAIN\"\n\
                 else echo \"resolve-trust-tool: error: $TRUST_MC_TRUST_TOOLCHAIN names no seal\" >&2; exit 2; fi\n\
                 case \"$1\" in trustc) echo \"$seal/bin/trustc\";; sysroot) echo \"$seal\";; *) exit 2;; esac\n",
                s8571.display(),
                s8560.display()
            ),
        );
        (repo, s8571, s8560)
    }

    #[cfg(unix)]
    #[test]
    fn trust_toolchain_without_override_attests_the_resolved_channel() {
        let (repo, s8571, _) = fake_resolver_repo("trust-unset");
        let trust = resolve_trust_toolchain(&repo, None).unwrap();
        assert_eq!(trust.channel, "trust");
        assert_eq!(trust.override_value, None);
        assert_eq!(trust.commit, "45dc60873c4fef21649ae277a93cc8cc9cf39191");
        assert_eq!(trust.sysroot.as_deref(), Some(s8571.as_path()));
        assert_eq!(trust.seal_build.as_deref(), Some("8571"));
        assert_eq!(trust.artifact_driver_sha256, Some("948b36c6".repeat(8)));
        let _ = std::fs::remove_dir_all(repo.parent().unwrap());
    }

    /// The measured defect: a run held on seal N through the override attested the
    /// moving channel's commit. It must attest the held seal, and say it was held.
    #[cfg(unix)]
    #[test]
    fn trust_toolchain_override_attests_the_held_seal() {
        let (repo, _, s8560) = fake_resolver_repo("trust-held");
        let trust = resolve_trust_toolchain(&repo, Some(s8560.clone().into_os_string())).unwrap();
        assert_eq!(trust.channel, "trust");
        assert_eq!(trust.override_value.as_deref(), Some(s8560.to_str().unwrap()));
        assert_eq!(trust.commit, "25ccaf01f102fe3b4127dabeffbeba7f55516b5a");
        assert_eq!(trust.sysroot.as_deref(), Some(s8560.as_path()));
        assert_eq!(trust.seal_build.as_deref(), Some("8560"));
        assert_eq!(trust.artifact_driver_sha256, Some("c2e8f179".repeat(8)));
        let _ = std::fs::remove_dir_all(repo.parent().unwrap());
    }

    #[cfg(unix)]
    #[test]
    fn trust_toolchain_override_that_does_not_resolve_refuses_to_start() {
        let (repo, s8571, s8560) = fake_resolver_repo("trust-refused");
        for value in [OsString::from("/nonexistent/store/trust/9999"), OsString::new()] {
            let error = resolve_trust_toolchain(&repo, Some(value.clone())).unwrap_err();
            let message = format!("{error:#}");
            assert!(message.contains("TRUST_MC_TRUST_TOOLCHAIN"), "{message}");
            assert!(message.contains("refusing to start"), "{message}");
            assert!(message.contains("names no seal"), "{message}");
        }
        // A held seal whose trustc reports no commit cannot be attested either.
        std::fs::write(s8560.join("bin/trustc"), "#!/bin/sh\necho 'rustc 1.99.0-dev'\n").unwrap();
        let message = format!("{:#}", resolve_trust_toolchain(&repo, Some(s8560.into_os_string())).unwrap_err());
        assert!(message.contains("no commit-hash"), "{message}");
        // Unset, the same failure is recorded, not refused.
        std::fs::write(s8571.join("bin/trustc"), "#!/bin/sh\nexit 1\n").unwrap();
        assert_eq!(resolve_trust_toolchain(&repo, None).unwrap().commit, "<unknown>");
        let _ = std::fs::remove_dir_all(repo.parent().unwrap());
    }

    #[test]
    fn trust_toolchain_without_a_resolver_is_unknown_unless_held() {
        let root = temp_root("trust-noresolver");
        let unset = resolve_trust_toolchain(&root, None).unwrap();
        assert_eq!(unset.commit, "<unknown>");
        assert_eq!((unset.sysroot, unset.seal_build, unset.artifact_driver_sha256), (None, None, None));
        assert!(resolve_trust_toolchain(&root, Some(OsString::from("trust-8571"))).is_err());
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn provenance_driver_sha_is_read_from_its_line() {
        assert_eq!(
            provenance_driver_sha256("# c\nartifact_driver_name=x\nartifact_driver_sha256=abc\n"),
            Some("abc".into())
        );
        assert_eq!(provenance_driver_sha256("artifact_driver_sha256=\n"), None);
        assert_eq!(provenance_driver_sha256(""), None);
    }

    #[test]
    fn ay_tree_follows_the_patch_path() {
        let root = temp_root("aytree");
        let repo = root.join("trust-mc");
        std::fs::create_dir_all(root.join("ay-fork/crates/ay")).unwrap();
        std::fs::create_dir_all(&repo).unwrap();
        std::fs::write(
            repo.join("Cargo.toml"),
            "[patch.\"https://github.com/alabsystems/ay.git\"]\nay = { path = \"../ay-fork/crates/ay\" }\n",
        )
        .unwrap();
        assert_eq!(ay_tree(&repo), Some(std::fs::canonicalize(root.join("ay-fork")).unwrap()));
        let _ = std::fs::remove_dir_all(&root);
    }
}
