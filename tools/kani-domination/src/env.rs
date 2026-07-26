// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Environment discovery: trust-mc repo root, the verifier binary + sysroot,
//! the `ay` SMT binary, the Kani cache dir, and the provenance authority tuple.

use anyhow::{Context, Result, bail};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::model::{Provenance, iso8601_utc};

/// Resolved paths and binaries for a domination run.
pub struct Env {
    /// trust-mc repository root.
    pub repo: PathBuf,
    /// The `trust-mc-driver` verifier binary.
    pub verifier: PathBuf,
    /// `TRUST_MC_SYSROOT` to export for the verifier.
    pub sysroot: PathBuf,
    /// The `ay` SMT binary (its directory is prepended to PATH for the verifier).
    pub ay: PathBuf,
    /// The `cargo` binary for cargo-project test units (its directory is
    /// prepended to PATH so the driver's internal `cargo` calls resolve).
    pub cargo: Option<PathBuf>,
    /// Cache root for the Kani clone, build artifacts and run reports.
    pub cache: PathBuf,
}

impl Env {
    pub fn discover() -> Result<Self> {
        let repo = find_repo_root().context("could not locate the trust-mc repo root")?;

        // Verifier: $TRUST_MC_TEST_BIN, else the build-dev sysroot driver.
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
                "verifier not found at {}\n  build it first: `cargo build-dev` (or set TRUST_MC_TEST_BIN)",
                verifier.display()
            );
        }

        let ay = resolve_ay(&repo)?;
        let cargo = resolve_cargo();
        let cache = repo.join("target/kani-domination");
        std::fs::create_dir_all(&cache).ok();

        Ok(Env { repo, verifier, sysroot, ay, cargo, cache })
    }

    pub fn kani_dir(&self) -> PathBuf {
        self.cache.join("kani")
    }
    pub fn build_base(&self) -> PathBuf {
        self.cache.join("build")
    }
    pub fn reports_dir(&self) -> PathBuf {
        self.cache.join("reports")
    }

    /// Assemble the full provenance authority tuple for a run.
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
        let ay_ver = ay_version(&self.ay).unwrap_or_else(|| "<unknown>".into());
        let ay_matches = pin != "<unknown>" && ay_ver.contains(&pin[..pin.len().min(12)]);
        let (kani_rev, kani_repo) = kani_provenance(&self.kani_dir());
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
        }
    }
}

/// Locate just the trust-mc repo root — no verifier / ay binaries required.
/// For text-only commands (`rekey-dry-run`) that never run a verification.
pub fn repo_root_lax() -> Result<PathBuf> {
    find_repo_root().context("could not locate the trust-mc repo root")
}

/// Walk up from the runtime override, configured build root, CWD, or compiled
/// manifest directory looking for the workspace root.
fn find_repo_root() -> Option<PathBuf> {
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

/// Locate an `ay` binary: $AY_BIN, then sibling `../ay` release/debug, then PATH.
fn resolve_ay(repo: &Path) -> Result<PathBuf> {
    if let Some(b) = std::env::var_os("AY_BIN") {
        let p = PathBuf::from(b);
        if p.exists() {
            return Ok(p);
        }
    }
    for rel in ["../ay/target/release/ay", "../ay/target/debug/ay"] {
        let p = repo.join(rel);
        if p.exists() {
            return Ok(p);
        }
    }
    if let Ok(p) = which::which("ay") {
        return Ok(p);
    }
    bail!(
        "no `ay` binary found (needed for the SMT/BMC path).\n  \
         set AY_BIN, build it in the sibling ../ay checkout (`cargo build --release -p ay`), \
         or put `ay` on PATH."
    )
}

/// Locate a `cargo` binary for cargo-project test units: PATH first, then the
/// conventional rustup home (`~/.cargo/bin/cargo`).
fn resolve_cargo() -> Option<PathBuf> {
    if let Ok(p) = which::which("cargo") {
        return Some(p);
    }
    let home = std::env::var_os("HOME").map(PathBuf::from)?;
    let p = home.join(".cargo/bin/cargo");
    p.exists().then_some(p)
}

fn ay_version(ay: &Path) -> Option<String> {
    let out = Command::new(ay).arg("--version").output().ok()?;
    let s = String::from_utf8_lossy(&out.stdout);
    s.lines().next().map(|l| l.trim().to_string())
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
