// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The compiler route a run measures (T1-D1; `docs/trust-lane-t1-implementation.md`, S8).
//!
//! `dev-cli` (the default) is the driver child this runner has always spawned: the
//! driver runs `trust-mc-compiler` from `TRUST_MC_SYSROOT`. `trustc` is the same
//! driver child plus `--compiler-route trustc --trustc <p> --backend-dylib <p>`
//! with `TRUST_MC_SYSROOT=<KEY>`: canonical trustc loads the trust-mc codegen
//! backend and compiles against the Kani library of that KEY.
//!
//! A trustc run is attested before the first unit (the trustc, its seal
//! PROVENANCE and installed driver, the KEY and its `KEY.json`, the backend dylib
//! and the driver it links), and every unit's output must carry the driver's
//! `[AY:COMPILER_ROUTE ...]` marker naming exactly those artifacts. Anything else
//! (a runner preflight failure, a driver refusal, a missing or disagreeing marker)
//! scores the row `error`: a route defect must never read as parity.

use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{Context, Result};

use crate::env::{TRUST_TOOLCHAIN_OVERRIDE_ENV, sha256_file};
use crate::model::RouteAttestation;

/// Which compiler builds the crates under verification (the driver's `--compiler-route`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, clap::ValueEnum)]
pub enum Route {
    /// `trust-mc-compiler` from the trust-mc install (every run before `--route` existed).
    #[default]
    DevCli,
    /// Canonical trustc loading the trust-mc codegen-backend dylib.
    Trustc,
}

impl Route {
    pub fn as_str(self) -> &'static str {
        match self {
            Route::DevCli => "dev-cli",
            Route::Trustc => "trustc",
        }
    }
}

/// The route of a row, sidecar or ledger entry written before `--route` existed:
/// all of them ran the DevCli route.
pub const LEGACY_ROUTE: &str = "dev-cli";

/// `route` as recorded, or [`LEGACY_ROUTE`] when the record predates the field.
pub fn route_or_legacy(route: Option<&str>) -> &str {
    route.unwrap_or(LEGACY_ROUTE)
}

/// The backend file `build-keyed --backend` installs under `<KEY>/codegen-backends`.
pub const BACKEND_DYLIB_FILE: &str = "librustc_codegen_trust_mc.dylib";
/// The driver's per-compile route marker.
pub const ROUTE_MARKER: &str = "[AY:COMPILER_ROUTE ";
/// Every Trustc route refusal the driver prints starts with this.
pub const ROUTE_REFUSED: &str = "compiler route trustc refused";
/// The only KEY grade whose rows count (T1-D5).
pub const PARITY_LIBRARY_MODE: &str = "parity";
/// What the runner does to harness names on the Trustc route (recorded in the attestation).
pub const TRUSTC_HARNESS_NAME_NORMALIZATION: &str = "strip the single-file crate prefix from `Checking harness` and `Verification failed for -` lines";

/// Route inputs as given on the command line; unset ones come from the
/// environment and then from the KEY.
#[derive(Debug, Clone, Default)]
pub struct TrustcRequest {
    pub trustc: Option<PathBuf>,
    pub backend_dylib: Option<PathBuf>,
    pub key: Option<PathBuf>,
}

/// The resolved inputs of a Trustc run, canonicalized when they exist.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustcInputs {
    pub trustc: PathBuf,
    pub backend_dylib: PathBuf,
    pub key_dir: PathBuf,
}

fn nonempty(value: Option<OsString>) -> Option<PathBuf> {
    value.filter(|v| !v.is_empty()).map(PathBuf::from)
}

fn canonical_or_given(path: &Path) -> PathBuf {
    std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

fn read_key_json(key_dir: &Path) -> Option<serde_json::Value> {
    let text = std::fs::read_to_string(key_dir.join("KEY.json")).ok()?;
    serde_json::from_str(&text).ok()
}

impl TrustcRequest {
    /// Resolve the inputs. Flags win over the driver's own environment names
    /// (`TRUST_MC_SYSROOT`, `TRUST_MC_TRUSTC`, `TRUST_MC_BACKEND_DYLIB`), and an
    /// empty variable counts as unset. Without either, trustc is the compiler
    /// `KEY.json` records as the KEY's builder and the dylib is the one
    /// `build-keyed --backend` installed into the KEY. Only a missing KEY or
    /// trustc is an error here; whether the inputs agree is the preflight's job.
    pub fn resolve(&self, env: impl Fn(&str) -> Option<OsString>) -> Result<TrustcInputs> {
        let key = self.key.clone().or_else(|| nonempty(env("TRUST_MC_SYSROOT"))).context(
            "--route trustc needs a KEY directory: pass --key <DIR> or set TRUST_MC_SYSROOT",
        )?;
        let key_dir = canonical_or_given(&key);
        let trustc = match self.trustc.clone().or_else(|| nonempty(env("TRUST_MC_TRUSTC"))) {
            Some(trustc) => trustc,
            None => read_key_json(&key_dir)
                .and_then(|json| json.pointer("/compiler/trustc")?.as_str().map(PathBuf::from))
                .with_context(|| {
                    format!(
                        "--route trustc needs a trustc: pass --trustc, set TRUST_MC_TRUSTC, or use a KEY \
                         whose KEY.json records compiler.trustc ({} does not)",
                        key_dir.join("KEY.json").display()
                    )
                })?,
        };
        let backend = self
            .backend_dylib
            .clone()
            .or_else(|| nonempty(env("TRUST_MC_BACKEND_DYLIB")))
            .unwrap_or_else(|| key_dir.join("codegen-backends").join(BACKEND_DYLIB_FILE));
        Ok(TrustcInputs {
            trustc: canonical_or_given(&trustc),
            backend_dylib: canonical_or_given(&backend),
            key_dir,
        })
    }
}

/// The host facts the preflight reads, behind a seam so every refusal is unit-testable.
pub trait RouteHost {
    /// Standard output of `<trustc> <args>`; the error text when it fails.
    fn trustc_stdout(&self, trustc: &Path, args: &[&str]) -> Result<String, String>;
    /// File names of the libraries `dylib` links (`otool -L` / `readelf -d`).
    fn linked_libraries(&self, dylib: &Path) -> Result<Vec<String>, String>;
    /// `tools/tuple-check --json` with the route's Trust sysroot held:
    /// `pass`, `fail: <check ids>` or `unavailable: <why>`.
    fn tuple_check(&self, trust_sysroot: &Path) -> String;
}

/// The real host.
pub struct SystemHost {
    /// trust-mc checkout whose `tools/tuple-check` is run.
    pub repo: PathBuf,
}

impl RouteHost for SystemHost {
    fn trustc_stdout(&self, trustc: &Path, args: &[&str]) -> Result<String, String> {
        let out = Command::new(trustc)
            .args(args)
            .stdin(Stdio::null())
            .output()
            .map_err(|e| format!("cannot run {}: {e}", trustc.display()))?;
        if !out.status.success() {
            return Err(format!(
                "`{} {}` exited with {}: {}",
                trustc.display(),
                args.join(" "),
                out.status,
                String::from_utf8_lossy(&out.stderr).trim()
            ));
        }
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    }

    fn linked_libraries(&self, dylib: &Path) -> Result<Vec<String>, String> {
        let (program, args): (&str, &[&str]) =
            if cfg!(target_os = "macos") { ("otool", &["-L"]) } else { ("readelf", &["-d"]) };
        let out = Command::new(program)
            .args(args)
            .arg(dylib)
            .stdin(Stdio::null())
            .output()
            .map_err(|e| format!("cannot run {program}: {e}"))?;
        if !out.status.success() {
            return Err(format!("`{program} {}` exited with {}", dylib.display(), out.status));
        }
        Ok(parse_linked_libraries(&String::from_utf8_lossy(&out.stdout)))
    }

    fn tuple_check(&self, trust_sysroot: &Path) -> String {
        let tool = self.repo.join("tools/tuple-check");
        let out = match Command::new(&tool)
            .arg("--json")
            .env(TRUST_TOOLCHAIN_OVERRIDE_ENV, trust_sysroot)
            .stdin(Stdio::null())
            .output()
        {
            Ok(out) => out,
            Err(e) => return format!("unavailable: cannot run {}: {e}", tool.display()),
        };
        summarize_tuple_check(&String::from_utf8_lossy(&out.stdout))
    }
}

/// `otool -L` (install names, one per indented line) or `readelf -d` (`(NEEDED)
/// Shared library: [name]`) output, reduced to library file names.
pub fn parse_linked_libraries(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in text.lines() {
        let name = if let Some(start) = line.find("Shared library: [") {
            let rest = &line[start + "Shared library: [".len()..];
            rest.split(']').next().unwrap_or("")
        } else if line.starts_with(char::is_whitespace) && line.contains(" (compatibility version")
        {
            line.trim().split(" (compatibility").next().unwrap_or("")
        } else {
            continue;
        };
        if let Some(file) = Path::new(name.trim()).file_name().and_then(OsStr::to_str) {
            out.push(file.to_string());
        }
    }
    out
}

/// The `tuple_check` value of a run whose inputs are the committed tuple's.
pub const TUPLE_CHECK_PASS: &str = "pass";

/// `pass`, `fail: <ids>` or `unavailable: <why>` from `tools/tuple-check --json` output.
pub fn summarize_tuple_check(json: &str) -> String {
    let Ok(value) = serde_json::from_str::<serde_json::Value>(json) else {
        return "unavailable: tools/tuple-check printed no JSON".to_string();
    };
    match value.get("ok").and_then(serde_json::Value::as_bool) {
        Some(true) => "pass".to_string(),
        Some(false) => {
            let failed: Vec<&str> = value
                .get("checks")
                .and_then(serde_json::Value::as_array)
                .into_iter()
                .flatten()
                .filter(|c| c.get("status").and_then(serde_json::Value::as_str) != Some("pass"))
                .filter_map(|c| c.get("id").and_then(serde_json::Value::as_str))
                .collect();
            format!("fail: {}", failed.join(","))
        }
        None => "unavailable: tools/tuple-check JSON has no `ok`".to_string(),
    }
}

fn provenance_field(text: &str, key: &str) -> Option<String> {
    text.lines()
        .find_map(|l| l.trim().strip_prefix(key)?.strip_prefix('=').map(str::trim))
        .filter(|v| !v.is_empty())
        .map(str::to_string)
}

fn differs(a: &Option<String>, b: &Option<String>) -> bool {
    matches!((a, b), (Some(a), Some(b)) if a != b)
}

/// Attest a Trustc run: read every artifact the rows will name and check that
/// they are one build. Every inconsistency lands in `preflight_errors`; a run
/// with any of them scores every unit `error` without spawning the driver.
/// The checks mirror the driver's own preflight (`docs/trust-lane-trustc-route.md`,
/// "Preflight") and add the ones only the runner can make: the KEY must name
/// the driver actually installed (`installed_driver_sha256`) and the trustc
/// commit it was built by.
pub fn attest_trustc(inputs: &TrustcInputs, host: &dyn RouteHost) -> RouteAttestation {
    let mut errors: Vec<String> = Vec::new();
    let trustc = &inputs.trustc;
    let trustc_sha256 = sha256_file(trustc);
    if trustc_sha256.is_none() {
        errors.push(format!("trustc {} is not a readable file", trustc.display()));
    }
    let trustc_commit = match host.trustc_stdout(trustc, &["-vV"]) {
        Ok(out) => {
            let commit = out
                .lines()
                .find_map(|l| l.strip_prefix("commit-hash:"))
                .map(|h| h.trim().to_string())
                .filter(|h| !h.is_empty() && h != "unknown");
            if commit.is_none() {
                errors.push(format!("`{} -vV` reports no commit-hash", trustc.display()));
            }
            commit
        }
        Err(e) => {
            errors.push(e);
            None
        }
    };
    let trust_sysroot = match host.trustc_stdout(trustc, &["--print", "sysroot"]) {
        Ok(out) => Some(canonical_or_given(Path::new(out.trim()))),
        Err(e) => {
            errors.push(e);
            None
        }
    };
    let mut seal_build = None;
    let (mut seal_provenance_sha256, mut seal_reported_commit) = (None, None);
    let mut seal_artifact_driver_sha256 = None;
    let (mut rustc_driver_name, mut installed_driver_sha256) = (None, None);
    if let Some(sysroot) = &trust_sysroot {
        if trustc.parent() != Some(sysroot.join("bin").as_path()) {
            errors.push(format!(
                "trustc {} is not in {}/bin, the sysroot it reports; pass that sysroot's bin/trustc itself",
                trustc.display(),
                sysroot.display()
            ));
        }
        seal_build = sysroot
            .file_name()
            .and_then(OsStr::to_str)
            .filter(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
            .map(str::to_string);
        let provenance = sysroot.join("PROVENANCE");
        seal_provenance_sha256 = sha256_file(&provenance);
        let text = std::fs::read_to_string(&provenance).unwrap_or_default();
        seal_reported_commit = provenance_field(&text, "reported_commit");
        seal_artifact_driver_sha256 = provenance_field(&text, "artifact_driver_sha256");
        let seal_artifact_driver_name = provenance_field(&text, "artifact_driver_name");
        if differs(&seal_reported_commit, &trustc_commit) {
            errors.push(format!(
                "seal PROVENANCE reported_commit {:?} differs from `trustc -vV` commit-hash {:?}",
                seal_reported_commit, trustc_commit
            ));
        }
        let mut drivers: Vec<String> = std::fs::read_dir(sysroot.join("lib"))
            .into_iter()
            .flatten()
            .flatten()
            .filter_map(|e| e.file_name().to_str().map(str::to_string))
            .filter(|n| n.starts_with("librustc_driver-"))
            .collect();
        drivers.sort();
        if drivers.len() == 1 {
            installed_driver_sha256 = sha256_file(&sysroot.join("lib").join(&drivers[0]));
            rustc_driver_name = drivers.pop();
        } else {
            errors.push(format!(
                "{}/lib must ship exactly one librustc_driver-*, found {drivers:?}",
                sysroot.display()
            ));
        }
        if differs(&seal_artifact_driver_name, &rustc_driver_name) {
            errors.push(format!(
                "seal PROVENANCE artifact_driver_name {seal_artifact_driver_name:?} is not the installed {rustc_driver_name:?}"
            ));
        }
    }
    // The driver identity a KEY is keyed by (T1-D9).
    let driver_identity =
        seal_artifact_driver_sha256.clone().or_else(|| installed_driver_sha256.clone());

    let key_dir = &inputs.key_dir;
    let key_json_sha256 = sha256_file(&key_dir.join("KEY.json"));
    let key_json = read_key_json(key_dir);
    if key_json.is_none() {
        errors.push(format!("{} is missing or not JSON", key_dir.join("KEY.json").display()));
    }
    let json = key_json.unwrap_or(serde_json::Value::Null);
    let field = |pointer: &str| {
        json.pointer(pointer).and_then(serde_json::Value::as_str).map(str::to_string)
    };
    let strings = |pointer: &str| -> Vec<String> {
        json.pointer(pointer)
            .and_then(serde_json::Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(|v| v.as_str().map(str::to_string))
            .collect()
    };
    let key = field("/key");
    let key_driver_sha256 = field("/driver_sha256");
    let key_installed_driver_sha256 = field("/installed_driver_sha256");
    let key_reported_commit = field("/reported_commit");
    let library_mode = field("/library_mode");
    let key_source_kind = field("/source/kind");
    let key_provenance = field("/compiler/provenance");
    if json.is_object() {
        let dir_name = key_dir.file_name().and_then(OsStr::to_str).map(str::to_string);
        if key.is_none() || dir_name != key {
            errors.push(format!(
                "KEY directory {} is named {dir_name:?} but KEY.json says {key:?}",
                key_dir.display()
            ));
        }
        if let Some(identity) = &driver_identity {
            if key_driver_sha256.as_deref() != Some(identity.as_str()) {
                errors.push(format!(
                    "KEY driver_sha256 {key_driver_sha256:?} differs from the trustc sysroot driver sha256 {identity}"
                ));
            }
            let expected_key = format!("driver-{}", &identity[..identity.len().min(16)]);
            if key.as_deref() != Some(expected_key.as_str()) {
                errors.push(format!(
                    "KEY {key:?} is not {expected_key}, the KEY of the trustc sysroot driver"
                ));
            }
        }
        if key_installed_driver_sha256.is_none()
            || key_installed_driver_sha256 != installed_driver_sha256
        {
            errors.push(format!(
                "KEY installed_driver_sha256 {key_installed_driver_sha256:?} is not the installed driver's {installed_driver_sha256:?}"
            ));
        }
        if differs(&key_reported_commit, &trustc_commit) {
            errors.push(format!(
                "KEY reported_commit {key_reported_commit:?} differs from the trustc commit {trustc_commit:?}"
            ));
        }
        if library_mode.is_none() {
            errors.push("KEY.json records no library_mode".to_string());
        }
        if key_source_kind.is_none() {
            errors.push(
                "KEY.json records no source.kind, so where its library sources came from is unattested"
                    .to_string(),
            );
        }
        // The PROVENANCE the KEY was built under must be this seal's: a KEY from
        // another seal with the same driver name could otherwise pass as this one.
        if let Some(sysroot) = &trust_sysroot {
            let seal_provenance = sysroot.join("PROVENANCE");
            match &key_provenance {
                Some(recorded)
                    if canonical_or_given(Path::new(recorded)) != canonical_or_given(&seal_provenance) =>
                {
                    errors.push(format!(
                        "KEY.json compiler.provenance {recorded} is not {}, the PROVENANCE of the trustc sysroot",
                        seal_provenance.display()
                    ));
                }
                None if seal_provenance_sha256.is_some() => errors.push(format!(
                    "KEY.json records no compiler.provenance but the trustc sysroot ships {}",
                    seal_provenance.display()
                )),
                _ => {}
            }
        }
    }

    let backend = &inputs.backend_dylib;
    let backend_dylib_sha256 = sha256_file(backend);
    let mut backend_linked_rustc_driver = None;
    if backend_dylib_sha256.is_none() {
        errors.push(format!("backend dylib {} is not a readable file", backend.display()));
    } else {
        match host.linked_libraries(backend) {
            Ok(libs) => {
                let linked: Vec<String> =
                    libs.into_iter().filter(|l| l.starts_with("librustc_driver-")).collect();
                if linked.len() == 1 {
                    backend_linked_rustc_driver = linked.first().cloned();
                }
                if rustc_driver_name.is_none()
                    || linked != rustc_driver_name.iter().cloned().collect::<Vec<_>>()
                {
                    errors.push(format!(
                        "backend dylib {} links {linked:?} but the trustc sysroot ships {rustc_driver_name:?}",
                        backend.display()
                    ));
                }
            }
            Err(e) => errors.push(e),
        }
    }
    let tuple_check = trust_sysroot.as_deref().map(|s| host.tuple_check(s));
    // Counted means "a row of tools/tuple.toml": no disagreement among the
    // artifacts, a parity library, and the tuple-check passing with this seal
    // held. A run on another seal (the store's `current` while the tuple names
    // an older build, say) is attested and scored, but it is not a row of this
    // tuple and never reaches the ledger (`score::ledger_refusal`).
    let counted = errors.is_empty()
        && library_mode.as_deref() == Some(PARITY_LIBRARY_MODE)
        && tuple_check.as_deref() == Some(TUPLE_CHECK_PASS);

    RouteAttestation {
        route: Route::Trustc.as_str().to_string(),
        trustc_path: trustc.display().to_string(),
        trustc_sha256,
        trustc_commit,
        trust_sysroot: trust_sysroot.as_deref().map(|p| p.display().to_string()),
        trust_seal_build: seal_build,
        seal_provenance_sha256,
        seal_reported_commit,
        seal_artifact_driver_sha256,
        rustc_driver_name,
        installed_driver_sha256,
        key_dir: key_dir.display().to_string(),
        key,
        key_json_sha256,
        key_source: field("/key_source"),
        key_source_kind,
        key_driver_sha256,
        key_installed_driver_sha256,
        key_provenance,
        key_provenance_class: field("/compiler/provenance_class"),
        library_mode,
        key_trust_mc_head: field("/trust_mc/head"),
        key_trust_mc_dirty: json.pointer("/trust_mc/dirty").and_then(serde_json::Value::as_bool),
        harness_posture: strings("/rustflags/target"),
        host_posture: strings("/rustflags/host"),
        backend_dylib_path: backend.display().to_string(),
        backend_dylib_sha256,
        backend_linked_rustc_driver,
        tuple_check,
        counted,
        preflight_errors: errors,
        harness_name_normalization: Some(TRUSTC_HARNESS_NAME_NORMALIZATION.to_string()),
    }
}

/// Decode a marker value: `%XX` is one byte, everything else is itself.
pub fn pct_decode(value: &str) -> Result<String, String> {
    let bytes = value.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' {
            let hex = bytes.get(i + 1..i + 3).filter(|h| h.iter().all(u8::is_ascii_hexdigit));
            let Some(hex) = hex else {
                return Err(format!("truncated or non-hex escape in {value:?}"));
            };
            let text = std::str::from_utf8(hex).map_err(|e| e.to_string())?;
            out.push(u8::from_str_radix(text, 16).map_err(|e| e.to_string())?);
            i += 3;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    String::from_utf8(out).map_err(|_| format!("{value:?} decodes to non-UTF-8 bytes"))
}

/// Every `[AY:COMPILER_ROUTE key=value ...]` marker in `text`, decoded, or the
/// reason one cannot be read.
pub fn route_markers(text: &str) -> Vec<Result<BTreeMap<String, String>, String>> {
    let mut out = Vec::new();
    for line in text.lines() {
        let mut rest = line;
        while let Some(start) = rest.find(ROUTE_MARKER) {
            let after = &rest[start + ROUTE_MARKER.len()..];
            let Some(end) = after.find(']') else {
                out.push(Err(format!("unterminated route marker: {}", line.trim())));
                break;
            };
            let mut fields = BTreeMap::new();
            let mut problem = None;
            for token in after[..end].split_whitespace() {
                let Some((k, v)) = token.split_once('=') else {
                    problem = Some(format!("route marker token {token:?} has no `=`"));
                    continue;
                };
                match pct_decode(v) {
                    Ok(v) => {
                        if fields.insert(k.to_string(), v).is_some() {
                            problem = Some(format!("route marker repeats `{k}`"));
                        }
                    }
                    Err(e) => problem = Some(format!("route marker `{k}`: {e}")),
                }
            }
            out.push(problem.map_or(Ok(fields), Err));
            rest = &after[end + 1..];
        }
    }
    out
}

/// THIS run's own route refusal, if it printed one.
///
/// A refusal is a DIAGNOSTIC the driver writes itself (`error: compiler route
/// trustc refused: ...`, then exit 1 with no verdict). The same text inside an
/// `[AY:...]` marker line was written by a process the driver RAN and quoted,
/// and belongs to that process, not to this run.
///
/// Measured on the T1 S7 acceptance chain: the driver's two-lane loop-contract
/// retry spawns child drivers that set engine environment knobs, the Trustc
/// route refuses such a child, and the parent quoted the child's stdout in its
/// own marker line —
///
/// ```text
/// [AY:LOOP_TWO_LANE] obligations lane did not prove: ["error: compiler route trustc refused: ..."]
/// ```
///
/// A bare `contains` read that as the RUN refusing and scored four rows —
/// each carrying a valid `[AY:COMPILER_ROUTE]` marker and a real verdict — as
/// route errors, failing two acceptance criteria for a refusal that happened
/// in a child. (The driver no longer starts a lane the route refuses; this
/// keeps any other quoted refusal from being misread the same way.)
///
/// Everything that is NOT an `[AY:...]` marker line still counts, whatever
/// surrounds the text on it, so an anyhow context line or a `Caused by:` chain
/// still fails the row closed.
fn own_route_refusal(combined: &str) -> Option<&str> {
    combined.lines().map(str::trim).find(|line| {
        line.contains(ROUTE_REFUSED) && !strip_thread_prefix(line).starts_with("[AY:")
    })
}

/// Whether a unit's output belongs to the route the run attests. `Err` names
/// why not, and the caller scores the row `error`.
///
/// On `trustc`: no driver refusal, at least one route marker (one per compile),
/// and every marker names the attested trustc, commit, rustc driver, backend
/// sha256 and KEY. On `dev-cli`: no Trustc route output at all.
pub fn check_route_output(
    route: Route,
    attestation: Option<&RouteAttestation>,
    combined: &str,
) -> Result<(), String> {
    let markers = route_markers(combined);
    let refusal = own_route_refusal(combined);
    match route {
        Route::DevCli => {
            if !markers.is_empty() || refusal.is_some() {
                return Err("a dev-cli run printed Trustc route output".to_string());
            }
            Ok(())
        }
        Route::Trustc => {
            if let Some(line) = refusal {
                return Err(format!("route refused: {line}"));
            }
            let Some(att) = attestation else {
                return Err("trustc run without a route attestation".to_string());
            };
            if markers.is_empty() {
                return Err(
                    "no [AY:COMPILER_ROUTE] marker: no compile ran through the attested trustc"
                        .to_string(),
                );
            }
            let commit12 = att.trustc_commit.as_deref().map(|c| c[..c.len().min(12)].to_string());
            let expected: [(&str, Option<String>); 6] = [
                ("route", Some(Route::Trustc.as_str().to_string())),
                ("trustc", Some(att.trustc_path.clone())),
                ("commit", commit12),
                ("driver", att.rustc_driver_name.clone()),
                ("backend_sha256", att.backend_dylib_sha256.clone()),
                ("key", att.key.clone()),
            ];
            for marker in markers {
                let marker = marker?;
                for (name, want) in &expected {
                    let got = marker.get(*name);
                    if want.is_none() || got != want.as_ref() {
                        return Err(format!(
                            "route marker {name}={} differs from the attested {}",
                            got.map_or("<absent>", String::as_str),
                            want.as_deref().unwrap_or("<unattested>")
                        ));
                    }
                }
            }
            Ok(())
        }
    }
}

/// The crate name rustc derives for a single-file unit.
pub fn single_file_crate_name(file: &Path) -> Option<String> {
    Some(file.file_stem()?.to_str()?.replace('-', "_"))
}

/// TEMPORARY. The Trustc route prints harness names crate-qualified
/// (`Checking harness forget_no_drop::main...`) where DevCli prints them bare
/// (`main`); the driver fix is on `t1/trust-lane-parity-1`. Until it lands the
/// runner rewrites the two line shapes per-harness scoring reads, so the
/// per-harness split and Kani's `expected` lines compare like for like. Remove
/// this, and its call in `runner.rs`, when that fix is on main: after it, a
/// harness in a module named like the crate would lose a real path segment.
pub fn strip_crate_qualified_harness_names(combined: &str, crate_name: &str) -> String {
    let qualified = format!("{crate_name}::");
    let mut out = String::with_capacity(combined.len());
    for line in combined.split_inclusive('\n') {
        let content = strip_thread_prefix(line);
        let prefix = &line[..line.len() - content.len()];
        let rewritten =
            ["Checking harness ", "Verification failed for - "].iter().find_map(|opener| {
                let name = content.strip_prefix(opener)?.strip_prefix(qualified.as_str())?;
                Some(format!("{prefix}{opener}{name}"))
            });
        match rewritten {
            Some(line) => out.push_str(&line),
            None => out.push_str(line),
        }
    }
    out
}

/// Strip the `Thread N: ` prefix multi-threaded driver runs tag lines with.
fn strip_thread_prefix(line: &str) -> &str {
    let Some(rest) = line.strip_prefix("Thread ") else { return line };
    let digits = rest.len() - rest.trim_start_matches(|c: char| c.is_ascii_digit()).len();
    if digits == 0 {
        return line;
    }
    rest[digits..].strip_prefix(": ").unwrap_or(line)
}

/// What a driver child verifies: a single file, or a cargo package in the
/// driver's `cargo trust-mc` identity.
#[derive(Debug, Clone, Copy)]
pub enum UnitArg<'a> {
    File(&'a Path),
    Cargo { harness: Option<&'a str> },
}

/// Everything about one driver child that does not depend on the route.
pub struct DriverInvocation<'a> {
    pub driver: &'a Path,
    pub unit: UnitArg<'a>,
    pub flags: &'a [String],
    pub cwd: &'a Path,
    pub target_dir: &'a Path,
    /// `TRUST_MC_SYSROOT` for the DevCli route.
    pub devcli_sysroot: &'a Path,
    pub path_env: &'a OsStr,
    pub ay: &'a Path,
    /// The test's own `kani-rustflags`, exported as `RUSTFLAGS` when present.
    pub rustflags: &'a [String],
    /// Variables removed from the child (`env::SCRUBBED_CHILD_ENV`).
    pub scrubbed: &'a [String],
    /// The run's `--jobs`, exported as `TRUST_MC_JOBS` (see [`JOBS_ENV`]).
    pub jobs: usize,
}

/// How many verifier children run at once. Exported to every child so the
/// driver can size itself for its share of the host: `fix/driver-deadline`
/// caps the in-process solver's memory at physical memory / (2 × jobs).
pub const JOBS_ENV: &str = "TRUST_MC_JOBS";

/// A compiler route: the driver child it spawns and what it attests.
pub trait Engine {
    fn route(&self) -> Route;
    fn command(&self, invocation: &DriverInvocation<'_>) -> Command;
    fn attest(&self) -> Option<&RouteAttestation>;
}

/// Today's driver child, unchanged.
#[derive(Debug, Clone)]
pub struct DevCliEngine;

/// The driver child on `--compiler-route trustc`.
#[derive(Debug, Clone)]
pub struct TrustcEngine {
    pub inputs: TrustcInputs,
    pub attestation: RouteAttestation,
}

/// The engine a run uses.
#[derive(Debug, Clone)]
pub enum RouteEngine {
    DevCli(DevCliEngine),
    Trustc(Box<TrustcEngine>),
}

impl RouteEngine {
    pub fn engine(&self) -> &dyn Engine {
        match self {
            RouteEngine::DevCli(e) => e,
            RouteEngine::Trustc(e) => e.as_ref(),
        }
    }
    pub fn route(&self) -> Route {
        self.engine().route()
    }
}

/// The driver command shared by both routes. Route arguments go right after the
/// unit, before the test's flags: a forwarded `--cbmc-args` consumes everything
/// after it. With no route arguments this is byte for byte the child the runner
/// spawned before `--route` existed.
fn driver_command(inv: &DriverInvocation<'_>, route_args: &[OsString], sysroot: &Path) -> Command {
    let mut cmd = Command::new(inv.driver);
    match inv.unit {
        UnitArg::File(file) => {
            cmd.arg(file).args(route_args).args(inv.flags).current_dir(inv.cwd);
        }
        UnitArg::Cargo { harness } => {
            cmd.arg("trust-mc").args(route_args).args(inv.flags).current_dir(inv.cwd);
            if let Some(h) = harness {
                cmd.args(["--harness", h]);
            }
        }
    }
    for key in inv.scrubbed {
        cmd.env_remove(key);
    }
    cmd.arg("--target-dir")
        .arg(inv.target_dir)
        .env("TRUST_MC_SYSROOT", sysroot)
        .env("PATH", inv.path_env)
        // The driver runs `$TRUST_MC_AY_BIN` in preference to PATH; name the
        // binary the provenance tuple records.
        .env("TRUST_MC_AY_BIN", inv.ay)
        .env("TRUST_MC_EMIT_EFFECTIVE_SUCCESS_MARKERS", "1")
        .env(JOBS_ENV, inv.jobs.to_string())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if !inv.rustflags.is_empty() {
        cmd.env("RUSTFLAGS", inv.rustflags.join(" "));
    }
    cmd
}

impl Engine for DevCliEngine {
    fn route(&self) -> Route {
        Route::DevCli
    }
    fn command(&self, inv: &DriverInvocation<'_>) -> Command {
        driver_command(inv, &[], inv.devcli_sysroot)
    }
    fn attest(&self) -> Option<&RouteAttestation> {
        None
    }
}

impl Engine for TrustcEngine {
    fn route(&self) -> Route {
        Route::Trustc
    }
    fn command(&self, inv: &DriverInvocation<'_>) -> Command {
        let args: Vec<OsString> = vec![
            "--compiler-route".into(),
            "trustc".into(),
            "--trustc".into(),
            self.inputs.trustc.clone().into_os_string(),
            "--backend-dylib".into(),
            self.inputs.backend_dylib.clone().into_os_string(),
        ];
        driver_command(inv, &args, &self.inputs.key_dir)
    }
    fn attest(&self) -> Option<&RouteAttestation> {
        Some(&self.attestation)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::ValueEnum;

    const SEAL_COMMIT: &str = "45dc60873c4fef21649ae277a93cc8cc9cf39191";
    const DRIVER_NAME: &str = "librustc_driver-98fef360a4a26975.dylib";

    fn temp_root(tag: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "kani-domination-route-{tag}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
        ));
        std::fs::create_dir_all(&root).unwrap();
        std::fs::canonicalize(&root).unwrap()
    }

    /// A seal (`store/trust/8571`), a KEY built for it and a backend dylib, all
    /// consistent. The host answers the trustc probes and the link table.
    struct Fixture {
        root: PathBuf,
        inputs: TrustcInputs,
        host: FakeHost,
    }

    struct FakeHost {
        commit: String,
        sysroot: PathBuf,
        linked: Vec<String>,
        /// What `tools/tuple-check --json` says with this seal held.
        tuple: String,
    }

    impl RouteHost for FakeHost {
        fn trustc_stdout(&self, _trustc: &Path, args: &[&str]) -> Result<String, String> {
            match args {
                ["-vV"] => Ok(format!(
                    "rustc 1.99.0-dev\ncommit-hash: {}\nhost: aarch64-apple-darwin\n",
                    self.commit
                )),
                ["--print", "sysroot"] => Ok(format!("{}\n", self.sysroot.display())),
                _ => Err(format!("unexpected probe {args:?}")),
            }
        }
        fn linked_libraries(&self, _dylib: &Path) -> Result<Vec<String>, String> {
            Ok(self.linked.clone())
        }
        fn tuple_check(&self, _trust_sysroot: &Path) -> String {
            self.tuple.clone()
        }
    }

    fn key_json(
        key: &str,
        driver_sha: &str,
        installed_sha: &str,
        mode: &str,
        trustc: &Path,
    ) -> String {
        serde_json::json!({
            "schema": "trust-mc-keyed-library/1", "key": key, "key_source": "provenance",
            "driver_sha256": driver_sha, "installed_driver_sha256": installed_sha,
            "driver_name": DRIVER_NAME, "reported_commit": SEAL_COMMIT, "library_mode": mode,
            "compiler": {
                "trustc": trustc,
                "provenance": trustc.parent().and_then(Path::parent).map(|seal| seal.join("PROVENANCE")),
                "provenance_class": "BUILD-STAMPED-CLEAN"
            },
            "source": {"kind": "seal-trust-src", "content_sha256": "5e41"},
            "rustflags": {"target": ["-Ztrust-verify=off"], "host": ["--cfg=kani", "-Ztrust-verify=off"]},
            "trust_mc": {"head": "29d8f04090967f08044f1848d02fa33b8b33ac28", "dirty": false}
        })
        .to_string()
    }

    fn fixture(tag: &str) -> Fixture {
        let root = temp_root(tag);
        let seal = root.join("store/trust/8571");
        std::fs::create_dir_all(seal.join("bin")).unwrap();
        std::fs::create_dir_all(seal.join("lib")).unwrap();
        std::fs::write(seal.join("bin/trustc"), "trustc").unwrap();
        std::fs::write(seal.join("lib").join(DRIVER_NAME), "installed driver bytes").unwrap();
        let installed = sha256_file(&seal.join("lib").join(DRIVER_NAME)).unwrap();
        let recorded = "948b36c62eacc5d19ae9308d2cdcffe55535a4519f3d4bdb2d4f5ae54a973055";
        std::fs::write(
            seal.join("PROVENANCE"),
            format!("# seal\nreported_commit={SEAL_COMMIT}\nartifact_driver_name={DRIVER_NAME}\nartifact_driver_sha256={recorded}\n"),
        )
        .unwrap();
        let key_dir = root.join("keyed/driver-948b36c62eacc5d1");
        std::fs::create_dir_all(key_dir.join("codegen-backends")).unwrap();
        std::fs::write(
            key_dir.join("KEY.json"),
            key_json(
                "driver-948b36c62eacc5d1",
                recorded,
                &installed,
                "parity",
                &seal.join("bin/trustc"),
            ),
        )
        .unwrap();
        std::fs::write(key_dir.join("codegen-backends").join(BACKEND_DYLIB_FILE), "backend bytes")
            .unwrap();
        let inputs = TrustcRequest { key: Some(key_dir.clone()), ..Default::default() }
            .resolve(|_| None)
            .unwrap();
        let host = FakeHost {
            commit: SEAL_COMMIT.to_string(),
            tuple: TUPLE_CHECK_PASS.to_string(),
            sysroot: seal,
            linked: vec![
                format!("@rpath/{BACKEND_DYLIB_FILE}"),
                DRIVER_NAME.to_string(),
                "libSystem.B.dylib".into(),
            ]
            .into_iter()
            .map(|l| Path::new(&l).file_name().unwrap().to_str().unwrap().to_string())
            .collect(),
        };
        Fixture { root, inputs, host }
    }

    #[test]
    fn route_values_are_dev_cli_and_trustc() {
        assert_eq!(Route::from_str("dev-cli", false).unwrap(), Route::DevCli);
        assert_eq!(Route::from_str("trustc", false).unwrap(), Route::Trustc);
        assert_eq!(Route::default(), Route::DevCli);
        assert_eq!(route_or_legacy(None), "dev-cli");
        assert_eq!(route_or_legacy(Some("trustc")), "trustc");
    }

    #[test]
    fn inputs_come_from_flags_then_environment_then_the_key() {
        let f = fixture("resolve");
        let seal_trustc = f.host.sysroot.join("bin/trustc");
        assert_eq!(f.inputs.trustc, seal_trustc, "trustc from KEY.json compiler.trustc");
        assert_eq!(
            f.inputs.backend_dylib,
            f.inputs.key_dir.join("codegen-backends").join(BACKEND_DYLIB_FILE)
        );

        let other = f.root.join("other");
        std::fs::create_dir_all(&other).unwrap();
        let env = |name: &str| match name {
            "TRUST_MC_SYSROOT" => Some(f.inputs.key_dir.clone().into_os_string()),
            "TRUST_MC_TRUSTC" => Some(other.join("env-trustc").into_os_string()),
            "TRUST_MC_BACKEND_DYLIB" => Some(OsString::new()),
            _ => None,
        };
        let from_env = TrustcRequest::default().resolve(env).unwrap();
        assert_eq!(from_env.key_dir, f.inputs.key_dir);
        assert_eq!(from_env.trustc, other.join("env-trustc"));
        assert_eq!(from_env.backend_dylib, f.inputs.backend_dylib, "an empty variable is unset");

        let flags = TrustcRequest {
            trustc: Some(other.join("flag-trustc")),
            backend_dylib: Some(other.join("flag.dylib")),
            key: Some(f.inputs.key_dir.clone()),
        };
        let from_flags = flags.resolve(env).unwrap();
        assert_eq!(
            (from_flags.trustc, from_flags.backend_dylib),
            (other.join("flag-trustc"), other.join("flag.dylib"))
        );

        let missing = format!("{:#}", TrustcRequest::default().resolve(|_| None).unwrap_err());
        assert!(missing.contains("--key"), "{missing}");
        let _ = std::fs::remove_dir_all(&f.root);
    }

    #[test]
    fn a_consistent_seal_key_and_backend_attest_clean_and_counted() {
        let f = fixture("clean");
        let att = attest_trustc(&f.inputs, &f.host);
        assert!(att.preflight_errors.is_empty(), "{:?}", att.preflight_errors);
        assert!(att.counted);
        assert_eq!(att.route, "trustc");
        assert_eq!(att.trustc_commit.as_deref(), Some(SEAL_COMMIT));
        assert_eq!(att.trust_seal_build.as_deref(), Some("8571"));
        assert_eq!(att.rustc_driver_name.as_deref(), Some(DRIVER_NAME));
        assert_eq!(att.backend_linked_rustc_driver.as_deref(), Some(DRIVER_NAME));
        assert_eq!(att.key.as_deref(), Some("driver-948b36c62eacc5d1"));
        assert_eq!(att.library_mode.as_deref(), Some("parity"));
        assert_eq!(att.key_installed_driver_sha256, att.installed_driver_sha256);
        assert_eq!(att.harness_posture, vec!["-Ztrust-verify=off"]);
        assert_eq!(att.key_provenance_class.as_deref(), Some("BUILD-STAMPED-CLEAN"));
        assert_eq!(att.key_source.as_deref(), Some("provenance"));
        assert_eq!(att.key_source_kind.as_deref(), Some("seal-trust-src"));
        assert_eq!(
            att.key_provenance.as_deref().map(Path::new),
            Some(f.host.sysroot.join("PROVENANCE").as_path())
        );
        assert_eq!(att.tuple_check.as_deref(), Some("pass"));
        assert!(
            att.key_json_sha256.is_some()
                && att.backend_dylib_sha256.is_some()
                && att.seal_provenance_sha256.is_some()
        );
        let _ = std::fs::remove_dir_all(&f.root);
    }

    fn rewrite_key(f: &Fixture, edit: impl Fn(&mut serde_json::Value)) {
        let path = f.inputs.key_dir.join("KEY.json");
        let mut value: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
        edit(&mut value);
        std::fs::write(path, value.to_string()).unwrap();
    }

    fn errors_of(f: &Fixture) -> String {
        let att = attest_trustc(&f.inputs, &f.host);
        assert!(!att.counted, "an inconsistent route must never count");
        att.preflight_errors.join(" | ")
    }

    #[test]
    fn a_key_for_another_driver_is_a_preflight_error_naming_both_values() {
        let f = fixture("otherdriver");
        rewrite_key(&f, |v| v["driver_sha256"] = "c2e8f1798de668fa".repeat(4).into());
        let errors = errors_of(&f);
        assert!(
            errors.contains("KEY driver_sha256")
                && errors.contains("c2e8f1798de668fa")
                && errors.contains("948b36c6"),
            "{errors}"
        );
        let _ = std::fs::remove_dir_all(&f.root);
    }

    #[test]
    fn a_key_bound_to_another_installed_driver_is_a_preflight_error() {
        let f = fixture("installed");
        rewrite_key(&f, |v| v["installed_driver_sha256"] = "e7a812eb".repeat(8).into());
        assert!(errors_of(&f).contains("installed_driver_sha256"));
        rewrite_key(&f, |v| {
            v.as_object_mut().unwrap().remove("installed_driver_sha256");
        });
        assert!(errors_of(&f).contains("installed_driver_sha256"));
        let _ = std::fs::remove_dir_all(&f.root);
    }

    /// A seal other than the committed tuple's (the store's `current` while
    /// `tools/tuple.toml` names an older build) attests clean and is scored, but
    /// it is not a row of this tuple: uncounted, with the check ids recorded. An
    /// unavailable tuple-check is uncounted too; no evidence is not a pass.
    #[test]
    fn an_off_tuple_seal_attests_clean_but_does_not_count() {
        let mut f = fixture("offtuple");
        f.host.tuple = "fail: trust_rev,trust_seal_build".to_string();
        let att = attest_trustc(&f.inputs, &f.host);
        assert!(att.preflight_errors.is_empty(), "{:?}", att.preflight_errors);
        assert_eq!(att.library_mode.as_deref(), Some("parity"));
        assert_eq!(att.tuple_check.as_deref(), Some("fail: trust_rev,trust_seal_build"));
        assert!(!att.counted, "a run on another seal is not a row of this tuple");

        f.host.tuple = "unavailable: cannot run tools/tuple-check".to_string();
        let att = attest_trustc(&f.inputs, &f.host);
        assert!(att.preflight_errors.is_empty());
        assert!(!att.counted, "no tuple evidence is not a pass");
        let _ = std::fs::remove_dir_all(&f.root);
    }

    #[test]
    fn a_smoke_key_attests_clean_but_does_not_count() {
        let f = fixture("smoke");
        rewrite_key(&f, |v| v["library_mode"] = "smoke".into());
        let att = attest_trustc(&f.inputs, &f.host);
        assert!(att.preflight_errors.is_empty(), "{:?}", att.preflight_errors);
        assert_eq!(att.library_mode.as_deref(), Some("smoke"));
        assert!(!att.counted);
        let _ = std::fs::remove_dir_all(&f.root);
    }

    #[test]
    fn a_backend_linking_another_driver_or_missing_is_a_preflight_error() {
        let mut f = fixture("backend");
        f.host.linked = vec!["librustc_driver-e5ab7a82643f630e.dylib".into()];
        assert!(errors_of(&f).contains("links [\"librustc_driver-e5ab7a82643f630e.dylib\"]"));
        f.inputs.backend_dylib = f.root.join("absent.dylib");
        assert!(errors_of(&f).contains("is not a readable file"));
        let _ = std::fs::remove_dir_all(&f.root);
    }

    #[test]
    fn a_trustc_outside_its_sysroot_or_from_another_commit_is_a_preflight_error() {
        let mut f = fixture("shim");
        let shim = f.root.join("shim/trustc");
        std::fs::create_dir_all(shim.parent().unwrap()).unwrap();
        std::fs::write(&shim, "shim").unwrap();
        f.inputs.trustc = shim;
        assert!(errors_of(&f).contains("is not in"));
        let mut f = fixture("commit");
        f.host.commit = "25ccaf01f102fe3b4127dabeffbeba7f55516b5a".into();
        let errors = errors_of(&f);
        assert!(errors.contains("reported_commit"), "{errors}");
        let _ = std::fs::remove_dir_all(&f.root);
    }

    #[test]
    fn a_key_under_another_seal_provenance_or_without_a_source_kind_is_a_preflight_error() {
        let f = fixture("keyprov");
        rewrite_key(&f, |v| v["compiler"]["provenance"] = "/store/trust/8560/PROVENANCE".into());
        let errors = errors_of(&f);
        assert!(errors.contains("compiler.provenance /store/trust/8560/PROVENANCE"), "{errors}");
        rewrite_key(&f, |v| {
            v["compiler"].as_object_mut().unwrap().remove("provenance");
        });
        assert!(errors_of(&f).contains("records no compiler.provenance"));
        let _ = std::fs::remove_dir_all(&f.root);

        let f = fixture("nokind");
        rewrite_key(&f, |v| {
            v.as_object_mut().unwrap().remove("source");
        });
        assert!(errors_of(&f).contains("source.kind"));
        let _ = std::fs::remove_dir_all(&f.root);
    }

    #[test]
    fn a_missing_key_json_is_a_preflight_error() {
        let f = fixture("nokey");
        std::fs::remove_file(f.inputs.key_dir.join("KEY.json")).unwrap();
        assert!(errors_of(&f).contains("KEY.json is missing"));
        let _ = std::fs::remove_dir_all(&f.root);
    }

    #[test]
    fn linked_libraries_parse_otool_and_readelf() {
        let otool = "/k/librustc_codegen_trust_mc.dylib:\n\t@rpath/librustc_codegen_trust_mc.dylib (compatibility version 0.0.0, current version 0.0.0)\n\t@rpath/librustc_driver-98fef360a4a26975.dylib (compatibility version 0.0.0, current version 0.0.0)\n\t/usr/lib/libSystem.B.dylib (compatibility version 1.0.0, current version 1351.0.0)\n";
        assert_eq!(
            parse_linked_libraries(otool),
            vec![
                "librustc_codegen_trust_mc.dylib",
                "librustc_driver-98fef360a4a26975.dylib",
                "libSystem.B.dylib"
            ]
        );
        let readelf = " 0x0000000000000001 (NEEDED)             Shared library: [librustc_driver-abc.so]\n 0x000000000000000e (SONAME)             Library soname: [x.so]\n";
        assert_eq!(parse_linked_libraries(readelf), vec!["librustc_driver-abc.so"]);
    }

    #[test]
    fn tuple_check_summary() {
        assert_eq!(summarize_tuple_check(r#"{"ok": true, "checks": []}"#), "pass");
        assert_eq!(
            summarize_tuple_check(
                r#"{"ok": false, "checks": [{"id":"trust.build","status":"fail"},{"id":"ay.rev","status":"pass"}]}"#
            ),
            "fail: trust.build"
        );
        assert!(summarize_tuple_check("garbage").starts_with("unavailable"));
    }

    fn attestation() -> RouteAttestation {
        RouteAttestation {
            route: "trustc".into(),
            trustc_path:
                "$HOME/Library/Application Support/aterm/pkg/store/trust/8571/bin/trustc".into(),
            trustc_commit: Some(SEAL_COMMIT.into()),
            rustc_driver_name: Some(DRIVER_NAME.into()),
            backend_dylib_sha256: Some(
                "6edf24db15dee517a0ef9b100908c09c657468df86c9f8101f4eab7b5a64bdc4".into(),
            ),
            key: Some("driver-948b36c62eacc5d1".into()),
            counted: true,
            ..Default::default()
        }
    }

    const MARKER: &str = "[AY:COMPILER_ROUTE route=trustc trustc=$HOME/Library/Application%20Support/aterm/pkg/store/trust/8571/bin/trustc commit=45dc60873c4f driver=librustc_driver-98fef360a4a26975.dylib backend_sha256=6edf24db15dee517a0ef9b100908c09c657468df86c9f8101f4eab7b5a64bdc4 key=driver-948b36c62eacc5d1]";

    #[test]
    fn route_markers_decode_pct1_values() {
        let markers = route_markers(&format!("noise\n{MARKER}\n"));
        assert_eq!(markers.len(), 1);
        let m = markers[0].as_ref().unwrap();
        assert_eq!(
            m["trustc"],
            "$HOME/Library/Application Support/aterm/pkg/store/trust/8571/bin/trustc"
        );
        assert_eq!(m["commit"], "45dc60873c4f");
        assert_eq!(pct_decode("a%5Db%25").unwrap(), "a]b%");
        assert!(
            pct_decode("bad%4").is_err()
                && pct_decode("bad%zz").is_err()
                && pct_decode("%FF").is_err()
        );
    }

    #[test]
    fn trustc_output_with_matching_markers_belongs_to_the_route() {
        let att = attestation();
        let out = format!(
            "{MARKER}\nChecking harness main::main...\nVERIFICATION:- SUCCESSFUL\n{MARKER}\n"
        );
        assert_eq!(check_route_output(Route::Trustc, Some(&att), &out), Ok(()));
    }

    #[test]
    fn a_refusal_a_missing_marker_or_a_disagreeing_marker_is_a_route_error() {
        let att = attestation();
        let refused = "error: compiler route trustc refused: KEY driver_sha256 c2e8 differs\n";
        assert!(
            check_route_output(Route::Trustc, Some(&att), refused)
                .unwrap_err()
                .starts_with("route refused")
        );
        // A refusal after a compile (BackendChanged) wins over the marker and any verdict.
        let late = format!("{MARKER}\nVERIFICATION:- SUCCESSFUL\n{refused}");
        assert!(check_route_output(Route::Trustc, Some(&att), &late).is_err());
        let bare = "VERIFICATION:- SUCCESSFUL\n";
        assert!(
            check_route_output(Route::Trustc, Some(&att), bare)
                .unwrap_err()
                .contains("no [AY:COMPILER_ROUTE]")
        );
        let rebuilt = MARKER.replace("backend_sha256=6edf", "backend_sha256=0000");
        let error = check_route_output(Route::Trustc, Some(&att), &rebuilt).unwrap_err();
        assert!(error.contains("backend_sha256=0000"), "{error}");
        let playback = MARKER.replace(
            "backend_sha256=6edf24db15dee517a0ef9b100908c09c657468df86c9f8101f4eab7b5a64bdc4",
            "backend=unused",
        );
        assert!(
            check_route_output(Route::Trustc, Some(&att), &playback)
                .unwrap_err()
                .contains("backend_sha256=<absent>")
        );
        let other_key =
            MARKER.replace("key=driver-948b36c62eacc5d1", "key=driver-c2e8f1798de668fa");
        assert!(check_route_output(Route::Trustc, Some(&att), &other_key).is_err());
        assert!(check_route_output(Route::Trustc, None, MARKER).is_err());
        let mut unattested = att.clone();
        unattested.backend_dylib_sha256 = None;
        assert!(
            check_route_output(Route::Trustc, Some(&unattested), MARKER)
                .unwrap_err()
                .contains("<unattested>")
        );
    }

    /// The exact shape of the four T1 S7 rows: an attested compile, a real
    /// verdict, and a LANE CHILD's refusal quoted inside the driver's own
    /// `[AY:LOOP_TWO_LANE]` marker line. That is the child's refusal, not this
    /// run's, and scoring the row a route error hides a measured verdict behind
    /// a defect that is not there.
    #[test]
    fn a_refusal_quoted_inside_a_marker_line_belongs_to_the_child_not_the_run() {
        let att = attestation();
        let quoted = format!(
            "{MARKER}\n\
             Checking harness decreases_binary_search::binary_search_harness...\n\
             [AY:LOOP_TWO_LANE] obligations lane did not prove: [\"error: compiler route \
             trustc refused: engine environment knob(s) TRUST_MC_COMPOUND_DECREASES are set\"]\n\
             VERIFICATION:- FAILED\n"
        );
        assert_eq!(check_route_output(Route::Trustc, Some(&att), &quoted), Ok(()));
        assert_eq!(own_route_refusal(&quoted), None);
        // A thread-prefixed marker line is quoting too.
        let threaded = quoted.replace("[AY:LOOP_TWO_LANE]", "Thread 2: [AY:LOOP_TWO_LANE]");
        assert_eq!(check_route_output(Route::Trustc, Some(&att), &threaded), Ok(()));
        // ...but ONLY a marker line. Every other shape still fails closed:
        // the bare diagnostic, an anyhow context line, and a `Caused by:` tail.
        for own in [
            "error: compiler route trustc refused: KEY driver_sha256 c2e8 differs",
            "error: failed to build the harness: compiler route trustc refused: KEY changed",
            "    compiler route trustc refused: the backend dylib changed",
        ] {
            let out = format!("{MARKER}\nVERIFICATION:- SUCCESSFUL\n{own}\n");
            assert!(
                check_route_output(Route::Trustc, Some(&att), &out)
                    .unwrap_err()
                    .starts_with("route refused"),
                "{own}"
            );
        }
    }

    /// A route LIMITATION is not a refusal: the run named an optional step the
    /// route could not take and still produced its verdict.
    #[test]
    fn a_named_route_limitation_is_not_a_route_error() {
        let att = attestation();
        let out = format!(
            "{MARKER}\n\
             [AY:ROUTE_LIMITATION:two-lane-loop-contract-retry route=trustc]\n\
             [AY:LOOP_TWO_LANE] not run on the trustc compiler route: the lanes need engine \
             environment knob(s) TRUST_MC_COMPOUND_DECREASES, TRUST_MC_NO_LOOP_RULE\n\
             VERIFICATION:- FAILED\n"
        );
        assert_eq!(check_route_output(Route::Trustc, Some(&att), &out), Ok(()));
    }

    #[test]
    fn dev_cli_output_carrying_trustc_route_output_is_a_route_error() {
        assert_eq!(check_route_output(Route::DevCli, None, "VERIFICATION:- SUCCESSFUL\n"), Ok(()));
        assert!(check_route_output(Route::DevCli, None, MARKER).is_err());
    }

    #[test]
    fn crate_qualified_harness_names_are_stripped_on_the_two_scored_lines_only() {
        let out = "[AY:CODEGEN_COMPLETE:harnesses=2]\n\
                   Checking harness float_remainder::check_f64_rem...\n\
                   Thread 1: Checking harness float_remainder::check_f32_rem...\n\
                   Manual Harness Summary:\n\
                   Verification failed for - float_remainder::check_f64_rem\n\
                   Verification failed for - other::check\n\
                   Checking harness check_bare...\n\
                   assertion in float_remainder::check_f64_rem";
        assert_eq!(
            strip_crate_qualified_harness_names(out, "float_remainder"),
            "[AY:CODEGEN_COMPLETE:harnesses=2]\n\
             Checking harness check_f64_rem...\n\
             Thread 1: Checking harness check_f32_rem...\n\
             Manual Harness Summary:\n\
             Verification failed for - check_f64_rem\n\
             Verification failed for - other::check\n\
             Checking harness check_bare...\n\
             assertion in float_remainder::check_f64_rem"
        );
        assert_eq!(
            single_file_crate_name(Path::new("tests/kani/x/access-padding-uninit.rs")).as_deref(),
            Some("access_padding_uninit")
        );
    }

    fn invocation<'a>(
        flags: &'a [String],
        rustflags: &'a [String],
        scrubbed: &'a [String],
    ) -> DriverInvocation<'a> {
        DriverInvocation {
            driver: Path::new("/b/bin/trust-mc-driver"),
            unit: UnitArg::File(Path::new("/k/tests/kani/a.rs")),
            flags,
            cwd: Path::new("/k"),
            target_dir: Path::new("/c/build/kani/a/target"),
            devcli_sysroot: Path::new("/b"),
            path_env: OsStr::new("/ay:/usr/bin"),
            ay: Path::new("/ay/ay"),
            rustflags,
            scrubbed,
            jobs: 6,
        }
    }

    fn argv(cmd: &Command) -> Vec<String> {
        cmd.get_args().map(|a| a.to_string_lossy().into_owned()).collect()
    }

    fn envs(cmd: &Command) -> Vec<(String, Option<String>)> {
        let mut out: Vec<_> = cmd
            .get_envs()
            .map(|(k, v)| {
                (k.to_string_lossy().into_owned(), v.map(|v| v.to_string_lossy().into_owned()))
            })
            .collect();
        out.sort();
        out
    }

    /// DevCli is the child the runner spawned before `--route` existed.
    #[test]
    fn dev_cli_command_is_the_pre_route_child() {
        let flags =
            vec!["-Z".to_string(), "unstable-options".into(), "--harness-timeout=15s".into()];
        let scrubbed = vec!["RUSTC".to_string()];
        let rustflags = vec!["--edition".to_string(), "2021".into()];
        let cmd = DevCliEngine.command(&invocation(&flags, &rustflags, &scrubbed));
        assert_eq!(cmd.get_program(), "/b/bin/trust-mc-driver");
        assert_eq!(
            argv(&cmd),
            [
                "/k/tests/kani/a.rs",
                "-Z",
                "unstable-options",
                "--harness-timeout=15s",
                "--target-dir",
                "/c/build/kani/a/target"
            ]
        );
        assert_eq!(cmd.get_current_dir(), Some(Path::new("/k")));
        let some = |s: &str| Some(s.to_string());
        assert_eq!(
            envs(&cmd),
            vec![
                ("PATH".to_string(), some("/ay:/usr/bin")),
                ("RUSTC".into(), None),
                ("RUSTFLAGS".into(), some("--edition 2021")),
                ("TRUST_MC_AY_BIN".into(), some("/ay/ay")),
                ("TRUST_MC_EMIT_EFFECTIVE_SUCCESS_MARKERS".into(), some("1")),
                ("TRUST_MC_JOBS".into(), some("6")),
                ("TRUST_MC_SYSROOT".into(), some("/b")),
            ]
        );
        assert!(DevCliEngine.attest().is_none());

        let mut cargo = invocation(&flags, &[], &[]);
        cargo.unit = UnitArg::Cargo { harness: Some("check_x") };
        assert_eq!(
            argv(&DevCliEngine.command(&cargo)),
            [
                "trust-mc",
                "-Z",
                "unstable-options",
                "--harness-timeout=15s",
                "--harness",
                "check_x",
                "--target-dir",
                "/c/build/kani/a/target"
            ]
        );
    }

    #[test]
    fn trustc_command_adds_the_route_inputs_and_exports_the_key() {
        let flags = vec!["--ay-chc".to_string(), "--cbmc-args".into(), "x".into()];
        let engine = TrustcEngine {
            inputs: TrustcInputs {
                trustc: PathBuf::from("/s/8571/bin/trustc"),
                backend_dylib: PathBuf::from("/K/codegen-backends/librustc_codegen_trust_mc.dylib"),
                key_dir: PathBuf::from("/K"),
            },
            attestation: attestation(),
        };
        let cmd = engine.command(&invocation(&flags, &[], &[]));
        assert_eq!(
            argv(&cmd),
            [
                "/k/tests/kani/a.rs",
                "--compiler-route",
                "trustc",
                "--trustc",
                "/s/8571/bin/trustc",
                "--backend-dylib",
                "/K/codegen-backends/librustc_codegen_trust_mc.dylib",
                "--ay-chc",
                "--cbmc-args",
                "x",
                "--target-dir",
                "/c/build/kani/a/target"
            ]
        );
        assert!(envs(&cmd).contains(&("TRUST_MC_SYSROOT".to_string(), Some("/K".to_string()))));
        let engine = RouteEngine::Trustc(Box::new(engine));
        assert_eq!(engine.route(), Route::Trustc);
        assert_eq!(
            engine.engine().attest().unwrap().key.as_deref(),
            Some("driver-948b36c62eacc5d1")
        );
    }
}
