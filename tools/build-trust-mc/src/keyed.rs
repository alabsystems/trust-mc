// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `build-keyed`: the Kani library built by one Trust compiler and stored under
//! that compiler's identity (T1 rulings T1-D8 and T1-D9).
//!
//! A library rlib embeds the version string of the compiler that produced it, so
//! it is loadable only by that exact compiler (anything else is E0514). The
//! output therefore lives at `target/trust-mc/keyed/<KEY>/`, where
//! `KEY = driver-<artifact_driver_sha256[:16]>` from the compiler sysroot's
//! `PROVENANCE`, falling back to the sha256 of `lib/librustc_driver-*` when the
//! sysroot has no PROVENANCE.
//!
//! Every tool comes from the compiler's own sysroot: `cargo` is
//! `<sysroot>/bin/cargo`, `RUSTC` is the given trustc, and nothing is looked up
//! on PATH. Library sources are the trust checkout at the compiler's
//! `reported_commit`, extracted with `git archive`. The paths outside `library/`
//! are derived by running `cargo metadata --locked` on the extracted tree until it
//! resolves, so a new first-party std path dependency is picked up (or refused)
//! instead of silently breaking `-Zbuild-std`. With `--trust-src` the sources are
//! instead a copy of the trust-src component the compiler's own sysroot ships
//! (`lib/rustlib/src/rust`), recorded by a content digest; nothing outside that
//! component is read, and `cargo metadata --locked` must resolve it as shipped.
//!
//! A KEY directory holds one compiler's library in one grade: a rebuild naming
//! another driver sha, commit or `--std` grade is refused before anything changes,
//! and one build at a time holds `<KEY>.lock` beside the directory.

use crate::parser::{BuildKeyedParser, StdMode};
use crate::sysroot::{
    LibToolchain, NO_CORE_CARGO_ARGS, NO_CORE_PACKAGES, PLAYBACK_FEATURES, StdLibs,
    VERIFICATION_PACKAGES, build_target, build_trust_mc_lib, copy_artifacts, lib_extension,
    trust_mc_repo_root,
};
use anyhow::{Context, Result, bail, format_err};
use std::collections::BTreeSet;
use std::ffi::OsString;
use std::fs;
use std::io::{ErrorKind, Read};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

/// Name of the identity record written into every KEY directory.
pub(crate) const KEY_JSON: &str = "KEY.json";
/// Schema 2 added `source.kind` (`git-archive` or `seal-trust-src`).
const KEY_SCHEMA: &str = "trust-mc-keyed-library/2";
/// Where a Trust sysroot's trust-src component keeps the library sources.
pub(crate) const TRUST_SRC_COMPONENT: &str = "lib/rustlib/src/rust";
/// Upper bound on `cargo metadata` rounds while deriving the source tree.
const SOURCE_DERIVATION_ROUNDS: usize = 16;
/// Flags every target unit of the keyed library gets on top of the Kani base set.
/// Strict Trust verification of kani/kani_core produced 430+ errors (T1-D6).
const KEYED_TARGET_RUSTFLAGS: [&str; 1] = ["-Ztrust-verify=off"];
/// Flags for host units (build scripts, kani_macros and its proc-macro deps).
const KEYED_HOST_RUSTFLAGS: [&str; 3] = ["--cfg=kani", "--cfg=kani_sysroot", "-Ztrust-verify=off"];
/// Environment a keyed library build must not inherit. `RUSTFLAGS` would lose to
/// `CARGO_ENCODED_RUSTFLAGS` anyway, but a wrapper, a redirected target dir, a
/// stale source root or an incremental override would silently change what is
/// built, and KEY.json records no effective profile.
const KEYED_ENV_REMOVE: [&str; 9] = [
    "RUSTFLAGS",
    "CARGO_BUILD_RUSTFLAGS",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    "CARGO_TARGET_DIR",
    "CARGO_BUILD_TARGET_DIR",
    "__CARGO_TESTS_ONLY_SRC_ROOT",
    "RUSTUP_TOOLCHAIN",
    "CARGO_INCREMENTAL",
];
/// Cargo reads every `CARGO_PROFILE_<profile>_<key>` (overflow-checks, opt-level,
/// codegen-units, ...) and `CARGO_UNSTABLE_<flag>` variable as configuration, so
/// each inherited one could change the parity std without KEY.json recording it.
const KEYED_ENV_REMOVE_PREFIXES: [&str; 2] = ["CARGO_PROFILE_", "CARGO_UNSTABLE_"];

/// Is `key` one the keyed cargo must not inherit?
fn is_keyed_env_removed(key: &str) -> bool {
    KEYED_ENV_REMOVE.contains(&key) || KEYED_ENV_REMOVE_PREFIXES.iter().any(|p| key.starts_with(p))
}

/// The variables the keyed cargo removes, given the names in the environment it
/// would inherit: every [`KEYED_ENV_REMOVE`] name, plus each inherited
/// `CARGO_PROFILE_*` / `CARGO_UNSTABLE_*` variable. Non-UTF-8 names are not cargo
/// configuration and are ignored.
pub(crate) fn keyed_env_remove<I, K>(inherited: I) -> Vec<String>
where
    I: IntoIterator<Item = K>,
    K: AsRef<std::ffi::OsStr>,
{
    let mut remove: Vec<String> = KEYED_ENV_REMOVE.iter().map(|k| k.to_string()).collect();
    remove.extend(
        inherited_keyed_env(inherited)
            .into_iter()
            .filter(|k| !KEYED_ENV_REMOVE.contains(&k.as_str())),
    );
    remove
}

/// The inherited variables among `inherited` that the keyed cargo removes, sorted:
/// what KEY.json records as `env_scrubbed`.
pub(crate) fn inherited_keyed_env<I, K>(inherited: I) -> Vec<String>
where
    I: IntoIterator<Item = K>,
    K: AsRef<std::ffi::OsStr>,
{
    let mut found: Vec<String> = inherited
        .into_iter()
        .filter_map(|k| k.as_ref().to_str().map(str::to_string))
        .filter(|k| is_keyed_env_removed(k))
        .collect();
    found.sort();
    found.dedup();
    found
}

impl StdMode {
    /// The library grade recorded in KEY.json (T1-D5): only `parity` rows count.
    pub(crate) fn library_mode(self) -> &'static str {
        match self {
            StdMode::BuildStd => "parity",
            StdMode::Prebuilt => "smoke",
        }
    }

    fn cli_name(self) -> &'static str {
        match self {
            StdMode::BuildStd => "build-std",
            StdMode::Prebuilt => "prebuilt",
        }
    }
}

// ---------------------------------------------------------------------------
// Compiler identity and KEY
// ---------------------------------------------------------------------------

/// The fields of a seal `PROVENANCE` file that key a library.
#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct Provenance {
    pub(crate) reported_commit: Option<String>,
    pub(crate) driver_sha256: Option<String>,
    pub(crate) driver_name: Option<String>,
    pub(crate) driver_bytes: Option<u64>,
    pub(crate) class: Option<String>,
}

/// Parse the `key=value` lines of a seal PROVENANCE file. Comments and keys this
/// tool does not use are ignored; a repeated key is refused because it makes the
/// identity ambiguous.
pub(crate) fn parse_provenance(text: &str) -> Result<Provenance> {
    let mut provenance = Provenance::default();
    let mut bytes: Option<String> = None;
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let Some((key, value)) = line.split_once('=') else { continue };
        let key = key.trim();
        let slot = match key {
            "reported_commit" => &mut provenance.reported_commit,
            "artifact_driver_sha256" => &mut provenance.driver_sha256,
            "artifact_driver_name" => &mut provenance.driver_name,
            "artifact_driver_bytes" => &mut bytes,
            "provenance_class" => &mut provenance.class,
            _ => continue,
        };
        if slot.replace(value.trim().to_string()).is_some() {
            bail!("PROVENANCE repeats `{key}`; refusing an ambiguous compiler identity");
        }
    }
    if let Some(bytes) = bytes {
        provenance.driver_bytes = Some(bytes.parse().map_err(|_| {
            format_err!("PROVENANCE artifact_driver_bytes `{bytes}` is not a byte count")
        })?);
    }
    Ok(provenance)
}

/// Where a KEY's driver sha256 came from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum KeySource {
    /// `artifact_driver_sha256` in the sysroot's PROVENANCE.
    Provenance,
    /// sha256 of the sysroot's only `lib/librustc_driver-*` file.
    DriverDylibSha256,
}

impl KeySource {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            KeySource::Provenance => "provenance",
            KeySource::DriverDylibSha256 => "driver-dylib-sha256",
        }
    }
}

/// Everything that names the compiler a keyed library belongs to.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct CompilerIdentity {
    pub(crate) key: String,
    pub(crate) key_source: KeySource,
    pub(crate) driver_sha256: String,
    pub(crate) driver_name: String,
    pub(crate) reported_commit: String,
    pub(crate) provenance_class: Option<String>,
    /// `artifact_driver_bytes` from PROVENANCE, when recorded.
    pub(crate) driver_bytes_recorded: Option<u64>,
    /// Size of the installed driver file.
    pub(crate) driver_bytes_installed: Option<u64>,
}

fn is_lower_hex(text: &str, len: usize) -> bool {
    text.len() == len && text.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// `driver-<sha256[:16]>` (T1-D9). Anything but a full lowercase sha256 is refused.
pub(crate) fn key_for(driver_sha256: &str) -> Result<String> {
    if !is_lower_hex(driver_sha256, 64) {
        bail!(
            "driver sha256 `{driver_sha256}` is not 64 lowercase hex digits; \
             refusing to derive a library KEY from it"
        );
    }
    Ok(format!("driver-{}", &driver_sha256[..16]))
}

/// The `librustc_driver-*` shared libraries directly under `<sysroot>/lib`, sorted.
fn driver_libraries(sysroot: &Path) -> Result<Vec<PathBuf>> {
    let lib = sysroot.join("lib");
    let entries = fs::read_dir(&lib).with_context(|| format!("cannot list {}", lib.display()))?;
    let suffix = format!(".{}", lib_extension());
    let mut drivers: Vec<PathBuf> = entries
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("librustc_driver-") && name.ends_with(&suffix))
                && path.is_file()
        })
        .collect();
    drivers.sort();
    Ok(drivers)
}

fn single_driver(sysroot: &Path) -> Result<PathBuf> {
    let drivers = driver_libraries(sysroot)?;
    match drivers.as_slice() {
        [driver] => Ok(driver.clone()),
        [] => bail!(
            "no librustc_driver-*.{} under {}; cannot identify the compiler",
            lib_extension(),
            sysroot.join("lib").display()
        ),
        many => bail!(
            "{} holds {} librustc_driver libraries ({}); without PROVENANCE the \
             compiler's driver is ambiguous, so no KEY can be derived",
            sysroot.join("lib").display(),
            many.len(),
            many.iter().map(|d| d.display().to_string()).collect::<Vec<_>>().join(", ")
        ),
    }
}

fn file_name_string(path: &Path) -> String {
    path.file_name().map(|name| name.to_string_lossy().into_owned()).unwrap_or_default()
}

/// Derive the identity of the compiler whose sysroot is `sysroot`.
///
/// `verbose_commit` is the `commit-hash:` line of `trustc -vV`; `provenance` is
/// the text of `<sysroot>/PROVENANCE` when that file exists.
pub(crate) fn derive_identity(
    sysroot: &Path,
    verbose_commit: Option<&str>,
    provenance: Option<&str>,
) -> Result<CompilerIdentity> {
    let provenance = provenance.map(parse_provenance).transpose()?;
    let verbose_commit = verbose_commit.map(str::trim).filter(|c| !c.is_empty() && *c != "unknown");
    let provenance_commit = provenance.as_ref().and_then(|p| p.reported_commit.as_deref());
    let reported_commit = match (provenance_commit, verbose_commit) {
        (Some(recorded), Some(reported)) if recorded != reported => bail!(
            "{}/PROVENANCE reported_commit {recorded} disagrees with the compiler's own \
             commit-hash {reported}; that PROVENANCE does not describe this trustc",
            sysroot.display()
        ),
        (Some(commit), _) | (None, Some(commit)) => commit.to_string(),
        (None, None) => bail!(
            "cannot name the compiler's commit: {} has no PROVENANCE reported_commit and \
             `trustc -vV` reports no commit-hash; refusing to choose library sources",
            sysroot.display()
        ),
    };
    if !is_lower_hex(&reported_commit, 40) {
        bail!("compiler commit `{reported_commit}` is not a full 40-hex git commit id");
    }

    let class = provenance.as_ref().and_then(|p| p.class.clone());
    // A driver PROVENANCE names must be installed, whether or not PROVENANCE also
    // records its sha256: otherwise the record describes another sysroot.
    let recorded_name = provenance.as_ref().and_then(|p| p.driver_name.clone());
    if let Some(name) = &recorded_name {
        if !sysroot.join("lib").join(name).is_file() {
            bail!(
                "{}/PROVENANCE names driver {name}, which is not in {}; \
                 that PROVENANCE does not describe this sysroot",
                sysroot.display(),
                sysroot.join("lib").display()
            );
        }
    }
    if let Some(sha) = provenance.as_ref().and_then(|p| p.driver_sha256.clone()) {
        let key = key_for(&sha)?;
        let driver_name = match recorded_name {
            Some(name) => name,
            None => file_name_string(&single_driver(sysroot)?),
        };
        // PROVENANCE's artifact identity establishes which build this is, not the
        // bytes of the installed file: packaging may rewrite the driver after
        // sealing (measured on build 8571: 438173224 recorded, 370030832
        // installed). The KEY follows PROVENANCE (T1-D9); a size difference is
        // reported and recorded, never used to re-key.
        let recorded = provenance.as_ref().and_then(|p| p.driver_bytes);
        let installed = fs::metadata(sysroot.join("lib").join(&driver_name)).ok().map(|m| m.len());
        if let (Some(recorded), Some(installed)) = (recorded, installed) {
            if recorded != installed {
                eprintln!(
                    "warning: {driver_name} is {installed} bytes installed but PROVENANCE \
                     records {recorded}; keying by PROVENANCE artifact_driver_sha256"
                );
            }
        }
        return Ok(CompilerIdentity {
            key,
            key_source: KeySource::Provenance,
            driver_sha256: sha,
            driver_name,
            reported_commit,
            provenance_class: class,
            driver_bytes_recorded: recorded,
            driver_bytes_installed: installed,
        });
    }

    // No recorded sha256: hash the driver PROVENANCE names, else the only one there.
    let driver = match recorded_name {
        Some(name) => sysroot.join("lib").join(name),
        None => single_driver(sysroot)?,
    };
    let sha = sha256_file(&driver)?;
    Ok(CompilerIdentity {
        key: key_for(&sha)?,
        key_source: KeySource::DriverDylibSha256,
        driver_sha256: sha,
        driver_name: file_name_string(&driver),
        reported_commit,
        provenance_class: class,
        driver_bytes_recorded: provenance.as_ref().and_then(|p| p.driver_bytes),
        driver_bytes_installed: fs::metadata(&driver).ok().map(|m| m.len()),
    })
}

/// What `trustc -vV` and `trustc --print sysroot` report.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct CompilerProbe {
    pub(crate) version: String,
    pub(crate) commit_hash: Option<String>,
    pub(crate) host: String,
}

pub(crate) fn parse_verbose_version(text: &str) -> Result<CompilerProbe> {
    let version = text.lines().next().unwrap_or_default().trim().to_string();
    if version.is_empty() {
        bail!("`trustc -vV` printed nothing");
    }
    let field = |name: &str| {
        text.lines().find_map(|line| line.strip_prefix(name).map(|v| v.trim().to_string()))
    };
    let host = field("host:").ok_or_else(|| format_err!("`trustc -vV` has no host: line"))?;
    Ok(CompilerProbe { version, commit_hash: field("commit-hash:"), host })
}

pub(crate) fn run_capture(command: &mut Command, what: &str) -> Result<String> {
    let output = command.output().with_context(|| format!("failed to run {what}"))?;
    if !output.status.success() {
        bail!(
            "{what} failed ({}): {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        );
    }
    Ok(String::from_utf8(output.stdout).with_context(|| format!("{what} printed non-UTF-8"))?)
}

// ---------------------------------------------------------------------------
// Existing KEY directories
// ---------------------------------------------------------------------------

/// Read a top-level string field such as `"driver_sha256": "…"` from KEY.json.
/// The fields read back are hex ids, so no unescaping is needed.
pub(crate) fn json_string_field(text: &str, field: &str) -> Option<String> {
    let needle = format!("\"{field}\"");
    let mut rest = text;
    while let Some(at) = rest.find(&needle) {
        rest = &rest[at + needle.len()..];
        let Some(value) = rest.trim_start().strip_prefix(':') else { continue };
        let Some(body) = value.trim_start().strip_prefix('"') else { continue };
        return body.find('"').map(|end| body[..end].to_string());
    }
    None
}

/// Refuse to build into a KEY directory whose KEY.json names another compiler,
/// or holds a library of another grade: parity and smoke share the KEY path, so an
/// in-place rebuild in the other `--std` mode would silently change what every
/// consumer of that KEY counts (T1-D5).
pub(crate) fn check_existing_key(
    key_json: Option<&str>,
    identity: &CompilerIdentity,
    std: StdMode,
    key_dir: &Path,
) -> Result<()> {
    let Some(text) = key_json else { return Ok(()) };
    let sha = json_string_field(text, "driver_sha256");
    let commit = json_string_field(text, "reported_commit");
    if sha.as_deref() != Some(identity.driver_sha256.as_str())
        || commit.as_deref() != Some(identity.reported_commit.as_str())
    {
        bail!(
            "KEY mismatch: {} records driver_sha256={} reported_commit={}, but --trustc is \
             driver_sha256={} reported_commit={}. A KEY directory holds one compiler's \
             libraries; build-keyed will not overwrite another compiler's KEY.",
            key_dir.join(KEY_JSON).display(),
            sha.as_deref().unwrap_or("<missing>"),
            commit.as_deref().unwrap_or("<missing>"),
            identity.driver_sha256,
            identity.reported_commit
        );
    }
    let mode = json_string_field(text, "library_mode");
    if mode.as_deref() != Some(std.library_mode()) {
        bail!(
            "KEY mode mismatch: {} holds a {} library, but --std {} builds a {} library. \
             build-keyed will not replace one grade with the other in place; remove {} \
             first if that is intended.",
            key_dir.join(KEY_JSON).display(),
            mode.as_deref().unwrap_or("<missing>"),
            std.cli_name(),
            std.library_mode(),
            key_dir.display()
        );
    }
    Ok(())
}

/// Take `key_dir` for a build: refuse another compiler's or another grade's KEY
/// and a source that cannot supply the library (a checkout without the commit, a
/// sysroot without a trust-src component), all before changing anything, then
/// drop the KEY.json and installed backend a rebuild is about to replace.
pub(crate) fn claim_key_dir(
    key_dir: &Path,
    identity: &CompilerIdentity,
    std: StdMode,
    source: &LibrarySource,
) -> Result<()> {
    let key_json_path = key_dir.join(KEY_JSON);
    let existing = match fs::read_to_string(&key_json_path) {
        Ok(text) => Some(text),
        Err(error) if error.kind() == ErrorKind::NotFound => None,
        Err(error) => {
            return Err(error).context(format!("cannot read {}", key_json_path.display()));
        }
    };
    check_existing_key(existing.as_deref(), identity, std, key_dir)?;
    // Refuse a source that cannot supply the library before touching the KEY
    // directory, so a refused rebuild leaves an existing KEY exactly as it was.
    source.preflight(&identity.reported_commit)?;
    fs::create_dir_all(key_dir)?;
    if existing.is_some() {
        // A rebuild that fails half way must not leave a KEY.json vouching for
        // libraries it has partly replaced.
        fs::remove_file(&key_json_path)?;
    }
    // A backend installed by an earlier build must not outlive a KEY.json that
    // no longer names it.
    let backends = key_dir.join("codegen-backends");
    if backends.exists() {
        fs::remove_dir_all(&backends)
            .with_context(|| format!("cannot clear {}", backends.display()))?;
    }
    Ok(())
}

/// Hold an exclusive lock on `<keyed root>/<KEY>.lock` for the whole build. Two
/// concurrent builds of one KEY would otherwise clear each other's sources and
/// libraries while an earlier KEY.json still vouches for them. The lock file sits
/// beside the KEY directory so removing that directory never unlinks a held lock.
fn lock_key(keyed_root: &Path, key: &str) -> Result<fs::File> {
    fs::create_dir_all(keyed_root)
        .with_context(|| format!("cannot create {}", keyed_root.display()))?;
    let path = keyed_root.join(format!("{key}.lock"));
    let file = fs::File::options()
        .create(true)
        .truncate(false)
        .write(true)
        .open(&path)
        .with_context(|| format!("cannot open {}", path.display()))?;
    match file.try_lock() {
        Ok(()) => Ok(file),
        Err(fs::TryLockError::WouldBlock) => bail!(
            "another build-keyed holds {}; refusing to build {key} concurrently",
            path.display()
        ),
        Err(fs::TryLockError::Error(error)) => {
            Err(error).with_context(|| format!("cannot lock {}", path.display()))
        }
    }
}

// ---------------------------------------------------------------------------
// Seal library sources (T1-D8)
// ---------------------------------------------------------------------------

fn git(checkout: &Path) -> Command {
    let mut command = Command::new("git");
    command.arg("-C").arg(checkout);
    for var in ["GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_OBJECT_DIRECTORY"] {
        command.env_remove(var);
    }
    command
}

/// Refuse unless `checkout` is the top level of a git checkout that contains
/// `commit`. Returns the commit's root tree id.
pub(crate) fn require_commit(checkout: &Path, commit: &str) -> Result<String> {
    let toplevel = git(checkout)
        .args(["rev-parse", "--show-toplevel"])
        .output()
        .context("failed to run git")?;
    let toplevel_path = PathBuf::from(String::from_utf8_lossy(&toplevel.stdout).trim());
    let canonical = fs::canonicalize(checkout)
        .with_context(|| format!("--trust-checkout {} does not exist", checkout.display()))?;
    if !toplevel.status.success() || fs::canonicalize(&toplevel_path).ok() != Some(canonical) {
        bail!("--trust-checkout {} is not the top level of a git checkout", checkout.display());
    }
    let verified = git(checkout)
        .args(["rev-parse", "--verify", "--quiet", &format!("{commit}^{{commit}}")])
        .output()
        .context("failed to run git rev-parse")?;
    if !verified.status.success() {
        bail!(
            "trust checkout {} does not contain commit {commit}, the compiler's \
             reported_commit. build-keyed builds library sources only from that exact \
             commit; fetch it into the checkout rather than substituting another revision.",
            checkout.display()
        );
    }
    let tree = run_capture(
        git(checkout).args(["rev-parse", &format!("{commit}^{{tree}}")]),
        "git rev-parse <commit>^{tree}",
    )?;
    Ok(tree.trim().to_string())
}

/// `(type, object id)` of `path` at `commit`, or None if the commit has no such path.
fn git_object(checkout: &Path, commit: &str, path: &str) -> Result<Option<(String, String)>> {
    let listing = run_capture(git(checkout).args(["ls-tree", commit, "--", path]), "git ls-tree")?;
    Ok(listing.lines().find_map(|line| {
        let (meta, name) = line.split_once('\t')?;
        let mut fields = meta.split_whitespace();
        let (_mode, kind, oid) = (fields.next()?, fields.next()?, fields.next()?);
        (name == path).then(|| (kind.to_string(), oid.to_string()))
    }))
}

fn git_show(checkout: &Path, commit: &str, path: &str) -> Option<String> {
    let output = git(checkout).args(["show", &format!("{commit}:{path}")]).output().ok()?;
    output.status.success().then(|| String::from_utf8_lossy(&output.stdout).into_owned())
}

/// `git archive <commit> -- <path> | tar -x -C <dest>`.
fn extract_path(checkout: &Path, commit: &str, path: &str, dest: &Path) -> Result<()> {
    let mut archive = git(checkout)
        .args(["archive", "--format=tar", commit, "--", path])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .context("failed to run git archive")?;
    let stdout = archive.stdout.take().context("git archive stdout was not captured")?;
    let tar = Command::new("tar")
        .arg("-x")
        .arg("-C")
        .arg(dest)
        .stdin(Stdio::from(stdout))
        .status()
        .context("failed to run tar")?;
    let archive = archive.wait_with_output().context("git archive did not finish")?;
    if !archive.status.success() || !tar.success() {
        bail!(
            "extracting {path} at {commit} from {} failed: {}",
            checkout.display(),
            String::from_utf8_lossy(&archive.stderr).trim()
        );
    }
    Ok(())
}

/// A `cargo metadata` failure build-keyed can repair by extracting one more path.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum MissingSource {
    /// Cargo could not read this manifest: a path dependency or `[patch]` target.
    Manifest(PathBuf),
    /// This manifest inherits from a workspace whose root is not extracted.
    WorkspaceRootFor(PathBuf),
}

fn backticked_after(text: &str, prefix: &str) -> Option<PathBuf> {
    let start = text.find(prefix)? + prefix.len();
    let end = text[start..].find('`')?;
    Some(PathBuf::from(&text[start..start + end]))
}

pub(crate) fn diagnose_metadata_failure(stderr: &str) -> Option<MissingSource> {
    if stderr.contains("failed to find a workspace root") {
        return backticked_after(stderr, "failed to parse manifest at `")
            .map(MissingSource::WorkspaceRootFor);
    }
    backticked_after(stderr, "failed to read `")
        .filter(|path| path.file_name().is_some_and(|name| name == "Cargo.toml"))
        .or_else(|| {
            // Targo reports a missing registry-patch directory differently
            // from a missing path dependency. Treat only this precise
            // diagnostic as a candidate manifest; materialize_sources still
            // confines it to the archive, requires the exact commit's path,
            // and refuses a repeated request after extraction.
            stderr.lines().find_map(|line| {
                let patch = line.trim().strip_prefix("error: patch location `")?;
                let (directory, package) =
                    patch.split_once("` does not contain packages matching `")?;
                let (package, suffix) = package.split_once('`')?;
                if directory.is_empty() || package.is_empty() || !suffix.trim().is_empty() {
                    return None;
                }
                Some(Path::new(directory).join("Cargo.toml"))
            })
        })
        .map(MissingSource::Manifest)
}

/// The manifests cargo tries as a workspace root for `manifest`, nearest first.
pub(crate) fn ancestor_manifests(manifest: &Path) -> Vec<PathBuf> {
    let mut candidates = Vec::new();
    let mut dir = manifest.parent();
    while let Some(current) = dir {
        let parent = current.parent();
        if let Some(parent) = parent {
            candidates.push(parent.join("Cargo.toml"));
        }
        dir = parent;
    }
    candidates
}

fn has_workspace_table(manifest: &str) -> bool {
    manifest.lines().any(|line| line.trim_start().starts_with("[workspace]"))
}

fn inherits_from_workspace(manifest: &str) -> bool {
    manifest.lines().any(|line| {
        let compact: String = line.chars().filter(|c| !c.is_whitespace()).collect();
        !compact.starts_with('#') && compact.contains("workspace=true")
    })
}

fn rel_string(path: &Path) -> String {
    path.components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join("/")
}

/// The nearest not-yet-extracted ancestor manifest at `commit` that declares a
/// workspace — the next root cargo would consider for `manifest_rel`.
fn nearest_workspace_manifest(
    checkout: &Path,
    commit: &str,
    manifest_rel: &Path,
    extracted: &BTreeSet<String>,
) -> Result<String> {
    for candidate in ancestor_manifests(manifest_rel) {
        let candidate = rel_string(&candidate);
        if extracted.contains(&candidate) {
            continue;
        }
        if git_show(checkout, commit, &candidate).is_some_and(|text| has_workspace_table(&text)) {
            return Ok(candidate);
        }
    }
    bail!(
        "{} inherits from a workspace, but commit {commit} has no further ancestor \
         Cargo.toml with [workspace] (already extracted: {})",
        manifest_rel.display(),
        extracted.iter().cloned().collect::<Vec<_>>().join(", ")
    )
}

/// One extracted path of the seal source tree.
#[derive(Debug)]
pub(crate) struct SourceEntry {
    pub(crate) path: String,
    pub(crate) kind: String,
    pub(crate) oid: String,
}

/// Where build-keyed takes the library sources from (T1-D8).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LibrarySource {
    /// `git archive` of this trust checkout at the compiler's reported_commit.
    Checkout(PathBuf),
    /// The trust-src component inside the compiler's own sysroot.
    SealComponent(PathBuf),
}

impl LibrarySource {
    /// Refuse a source that cannot supply the compiler's library.
    fn preflight(&self, commit: &str) -> Result<()> {
        match self {
            LibrarySource::Checkout(checkout) => require_commit(checkout, commit).map(drop),
            LibrarySource::SealComponent(component) => require_seal_component(component),
        }
    }
}

/// How the seal library source was obtained.
#[derive(Debug)]
pub(crate) enum SourceOrigin {
    /// Paths extracted by `git archive` from a trust checkout.
    GitArchive { checkout: PathBuf, commit_tree: String, entries: Vec<SourceEntry> },
    /// A copy of the trust-src component the compiler's sysroot ships.
    SealComponent { component: PathBuf, copy: ComponentCopy },
}

/// The extracted seal library source and how it was derived.
#[derive(Debug)]
pub(crate) struct SourceTree {
    pub(crate) commit: String,
    pub(crate) origin: SourceOrigin,
    /// Path packages cargo resolved outside `library/`: `(name, manifest)`.
    pub(crate) outside_packages: Vec<(String, String)>,
    pub(crate) metadata_rounds: usize,
}

impl SourceTree {
    /// One line naming where the sources came from.
    pub(crate) fn describe(&self) -> String {
        match &self.origin {
            SourceOrigin::GitArchive { checkout, entries, .. } => format!(
                "{} at {} (+ {})",
                checkout.display(),
                self.commit,
                entries
                    .iter()
                    .filter(|e| e.path != "library")
                    .map(|e| e.path.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            SourceOrigin::SealComponent { component, copy } => format!(
                "trust-src component {} for {} ({} files, sha256 {}; + {})",
                component.display(),
                self.commit,
                copy.files,
                copy.sha256,
                copy.out_of_library_paths.join(", ")
            ),
        }
    }
}

fn metadata_command(cargo: &Path, trustc: &Path, src: &Path) -> cargo_metadata::MetadataCommand {
    let mut command = cargo_metadata::MetadataCommand::new();
    command
        .cargo_path(cargo)
        .manifest_path(src.join("library/Cargo.toml"))
        .current_dir(src)
        // The commit's own Cargo.lock must resolve unchanged. A wrong workspace
        // root (for example one that inherits another package version) rewrites
        // the lock and is refused here instead of producing a different std.
        .other_options(vec!["--locked".to_string()])
        .env("RUSTC", trustc)
        .env("RUSTC_WRAPPER", "")
        .env("CARGO_BUILD_RUSTC_WRAPPER", "");
    command
}

/// Keyed Trust builds use the held seal's Trust frontend, never its
/// compatibility `cargo` persona or a program found on PATH. The frozen
/// stock oracle is a separate build-dev lane, not a canonical Trustc KEY.
fn keyed_targo(sysroot: &Path) -> Result<PathBuf> {
    let targo = sysroot.join("bin/targo");
    if !targo.is_file() {
        bail!(
            "{} has no bin/targo; build-keyed requires the Trust frontend from the compiler's sysroot",
            sysroot.display()
        );
    }
    Ok(targo)
}

/// Workspace root cargo uses for `manifest`, if it can find one.
fn located_workspace_root(cargo: &Path, trustc: &Path, manifest: &Path) -> Option<PathBuf> {
    let output = Command::new(cargo)
        .args(["locate-project", "--workspace", "--message-format", "plain", "--manifest-path"])
        .arg(manifest)
        .env("RUSTC", trustc)
        .output()
        .ok()?;
    output.status.success().then(|| PathBuf::from(String::from_utf8_lossy(&output.stdout).trim()))
}

/// Extract `library/` at `commit` into `src`, then every path outside it that
/// `cargo metadata --locked` needs, until cargo resolves the library workspace.
pub(crate) fn materialize_sources(
    cargo: &Path,
    trustc: &Path,
    checkout: &Path,
    commit: &str,
    src: &Path,
) -> Result<SourceTree> {
    let commit_tree = require_commit(checkout, commit)?;
    if src.exists() {
        fs::remove_dir_all(src).with_context(|| format!("cannot clear {}", src.display()))?;
    }
    fs::create_dir_all(src)?;
    let src = fs::canonicalize(src)?;
    let library_root = src.join("library");
    let mut extracted = BTreeSet::new();
    let mut next = "library".to_string();

    for round in 1..=SOURCE_DERIVATION_ROUNDS {
        if !extracted.insert(next.clone()) {
            bail!("cargo metadata still needs `{next}` after it was extracted at {commit}");
        }
        if git_object(checkout, commit, &next)?.is_none() {
            bail!(
                "the std library at {commit} needs `{next}`, which does not exist in that \
                 commit of {}",
                checkout.display()
            );
        }
        extract_path(checkout, commit, &next, &src)?;
        println!("-- seal source: extracted {next} (round {round})");

        let relative = |path: &Path| -> Result<PathBuf> {
            path.strip_prefix(&src).map(Path::to_path_buf).map_err(|_| {
                format_err!(
                    "cargo resolved {} outside the extracted seal source {}; refusing a \
                     library tree that reaches beyond commit {commit}",
                    path.display(),
                    src.display()
                )
            })
        };

        next = match metadata_command(cargo, trustc, &src).exec() {
            Ok(metadata) => {
                let mut outside = Vec::new();
                for package in metadata.packages.iter().filter(|p| p.source.is_none()) {
                    let manifest = package.manifest_path.as_std_path();
                    if !manifest.starts_with(&library_root) {
                        outside.push((package.name.to_string(), manifest.to_path_buf()));
                    }
                }
                let mut pending = None;
                for (_, manifest) in &outside {
                    let rel = relative(manifest)?;
                    let inherits = fs::read_to_string(manifest)
                        .is_ok_and(|text| inherits_from_workspace(&text));
                    let root_inside = located_workspace_root(cargo, trustc, manifest)
                        .is_some_and(|root| root.starts_with(&src));
                    if inherits && !root_inside {
                        pending =
                            Some(nearest_workspace_manifest(checkout, commit, &rel, &extracted)?);
                        break;
                    }
                }
                match pending {
                    Some(path) => path,
                    None => {
                        let mut entries = Vec::new();
                        for path in &extracted {
                            let (kind, oid) = git_object(checkout, commit, path)?
                                .ok_or_else(|| format_err!("{path} vanished from {commit}"))?;
                            entries.push(SourceEntry { path: path.clone(), kind, oid });
                        }
                        let outside_packages = outside
                            .iter()
                            .map(|(name, manifest)| {
                                Ok((name.clone(), rel_string(&relative(manifest)?)))
                            })
                            .collect::<Result<Vec<_>>>()?;
                        return Ok(SourceTree {
                            commit: commit.to_string(),
                            origin: SourceOrigin::GitArchive {
                                checkout: checkout.to_path_buf(),
                                commit_tree,
                                entries,
                            },
                            outside_packages,
                            metadata_rounds: round,
                        });
                    }
                }
            }
            Err(cargo_metadata::Error::CargoMetadata { stderr }) => {
                match diagnose_metadata_failure(&stderr) {
                    Some(MissingSource::Manifest(manifest)) => {
                        let rel = relative(&manifest)?;
                        rel_string(rel.parent().unwrap_or(Path::new("")))
                    }
                    Some(MissingSource::WorkspaceRootFor(manifest)) => nearest_workspace_manifest(
                        checkout,
                        commit,
                        &relative(&manifest)?,
                        &extracted,
                    )?,
                    None => bail!(
                        "cargo metadata --locked on the seal library sources failed for a \
                         reason build-keyed cannot map to a missing trust path:\n{stderr}"
                    ),
                }
            }
            Err(other) => {
                return Err(other).context("running cargo metadata on the seal library sources");
            }
        };
    }
    bail!("seal library source derivation did not converge in {SOURCE_DERIVATION_ROUNDS} rounds")
}

/// How [`ComponentCopy::sha256`] is computed, recorded in KEY.json.
pub(crate) const COMPONENT_DIGEST_FORMAT: &str = "sha256 over every entry in byte order of its \
    /-joined relative path: 'D <path>' NUL for a directory, 'F <path>' NUL <decimal byte length> \
    NUL <bytes> for a file";

/// What a copied trust-src component holds.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct ComponentCopy {
    /// See [`COMPONENT_DIGEST_FORMAT`].
    pub(crate) sha256: String,
    pub(crate) files: u64,
    pub(crate) bytes: u64,
    /// Directories two levels deep outside `library/` (`crates/trust-bignum`).
    pub(crate) out_of_library_paths: Vec<String>,
}

/// Refuse unless `component` is a trust-src component directory carrying the
/// library workspace manifest and its lock file.
pub(crate) fn require_seal_component(component: &Path) -> Result<()> {
    let metadata = fs::symlink_metadata(component).map_err(|error| {
        format_err!(
            "the compiler sysroot ships no trust-src component at {} ({error}). --trust-src \
             needs a seal whose trust-src component carries library/ and every path it \
             resolves outside library/; otherwise pass --trust-checkout with a checkout \
             containing the compiler's reported_commit",
            component.display()
        )
    })?;
    if !metadata.is_dir() {
        bail!(
            "the trust-src component {} is not a directory (a symbolic link is not followed)",
            component.display()
        );
    }
    for required in ["library/Cargo.toml", "library/Cargo.lock"] {
        if !component.join(required).is_file() {
            bail!("the trust-src component {} has no {required}", component.display());
        }
    }
    Ok(())
}

/// Copy every file and directory of `component` into `dest`, hashing the content
/// as it goes. A symbolic link or special file is refused rather than followed:
/// the copy must hold only what the seal ships.
pub(crate) fn copy_component(component: &Path, dest: &Path) -> Result<ComponentCopy> {
    let mut entries: Vec<(String, bool)> = Vec::new();
    let mut pending = vec![PathBuf::new()];
    while let Some(relative) = pending.pop() {
        let dir = component.join(&relative);
        let listing =
            fs::read_dir(&dir).with_context(|| format!("cannot list {}", dir.display()))?;
        for entry in listing {
            let entry = entry.with_context(|| format!("cannot list {}", dir.display()))?;
            let path = relative.join(entry.file_name());
            if entry.file_name().to_str().is_none() {
                bail!(
                    "the trust-src component entry {} is not UTF-8",
                    component.join(&path).display()
                );
            }
            let kind = entry.file_type()?;
            if kind.is_dir() {
                entries.push((rel_string(&path), true));
                pending.push(path);
            } else if kind.is_file() {
                entries.push((rel_string(&path), false));
            } else {
                bail!(
                    "the trust-src component entry {} is neither a file nor a directory; \
                     build-keyed copies no symbolic links or special files out of a seal",
                    component.join(&path).display()
                );
            }
        }
    }
    entries.sort();
    let mut hasher = Sha256::new();
    let (mut files, mut bytes) = (0u64, 0u64);
    let mut out_of_library_paths = Vec::new();
    for (name, is_dir) in &entries {
        let (from, to) = (component.join(name), dest.join(name));
        if *is_dir {
            hasher.update(format!("D {name}\0").as_bytes());
            fs::create_dir_all(&to).with_context(|| format!("cannot create {}", to.display()))?;
            if name.split('/').count() == 2 && !name.starts_with("library/") {
                out_of_library_paths.push(name.clone());
            }
            continue;
        }
        let content = fs::read(&from).with_context(|| format!("cannot read {}", from.display()))?;
        hasher.update(format!("F {name}\0{}\0", content.len()).as_bytes());
        hasher.update(&content);
        if let Some(parent) = to.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&to, &content).with_context(|| format!("cannot write {}", to.display()))?;
        fs::set_permissions(&to, fs::metadata(&from)?.permissions())?;
        files += 1;
        bytes += content.len() as u64;
    }
    Ok(ComponentCopy { sha256: hasher.finish(), files, bytes, out_of_library_paths })
}

/// Copy the seal's trust-src `component` into `src` and require `cargo metadata
/// --locked` to resolve the library workspace inside that copy, as shipped.
pub(crate) fn materialize_seal_component(
    cargo: &Path,
    trustc: &Path,
    component: &Path,
    commit: &str,
    src: &Path,
) -> Result<SourceTree> {
    require_seal_component(component)?;
    if src.exists() {
        fs::remove_dir_all(src).with_context(|| format!("cannot clear {}", src.display()))?;
    }
    fs::create_dir_all(src)?;
    let src = fs::canonicalize(src)?;
    let copy = copy_component(component, &src)?;
    println!(
        "-- seal source: copied trust-src component {} ({} files, {} bytes, sha256 {})",
        component.display(),
        copy.files,
        copy.bytes,
        copy.sha256
    );
    let metadata = match metadata_command(cargo, trustc, &src).exec() {
        Ok(metadata) => metadata,
        Err(cargo_metadata::Error::CargoMetadata { stderr }) => {
            let missing = match diagnose_metadata_failure(&stderr) {
                Some(MissingSource::Manifest(manifest)) => {
                    format!("it does not carry {}", manifest.display())
                }
                Some(MissingSource::WorkspaceRootFor(manifest)) => format!(
                    "{} inherits from a workspace root it does not carry",
                    manifest.display()
                ),
                None => "cargo could not resolve it".to_string(),
            };
            bail!(
                "cargo metadata --locked on the trust-src component copied from {} failed: \
                 {missing}. build-keyed takes nothing from outside the component, so Trust's \
                 trust-src dist step must carry every path library/ resolves.\n{stderr}",
                component.display()
            );
        }
        Err(other) => {
            return Err(other).context("running cargo metadata on the trust-src component");
        }
    };
    let library_root = src.join("library");
    let mut outside_packages = Vec::new();
    for package in metadata.packages.iter().filter(|p| p.source.is_none()) {
        let manifest = package.manifest_path.as_std_path();
        if manifest.starts_with(&library_root) {
            continue;
        }
        let relative = manifest.strip_prefix(&src).map_err(|_| {
            format_err!(
                "cargo resolved {} outside the copied trust-src component {}; refusing a \
                 library tree that reaches beyond the seal",
                manifest.display(),
                src.display()
            )
        })?;
        outside_packages.push((package.name.to_string(), rel_string(relative)));
    }
    outside_packages.sort();
    Ok(SourceTree {
        commit: commit.to_string(),
        origin: SourceOrigin::SealComponent { component: component.to_path_buf(), copy },
        outside_packages,
        metadata_rounds: 1,
    })
}

// ---------------------------------------------------------------------------
// KEY.json
// ---------------------------------------------------------------------------

pub(crate) fn json_str(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json_path(path: &Path) -> String {
    json_str(&path.to_string_lossy())
}

fn json_opt(value: Option<&str>) -> String {
    value.map_or_else(|| "null".to_string(), json_str)
}

fn json_str_list<S: AsRef<str>>(items: &[S]) -> String {
    format!("[{}]", items.iter().map(|s| json_str(s.as_ref())).collect::<Vec<_>>().join(", "))
}

/// Everything KEY.json records.
pub(crate) struct KeyRecord<'a> {
    pub(crate) identity: &'a CompilerIdentity,
    /// sha256 of the installed `lib/<driver_name>`. It differs from a PROVENANCE
    /// `driver_sha256` on every seal measured, because packaging rewrites the
    /// driver after sealing; recording it binds the KEY to the bytes installed.
    pub(crate) installed_driver_sha256: &'a str,
    /// Inherited cargo configuration variables the keyed cargo removed.
    pub(crate) env_scrubbed: &'a [String],
    pub(crate) trustc: &'a Path,
    pub(crate) cargo: &'a Path,
    pub(crate) probe: &'a CompilerProbe,
    pub(crate) sysroot: &'a Path,
    pub(crate) provenance: Option<&'a Path>,
    pub(crate) std: StdMode,
    pub(crate) sources: &'a SourceTree,
    pub(crate) target_rustflags: &'a [String],
    pub(crate) host_rustflags: &'a [String],
    pub(crate) trust_mc_head: Option<&'a str>,
    pub(crate) trust_mc_dirty: Option<bool>,
    pub(crate) backend: Option<&'a Path>,
    pub(crate) wall_seconds: f64,
}

/// The `source` object of KEY.json, indented to sit at the top level.
fn render_source_json(sources: &SourceTree) -> String {
    let outside = sources
        .outside_packages
        .iter()
        .map(|(name, manifest)| {
            format!("{{\"name\": {}, \"manifest\": {}}}", json_str(name), json_str(manifest))
        })
        .collect::<Vec<_>>()
        .join(", ");
    match &sources.origin {
        SourceOrigin::GitArchive { checkout, commit_tree, entries } => {
            let paths = entries
                .iter()
                .map(|e| {
                    format!(
                        "{{\"path\": {}, \"type\": {}, \"oid\": {}}}",
                        json_str(&e.path),
                        json_str(&e.kind),
                        json_str(&e.oid)
                    )
                })
                .collect::<Vec<_>>()
                .join(",\n      ");
            let escapes: Vec<&str> =
                entries.iter().map(|e| e.path.as_str()).filter(|p| *p != "library").collect();
            format!(
                r#"{{
    "kind": "git-archive",
    "checkout": {checkout},
    "commit": {commit},
    "commit_tree": {commit_tree},
    "derivation": "git archive; out-of-library paths from cargo metadata --locked ({rounds} rounds)",
    "out_of_library_paths": {escapes},
    "paths": [
      {paths}
    ],
    "out_of_library_packages": [{outside}]
  }}"#,
                checkout = json_path(checkout),
                commit = json_str(&sources.commit),
                commit_tree = json_str(commit_tree),
                rounds = sources.metadata_rounds,
                escapes = json_str_list(&escapes),
            )
        }
        SourceOrigin::SealComponent { component, copy } => format!(
            r#"{{
    "kind": "seal-trust-src",
    "component": {component},
    "commit": {commit},
    "attestation": "shipped inside the sysroot whose PROVENANCE names this commit; not a git object",
    "content_sha256": {sha256},
    "content_sha256_format": {digest_format},
    "files": {files},
    "bytes": {bytes},
    "derivation": "copy of the seal trust-src component; out-of-library packages from cargo metadata --locked",
    "out_of_library_paths": {paths},
    "out_of_library_packages": [{outside}]
  }}"#,
            component = json_path(component),
            commit = json_str(&sources.commit),
            sha256 = json_str(&copy.sha256),
            digest_format = json_str(COMPONENT_DIGEST_FORMAT),
            files = copy.files,
            bytes = copy.bytes,
            paths = json_str_list(&copy.out_of_library_paths),
        ),
    }
}

pub(crate) fn render_key_json(record: &KeyRecord<'_>) -> String {
    let id = record.identity;
    let source = render_source_json(record.sources);
    let dirty = record.trust_mc_dirty.map_or("null", |d| if d { "true" } else { "false" });
    format!(
        r#"{{
  "schema": {schema},
  "key": {key},
  "key_source": {key_source},
  "driver_sha256": {driver_sha256},
  "installed_driver_sha256": {installed_driver_sha256},
  "driver_name": {driver_name},
  "reported_commit": {reported_commit},
  "driver_bytes": {{"provenance": {bytes_recorded}, "installed": {bytes_installed}}},
  "library_mode": {library_mode},
  "std": {std},
  "build_std": {build_std},
  "compiler": {{
    "trustc": {trustc},
    "cargo": {cargo},
    "version": {version},
    "commit_hash": {commit_hash},
    "host": {host},
    "sysroot": {sysroot},
    "provenance": {provenance},
    "provenance_class": {provenance_class}
  }},
  "source": {source},
  "rustflags": {{
    "target": {target_flags},
    "host": {host_flags}
  }},
  "env_scrubbed": {env_scrubbed},
  "trust_mc": {{
    "head": {head},
    "dirty": {dirty}
  }},
  "backend": {backend},
  "wall_seconds": {wall:.1}
}}
"#,
        schema = json_str(KEY_SCHEMA),
        key = json_str(&id.key),
        key_source = json_str(id.key_source.as_str()),
        driver_sha256 = json_str(&id.driver_sha256),
        installed_driver_sha256 = json_str(record.installed_driver_sha256),
        driver_name = json_str(&id.driver_name),
        reported_commit = json_str(&id.reported_commit),
        bytes_recorded =
            id.driver_bytes_recorded.map_or_else(|| "null".to_string(), |b| b.to_string()),
        bytes_installed =
            id.driver_bytes_installed.map_or_else(|| "null".to_string(), |b| b.to_string()),
        library_mode = json_str(record.std.library_mode()),
        std = json_str(record.std.cli_name()),
        build_std = record.std == StdMode::BuildStd,
        trustc = json_path(record.trustc),
        cargo = json_path(record.cargo),
        version = json_str(&record.probe.version),
        commit_hash = json_opt(record.probe.commit_hash.as_deref()),
        host = json_str(&record.probe.host),
        sysroot = json_path(record.sysroot),
        provenance = record.provenance.map_or_else(|| "null".to_string(), json_path),
        provenance_class = json_opt(id.provenance_class.as_deref()),
        target_flags = json_str_list(record.target_rustflags),
        host_flags = json_str_list(record.host_rustflags),
        env_scrubbed = json_str_list(record.env_scrubbed),
        head = json_opt(record.trust_mc_head),
        backend = record.backend.map_or_else(|| "null".to_string(), json_path),
        wall = record.wall_seconds,
    )
}

// ---------------------------------------------------------------------------
// The subcommand
// ---------------------------------------------------------------------------

/// `target/trust-mc/keyed` in this repository.
pub(crate) fn keyed_root() -> PathBuf {
    trust_mc_repo_root().join("target/trust-mc/keyed")
}

fn trust_mc_git_state() -> (Option<String>, Option<bool>) {
    let root = trust_mc_repo_root();
    let head = git(&root)
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string());
    let dirty = git(&root)
        .args(["status", "--porcelain"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| !o.stdout.is_empty());
    (head, dirty)
}

pub(crate) fn build_keyed(args: &BuildKeyedParser) -> Result<()> {
    let started = Instant::now();
    let trustc = fs::canonicalize(&args.trustc)
        .with_context(|| format!("--trustc {} does not exist", args.trustc.display()))?;
    if !trustc.is_file() {
        bail!("--trustc {} is not a file", trustc.display());
    }
    let probe =
        parse_verbose_version(&run_capture(Command::new(&trustc).arg("-vV"), "trustc -vV")?)?;
    let sysroot = PathBuf::from(
        run_capture(Command::new(&trustc).args(["--print", "sysroot"]), "trustc --print sysroot")?
            .trim(),
    );
    let sysroot = fs::canonicalize(&sysroot)
        .with_context(|| format!("trustc reports a missing sysroot {}", sysroot.display()))?;
    // The KEY names the sysroot trustc reports, while cargo runs the given path as
    // RUSTC. A wrapper or rustup proxy elsewhere could report one sysroot and run
    // another compiler (for example after `current` moves), so the two must agree.
    if trustc.parent() != Some(sysroot.join("bin").as_path()) {
        bail!(
            "--trustc {} is not in its own sysroot's bin directory {}; pass the sealed \
             compiler binary itself, not a wrapper or proxy",
            trustc.display(),
            sysroot.join("bin").display()
        );
    }
    let provenance_path = sysroot.join("PROVENANCE");
    let provenance = match fs::read_to_string(&provenance_path) {
        Ok(text) => Some(text),
        Err(error) if error.kind() == ErrorKind::NotFound => {
            eprintln!(
                "warning: {} has no PROVENANCE; keying by the sha256 of its librustc_driver",
                sysroot.display()
            );
            None
        }
        Err(error) => {
            return Err(error)
                .with_context(|| format!("cannot read {}", provenance_path.display()));
        }
    };
    let identity = derive_identity(&sysroot, probe.commit_hash.as_deref(), provenance.as_deref())?;
    let key_dir = keyed_root().join(&identity.key);
    println!(
        "-- build-keyed KEY={} (from {}) driver={} commit={} trustc={}",
        identity.key,
        identity.key_source.as_str(),
        identity.driver_name,
        identity.reported_commit,
        trustc.display()
    );
    if args.print_key {
        println!("{}", identity.key);
        println!("{}", key_dir.display());
        return Ok(());
    }
    let Some(std_mode) = args.std else {
        bail!("build-keyed needs --std unless --print-key is given");
    };
    let checkout = match (args.trust_checkout.as_deref(), args.trust_src) {
        (Some(_), true) => {
            bail!("--trust-checkout and --trust-src name two library sources; pass one")
        }
        (None, false) => {
            bail!("build-keyed needs --trust-checkout or --trust-src unless --print-key is given")
        }
        (checkout, _) => checkout,
    };

    if probe.host != build_target() {
        bail!(
            "--trustc host {} differs from build-trust-mc's host {}; build-keyed does not \
             cross-compile",
            probe.host,
            build_target()
        );
    }
    let cargo = keyed_targo(&sysroot)?;
    let backend = match &args.backend {
        Some(path) => Some(
            fs::canonicalize(path)
                .with_context(|| format!("--backend {} does not exist", path.display()))?,
        ),
        None => None,
    };
    // PROVENANCE names the build; the installed bytes are what trustc loads. The
    // fallback KEY already is the installed sha256, so it is not hashed twice.
    let installed_driver = sysroot.join("lib").join(&identity.driver_name);
    let installed_driver_sha256 = match identity.key_source {
        KeySource::DriverDylibSha256 => identity.driver_sha256.clone(),
        KeySource::Provenance => sha256_file(&installed_driver)?,
    };
    println!("-- installed driver {} sha256={installed_driver_sha256}", installed_driver.display());
    let inherited_env: Vec<OsString> = std::env::vars_os().map(|(key, _)| key).collect();
    let env_scrubbed = inherited_keyed_env(&inherited_env);

    let key_json_path = key_dir.join(KEY_JSON);
    // The trust-src component is read from the sysroot trustc reports, never from
    // a path the caller names: it is only as good as the seal that ships it.
    let source = match checkout {
        Some(checkout) => {
            LibrarySource::Checkout(fs::canonicalize(checkout).with_context(|| {
                format!("--trust-checkout {} does not exist", checkout.display())
            })?)
        }
        None => LibrarySource::SealComponent(sysroot.join(TRUST_SRC_COMPONENT)),
    };
    let _key_lock = lock_key(&keyed_root(), &identity.key)?;
    claim_key_dir(&key_dir, &identity, std_mode, &source)?;

    let src = key_dir.join("src");
    let sources = match &source {
        LibrarySource::Checkout(checkout) => {
            materialize_sources(&cargo, &trustc, checkout, &identity.reported_commit, &src)?
        }
        LibrarySource::SealComponent(component) => {
            materialize_seal_component(&cargo, &trustc, component, &identity.reported_commit, &src)?
        }
    };
    let src = fs::canonicalize(&src)?;
    println!("-- seal source: {}", sources.describe());

    let target_dir = trust_mc_repo_root().join("target/build-libs/keyed").join(&identity.key);
    let target_rustflags: Vec<String> =
        KEYED_TARGET_RUSTFLAGS.iter().map(|s| s.to_string()).collect();
    let host_rustflags: Vec<String> = KEYED_HOST_RUSTFLAGS.iter().map(|s| s.to_string()).collect();
    let mut toolchain = LibToolchain {
        cargo: cargo.clone().into_os_string(),
        rustc: trustc.clone(),
        target_dir: target_dir.clone(),
        target_rustflags: target_rustflags.clone(),
        host_rustflags: host_rustflags.clone(),
        env: vec![
            ("RUSTC_WRAPPER".to_string(), OsString::new()),
            ("CARGO_BUILD_RUSTC_WRAPPER".to_string(), OsString::new()),
        ],
        env_remove: keyed_env_remove(&inherited_env),
    };

    // no_core: kani_core against the compiler's own core; no std closure.
    let artifacts = build_trust_mc_lib(&toolchain, &NO_CORE_PACKAGES, &NO_CORE_CARGO_ARGS, &[])?;
    copy_artifacts(&artifacts, &key_dir.join("no_core/lib"), &StdLibs::None)?;

    if std_mode == StdMode::BuildStd {
        toolchain.env.push((
            "__CARGO_TESTS_ONLY_SRC_ROOT".to_string(),
            src.join("library").into_os_string(),
        ));
    }
    let prebuilt_std = sysroot.join("lib/rustlib").join(build_target()).join("lib");
    let std_libs = match std_mode {
        StdMode::BuildStd => StdLibs::TargetUnits(&target_dir),
        StdMode::Prebuilt => StdLibs::LinkPrebuilt(&prebuilt_std),
    };
    let (verification_args, playback_args): (Vec<&str>, Vec<&str>) = match std_mode {
        StdMode::BuildStd => (
            vec!["-Z", "build-std=panic_abort,std,test", "--config", "profile.dev.panic=\"abort\""],
            vec![PLAYBACK_FEATURES, "-Z", "build-std=std,test"],
        ),
        StdMode::Prebuilt => (vec![], vec![PLAYBACK_FEATURES]),
    };
    let artifacts =
        build_trust_mc_lib(&toolchain, &VERIFICATION_PACKAGES, &verification_args, &[])?;
    copy_artifacts(&artifacts, &key_dir.join("lib"), &std_libs)?;
    let artifacts = build_trust_mc_lib(&toolchain, &VERIFICATION_PACKAGES, &playback_args, &[])?;
    copy_artifacts(&artifacts, &key_dir.join("playback/lib"), &std_libs)?;

    if let Some(backend) = &backend {
        let dir = key_dir.join("codegen-backends");
        fs::create_dir_all(&dir)?;
        let installed = dir.join(format!("librustc_codegen_trust_mc.{}", lib_extension()));
        fs::copy(backend, &installed)
            .with_context(|| format!("cannot install {}", installed.display()))?;
    }

    let (head, dirty) = trust_mc_git_state();
    let wall_seconds = started.elapsed().as_secs_f64();
    let record = KeyRecord {
        identity: &identity,
        installed_driver_sha256: &installed_driver_sha256,
        env_scrubbed: &env_scrubbed,
        trustc: &trustc,
        cargo: &cargo,
        probe: &probe,
        sysroot: &sysroot,
        provenance: provenance.as_ref().map(|_| provenance_path.as_path()),
        std: std_mode,
        sources: &sources,
        target_rustflags: &target_rustflags,
        host_rustflags: &host_rustflags,
        trust_mc_head: head.as_deref(),
        trust_mc_dirty: dirty,
        backend: backend.as_deref(),
        wall_seconds,
    };
    fs::write(&key_json_path, render_key_json(&record))?;
    println!(
        "-- build-keyed done: {} ({} library, {:.1} s)",
        key_dir.display(),
        std_mode.library_mode(),
        wall_seconds
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// SHA-256 (the PROVENANCE-less fallback key); no new dependency.
// ---------------------------------------------------------------------------

const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

pub(crate) struct Sha256 {
    state: [u32; 8],
    block: [u8; 64],
    filled: usize,
    length: u64,
}

impl Sha256 {
    pub(crate) fn new() -> Self {
        Sha256 {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ],
            block: [0; 64],
            filled: 0,
            length: 0,
        }
    }

    fn compress(state: &mut [u32; 8], block: &[u8; 64]) {
        let mut schedule = [0u32; 64];
        for (word_index, chunk) in block.as_chunks::<4>().0.iter().enumerate() {
            schedule[word_index] = u32::from_be_bytes(*chunk);
        }
        for word_index in 16..64 {
            let s0 = schedule[word_index - 15].rotate_right(7)
                ^ schedule[word_index - 15].rotate_right(18)
                ^ (schedule[word_index - 15] >> 3);
            let s1 = schedule[word_index - 2].rotate_right(17)
                ^ schedule[word_index - 2].rotate_right(19)
                ^ (schedule[word_index - 2] >> 10);
            schedule[word_index] = schedule[word_index - 16]
                .wrapping_add(s0)
                .wrapping_add(schedule[word_index - 7])
                .wrapping_add(s1);
        }
        let [
            mut work_a,
            mut work_b,
            mut work_c,
            mut work_d,
            mut work_e,
            mut work_f,
            mut work_g,
            mut work_h,
        ] = *state;
        for word_index in 0..64 {
            let sum1 = work_e.rotate_right(6) ^ work_e.rotate_right(11) ^ work_e.rotate_right(25);
            let choose = (work_e & work_f) ^ (!work_e & work_g);
            let temporary1 = work_h
                .wrapping_add(sum1)
                .wrapping_add(choose)
                .wrapping_add(SHA256_K[word_index])
                .wrapping_add(schedule[word_index]);
            let sum0 = work_a.rotate_right(2) ^ work_a.rotate_right(13) ^ work_a.rotate_right(22);
            let majority = (work_a & work_b) ^ (work_a & work_c) ^ (work_b & work_c);
            let temporary2 = sum0.wrapping_add(majority);
            work_h = work_g;
            work_g = work_f;
            work_f = work_e;
            work_e = work_d.wrapping_add(temporary1);
            work_d = work_c;
            work_c = work_b;
            work_b = work_a;
            work_a = temporary1.wrapping_add(temporary2);
        }
        for (slot, value) in
            state.iter_mut().zip([work_a, work_b, work_c, work_d, work_e, work_f, work_g, work_h])
        {
            *slot = slot.wrapping_add(value);
        }
    }

    pub(crate) fn update(&mut self, mut data: &[u8]) {
        self.length = self.length.wrapping_add(data.len() as u64);
        while !data.is_empty() {
            let take = (64 - self.filled).min(data.len());
            self.block[self.filled..self.filled + take].copy_from_slice(&data[..take]);
            self.filled += take;
            data = &data[take..];
            if self.filled == 64 {
                Self::compress(&mut self.state, &self.block);
                self.filled = 0;
            }
        }
    }

    pub(crate) fn finish(mut self) -> String {
        let bits = self.length.wrapping_mul(8);
        self.update(&[0x80]);
        while self.filled != 56 {
            self.update(&[0]);
        }
        self.update(&bits.to_be_bytes());
        self.state.iter().map(|word| format!("{word:08x}")).collect()
    }
}

pub(crate) fn sha256_file(path: &Path) -> Result<String> {
    let mut file =
        fs::File::open(path).with_context(|| format!("cannot open {}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut buffer = vec![0u8; 1 << 20];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(hasher.finish())
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;

    const SHA_8571: &str = "948b36c62eacc5d19ae9308d2cdcffe55535a4519f3d4bdb2d4f5ae54a973055";
    const COMMIT_8571: &str = "45dc60873c4fef21649ae277a93cc8cc9cf39191";

    /// A fresh directory under this repo's target dir (never /tmp).
    fn scratch(name: &str) -> PathBuf {
        let dir = trust_mc_repo_root()
            .join("target/tmp/build-trust-mc-tests")
            .join(format!("{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn fake_sysroot(name: &str, drivers: &[(&str, &[u8])], provenance: Option<&str>) -> PathBuf {
        let root = scratch(name);
        fs::create_dir_all(root.join("lib")).unwrap();
        for (file, bytes) in drivers {
            fs::write(root.join("lib").join(file), bytes).unwrap();
        }
        if let Some(text) = provenance {
            fs::write(root.join("PROVENANCE"), text).unwrap();
        }
        root
    }

    fn driver_file(hash: &str) -> String {
        format!("librustc_driver-{hash}.{}", lib_extension())
    }

    fn sha(data: &[u8]) -> String {
        let mut hasher = Sha256::new();
        hasher.update(data);
        hasher.finish()
    }

    #[test]
    fn sha256_matches_published_vectors() {
        assert_eq!(sha(b""), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
        assert_eq!(sha(b"abc"), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
        assert_eq!(
            sha(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
        let million = vec![b'a'; 1_000_000];
        assert_eq!(
            sha(&million),
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
        );
        // Streaming in odd-sized pieces gives the same digest.
        let mut hasher = Sha256::new();
        for piece in million.chunks(777) {
            hasher.update(piece);
        }
        assert_eq!(hasher.finish(), sha(&million));
    }

    #[test]
    fn key_is_driver_prefix_of_full_sha() {
        assert_eq!(key_for(SHA_8571).unwrap(), "driver-948b36c62eacc5d1");
        for bad in [&SHA_8571[..63], &SHA_8571.to_uppercase(), "zz", ""] {
            let error = key_for(bad).unwrap_err().to_string();
            assert!(error.contains("not 64 lowercase hex"), "{error}");
        }
    }

    #[test]
    fn provenance_parse_takes_identity_fields_and_ignores_the_rest() {
        let text = format!(
            "# comment with reported_commit=deadbeef\nprovenance_class=BUILD-STAMPED-CLEAN\n\
             reported_rev=45dc60873\nreported_commit={COMMIT_8571}\n\
             artifact_driver_name={}\nartifact_driver_sha256={SHA_8571}\n\
             artifact_driver_bytes=438173224\nbuild_stamp:head={COMMIT_8571}\n",
            driver_file("98fef360a4a26975")
        );
        let parsed = parse_provenance(&text).unwrap();
        assert_eq!(parsed.reported_commit.as_deref(), Some(COMMIT_8571));
        assert_eq!(parsed.driver_sha256.as_deref(), Some(SHA_8571));
        assert_eq!(parsed.driver_bytes, Some(438_173_224));
        assert_eq!(parsed.class.as_deref(), Some("BUILD-STAMPED-CLEAN"));
        let repeated = format!("reported_commit={COMMIT_8571}\nreported_commit={COMMIT_8571}\n");
        assert!(parse_provenance(&repeated).unwrap_err().to_string().contains("repeats"));
    }

    #[test]
    fn identity_from_provenance_keys_by_recorded_driver_sha() {
        let name = driver_file("98fef360a4a26975");
        let provenance = format!(
            "reported_commit={COMMIT_8571}\nartifact_driver_name={name}\n\
             artifact_driver_sha256={SHA_8571}\nartifact_driver_bytes=5\n"
        );
        let sysroot = fake_sysroot("prov", &[(&name, b"12345")], Some(&provenance));
        let text = fs::read_to_string(sysroot.join("PROVENANCE")).unwrap();
        let identity = derive_identity(&sysroot, Some(COMMIT_8571), Some(&text)).unwrap();
        assert_eq!(identity.key, "driver-948b36c62eacc5d1");
        assert_eq!(identity.key_source, KeySource::Provenance);
        assert_eq!(identity.driver_name, name);
        assert_eq!(identity.reported_commit, COMMIT_8571);
    }

    #[test]
    fn missing_provenance_falls_back_to_driver_sha256_and_verbose_commit() {
        let name = driver_file("0123456789abcdef");
        let sysroot = fake_sysroot("noprov", &[(&name, b"abc")], None);
        let identity = derive_identity(&sysroot, Some(COMMIT_8571), None).unwrap();
        assert_eq!(identity.key_source, KeySource::DriverDylibSha256);
        assert_eq!(
            identity.driver_sha256,
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(identity.key, "driver-ba7816bf8f01cfea");
        assert_eq!(identity.driver_name, name);
        assert_eq!(identity.reported_commit, COMMIT_8571);
    }

    #[test]
    fn missing_provenance_without_a_commit_is_refused() {
        let sysroot = fake_sysroot("nocommit", &[(&driver_file("0123456789abcdef"), b"abc")], None);
        for commit in [None, Some("unknown"), Some("")] {
            let error = derive_identity(&sysroot, commit, None).unwrap_err().to_string();
            assert!(error.contains("cannot name the compiler's commit"), "{error}");
        }
        let short = derive_identity(&sysroot, Some("45dc60873"), None).unwrap_err().to_string();
        assert!(short.contains("not a full 40-hex"), "{short}");
    }

    #[test]
    fn missing_provenance_with_no_or_several_drivers_is_refused() {
        let none = fake_sysroot("nodriver", &[], None);
        let error = derive_identity(&none, Some(COMMIT_8571), None).unwrap_err().to_string();
        assert!(error.contains("no librustc_driver"), "{error}");
        let two = fake_sysroot(
            "twodrivers",
            &[(&driver_file("0123456789abcdef"), b"a"), (&driver_file("fedcba9876543210"), b"b")],
            None,
        );
        let error = derive_identity(&two, Some(COMMIT_8571), None).unwrap_err().to_string();
        assert!(error.contains("ambiguous"), "{error}");
    }

    #[test]
    fn provenance_that_does_not_describe_the_compiler_is_refused() {
        let name = driver_file("98fef360a4a26975");
        let sysroot = fake_sysroot("mismatch", &[(&name, b"12345")], None);
        let other = "25ccaf01f102fe3b4127dabeffbeba7f55516b5a";
        let wrong_commit = format!("reported_commit={other}\nartifact_driver_sha256={SHA_8571}\n");
        let error = derive_identity(&sysroot, Some(COMMIT_8571), Some(&wrong_commit))
            .unwrap_err()
            .to_string();
        assert!(error.contains("disagrees") && error.contains(other), "{error}");

        let absent_driver = format!(
            "reported_commit={COMMIT_8571}\nartifact_driver_sha256={SHA_8571}\n\
             artifact_driver_name={}\n",
            driver_file("e5ab7a82643f630e")
        );
        let error = derive_identity(&sysroot, Some(COMMIT_8571), Some(&absent_driver))
            .unwrap_err()
            .to_string();
        assert!(error.contains("not in"), "{error}");
    }

    #[test]
    fn provenance_without_a_driver_sha_keys_by_the_installed_driver_it_names() {
        let named = driver_file("98fef360a4a26975");
        let other = driver_file("e5ab7a82643f630e");
        // Two drivers installed: without a name the fallback would be ambiguous, so
        // the named one must be the one hashed.
        let sysroot =
            fake_sysroot("provnosha", &[(&named, b"abc"), (&other, b"other driver")], None);
        let provenance = format!(
            "provenance_class=BUILD-STAMPED-CLEAN\nreported_commit={COMMIT_8571}\n\
             artifact_driver_name={named}\n"
        );
        let identity = derive_identity(&sysroot, Some(COMMIT_8571), Some(&provenance)).unwrap();
        assert_eq!(identity.key_source, KeySource::DriverDylibSha256);
        assert_eq!(identity.driver_sha256, sha(b"abc"));
        assert_eq!(identity.key, "driver-ba7816bf8f01cfea");
        assert_eq!(identity.driver_name, named);
        assert_eq!(identity.provenance_class.as_deref(), Some("BUILD-STAMPED-CLEAN"));

        // A named driver that is not installed is refused, not replaced by another.
        let absent = format!(
            "reported_commit={COMMIT_8571}\nartifact_driver_name={}\n",
            driver_file("0123456789abcdef")
        );
        let error =
            derive_identity(&sysroot, Some(COMMIT_8571), Some(&absent)).unwrap_err().to_string();
        assert!(error.contains("not in") && error.contains("0123456789abcdef"), "{error}");
        let lone = fake_sysroot("provnosha-lone", &[(&other, b"other driver")], None);
        let error =
            derive_identity(&lone, Some(COMMIT_8571), Some(&absent)).unwrap_err().to_string();
        assert!(error.contains("not in"), "{error}");

        // Without a name either, the single installed driver is hashed.
        let unnamed = format!("reported_commit={COMMIT_8571}\n");
        let identity = derive_identity(&lone, None, Some(&unnamed)).unwrap();
        assert_eq!(identity.key_source, KeySource::DriverDylibSha256);
        assert_eq!(identity.driver_sha256, sha(b"other driver"));
    }

    #[test]
    fn keyed_cargo_removes_inherited_profile_unstable_and_incremental_settings() {
        let inherited = [
            "CARGO_PROFILE_DEV_OVERFLOW_CHECKS",
            "CARGO_PROFILE_RELEASE_CODEGEN_UNITS",
            "CARGO_UNSTABLE_BUILD_STD",
            "CARGO_INCREMENTAL",
            "RUSTFLAGS",
            "CARGO_HOME",
            "CARGO_NET_OFFLINE",
            "PATH",
            "CARGO_PROFILE_DEV_OVERFLOW_CHECKS",
        ];
        let remove = keyed_env_remove(inherited);
        for key in KEYED_ENV_REMOVE {
            assert_eq!(remove.iter().filter(|k| *k == key).count(), 1, "{key}: {remove:?}");
        }
        for key in [
            "CARGO_PROFILE_DEV_OVERFLOW_CHECKS",
            "CARGO_PROFILE_RELEASE_CODEGEN_UNITS",
            "CARGO_UNSTABLE_BUILD_STD",
            "CARGO_INCREMENTAL",
        ] {
            assert!(remove.iter().any(|k| k == key), "{key}: {remove:?}");
        }
        for key in ["CARGO_HOME", "CARGO_NET_OFFLINE", "PATH"] {
            assert!(!remove.iter().any(|k| k == key), "{key}: {remove:?}");
        }
        assert_eq!(
            inherited_keyed_env(inherited),
            [
                "CARGO_INCREMENTAL",
                "CARGO_PROFILE_DEV_OVERFLOW_CHECKS",
                "CARGO_PROFILE_RELEASE_CODEGEN_UNITS",
                "CARGO_UNSTABLE_BUILD_STD",
                "RUSTFLAGS",
            ]
        );
        // With nothing inherited, only the fixed names are removed.
        assert_eq!(keyed_env_remove(std::iter::empty::<&str>()), KEYED_ENV_REMOVE);
    }

    #[test]
    fn installed_driver_size_differing_from_provenance_is_recorded_not_rekeyed() {
        // Build 8571 ships a 370030832-byte driver whose PROVENANCE records
        // 438173224 bytes; the KEY must still be the PROVENANCE sha.
        let name = driver_file("98fef360a4a26975");
        let sysroot = fake_sysroot("size", &[(&name, b"12345")], None);
        let provenance = format!(
            "reported_commit={COMMIT_8571}\nartifact_driver_sha256={SHA_8571}\n\
             artifact_driver_name={name}\nartifact_driver_bytes=438173224\n"
        );
        let identity = derive_identity(&sysroot, Some(COMMIT_8571), Some(&provenance)).unwrap();
        assert_eq!(identity.key, "driver-948b36c62eacc5d1");
        assert_eq!(identity.key_source, KeySource::Provenance);
        assert_eq!(identity.driver_bytes_recorded, Some(438_173_224));
        assert_eq!(identity.driver_bytes_installed, Some(5));
    }

    #[test]
    fn provenance_commit_without_verbose_commit_is_used() {
        let name = driver_file("98fef360a4a26975");
        let provenance =
            format!("reported_commit={COMMIT_8571}\nartifact_driver_sha256={SHA_8571}\n");
        let sysroot = fake_sysroot("provcommit", &[(&name, b"x")], None);
        let identity = derive_identity(&sysroot, None, Some(&provenance)).unwrap();
        assert_eq!(identity.reported_commit, COMMIT_8571);
        assert_eq!(identity.driver_name, name);
    }

    #[test]
    fn verbose_version_parses_trustc_output() {
        let text = "rustc 1.99.0-dev (45dc60873 2026-09-10) (trustc 0.1.0)\nbinary: trustc\n\
                    commit-hash: 45dc60873c4fef21649ae277a93cc8cc9cf39191\n\
                    host: aarch64-apple-darwin\nrelease: 1.99.0-dev\n";
        let probe = parse_verbose_version(text).unwrap();
        assert_eq!(probe.version, "rustc 1.99.0-dev (45dc60873 2026-09-10) (trustc 0.1.0)");
        assert_eq!(probe.commit_hash.as_deref(), Some(COMMIT_8571));
        assert_eq!(probe.host, "aarch64-apple-darwin");
        assert!(parse_verbose_version("").is_err());
    }

    fn identity() -> CompilerIdentity {
        CompilerIdentity {
            key: key_for(SHA_8571).unwrap(),
            key_source: KeySource::Provenance,
            driver_sha256: SHA_8571.to_string(),
            driver_name: driver_file("98fef360a4a26975"),
            reported_commit: COMMIT_8571.to_string(),
            provenance_class: None,
            driver_bytes_recorded: Some(438_173_224),
            driver_bytes_installed: Some(370_030_832),
        }
    }

    #[test]
    fn existing_key_for_another_compiler_is_refused() {
        let dir = Path::new("target/trust-mc/keyed/driver-948b36c62eacc5d1");
        assert!(check_existing_key(None, &identity(), StdMode::BuildStd, dir).is_ok());
        let same = format!(
            "{{\"driver_sha256\": \"{SHA_8571}\",\n \"reported_commit\" : \"{COMMIT_8571}\", \
             \"library_mode\": \"parity\"}}"
        );
        assert!(check_existing_key(Some(&same), &identity(), StdMode::BuildStd, dir).is_ok());
        // Parity and smoke share the KEY path: switching grade in place is refused.
        let error = check_existing_key(Some(&same), &identity(), StdMode::Prebuilt, dir)
            .unwrap_err()
            .to_string();
        assert!(error.contains("KEY mode mismatch") && error.contains("parity"), "{error}");
        let no_mode = same.replace("library_mode", "other_field");
        let error = check_existing_key(Some(&no_mode), &identity(), StdMode::BuildStd, dir)
            .unwrap_err()
            .to_string();
        assert!(error.contains("KEY mode mismatch") && error.contains("<missing>"), "{error}");
        let other_sha = SHA_8571.replacen("5", "6", 1);
        let other = format!(
            "{{\"driver_sha256\": \"{other_sha}\", \"reported_commit\": \"{COMMIT_8571}\"}}"
        );
        let error = check_existing_key(Some(&other), &identity(), StdMode::BuildStd, dir)
            .unwrap_err()
            .to_string();
        assert!(error.contains("KEY mismatch") && error.contains(&other_sha), "{error}");
        let error = check_existing_key(Some("{}"), &identity(), StdMode::BuildStd, dir)
            .unwrap_err()
            .to_string();
        assert!(error.contains("<missing>"), "{error}");
    }

    #[test]
    fn rendered_key_json_reads_back_its_identity() {
        let identity = identity();
        let probe = parse_verbose_version(
            "rustc 1.99.0-dev (45dc60873 2026-09-10) (trustc 0.1.0)\nhost: aarch64-apple-darwin\n",
        )
        .unwrap();
        let sources = SourceTree {
            commit: COMMIT_8571.to_string(),
            origin: SourceOrigin::GitArchive {
                checkout: PathBuf::from("$HOME/trust"),
                commit_tree: "f".repeat(40),
                entries: vec![
                    SourceEntry {
                        path: "library".into(),
                        kind: "tree".into(),
                        oid: "a".repeat(40),
                    },
                    SourceEntry {
                        path: "crates/Cargo.toml".into(),
                        kind: "blob".into(),
                        oid: "b".repeat(40),
                    },
                ],
            },
            outside_packages: vec![(
                "trust-bignum".into(),
                "crates/trust-bignum/Cargo.toml".into(),
            )],
            metadata_rounds: 4,
        };
        let flags = vec!["-Ztrust-verify=off".to_string()];
        let installed = "e7a812eba61a0469".repeat(4);
        let scrubbed = vec!["CARGO_PROFILE_DEV_OPT_LEVEL".to_string()];
        let record = KeyRecord {
            identity: &identity,
            installed_driver_sha256: &installed,
            env_scrubbed: &scrubbed,
            trustc: Path::new("/Application Support/trust/bin/trustc"),
            cargo: Path::new("/Application Support/trust/bin/cargo"),
            probe: &probe,
            sysroot: Path::new("/Application Support/trust"),
            provenance: None,
            std: StdMode::BuildStd,
            sources: &sources,
            target_rustflags: &flags,
            host_rustflags: &flags,
            trust_mc_head: Some("c1c889ad0"),
            trust_mc_dirty: Some(false),
            backend: None,
            wall_seconds: 12.34,
        };
        let json = render_key_json(&record);
        assert_eq!(json_string_field(&json, "driver_sha256").as_deref(), Some(SHA_8571));
        assert_eq!(
            json_string_field(&json, "installed_driver_sha256").as_deref(),
            Some(installed.as_str())
        );
        assert!(json.contains("\"env_scrubbed\": [\"CARGO_PROFILE_DEV_OPT_LEVEL\"]"), "{json}");
        assert_eq!(json_string_field(&json, "reported_commit").as_deref(), Some(COMMIT_8571));
        assert_eq!(json_string_field(&json, "library_mode").as_deref(), Some("parity"));
        assert_eq!(json_string_field(&json, "key").as_deref(), Some("driver-948b36c62eacc5d1"));
        assert!(json.contains("\"out_of_library_paths\": [\"crates/Cargo.toml\"]"), "{json}");
        assert!(
            json.contains(
                "\"driver_bytes\": {\"provenance\": 438173224, \"installed\": 370030832}"
            ),
            "{json}"
        );
        assert!(
            check_existing_key(Some(&json), &identity, StdMode::BuildStd, Path::new("k")).is_ok()
        );
        assert!(json.contains("\"kind\": \"git-archive\""), "{json}");

        // A KEY built from the seal's trust-src component records the component and
        // its content digest instead of a checkout and git objects.
        let seal = SourceTree {
            commit: COMMIT_8571.to_string(),
            origin: SourceOrigin::SealComponent {
                component: PathBuf::from("/Application Support/trust/lib/rustlib/src/rust"),
                copy: ComponentCopy {
                    sha256: "c".repeat(64),
                    files: 3578,
                    bytes: 80_000_000,
                    out_of_library_paths: vec![
                        "crates/trust-bignum".into(),
                        "crates/trust-memchr".into(),
                    ],
                },
            },
            outside_packages: vec![(
                "trust-bignum".into(),
                "crates/trust-bignum/Cargo.toml".into(),
            )],
            metadata_rounds: 1,
        };
        let json = render_key_json(&KeyRecord { sources: &seal, ..record });
        assert!(json.contains("\"kind\": \"seal-trust-src\""), "{json}");
        assert_eq!(
            json_string_field(&json, "content_sha256").as_deref(),
            Some("c".repeat(64).as_str())
        );
        assert!(
            json.contains(
                "\"out_of_library_paths\": [\"crates/trust-bignum\", \"crates/trust-memchr\"]"
            ),
            "{json}"
        );
        assert!(!json.contains("\"checkout\""), "{json}");
        assert!(
            check_existing_key(Some(&json), &identity, StdMode::BuildStd, Path::new("k")).is_ok()
        );
    }

    #[test]
    fn json_strings_are_escaped() {
        assert_eq!(json_str("a\"b\\c\nd\u{1}"), "\"a\\\"b\\\\c\\nd\\u0001\"");
    }

    #[test]
    fn keyed_build_requires_the_held_seals_targo() {
        let sysroot = scratch("keyed-targo");
        fs::create_dir_all(sysroot.join("bin")).unwrap();
        fs::write(sysroot.join("bin/cargo"), "compatibility persona").unwrap();
        let error = keyed_targo(&sysroot).unwrap_err().to_string();
        assert!(error.contains("no bin/targo"), "{error}");
        let expected = sysroot.join("bin/targo");
        fs::write(&expected, "Trust frontend").unwrap();
        assert_eq!(keyed_targo(&sysroot).unwrap(), expected);
    }

    #[test]
    fn metadata_failures_map_to_the_missing_trust_path() {
        let missing = "error: failed to load manifest for workspace member `/k/src/library/sysroot`\n\
            Caused by:\n  failed to load manifest for dependency `trust-bignum`\n\n\
            Caused by:\n  failed to read `/k/src/crates/trust-bignum/Cargo.toml`\n\n\
            Caused by:\n  No such file or directory (os error 2)\n";
        assert_eq!(
            diagnose_metadata_failure(missing),
            Some(MissingSource::Manifest(PathBuf::from("/k/src/crates/trust-bignum/Cargo.toml")))
        );
        let root = "Caused by:\n  failed to parse manifest at `/k/src/crates/trust-bignum/Cargo.toml`\n\n\
            Caused by:\n  error inheriting `edition` from workspace root manifest's \
            `workspace.package.edition`\n\nCaused by:\n  failed to find a workspace root\n";
        assert_eq!(
            diagnose_metadata_failure(root),
            Some(MissingSource::WorkspaceRootFor(PathBuf::from(
                "/k/src/crates/trust-bignum/Cargo.toml"
            )))
        );
        let patch = "error: patch location `/k with spaces/src/crates/trust-memchr` does not contain packages matching `memchr`\n\
            help: check `memchr` patch definition for `https://github.com/rust-lang/crates.io-index`";
        assert_eq!(
            diagnose_metadata_failure(patch),
            Some(MissingSource::Manifest(PathBuf::from(
                "/k with spaces/src/crates/trust-memchr/Cargo.toml"
            )))
        );
        for unrelated in [
            "error: patch location `/k/src/crates/trust-memchr` conflicts with another package",
            "error: patch location `/k/src/crates/trust-memchr` does not contain packages matching `memchr` extra text",
            "error: patch location `` does not contain packages matching `memchr`",
            "error: patch location `/k/src/crates/trust-memchr` does not contain packages matching ``",
        ] {
            assert_eq!(diagnose_metadata_failure(unrelated), None, "{unrelated}");
        }
        let lock = "error: the lock file /k/src/library/Cargo.lock needs to be updated but --locked was passed";
        assert_eq!(diagnose_metadata_failure(lock), None);
        let not_manifest = "failed to read `/k/src/library/std/src/lib.rs`";
        assert_eq!(diagnose_metadata_failure(not_manifest), None);
    }

    #[test]
    fn workspace_root_candidates_are_nearest_first() {
        assert_eq!(
            ancestor_manifests(Path::new("crates/trust-bignum/Cargo.toml")),
            vec![PathBuf::from("crates/Cargo.toml"), PathBuf::from("Cargo.toml")]
        );
        assert!(ancestor_manifests(Path::new("Cargo.toml")).is_empty());
        assert!(inherits_from_workspace("[package]\nedition.workspace = true\n"));
        assert!(inherits_from_workspace("[lints]\nworkspace = true\n"));
        assert!(!inherits_from_workspace("# workspace = true\nedition = \"2024\"\n"));
        assert!(has_workspace_table("[package]\n[workspace]\nmembers = []\n"));
        assert!(!has_workspace_table("[workspace.package]\n"));
    }

    fn git_repo(name: &str) -> (PathBuf, String) {
        let repo = scratch(name);
        let run = |args: &[&str]| {
            let status = Command::new("git")
                .arg("-C")
                .arg(&repo)
                .args(["-c", "user.name=t", "-c", "user.email=t@example.invalid"])
                .args(args)
                .stdout(Stdio::null())
                .status()
                .unwrap();
            assert!(status.success(), "git {args:?}");
        };
        run(&["init", "-q"]);
        fs::create_dir_all(repo.join("library")).unwrap();
        fs::write(repo.join("library/Cargo.toml"), "[workspace]\n").unwrap();
        run(&["add", "."]);
        run(&["commit", "-q", "-m", "fixture"]);
        let head = run_capture(git(&repo).args(["rev-parse", "HEAD"]), "git rev-parse").unwrap();
        (repo, head.trim().to_string())
    }

    #[cfg(unix)]
    fn persistent_patch_error_cargo(name: &str, directory: &Path) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let cargo = scratch(name).join("fake-targo");
        let message = format!(
            "error: patch location `{}` does not contain packages matching `memchr`",
            directory.display()
        );
        let quoted = message.replace('\'', "'\\''");
        fs::write(&cargo, format!("#!/bin/sh\nprintf '%s\\n' '{quoted}' >&2\nexit 1\n")).unwrap();
        fs::set_permissions(&cargo, fs::Permissions::from_mode(0o755)).unwrap();
        cargo
    }

    #[cfg(unix)]
    #[test]
    fn patch_package_mismatch_after_extraction_is_refused() {
        let (repo, _) = git_repo("patch-mismatch-repo");
        let patch = repo.join("crates/trust-memchr");
        fs::create_dir_all(&patch).unwrap();
        fs::write(
            patch.join("Cargo.toml"),
            "[package]\nname = \"not-memchr\"\nversion = \"1.0.0\"\n",
        )
        .unwrap();
        assert!(git(&repo).args(["add", "."]).status().unwrap().success());
        assert!(
            git(&repo)
                .args([
                    "-c",
                    "user.name=t",
                    "-c",
                    "user.email=t@example.invalid",
                    "commit",
                    "-q",
                    "-m",
                    "wrong package"
                ])
                .status()
                .unwrap()
                .success()
        );
        let head = run_capture(git(&repo).args(["rev-parse", "HEAD"]), "git rev-parse").unwrap();
        let src = fs::canonicalize(scratch("patch-mismatch-src")).unwrap();
        let cargo =
            persistent_patch_error_cargo("patch-mismatch-tool", &src.join("crates/trust-memchr"));
        let error =
            materialize_sources(&cargo, Path::new("/unused/trustc"), &repo, head.trim(), &src)
                .unwrap_err()
                .to_string();
        assert!(
            error.contains("still needs `crates/trust-memchr` after it was extracted"),
            "{error}"
        );
        assert!(src.join("crates/trust-memchr/Cargo.toml").is_file());
    }

    #[cfg(unix)]
    #[test]
    fn patch_source_outside_archive_is_refused() {
        let (repo, head) = git_repo("patch-outside-repo");
        let src = fs::canonicalize(scratch("patch-outside-src")).unwrap();
        let outside = fs::canonicalize(scratch("patch-outside-dependency")).unwrap();
        let cargo = persistent_patch_error_cargo("patch-outside-tool", &outside);
        let error = materialize_sources(&cargo, Path::new("/unused/trustc"), &repo, &head, &src)
            .unwrap_err()
            .to_string();
        assert!(error.contains("outside the extracted seal source"), "{error}");
        assert!(!outside.join("Cargo.toml").exists());
    }

    #[test]
    fn missing_commit_is_refused() {
        let (repo, head) = git_repo("commit");
        assert!(require_commit(&repo, &head).is_ok());
        let absent = "0123456789012345678901234567890123456789";
        let error = require_commit(&repo, absent).unwrap_err().to_string();
        assert!(error.contains("does not contain commit") && error.contains(absent), "{error}");
        assert_eq!(git_object(&repo, &head, "library").unwrap().unwrap().0, "tree");
        assert!(git_object(&repo, &head, "crates/trust-bignum").unwrap().is_none());
    }

    #[test]
    fn a_checkout_that_is_not_a_git_top_level_is_refused() {
        // A plain directory inside this repository resolves to trust-mc's own
        // top level, which must not be mistaken for the trust checkout.
        let plain = scratch("plain");
        let error = require_commit(&plain, COMMIT_8571).unwrap_err().to_string();
        assert!(error.contains("not the top level of a git checkout"), "{error}");
        let missing = plain.join("absent");
        assert!(require_commit(&missing, COMMIT_8571).is_err());
    }

    #[test]
    fn sources_are_extracted_by_git_archive_at_the_commit() {
        let (repo, head) = git_repo("archive");
        let dest = scratch("archive-dest");
        extract_path(&repo, &head, "library", &dest).unwrap();
        assert!(dest.join("library/Cargo.toml").is_file());
        assert!(extract_path(&repo, &head, "crates", &dest).is_err());
    }

    #[test]
    fn claiming_a_key_refuses_before_changing_it_and_clears_what_a_rebuild_replaces() {
        let (repo, head) = git_repo("claim");
        let source = LibrarySource::Checkout(repo.clone());
        let mut id = identity();
        id.reported_commit = head.clone();
        let key_dir = scratch("claim-key");
        let key_json = key_dir.join(KEY_JSON);
        let recorded = format!(
            "{{\"driver_sha256\": \"{SHA_8571}\", \"reported_commit\": \"{head}\", \
             \"library_mode\": \"parity\"}}"
        );
        fs::write(&key_json, &recorded).unwrap();
        fs::create_dir_all(key_dir.join("codegen-backends")).unwrap();
        fs::write(key_dir.join("codegen-backends/stale.dylib"), b"old").unwrap();

        // A checkout without the commit, and a grade switch, leave the KEY untouched.
        // Another repository whose only commit differs (a byte-identical fixture
        // committed in the same second would share the commit id).
        let other_repo = scratch("claim-other");
        let other_git = |args: &[&str]| {
            let status = Command::new("git")
                .arg("-C")
                .arg(&other_repo)
                .args(["-c", "user.name=t", "-c", "user.email=t@example.invalid"])
                .args(args)
                .stdout(Stdio::null())
                .status()
                .unwrap();
            assert!(status.success(), "git {args:?}");
        };
        other_git(&["init", "-q"]);
        fs::write(other_repo.join("other.txt"), b"not the fixture").unwrap();
        other_git(&["add", "."]);
        other_git(&["commit", "-q", "-m", "other"]);
        let other = LibrarySource::Checkout(other_repo.clone());
        assert!(claim_key_dir(&key_dir, &id, StdMode::BuildStd, &other).is_err());
        assert!(claim_key_dir(&key_dir, &id, StdMode::Prebuilt, &source).is_err());
        // So does a sysroot that ships no trust-src component.
        let no_component = LibrarySource::SealComponent(scratch("claim-no-component").join("rust"));
        assert!(claim_key_dir(&key_dir, &id, StdMode::BuildStd, &no_component).is_err());
        assert_eq!(fs::read_to_string(&key_json).unwrap(), recorded);
        assert!(key_dir.join("codegen-backends/stale.dylib").is_file());

        // A rebuild by the same compiler in the same grade drops KEY.json and the
        // previously installed backend before anything is rebuilt.
        claim_key_dir(&key_dir, &id, StdMode::BuildStd, &source).unwrap();
        assert!(!key_json.exists());
        assert!(!key_dir.join("codegen-backends").exists());
        // A fresh KEY directory is created.
        let fresh = scratch("claim-fresh").join("driver-948b36c62eacc5d1");
        claim_key_dir(&fresh, &id, StdMode::BuildStd, &source).unwrap();
        assert!(fresh.is_dir());
    }

    /// A trust-src component shaped like the one seal 8589 ships.
    fn fake_component(name: &str) -> PathBuf {
        let root = scratch(name);
        fs::create_dir_all(root.join("library/std/src")).unwrap();
        fs::write(root.join("library/Cargo.toml"), "[workspace]\n").unwrap();
        fs::write(root.join("library/Cargo.lock"), "version = 4\n").unwrap();
        fs::write(root.join("library/std/src/lib.rs"), "// std\n").unwrap();
        fs::create_dir_all(root.join("crates/trust-memchr")).unwrap();
        fs::write(root.join("crates/trust-memchr/Cargo.toml"), "[package]\n").unwrap();
        fs::create_dir_all(root.join("src/llvm-project/libunwind")).unwrap();
        root
    }

    #[test]
    fn a_seal_component_is_copied_with_a_content_digest() {
        let component = fake_component("component");
        let first = scratch("component-copy-1");
        let copy = copy_component(&component, &first).unwrap();
        assert_eq!(fs::read_to_string(first.join("library/std/src/lib.rs")).unwrap(), "// std\n");
        assert!(first.join("src/llvm-project/libunwind").is_dir());
        assert_eq!((copy.files, copy.bytes), (4, 41));
        assert_eq!(copy.out_of_library_paths, vec!["crates/trust-memchr", "src/llvm-project"]);
        assert!(require_seal_component(&component).is_ok());
        // The digest is a function of the content alone: a second copy agrees, while
        // a changed byte or an added empty directory changes it.
        let second = copy_component(&component, &scratch("component-copy-2")).unwrap();
        assert_eq!(second.sha256, copy.sha256);
        fs::write(component.join("library/std/src/lib.rs"), "// Std\n").unwrap();
        let changed = copy_component(&component, &scratch("component-copy-3")).unwrap();
        assert_ne!(changed.sha256, copy.sha256);
        fs::create_dir_all(component.join("crates/empty")).unwrap();
        let grown = copy_component(&component, &scratch("component-copy-4")).unwrap();
        assert_ne!(grown.sha256, changed.sha256);
    }

    #[cfg(unix)]
    #[test]
    fn a_seal_component_with_a_symbolic_link_or_no_library_is_refused() {
        let component = fake_component("component-link");
        std::os::unix::fs::symlink("/etc", component.join("crates/escape")).unwrap();
        let error =
            copy_component(&component, &scratch("component-link-copy")).unwrap_err().to_string();
        assert!(error.contains("neither a file nor a directory"), "{error}");
        let linked = scratch("component-linked").join("rust");
        std::os::unix::fs::symlink(fake_component("component-target"), &linked).unwrap();
        let error = require_seal_component(&linked).unwrap_err().to_string();
        assert!(error.contains("not a directory"), "{error}");
        let empty = scratch("component-empty");
        let error = require_seal_component(&empty).unwrap_err().to_string();
        assert!(error.contains("library/Cargo.toml"), "{error}");
        let error = require_seal_component(&empty.join("lib/rustlib/src/rust")).unwrap_err();
        assert!(error.to_string().contains("ships no trust-src component"), "{error}");
    }

    #[test]
    fn a_key_is_built_by_one_build_keyed_at_a_time() {
        let root = scratch("lock");
        let held = lock_key(&root, "driver-948b36c62eacc5d1").unwrap();
        let error = lock_key(&root, "driver-948b36c62eacc5d1").unwrap_err().to_string();
        assert!(error.contains("another build-keyed holds"), "{error}");
        assert!(lock_key(&root, "driver-0000000000000000").is_ok());
        // Unlock explicitly: a flock belongs to the open file description, and a
        // sibling test forking git at this moment briefly shares it, so a plain
        // drop does not reliably release the lock before the next assertion.
        held.unlock().unwrap();
        assert!(lock_key(&root, "driver-948b36c62eacc5d1").is_ok());
    }
}
