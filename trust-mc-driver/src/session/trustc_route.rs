// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The Trustc compiler route (T1-D1, T1-D6, T1-D9).
//!
//! On this route trust-mc-driver compiles with canonical `trustc` and
//! `-Zcodegen-backend=<canonical trust-mc backend dylib> -Ztrust-verify=off`,
//! where the DevCli route runs `trust-mc-compiler --kani-compiler`. Nothing
//! after the compile changes: kani-metadata.json, the per-harness `.smt2` and
//! `.vc.json` files and `run_ay` are read exactly as before.
//!
//! Before the first compile, [`preflight`] establishes that the three artifacts
//! that must come from one build really do, and refuses with a typed
//! [`TrustcRouteError`] (so no verdict is ever printed) when:
//!
//! - the canonical trustc is not `<sysroot>/bin/<file>` of the sysroot it
//!   reports, so a shim or proxy could compile with a build other than the one
//!   that answered the identity probes (a seal promotion re-points one mid-run);
//! - `KEY.json`'s `driver_sha256` differs from the trustc sysroot's
//!   `artifact_driver_sha256` (PROVENANCE, or the sha256 of the sysroot's
//!   `librustc_driver-*` when PROVENANCE does not record it), or the KEY
//!   directory is not named `driver-<that sha256[:16]>`;
//! - the backend dylib, or any directory above it, is world-writable (P14), or
//!   so is `KEY.json`, a directory above it, or anything in the KEY's library
//!   folders (`lib`, `no_core/lib`, `playback/lib`), whose rlibs decide what is
//!   verified;
//! - the backend dylib does not link exactly the sysroot's `librustc_driver-*`.
//!
//! After every compile that loaded the backend, the driver re-hashes the dylib
//! and refuses with [`TrustcRouteError::BackendChanged`] when its bytes differ
//! from the preflight's, and with [`TrustcRouteError::KeyLibraryChanged`] when
//! an entry of a KEY library folder was added, removed, replaced or written
//! ([`TrustcIdentity::recheck_backend`]): trustc dlopens
//! the path per compile, so a replacement after the preflight would otherwise be
//! loaded under a marker naming the old sha256.
//!
//! Concrete playback builds a real test executable and never loads the backend,
//! so it runs only the trustc, PROVENANCE and KEY checks ([`preflight_key`]) and
//! its marker says `backend=unused`.
//!
//! The trustc child also runs without any `TRUST_MC_*` or `AY_*` variable
//! ([`scrub_engine_env`]). Because the engine reads some of those as semantic
//! knobs, the route refuses outright while any of [`ENGINE_ENV_KNOBS`] is set
//! ([`refuse_engine_env_knobs`]) rather than silently compiling without it. A
//! cargo `[env]` table sets variables on every rustc cargo runs, after those
//! edits, so before any cargo compile the route reads the effective table with
//! the seal's own cargo and refuses any `TRUST_MC_*` / `AY_*` key there
//! ([`probe_cargo_env_table`]); the trustc-hosted backend refuses a set knob in
//! its own environment as well, so no channel reaches the engine silently.
//!
//! Ambient `RUSTFLAGS` is forwarded to every compile (compiletest's
//! `compile-flags` headers arrive that way), so the route refuses any token of
//! it that reaches an option the route sets itself: `-Cllvm-args` (the engine's
//! argument channel, where `--no-unwinding-checks` would silently turn a
//! reachable failure into SUCCESSFUL), `-Zcodegen-backend`, `-Ztrust-verify`,
//! `-Zno-codegen`, or an `@argfile` rustc would expand
//! ([`refuse_route_owned_rustflags`]).
//!
//! See `docs/trust-lane-trustc-route.md`.

use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_mc_metadata::engine_args::encode_token;

/// Harness posture on the Trustc route (T1-D6): verification off for the unit.
pub(crate) const TRUST_VERIFY_OFF: &str = "-Ztrust-verify=off";
/// Prefix of the backend selection flag; the value is the canonical dylib path.
pub(crate) const CODEGEN_BACKEND_FLAG: &str = "-Zcodegen-backend=";
/// The KEY identity file (S4).
pub(crate) const KEY_JSON_FILE: &str = "KEY.json";
/// The seal identity file at the root of a Trust sysroot.
pub(crate) const PROVENANCE_FILE: &str = "PROVENANCE";
/// KEY directory names are `driver-<driver sha256[:16]>` (T1-D9).
pub(crate) const KEY_PREFIX: &str = "driver-";
const KEY_SHA_PREFIX_LEN: usize = 16;
const SHA256_HEX_LEN: usize = 64;

/// The KEY library folders whose contents the route compiles against.
pub(crate) const KEY_LIBRARY_DIRS: &[&str] = &["lib", "no_core/lib", "playback/lib"];

/// rustc options this route sets itself, spelled as rustc matches them once `_`
/// is read as `-` (rustc treats the two as the same in `-C`/`-Z` option names).
/// A `RUSTFLAGS` token that mentions one of them is refused: `llvm-args` carries
/// the engine's arguments (the `pct1` groups), `codegen-backend` selects the
/// engine, and `trust-verify` and `no-codegen` set the harness posture (T1-D6,
/// and `--no-codegen` is refused on this route).
pub(crate) const ROUTE_OWNED_RUSTC_OPTIONS: &[&str] =
    &["llvm-args", "codegen-backend", "trust-verify", "no-codegen"];

/// Environment prefixes the trustc child never sees.
const SCRUBBED_ENV_PREFIXES: &[&str] = &["TRUST_MC_", "AY_"];

/// Environment variables that put a program between cargo and rustc: cargo runs
/// `<wrapper> <rustc> <args>` for every unit, and the workspace wrapper for
/// workspace members, nested inside the other one. Measured on seal 8571's cargo:
/// `build.rustc-wrapper` and `build.rustc-workspace-wrapper` in a cargo
/// configuration file are honored unless the matching variable is set; set to the
/// empty string, a variable disables its wrapper; and emptying `RUSTC_WRAPPER`
/// alone leaves a configured workspace wrapper running. A wrapper sees and can
/// rewrite every argument, the engine's `-Cllvm-args` and `-Zcodegen-backend`
/// included.
pub(crate) const RUSTC_WRAPPER_ENV_VARS: &[&str] = &[
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
];

/// Rustflags of host units (build scripts, proc-macros and their dependencies) on
/// the Trustc cargo route: Kani's `kani_host` cfg and verification off (T1-D6).
/// They never select the engine backend or carry engine arguments. Those are
/// target rustflags (`CARGO_ENCODED_RUSTFLAGS`), which cargo does not apply to
/// host units once `--target` is given (measured on seal 8571's cargo, with
/// `target-applies-to-host` unset, true and false).
pub(crate) const TRUSTC_HOST_RUSTFLAGS: &[&str] = &["--cfg=kani_host", TRUST_VERIFY_OFF];

/// Variables the trust-mc engine reads from its own environment that change
/// what it generates: the shared list in `trust_mc_metadata::engine_args`, which
/// the trustc-hosted backend refuses on too, so no channel the driver cannot see
/// (a cargo `[env]` table, a wrapper) can set one silently.
/// `compiler_route_engine_env_knobs_cover_the_engine_sources` keeps the list
/// honest against the `"TRUST_MC_*"` literals in `trust-mc-compiler/src`.
/// `loop_two_lane` sets one of them (`TRUST_MC_COMPOUND_DECREASES`) on its
/// retry lane child, so scrubbing it silently would change what the lane
/// proves. (Read by that test and the docs; the
/// refusal itself goes through `set_engine_env_knobs`.)
#[allow(unused_imports)]
pub(crate) use trust_mc_metadata::engine_args::ENGINE_ENV_KNOBS;

const REFUSED: &str = "compiler route trustc refused";

/// Why the Trustc route will not compile. Every variant is a refusal before any
/// compile runs, so no verdict follows it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TrustcRouteError {
    /// A required route input was given neither as a flag nor in the environment.
    MissingInput { what: &'static str, flag: Option<&'static str>, env: &'static str },
    /// A route input path does not exist or cannot be read.
    BadPath { what: &'static str, path: PathBuf, detail: String },
    /// `--no-codegen` asks for a compile whose backend never runs.
    NoCodegen,
    /// Engine knobs are set that the trustc child would silently lose.
    EngineEnvKnobs { vars: Vec<String> },
    /// Ambient `RUSTFLAGS` tokens reach an option the route sets itself, or name
    /// an argfile rustc would expand.
    RouteOwnedRustflags { tokens: Vec<String> },
    /// `trustc --print sysroot` or `trustc -vV` failed.
    SysrootProbe { trustc: PathBuf, detail: String },
    /// The trustc path is not a file in `<sysroot>/bin` of the sysroot it reports.
    TrustcOutsideSysroot { trustc: PathBuf, sysroot: PathBuf },
    /// The sysroot PROVENANCE file is unreadable or inconsistent.
    Provenance { path: PathBuf, detail: String },
    /// The sysroot does not ship exactly one `librustc_driver-*`.
    SysrootDriver { lib_dir: PathBuf, found: Vec<String> },
    /// PROVENANCE names a different driver than the one installed.
    ProvenanceDriverName { provenance: PathBuf, recorded: String, installed: String },
    /// PROVENANCE `reported_commit` is not the commit `trustc -vV` reports.
    ProvenanceCommit { provenance: PathBuf, recorded: String, trustc: PathBuf, reported: String },
    /// KEY.json is missing, malformed, or carries no usable `driver_sha256`.
    KeyJson { path: PathBuf, detail: String },
    /// The Kani library under this KEY was built by a different driver.
    KeyDriverSha {
        key_json: PathBuf,
        key_driver_sha256: String,
        sysroot_source: PathBuf,
        sysroot_driver_sha256: String,
    },
    /// The KEY directory name does not match its driver.
    KeyName { key_dir: PathBuf, key: String, expected: String },
    /// The backend dylib, or a directory above it, is world-writable.
    WorldWritable { dylib: PathBuf, path: PathBuf, mode: u32 },
    /// KEY.json, a directory above it, or an entry of a KEY library folder is
    /// world-writable.
    KeyWorldWritable { key_dir: PathBuf, path: PathBuf, mode: u32 },
    /// The backend dylib's bytes changed between the preflight and a compile's end.
    BackendChanged { dylib: PathBuf, preflight_sha256: String, current_sha256: String },
    /// KEY.json was removed, rewritten or became unreadable after the preflight
    /// (`build-keyed` removes it before it rebuilds the KEY's libraries).
    KeyChanged { key_json: PathBuf, detail: String },
    /// An entry of a KEY library folder was added, removed, replaced or written
    /// after the preflight.
    KeyLibraryChanged { key_dir: PathBuf, entry: String, detail: String },
    /// The backend dylib's load commands could not be read.
    LinkedLibraries { dylib: PathBuf, detail: String },
    /// The backend dylib links a different `librustc_driver-*` (or none).
    BackendDriver { dylib: PathBuf, linked: Vec<String>, sysroot_driver: String },
    /// The environment names a rustc wrapper for the cargo route (`NAME=value` each).
    RustcWrapper { vars: Vec<String> },
    /// The trustc sysroot has no usable `bin/targo` of its own.
    SealCargo { sysroot: PathBuf, detail: String },
    /// The effective cargo `[env]` table sets a `TRUST_MC_*` / `AY_*` variable on
    /// every rustc cargo runs (`NAME=value` each).
    CargoEnvTable { vars: Vec<String> },
    /// `cargo config get env` could not establish the effective `[env]` table.
    CargoEnvProbe { cargo: PathBuf, detail: String },
    /// A `CARGO_HOST_*` variable (cargo's `[host]` tables, which reach build
    /// scripts and proc-macros) carries a token that reaches a route-owned option.
    HostRustflags { vars: Vec<String> },
}

impl fmt::Display for TrustcRouteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingInput { what, flag: Some(flag), env } => {
                write!(f, "{REFUSED}: no {what}; pass {flag} or set {env}")
            }
            Self::MissingInput { what, flag: None, env } => {
                write!(f, "{REFUSED}: no {what}; set {env}")
            }
            Self::BadPath { what, path, detail } => {
                write!(f, "{REFUSED}: {what} {}: {detail}", path.display())
            }
            Self::NoCodegen => write!(
                f,
                "{REFUSED}: --no-codegen cannot run on this route: under -Z no-codegen the \
                 backend's codegen_crate never runs, so neither the crate-item checks nor VC \
                 generation would run"
            ),
            Self::EngineEnvKnobs { vars } => write!(
                f,
                "{REFUSED}: engine environment knob(s) {} are set, but the trustc child runs \
                 without TRUST_MC_* and AY_*, so the engine would silently compile without \
                 them; unset them or use --compiler-route dev-cli",
                vars.join(", ")
            ),
            Self::RouteOwnedRustflags { tokens } => write!(
                f,
                "{REFUSED}: RUSTFLAGS token(s) {tokens:?} reach rustc options this route sets \
                 itself (-Cllvm-args carries the engine's arguments, -Zcodegen-backend selects \
                 the engine, -Ztrust-verify and -Zno-codegen set the harness posture) or name an \
                 argfile rustc would expand; RUSTFLAGS reaches every compile, so an engine flag \
                 there (such as --no-unwinding-checks) would silently change what the harnesses \
                 prove; pass engine options as trust-mc-driver flags and remove these tokens \
                 from RUSTFLAGS"
            ),
            Self::SysrootProbe { trustc, detail } => {
                write!(f, "{REFUSED}: cannot identify trustc {}: {detail}", trustc.display())
            }
            Self::TrustcOutsideSysroot { trustc, sysroot } => write!(
                f,
                "{REFUSED}: trustc {} is not in {}/bin, the sysroot it reports; a shim, proxy \
                 or copy can answer the identity probes as one build and compile as another \
                 (a seal promotion re-points a shim mid-run), so pass {}/bin/trustc itself",
                trustc.display(),
                sysroot.display(),
                sysroot.display()
            ),
            Self::Provenance { path, detail } => {
                write!(f, "{REFUSED}: sysroot provenance {}: {detail}", path.display())
            }
            Self::SysrootDriver { lib_dir, found } => write!(
                f,
                "{REFUSED}: trustc sysroot {} must ship exactly one librustc_driver, found {:?}",
                lib_dir.display(),
                found
            ),
            Self::ProvenanceDriverName { provenance, recorded, installed } => write!(
                f,
                "{REFUSED}: {} records artifact_driver_name={recorded} but the sysroot ships \
                 {installed}",
                provenance.display()
            ),
            Self::ProvenanceCommit { provenance, recorded, trustc, reported } => write!(
                f,
                "{REFUSED}: {} records reported_commit={recorded} but {} -vV reports \
                 commit-hash {reported}; that PROVENANCE does not describe this trustc",
                provenance.display(),
                trustc.display()
            ),
            Self::KeyJson { path, detail } => {
                write!(f, "{REFUSED}: KEY identity {}: {detail}", path.display())
            }
            Self::KeyDriverSha {
                key_json,
                key_driver_sha256,
                sysroot_source,
                sysroot_driver_sha256,
            } => write!(
                f,
                "{REFUSED}: KEY driver_sha256 {key_driver_sha256} ({}) differs from the trustc \
                 sysroot driver sha256 {sysroot_driver_sha256} ({}); the Kani library under \
                 this KEY was built by a different librustc_driver",
                key_json.display(),
                sysroot_source.display()
            ),
            Self::KeyName { key_dir, key, expected } => write!(
                f,
                "{REFUSED}: KEY directory {} is named {key:?} but its driver makes it {expected}",
                key_dir.display()
            ),
            Self::WorldWritable { dylib, path, mode } => write!(
                f,
                "{REFUSED}: backend dylib {} sits under world-writable {} (mode {mode:o}); any \
                 local user could replace the code trustc would load",
                dylib.display(),
                path.display()
            ),
            Self::KeyWorldWritable { key_dir, path, mode } => write!(
                f,
                "{REFUSED}: KEY directory {} has world-writable {} (mode {mode:o}); any local \
                 user could replace the Kani library the compile links",
                key_dir.display(),
                path.display()
            ),
            Self::KeyChanged { key_json, detail } => write!(
                f,
                "{REFUSED}: KEY {} changed during the session: {detail}; the libraries that \
                 compile used are not the ones the preflight accepted",
                key_json.display()
            ),
            Self::KeyLibraryChanged { key_dir, entry, detail } => write!(
                f,
                "{REFUSED}: KEY {} library entry {entry} changed during the session: {detail}; \
                 the libraries that compile used are not the ones the preflight accepted, so \
                 no verdict is reported",
                key_dir.display()
            ),
            Self::BackendChanged { dylib, preflight_sha256, current_sha256 } => write!(
                f,
                "{REFUSED}: backend dylib {} changed during the session: sha256 {preflight_sha256} \
                 at preflight, {current_sha256} after the compile; the compile may have loaded \
                 code the route marker does not name, so no verdict is reported",
                dylib.display()
            ),
            Self::LinkedLibraries { dylib, detail } => write!(
                f,
                "{REFUSED}: cannot read the libraries backend dylib {} links: {detail}",
                dylib.display()
            ),
            Self::BackendDriver { dylib, linked, sysroot_driver } => write!(
                f,
                "{REFUSED}: backend dylib {} links {:?} but the trustc sysroot ships \
                 {sysroot_driver}; a backend loads only under the driver it was built against",
                dylib.display(),
                linked
            ),
            Self::RustcWrapper { vars } => write!(
                f,
                "{REFUSED}: rustc wrapper variable(s) {} are set; cargo would run that program in \
                 place of trustc for every unit, where it can rewrite the engine's -Cllvm-args \
                 and the backend a unit loads, so the cargo route never runs through a wrapper; \
                 unset them (the route itself disables wrappers named in cargo configuration \
                 files)",
                vars.join(", ")
            ),
            Self::SealCargo { sysroot, detail } => write!(
                f,
                "{REFUSED}: trustc sysroot {} has no Targo of its own: {detail}; the cargo route \
                 runs <sysroot>/bin/targo, never a frontend from another toolchain",
                sysroot.display()
            ),
            Self::CargoEnvTable { vars } => write!(
                f,
                "{REFUSED}: the cargo [env] table in effect here sets {} on every rustc cargo \
                 runs; the trustc child must see no TRUST_MC_* or AY_* variable (the engine \
                 reads some as generation knobs), and a table entry bypasses the driver's own \
                 environment edits; remove it from every .cargo/config.toml cargo reads for \
                 this package (cargo config get env shows the effective table)",
                vars.join(", ")
            ),
            Self::CargoEnvProbe { cargo, detail } => write!(
                f,
                "{REFUSED}: cannot read the effective cargo [env] table with {} config get \
                 env: {detail}; without it the route cannot show that no TRUST_MC_* or AY_* \
                 variable reaches the trustc child",
                cargo.display()
            ),
            Self::HostRustflags { vars } => write!(
                f,
                "{REFUSED}: host rustflags variable(s) {} carry a token that reaches an option \
                 this route sets itself (-Cllvm-args, -Zcodegen-backend, -Ztrust-verify, \
                 -Zno-codegen) or name an argfile; cargo's [host] tables reach build scripts \
                 and proc-macros, which must never load the engine or carry engine arguments; \
                 unset them",
                vars.join(", ")
            ),
        }
    }
}

impl std::error::Error for TrustcRouteError {}

/// The backend dylib a Trustc compile loads, and its sha256 at preflight.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BackendIdentity {
    pub(crate) path: PathBuf,
    pub(crate) sha256: String,
}

/// What the preflight established about one Trustc compile.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TrustcIdentity {
    pub(crate) trustc: PathBuf,
    pub(crate) sysroot: PathBuf,
    pub(crate) commit: String,
    pub(crate) driver_name: String,
    pub(crate) driver_sha256: String,
    /// The backend the compile loads; `None` for concrete playback, which loads none.
    pub(crate) backend: Option<BackendIdentity>,
    pub(crate) key_dir: PathBuf,
    pub(crate) key: String,
    /// The KEY library folders as the preflight accepted them.
    pub(crate) key_libraries: KeyLibraryFingerprint,
    /// The KEY's content identity ([`key_content_sha256`]): sha256 over the bytes
    /// of `KEY.json` and every entry of `key_libraries`, part of the target-dir
    /// namespace so artifacts compiled against one KEY are never fresh under
    /// another built at the same path.
    pub(crate) key_sha256: String,
}

/// The metadata of every entry under a KEY's library folders ([`KEY_LIBRARY_DIRS`]),
/// keyed by its path relative to the KEY: kind, size, device, inode, and the
/// modification and status-change times (`symlink:` entries add their target and
/// the target's metadata, and a linked directory is walked).
///
/// Hashing the rlibs' bytes after every compile would cost hundreds of megabytes
/// per cargo target. The status-change time is the cheap equivalent: any write,
/// rename-over, clone-over, `chmod` or restored modification time moves it, and
/// only the kernel sets it. What this cannot see is a write and a restoring write
/// inside one clock tick of the filesystem, which needs a deliberate owner.
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct KeyLibraryFingerprint(BTreeMap<String, String>);

impl fmt::Debug for KeyLibraryFingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "KeyLibraryFingerprint({} entries)", self.0.len())
    }
}

impl KeyLibraryFingerprint {
    /// Every entry as `<path>\0<stamp>\n`, in path order: what
    /// [`key_content_sha256`] hashes.
    fn canonical_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        for (name, stamp) in &self.0 {
            bytes.extend_from_slice(name.as_bytes());
            bytes.push(0);
            bytes.extend_from_slice(stamp.as_bytes());
            bytes.push(b'\n');
        }
        bytes
    }

    /// The first entry (in path order) that differs between `self` and `now`, with
    /// what happened to it.
    fn first_difference(&self, now: &Self) -> Option<(String, String)> {
        let mut names: Vec<&String> = self.0.keys().chain(now.0.keys()).collect();
        names.sort();
        names.dedup();
        names.into_iter().find_map(|name| match (self.0.get(name), now.0.get(name)) {
            (Some(before), Some(after)) if before == after => None,
            (Some(before), Some(after)) => {
                Some((name.clone(), format!("was [{before}], is now [{after}]")))
            }
            (Some(before), None) => Some((name.clone(), format!("removed (was [{before}])"))),
            (None, Some(after)) => Some((name.clone(), format!("added ([{after}])"))),
            (None, None) => None,
        })
    }
}

/// One entry's stamp: everything a replacement or a write changes.
#[cfg(unix)]
fn metadata_stamp(metadata: &fs::Metadata) -> String {
    use std::os::unix::fs::MetadataExt;
    let kind = if metadata.is_dir() {
        "dir"
    } else if metadata.file_type().is_symlink() {
        "symlink"
    } else {
        "file"
    };
    if metadata.is_dir() {
        // A directory's own times move whenever an entry is added or removed, and
        // those entries are recorded themselves.
        return format!("{kind} dev={} ino={}", metadata.dev(), metadata.ino());
    }
    format!(
        "{kind} len={} dev={} ino={} mtime={}.{:09} ctime={}.{:09}",
        metadata.len(),
        metadata.dev(),
        metadata.ino(),
        metadata.mtime(),
        metadata.mtime_nsec(),
        metadata.ctime(),
        metadata.ctime_nsec()
    )
}

/// Non-unix hosts: size and modification time only.
#[cfg(not(unix))]
fn metadata_stamp(metadata: &fs::Metadata) -> String {
    let kind = if metadata.is_dir() { "dir" } else { "file" };
    if metadata.is_dir() {
        return kind.to_string();
    }
    format!("{kind} len={} modified={:?}", metadata.len(), metadata.modified().ok())
}

/// Fingerprint the KEY's library folders (see [`KeyLibraryFingerprint`]). A folder
/// that does not exist is recorded as absent, so creating it later is a change.
pub(crate) fn key_library_fingerprint(
    key_dir: &Path,
) -> Result<KeyLibraryFingerprint, TrustcRouteError> {
    let bad = |path: &Path, error: std::io::Error| TrustcRouteError::BadPath {
        what: "KEY library entry",
        path: path.to_path_buf(),
        detail: error.to_string(),
    };
    let mut entries = BTreeMap::new();
    let mut visited_dirs = std::collections::BTreeSet::new();
    for subdir in KEY_LIBRARY_DIRS {
        let root = key_dir.join(subdir);
        match fs::symlink_metadata(&root) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                entries.insert((*subdir).to_string(), "absent".to_string());
                continue;
            }
            Err(error) => return Err(bad(&root, error)),
            Ok(_) => {}
        }
        let mut stack = vec![(root, (*subdir).to_string())];
        while let Some((path, name)) = stack.pop() {
            let own = fs::symlink_metadata(&path).map_err(|error| bad(&path, error))?;
            let mut stamp = metadata_stamp(&own);
            let followed = if own.file_type().is_symlink() {
                let target = fs::read_link(&path).map_err(|error| bad(&path, error))?;
                let target_metadata = fs::metadata(&path).map_err(|error| bad(&path, error))?;
                stamp.push_str(&format!(
                    " -> {} [{}]",
                    target.display(),
                    metadata_stamp(&target_metadata)
                ));
                target_metadata
            } else {
                own
            };
            entries.insert(name.clone(), stamp);
            if followed.is_dir() {
                // A linked directory can lead back up; walk each real directory once.
                let canonical = fs::canonicalize(&path).map_err(|error| bad(&path, error))?;
                if !visited_dirs.insert(canonical) {
                    continue;
                }
                for entry in fs::read_dir(&path).map_err(|error| bad(&path, error))? {
                    let entry = entry.map_err(|error| bad(&path, error))?;
                    let child = format!("{name}/{}", entry.file_name().to_string_lossy());
                    stack.push((entry.path(), child));
                }
            }
        }
    }
    Ok(KeyLibraryFingerprint(entries))
}

/// The KEY's content identity: sha256 over `KEY.json`'s bytes (length-prefixed)
/// followed by the library fingerprint's entries.
///
/// Cargo fingerprints the `--sysroot <KEY>` path and `rustc -vV`, not the rlibs
/// under it. A KEY rebuilt at the same `driver-<sha16>` path (`build-keyed` after
/// a library change, or a smoke and a parity library that share the path) would
/// otherwise leave the previous library's `.rlib`, `kani-metadata.json` and
/// `.vc.json` files fresh, and a verdict computed against a library that no
/// longer exists would be attested under the current KEY (review finding, T1
/// S7). The fingerprint's stamps (size, inode, modification and status-change
/// times) move on every rebuild, rename-over, clone-over or in-place write, so
/// the namespace moves with them.
pub(crate) fn key_content_sha256(key_json: &[u8], libraries: &KeyLibraryFingerprint) -> String {
    let mut bytes = Vec::with_capacity(key_json.len() + 64);
    bytes.extend_from_slice(b"trust-mc-key-content/1\n");
    bytes.extend_from_slice(key_json.len().to_string().as_bytes());
    bytes.push(b'\n');
    bytes.extend_from_slice(key_json);
    bytes.push(b'\n');
    bytes.extend_from_slice(&libraries.canonical_bytes());
    trust_mc_core::evidence::EvidenceHash::sha256_bytes(&bytes).value
}

impl TrustcIdentity {
    /// The first 12 characters of the trustc commit.
    pub(crate) fn commit12(&self) -> &str {
        self.commit.get(..12).unwrap_or(&self.commit)
    }

    /// Cargo target-dir namespace:
    /// `kani-trustc-<commit12>-<backend sha256[:12]>-<KEY content sha256[:12]>`.
    ///
    /// Fingerprints never mix with DevCli's `kani` builds, and they survive neither
    /// a backend rebuild nor a KEY rebuild: cargo fingerprints the
    /// `-Zcodegen-backend=<path>` and `--sysroot <path>` flags and `rustc -vV`, not
    /// the dylib's or the rlibs' bytes, so an engine or a library rebuilt at the
    /// same path under the same trustc would otherwise reuse the `.rlib`,
    /// `kani-metadata.json` and `.vc.json` files the previous one wrote
    /// ([`key_content_sha256`]).
    pub(crate) fn target_namespace(&self) -> String {
        let backend12 = self
            .backend
            .as_ref()
            .map_or("unused", |backend| backend.sha256.get(..12).unwrap_or(&backend.sha256));
        let key12 = self.key_sha256.get(..12).unwrap_or(&self.key_sha256);
        format!("kani-trustc-{}-{backend12}-{key12}", self.commit12())
    }

    /// Refuse when the KEY or the backend dylib changed since the preflight: KEY.json
    /// must still name the preflight's driver sha256 (`build-keyed` removes it before
    /// rebuilding the libraries), every entry of the KEY library folders must carry the
    /// metadata the preflight recorded ([`KeyLibraryFingerprint`]), and the dylib's
    /// bytes must equal those the preflight hashed. A compile that loads no backend
    /// re-checks only the KEY.
    pub(crate) fn recheck_backend(&self) -> Result<(), TrustcRouteError> {
        let key_json = self.key_dir.join(KEY_JSON_FILE);
        match read_key_driver_sha256(&key_json) {
            Ok(sha256) if sha256 == self.driver_sha256 => {}
            Ok(sha256) => {
                return Err(TrustcRouteError::KeyChanged {
                    key_json,
                    detail: format!(
                        "driver_sha256 is now {sha256}, the preflight accepted {}",
                        self.driver_sha256
                    ),
                });
            }
            Err(error) => {
                return Err(TrustcRouteError::KeyChanged { key_json, detail: error.to_string() });
            }
        }
        let key_library_changed = |entry: String, detail: String| {
            TrustcRouteError::KeyLibraryChanged { key_dir: self.key_dir.clone(), entry, detail }
        };
        let libraries = match key_library_fingerprint(&self.key_dir) {
            Ok(libraries) => libraries,
            // An entry that vanished mid-walk, or became unreadable, is a change too.
            Err(TrustcRouteError::BadPath { path, detail, .. }) => {
                let entry = path
                    .strip_prefix(&self.key_dir)
                    .map_or_else(|_| path.display().to_string(), |p| p.display().to_string());
                return Err(key_library_changed(entry, format!("unreadable: {detail}")));
            }
            Err(error) => return Err(error),
        };
        if let Some((entry, detail)) = self.key_libraries.first_difference(&libraries) {
            return Err(key_library_changed(entry, detail));
        }
        let Some(backend) = &self.backend else { return Ok(()) };
        let current_sha256 = sha256_file(&backend.path, "backend dylib")?;
        if current_sha256 == backend.sha256 {
            Ok(())
        } else {
            Err(TrustcRouteError::BackendChanged {
                dylib: backend.path.clone(),
                preflight_sha256: backend.sha256.clone(),
                current_sha256,
            })
        }
    }

    /// The stdout marker printed once per compile. Values are `pct1`-escaped
    /// (and `]` as `%5D`) so a path with spaces stays one field. A compile that
    /// loads no backend (concrete playback) says `backend=unused` rather than
    /// naming a dylib it never ran.
    pub(crate) fn marker(&self) -> String {
        let backend = match &self.backend {
            Some(backend) => format!("backend_sha256={}", marker_value(&backend.sha256)),
            None => "backend=unused".to_string(),
        };
        format!(
            "[AY:COMPILER_ROUTE route=trustc trustc={} commit={} driver={} {backend} key={}]",
            marker_value(&self.trustc.to_string_lossy()),
            marker_value(self.commit12()),
            marker_value(&self.driver_name),
            marker_value(&self.key),
        )
    }
}

impl TrustcIdentity {
    /// The seal's own Trust frontend, `<sysroot>/bin/targo` ([`seal_cargo_in`]).
    pub(crate) fn seal_cargo(&self) -> Result<PathBuf, TrustcRouteError> {
        seal_cargo_in(&self.sysroot)
    }
}

/// `<sysroot>/bin/targo`, which must be a regular file. A symbolic link is refused:
/// it can lead to a frontend that moves with another toolchain (atpkg's shims and
/// rustup's proxies are links). A missing Trust frontend never falls back to the
/// compatibility Cargo persona, PATH, or the frozen stock oracle.
pub(crate) fn seal_cargo_in(sysroot: &Path) -> Result<PathBuf, TrustcRouteError> {
    let cargo = sysroot.join("bin").join(format!("targo{}", std::env::consts::EXE_SUFFIX));
    let refuse =
        |detail: String| TrustcRouteError::SealCargo { sysroot: sysroot.to_path_buf(), detail };
    let metadata = fs::symlink_metadata(&cargo)
        .map_err(|error| refuse(format!("{}: {error}", cargo.display())))?;
    if metadata.file_type().is_file() {
        Ok(cargo)
    } else {
        Err(refuse(format!("{} is not a regular file", cargo.display())))
    }
}

/// Refuse while the environment names a rustc wrapper ([`RUSTC_WRAPPER_ENV_VARS`])
/// with a non-empty value. An empty value is how cargo is told to run no wrapper.
pub(crate) fn refuse_rustc_wrappers<I, K, V>(env: I) -> Result<(), TrustcRouteError>
where
    I: IntoIterator<Item = (K, V)>,
    K: AsRef<OsStr>,
    V: AsRef<OsStr>,
{
    let mut vars: Vec<String> = env
        .into_iter()
        .filter(|(key, value)| {
            !value.as_ref().is_empty()
                && key.as_ref().to_str().is_some_and(|key| RUSTC_WRAPPER_ENV_VARS.contains(&key))
        })
        .map(|(key, value)| {
            format!("{}={}", key.as_ref().to_string_lossy(), value.as_ref().to_string_lossy())
        })
        .collect();
    vars.sort();
    vars.dedup();
    if vars.is_empty() { Ok(()) } else { Err(TrustcRouteError::RustcWrapper { vars }) }
}

/// The refusals of a verification cargo process that read only the driver's
/// environment, all before the identity preflight probes anything: a rustc wrapper
/// ([`refuse_rustc_wrappers`]), then the single-file route's own refusals, a set
/// engine knob ([`refuse_engine_env_knobs`]) and a `RUSTFLAGS` token that reaches a
/// route-owned option ([`refuse_route_owned_rustflags`]), then a `CARGO_HOST_*`
/// variable carrying such a token ([`refuse_host_rustflags`]). A cargo unit
/// forwards `RUSTFLAGS` to every target unit through `CARGO_ENCODED_RUSTFLAGS`, so
/// an engine flag there would change what the package's harnesses prove exactly as
/// it would for a standalone file. The effective cargo `[env]` table is a cargo
/// process away and is refused separately ([`probe_cargo_env_table`]).
pub(crate) fn refuse_cargo_route_env(env: &[(OsString, OsString)]) -> Result<(), TrustcRouteError> {
    refuse_rustc_wrappers(env.iter().map(|(key, value)| (key, value)))?;
    refuse_engine_env_knobs(env.iter().map(|(key, _)| key))?;
    let rustflags = env
        .iter()
        .rev()
        .find(|(key, _)| key.as_os_str() == OsStr::new("RUSTFLAGS"))
        .map(|(_, value)| value.to_string_lossy().into_owned());
    refuse_route_owned_rustflags(rustflags.as_deref())?;
    refuse_host_rustflags(env.iter().map(|(key, value)| (key, value)))
}

/// Prefix of the environment form of cargo's `[host]` and `[host.<triple>]`
/// tables (`CARGO_HOST_RUSTFLAGS`, `CARGO_HOST_<TRIPLE>_RUSTFLAGS`, ...), which
/// cargo prepends to the route's host posture for build scripts and proc-macros
/// (measured on seal 8589's cargo).
pub(crate) const CARGO_HOST_ENV_PREFIX: &str = "CARGO_HOST_";

/// Refuse while a `CARGO_HOST_*` variable carries a token that reaches a
/// route-owned option ([`is_route_owned_rustflags_token`]), or names an argfile.
/// The dangerous payloads fail closed on their own (the backend, with or without
/// engine arguments, kills cargo's target-information probe), but a refusal
/// before any probe names the cause instead of a cargo error. Other host flags
/// from the environment (a `--cfg`, a lint) are forwarded to host units.
pub(crate) fn refuse_host_rustflags<I, K, V>(env: I) -> Result<(), TrustcRouteError>
where
    I: IntoIterator<Item = (K, V)>,
    K: AsRef<OsStr>,
    V: AsRef<OsStr>,
{
    let mut vars: Vec<String> = env
        .into_iter()
        .filter(|(key, _)| {
            key.as_ref().to_str().is_some_and(|key| key.starts_with(CARGO_HOST_ENV_PREFIX))
        })
        .filter(|(_, value)| {
            let value = value.as_ref().to_string_lossy();
            crate::call_single_file::rustflags_tokens(&value)
                .into_iter()
                .any(is_route_owned_rustflags_token)
        })
        .map(|(key, value)| {
            format!("{}={}", key.as_ref().to_string_lossy(), value.as_ref().to_string_lossy())
        })
        .collect();
    vars.sort();
    vars.dedup();
    if vars.is_empty() { Ok(()) } else { Err(TrustcRouteError::HostRustflags { vars }) }
}

/// The arguments of the `[env]` table probe: `cargo -Zunstable-options config get
/// env --format json-value` prints the effective table (every configuration file
/// cargo reads from the working directory up, and `CARGO_HOME`) as one JSON
/// object, and exits 101 with `config value \`env\` is not set` when no file
/// defines one.
pub(crate) const CARGO_ENV_TABLE_PROBE_ARGS: &[&str] =
    &["-Zunstable-options", "config", "get", "env", "--format", "json-value"];

/// Refuse while the effective cargo `[env]` table (as `config get env
/// --format json-value` prints it) sets any `TRUST_MC_*` or `AY_*` variable. A
/// table entry is applied to every rustc cargo runs after the launcher's own
/// environment edits, so it is the one channel through which a scrubbed variable
/// (an engine knob among them) reaches the trustc child.
pub(crate) fn refuse_cargo_env_table_json(json: &str) -> Result<(), TrustcRouteError> {
    let value: serde_json::Value =
        serde_json::from_str(json).map_err(|error| TrustcRouteError::CargoEnvProbe {
            cargo: PathBuf::from("cargo"),
            detail: format!("the env table is not JSON: {error}"),
        })?;
    let Some(table) = value.as_object() else {
        return Err(TrustcRouteError::CargoEnvProbe {
            cargo: PathBuf::from("cargo"),
            detail: format!("the env table is not a JSON object: {value}"),
        });
    };
    let mut vars: Vec<String> = table
        .iter()
        .filter(|(key, _)| is_scrubbed_env_key(OsStr::new(key)))
        .map(|(key, value)| {
            // `"NAME": "value"` or `"NAME": {"value": "...", "force": true, ...}`.
            let rendered = match value {
                serde_json::Value::String(text) => text.clone(),
                serde_json::Value::Object(fields) => fields
                    .get("value")
                    .and_then(serde_json::Value::as_str)
                    .map_or_else(|| value.to_string(), str::to_string),
                other => other.to_string(),
            };
            format!("{key}={rendered}")
        })
        .collect();
    vars.sort();
    vars.dedup();
    if vars.is_empty() { Ok(()) } else { Err(TrustcRouteError::CargoEnvTable { vars }) }
}

/// Run `cargo` (a command already carrying the route's cargo environment and
/// working directory) as the `[env]` table probe and judge its output
/// ([`refuse_cargo_env_table_json`]). Any failure other than "no table" refuses:
/// the route cannot show what the child would see.
pub(crate) fn probe_cargo_env_table(mut cargo: Command) -> Result<(), TrustcRouteError> {
    let program = PathBuf::from(cargo.get_program());
    let refuse =
        |detail: String| TrustcRouteError::CargoEnvProbe { cargo: program.clone(), detail };
    cargo.args(CARGO_ENV_TABLE_PROBE_ARGS);
    cargo.stdin(std::process::Stdio::null());
    let output = cargo.output().map_err(|error| refuse(format!("cannot run it: {error}")))?;
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() {
        if stderr.contains("config value `env` is not set") {
            return Ok(());
        }
        return Err(refuse(format!("exited with {}: {}", output.status, stderr.trim())));
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    refuse_cargo_env_table_json(stdout.trim()).map_err(|error| match error {
        TrustcRouteError::CargoEnvProbe { detail, .. } => refuse(detail),
        other => other,
    })
}

/// The environment of a cargo whose `RUSTC` is `trustc`, as edits: `Some(value)`
/// sets a variable and `None` removes it. `RUSTC` names trustc; every
/// [`RUSTC_WRAPPER_ENV_VARS`] variable is set empty, which also disables a wrapper
/// named in any cargo configuration file; `RUSTUP_TOOLCHAIN` is removed, so no
/// rustup proxy a unit reaches follows the driver's build toolchain; and every
/// inherited `TRUST_MC_*` / `AY_*` variable is removed, as for the trustc child.
pub(crate) fn trustc_cargo_env<I>(
    trustc: &Path,
    parent_keys: I,
) -> Vec<(OsString, Option<OsString>)>
where
    I: IntoIterator<Item = OsString>,
{
    let mut edits = vec![(OsString::from("RUSTC"), Some(trustc.as_os_str().to_os_string()))];
    edits.extend(
        RUSTC_WRAPPER_ENV_VARS.iter().map(|var| (OsString::from(*var), Some(OsString::new()))),
    );
    edits.push((OsString::from("RUSTUP_TOOLCHAIN"), None));
    edits.extend(
        parent_keys.into_iter().filter(|key| is_scrubbed_env_key(key)).map(|key| (key, None)),
    );
    edits
}

/// Whether a Targo subprocess compiles code or only queries project context.
///
/// Trust requires an explicit lane on compilation commands, while query commands
/// (`metadata`, `pkgid`, `locate-project`, `config get`) reject `--unverified`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CargoInvocation {
    Build,
    Query,
}

/// A Targo command on the Trustc route, given the driver's environment: refuse a
/// rustc wrapper there ([`refuse_rustc_wrappers`]), then the held seal's regular
/// Trust frontend ([`seal_cargo_in`]) with [`trustc_cargo_env`] applied.
pub(crate) fn trustc_cargo_command<I>(
    identity: &TrustcIdentity,
    env: I,
    invocation: CargoInvocation,
) -> Result<Command, TrustcRouteError>
where
    I: IntoIterator<Item = (OsString, OsString)>,
{
    let env: Vec<(OsString, OsString)> = env.into_iter().collect();
    refuse_rustc_wrappers(env.iter().map(|(key, value)| (key, value)))?;
    let mut cmd = Command::new(identity.seal_cargo()?);
    if invocation == CargoInvocation::Build {
        cmd.arg("--unverified");
    }
    apply_env_edits(
        &mut cmd,
        trustc_cargo_env(&identity.trustc, env.into_iter().map(|(key, _)| key)),
    );
    Ok(cmd)
}

/// Apply [`trustc_cargo_env`]-style edits to `cmd`.
pub(crate) fn apply_env_edits(cmd: &mut Command, edits: Vec<(OsString, Option<OsString>)>) {
    for (key, value) in edits {
        match value {
            Some(value) => {
                cmd.env(key, value);
            }
            None => {
                cmd.env_remove(key);
            }
        }
    }
}

fn marker_value(value: &str) -> String {
    encode_token(value).replace(']', "%5D")
}

/// The host facts the preflight needs, behind a seam so every refusal can be
/// unit-tested against fake paths.
pub(crate) trait RouteHost {
    /// `<trustc> --print sysroot`, canonicalized.
    fn trustc_sysroot(&self, trustc: &Path) -> Result<PathBuf, TrustcRouteError>;
    /// The `commit-hash:` line of `<trustc> -vV`; `None` when it reports none.
    fn trustc_commit_hash(&self, trustc: &Path) -> Result<Option<String>, TrustcRouteError>;
    /// File names of the libraries `dylib` links (`otool -L` / `readelf -d`).
    fn linked_libraries(&self, dylib: &Path) -> Result<Vec<String>, TrustcRouteError>;
    /// The innermost world-writable path among `path` and its ancestors.
    fn world_writable_ancestor(
        &self,
        path: &Path,
    ) -> Result<Option<(PathBuf, u32)>, TrustcRouteError>;
    /// A world-writable entry at or below `dir` (`None` when `dir` does not exist).
    fn world_writable_within(&self, dir: &Path)
    -> Result<Option<(PathBuf, u32)>, TrustcRouteError>;
}

/// The real host.
pub(crate) struct SystemHost;

impl RouteHost for SystemHost {
    fn trustc_sysroot(&self, trustc: &Path) -> Result<PathBuf, TrustcRouteError> {
        let stdout = probe_trustc(trustc, &["--print", "sysroot"])?;
        let reported = PathBuf::from(stdout.trim());
        reported.canonicalize().map_err(|error| TrustcRouteError::SysrootProbe {
            trustc: trustc.to_path_buf(),
            detail: format!("reported sysroot {} is unusable: {error}", reported.display()),
        })
    }

    fn trustc_commit_hash(&self, trustc: &Path) -> Result<Option<String>, TrustcRouteError> {
        Ok(parse_commit_hash(&probe_trustc(trustc, &["-vV"])?))
    }

    fn linked_libraries(&self, dylib: &Path) -> Result<Vec<String>, TrustcRouteError> {
        let (tool, args): (&str, &[&str]) =
            if cfg!(target_os = "macos") { ("otool", &["-L"]) } else { ("readelf", &["-d"]) };
        let output = Command::new(tool).args(args).arg(dylib).output().map_err(|error| {
            TrustcRouteError::LinkedLibraries {
                dylib: dylib.to_path_buf(),
                detail: format!("cannot run {tool}: {error}"),
            }
        })?;
        if !output.status.success() {
            return Err(TrustcRouteError::LinkedLibraries {
                dylib: dylib.to_path_buf(),
                detail: format!(
                    "{tool} exited with {}: {}",
                    output.status,
                    String::from_utf8_lossy(&output.stderr).trim()
                ),
            });
        }
        let stdout = String::from_utf8_lossy(&output.stdout);
        Ok(if cfg!(target_os = "macos") {
            parse_otool_libraries(&stdout)
        } else {
            parse_readelf_needed(&stdout)
        })
    }

    fn world_writable_ancestor(
        &self,
        path: &Path,
    ) -> Result<Option<(PathBuf, u32)>, TrustcRouteError> {
        world_writable_ancestor(path)
    }

    fn world_writable_within(
        &self,
        dir: &Path,
    ) -> Result<Option<(PathBuf, u32)>, TrustcRouteError> {
        world_writable_within(dir)
    }
}

fn probe_trustc(trustc: &Path, args: &[&str]) -> Result<String, TrustcRouteError> {
    let mut cmd = Command::new(trustc);
    cmd.args(args);
    scrub_engine_env(&mut cmd, std::env::vars_os().map(|(key, _)| key));
    let rendered = format!("{} {}", trustc.display(), args.join(" "));
    let output = cmd.output().map_err(|error| TrustcRouteError::SysrootProbe {
        trustc: trustc.to_path_buf(),
        detail: format!("cannot run `{rendered}`: {error}"),
    })?;
    if !output.status.success() {
        return Err(TrustcRouteError::SysrootProbe {
            trustc: trustc.to_path_buf(),
            detail: format!(
                "`{rendered}` exited with {}: {}",
                output.status,
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        });
    }
    String::from_utf8(output.stdout).map_err(|_| TrustcRouteError::SysrootProbe {
        trustc: trustc.to_path_buf(),
        detail: format!("`{rendered}` printed non-UTF-8 output"),
    })
}

fn parse_commit_hash(version_verbose: &str) -> Option<String> {
    version_verbose
        .lines()
        .find_map(|line| line.strip_prefix("commit-hash:"))
        .map(str::trim)
        .filter(|hash| !hash.is_empty() && *hash != "unknown")
        .map(str::to_string)
}

/// Library file names from `otool -L` output (the first line names the file).
pub(crate) fn parse_otool_libraries(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .skip(1)
        .filter_map(|line| {
            let line = line.trim();
            let path = line.rsplit_once(" (").map_or(line, |(path, _)| path);
            Path::new(path).file_name().map(|name| name.to_string_lossy().into_owned())
        })
        .collect()
}

/// `NEEDED` entries from `readelf -d` output.
pub(crate) fn parse_readelf_needed(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .filter(|line| line.contains("(NEEDED)"))
        .filter_map(|line| {
            let start = line.find('[')? + 1;
            let end = line[start..].find(']')? + start;
            Some(line[start..end].to_string())
        })
        .collect()
}

/// The innermost world-writable path among `path` and its ancestors, with its mode.
#[cfg(unix)]
pub(crate) fn world_writable_ancestor(
    path: &Path,
) -> Result<Option<(PathBuf, u32)>, TrustcRouteError> {
    use std::os::unix::fs::PermissionsExt;
    for candidate in path.ancestors().filter(|p| !p.as_os_str().is_empty()) {
        let metadata = fs::metadata(candidate).map_err(|error| TrustcRouteError::BadPath {
            what: "backend dylib location",
            path: candidate.to_path_buf(),
            detail: error.to_string(),
        })?;
        let mode = metadata.permissions().mode() & 0o7777;
        if mode & 0o002 != 0 {
            return Ok(Some((candidate.to_path_buf(), mode)));
        }
    }
    Ok(None)
}

/// Non-unix hosts have no mode bits to check.
#[cfg(not(unix))]
pub(crate) fn world_writable_ancestor(
    _path: &Path,
) -> Result<Option<(PathBuf, u32)>, TrustcRouteError> {
    Ok(None)
}

/// A world-writable entry at or below `dir`: the directory itself, a file, or a
/// symbolic link's target or any directory above that target (checked, but not
/// descended into). `None` when `dir` does not exist.
#[cfg(unix)]
pub(crate) fn world_writable_within(
    dir: &Path,
) -> Result<Option<(PathBuf, u32)>, TrustcRouteError> {
    use std::os::unix::fs::PermissionsExt;
    let bad = |path: &Path, error: std::io::Error| TrustcRouteError::BadPath {
        what: "KEY library entry",
        path: path.to_path_buf(),
        detail: error.to_string(),
    };
    match fs::symlink_metadata(dir) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(bad(dir, error)),
        Ok(_) => {}
    }
    let mut stack = vec![dir.to_path_buf()];
    while let Some(path) = stack.pop() {
        let metadata = fs::metadata(&path).map_err(|error| bad(&path, error))?;
        let mode = metadata.permissions().mode() & 0o7777;
        if mode & 0o002 != 0 {
            return Ok(Some((path, mode)));
        }
        let file_type = fs::symlink_metadata(&path).map_err(|error| bad(&path, error))?.file_type();
        if file_type.is_symlink() {
            // A link is only as trustworthy as every directory above its target.
            let target = fs::canonicalize(&path).map_err(|error| bad(&path, error))?;
            if let Some(found) = world_writable_ancestor(&target)? {
                return Ok(Some(found));
            }
        }
        let is_real_dir = file_type.is_dir();
        if is_real_dir {
            for entry in fs::read_dir(&path).map_err(|error| bad(&path, error))? {
                stack.push(entry.map_err(|error| bad(&path, error))?.path());
            }
        }
    }
    Ok(None)
}

/// Non-unix hosts have no mode bits to check.
#[cfg(not(unix))]
pub(crate) fn world_writable_within(
    _dir: &Path,
) -> Result<Option<(PathBuf, u32)>, TrustcRouteError> {
    Ok(None)
}

fn is_driver_library_name(name: &str) -> bool {
    name.strip_prefix(std::env::consts::DLL_PREFIX)
        .and_then(|rest| rest.strip_prefix("rustc_driver-"))
        .is_some_and(|rest| rest.ends_with(std::env::consts::DLL_SUFFIX))
}

/// The single `librustc_driver-*` a sysroot's `lib` directory ships.
pub(crate) fn sysroot_driver_name(lib_dir: &Path) -> Result<String, TrustcRouteError> {
    let entries = fs::read_dir(lib_dir).map_err(|error| TrustcRouteError::BadPath {
        what: "trustc sysroot lib directory",
        path: lib_dir.to_path_buf(),
        detail: error.to_string(),
    })?;
    let mut found: Vec<String> = entries
        .filter_map(Result::ok)
        .filter_map(|entry| entry.file_name().into_string().ok())
        .filter(|name| is_driver_library_name(name))
        .collect();
    found.sort();
    if found.len() == 1 {
        Ok(found.remove(0))
    } else {
        Err(TrustcRouteError::SysrootDriver { lib_dir: lib_dir.to_path_buf(), found })
    }
}

/// `key=value` lines of a PROVENANCE file; `None` when the file does not exist.
pub(crate) fn read_provenance(
    path: &Path,
) -> Result<Option<BTreeMap<String, String>>, TrustcRouteError> {
    let text = match fs::read_to_string(path) {
        Ok(text) => text,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => {
            return Err(TrustcRouteError::Provenance {
                path: path.to_path_buf(),
                detail: error.to_string(),
            });
        }
    };
    let mut fields = BTreeMap::new();
    for line in text.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let Some((key, value)) = line.split_once('=') else { continue };
        if let Some(previous) = fields.get(key)
            && previous != value
        {
            return Err(TrustcRouteError::Provenance {
                path: path.to_path_buf(),
                detail: format!("conflicting values for {key}: {previous:?} and {value:?}"),
            });
        }
        fields.insert(key.to_string(), value.to_string());
    }
    Ok(Some(fields))
}

fn canonical_sha256(value: &str) -> Option<String> {
    let value = value.trim().to_ascii_lowercase();
    (value.len() == SHA256_HEX_LEN && value.bytes().all(|b| b.is_ascii_hexdigit())).then_some(value)
}

fn sha256_file(path: &Path, what: &'static str) -> Result<String, TrustcRouteError> {
    let bytes = fs::read(path).map_err(|error| TrustcRouteError::BadPath {
        what,
        path: path.to_path_buf(),
        detail: error.to_string(),
    })?;
    Ok(trust_mc_core::evidence::EvidenceHash::sha256_bytes(&bytes).value)
}

fn read_key_driver_sha256(path: &Path) -> Result<String, TrustcRouteError> {
    let refuse = |detail: String| TrustcRouteError::KeyJson { path: path.to_path_buf(), detail };
    let text = fs::read_to_string(path).map_err(|error| refuse(error.to_string()))?;
    let value: serde_json::Value =
        serde_json::from_str(&text).map_err(|error| refuse(format!("not JSON: {error}")))?;
    let sha = value
        .get("driver_sha256")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| refuse("no string field driver_sha256".to_string()))?;
    canonical_sha256(sha)
        .ok_or_else(|| refuse(format!("driver_sha256 {sha:?} is not a sha256 hex digest")))
}

/// Establish the identity of one Trustc compile that loads `backend`, or refuse.
///
/// `trustc`, `backend` and `key_dir` are the canonical paths the route resolved.
pub(crate) fn preflight(
    trustc: &Path,
    backend: &Path,
    key_dir: &Path,
    host: &dyn RouteHost,
) -> Result<TrustcIdentity, TrustcRouteError> {
    let mut identity = preflight_key(trustc, key_dir, host)?;

    if let Some((path, mode)) = host.world_writable_ancestor(backend)? {
        return Err(TrustcRouteError::WorldWritable { dylib: backend.to_path_buf(), path, mode });
    }

    let linked: Vec<String> = host
        .linked_libraries(backend)?
        .into_iter()
        .filter(|name| is_driver_library_name(name))
        .collect();
    if linked.len() != 1 || linked[0] != identity.driver_name {
        return Err(TrustcRouteError::BackendDriver {
            dylib: backend.to_path_buf(),
            linked,
            sysroot_driver: identity.driver_name,
        });
    }

    let sha256 = sha256_file(backend, "backend dylib")?;
    identity.backend = Some(BackendIdentity { path: backend.to_path_buf(), sha256 });
    Ok(identity)
}

/// The trustc, PROVENANCE and KEY half of [`preflight`], for a compile that loads
/// no backend (concrete playback): the returned identity has `backend: None`.
pub(crate) fn preflight_key(
    trustc: &Path,
    key_dir: &Path,
    host: &dyn RouteHost,
) -> Result<TrustcIdentity, TrustcRouteError> {
    let sysroot = host.trustc_sysroot(trustc)?;
    // The compile runs `trustc` itself, not the probes' answer: only a trustc that
    // lives in the sysroot it reports loads that sysroot's librustc_driver.
    if trustc.parent() != Some(sysroot.join("bin").as_path()) {
        return Err(TrustcRouteError::TrustcOutsideSysroot {
            trustc: trustc.to_path_buf(),
            sysroot,
        });
    }
    let lib_dir = sysroot.join("lib");
    let driver_name = sysroot_driver_name(&lib_dir)?;

    let provenance_path = sysroot.join(PROVENANCE_FILE);
    let provenance = read_provenance(&provenance_path)?.unwrap_or_default();
    if let Some(recorded) = provenance.get("artifact_driver_name")
        && *recorded != driver_name
    {
        return Err(TrustcRouteError::ProvenanceDriverName {
            provenance: provenance_path,
            recorded: recorded.clone(),
            installed: driver_name,
        });
    }
    let (driver_sha256, sysroot_source) = match provenance.get("artifact_driver_sha256") {
        Some(recorded) => {
            let sha = canonical_sha256(recorded).ok_or_else(|| TrustcRouteError::Provenance {
                path: provenance_path.clone(),
                detail: format!("artifact_driver_sha256 {recorded:?} is not a sha256 hex digest"),
            })?;
            (sha, provenance_path.clone())
        }
        None => {
            let driver = lib_dir.join(&driver_name);
            (sha256_file(&driver, "trustc sysroot librustc_driver")?, driver)
        }
    };
    // Always ask the compiler itself. A PROVENANCE copied from another build must
    // not name the commit in the marker and the target-dir namespace; build-keyed's
    // `derive_identity` refuses the same disagreement.
    let commit = match (provenance.get("reported_commit"), host.trustc_commit_hash(trustc)?) {
        (Some(recorded), Some(reported)) if *recorded != reported => {
            return Err(TrustcRouteError::ProvenanceCommit {
                provenance: provenance_path,
                recorded: recorded.clone(),
                trustc: trustc.to_path_buf(),
                reported,
            });
        }
        (Some(commit), _) => commit.clone(),
        (None, Some(commit)) => commit,
        (None, None) => {
            return Err(TrustcRouteError::SysrootProbe {
                trustc: trustc.to_path_buf(),
                detail: "`trustc -vV` reports no commit-hash and the sysroot PROVENANCE records \
                         no reported_commit"
                    .to_string(),
            });
        }
    };

    let key_json = key_dir.join(KEY_JSON_FILE);
    let key_driver_sha256 = read_key_driver_sha256(&key_json)?;
    if key_driver_sha256 != driver_sha256 {
        return Err(TrustcRouteError::KeyDriverSha {
            key_json,
            key_driver_sha256,
            sysroot_source,
            sysroot_driver_sha256: driver_sha256,
        });
    }
    let expected = format!("{KEY_PREFIX}{}", &driver_sha256[..KEY_SHA_PREFIX_LEN]);
    let key =
        key_dir.file_name().map(|name| name.to_string_lossy().into_owned()).unwrap_or_default();
    if key != expected {
        return Err(TrustcRouteError::KeyName { key_dir: key_dir.to_path_buf(), key, expected });
    }
    // The KEY decides what is verified as much as the dylib does (P14).
    let key_world_writable = |(path, mode): (PathBuf, u32)| TrustcRouteError::KeyWorldWritable {
        key_dir: key_dir.to_path_buf(),
        path,
        mode,
    };
    if let Some(found) = host.world_writable_ancestor(&key_json)? {
        return Err(key_world_writable(found));
    }
    for subdir in KEY_LIBRARY_DIRS {
        if let Some(found) = host.world_writable_within(&key_dir.join(subdir))? {
            return Err(key_world_writable(found));
        }
    }
    // What the compiles must still find after they ran (`recheck_backend`), and
    // what the target-dir namespace is keyed by.
    let key_libraries = key_library_fingerprint(key_dir)?;
    let key_json_bytes = fs::read(&key_json).map_err(|error| TrustcRouteError::KeyJson {
        path: key_json.clone(),
        detail: error.to_string(),
    })?;
    let key_sha256 = key_content_sha256(&key_json_bytes, &key_libraries);

    Ok(TrustcIdentity {
        trustc: trustc.to_path_buf(),
        sysroot,
        commit,
        driver_name,
        driver_sha256,
        backend: None,
        key_dir: key_dir.to_path_buf(),
        key,
        key_libraries,
        key_sha256,
    })
}

/// Refuse on engine knobs and route-owned `RUSTFLAGS`, then run [`preflight`]
/// against the real host.
pub(crate) fn establish_identity(
    trustc: &Path,
    backend: &Path,
    key_dir: &Path,
) -> Result<TrustcIdentity, TrustcRouteError> {
    establish_identity_on(
        std::env::vars_os().map(|(key, _)| key),
        crate::call_single_file::ambient_rustflags().as_deref(),
        trustc,
        backend,
        key_dir,
        &SystemHost,
    )
}

/// [`establish_identity`] with the environment's variable names, its `RUSTFLAGS`
/// (the value every compile forwards) and the host passed in. Both refusals come
/// before any probe, so no marker and no verdict follow them.
pub(crate) fn establish_identity_on<I, K>(
    env_keys: I,
    rustflags: Option<&str>,
    trustc: &Path,
    backend: &Path,
    key_dir: &Path,
    host: &dyn RouteHost,
) -> Result<TrustcIdentity, TrustcRouteError>
where
    I: IntoIterator<Item = K>,
    K: AsRef<OsStr>,
{
    refuse_engine_env_knobs(env_keys)?;
    refuse_route_owned_rustflags(rustflags)?;
    preflight(trustc, backend, key_dir, host)
}

/// [`preflight_key`] against the real host, for concrete playback. No engine runs,
/// so engine knobs are not refused; route-owned `RUSTFLAGS` are, because the
/// playback compile forwards `RUSTFLAGS` too and `-Zcodegen-backend` there would
/// load a backend under a marker that says `backend=unused`.
pub(crate) fn establish_playback_identity(
    trustc: &Path,
    key_dir: &Path,
) -> Result<TrustcIdentity, TrustcRouteError> {
    establish_playback_identity_on(
        crate::call_single_file::ambient_rustflags().as_deref(),
        trustc,
        key_dir,
        &SystemHost,
    )
}

/// [`establish_playback_identity`] with `RUSTFLAGS` and the host passed in.
pub(crate) fn establish_playback_identity_on(
    rustflags: Option<&str>,
    trustc: &Path,
    key_dir: &Path,
    host: &dyn RouteHost,
) -> Result<TrustcIdentity, TrustcRouteError> {
    refuse_route_owned_rustflags(rustflags)?;
    preflight_key(trustc, key_dir, host)
}

/// Does this `RUSTFLAGS` token reach an option the route sets itself?
///
/// The match is deliberately a substring over the whole token, with `_` read as
/// `-`, because rustc accepts the options in many shapes: `-Cllvm-args=x`, `-C`
/// followed by a separate `llvm-args=x` token, `--codegen=llvm-args=x`,
/// `--codegen llvm_args=x`, and getopts short-option clusters such as
/// `-OCllvm-args=x` (a flag, then `-C` taking the rest of the token). A token
/// starting with `@` is an argfile, which rustc expands into arguments before
/// parsing, so its contents cannot be judged here and it is refused outright.
pub(crate) fn is_route_owned_rustflags_token(token: &str) -> bool {
    if token.starts_with('@') {
        return true;
    }
    let normalized = token.replace('_', "-");
    ROUTE_OWNED_RUSTC_OPTIONS.iter().any(|option| normalized.contains(option))
}

/// Refuse while `RUSTFLAGS` carries a token that reaches an option the route sets
/// itself ([`is_route_owned_rustflags_token`]). Every other token (an edition, a
/// `--cfg`, `-Coverflow-checks=off` from a compile-flags header) is still forwarded.
pub(crate) fn refuse_route_owned_rustflags(
    rustflags: Option<&str>,
) -> Result<(), TrustcRouteError> {
    let tokens: Vec<String> = rustflags
        .into_iter()
        .flat_map(crate::call_single_file::rustflags_tokens)
        .filter(|token| is_route_owned_rustflags_token(token))
        .map(str::to_string)
        .collect();
    if tokens.is_empty() { Ok(()) } else { Err(TrustcRouteError::RouteOwnedRustflags { tokens }) }
}

/// Is `key` one the trustc child must not see?
pub(crate) fn is_scrubbed_env_key(key: &OsStr) -> bool {
    let bytes = key.as_encoded_bytes();
    SCRUBBED_ENV_PREFIXES.iter().any(|prefix| bytes.starts_with(prefix.as_bytes()))
}

/// Remove every `TRUST_MC_*` / `AY_*` variable from `cmd`'s environment: those
/// the child would inherit (named by `parent_keys`) and any set on `cmd` itself.
pub(crate) fn scrub_engine_env<I>(cmd: &mut Command, parent_keys: I)
where
    I: IntoIterator<Item = OsString>,
{
    let explicit: Vec<OsString> = cmd
        .get_envs()
        .filter(|(key, value)| value.is_some() && is_scrubbed_env_key(key))
        .map(|(key, _)| key.to_os_string())
        .collect();
    let inherited = parent_keys.into_iter().filter(|key| is_scrubbed_env_key(key));
    for key in inherited.chain(explicit) {
        cmd.env_remove(key);
    }
}

/// Refuse while an engine knob is set that [`scrub_engine_env`] would drop.
pub(crate) fn refuse_engine_env_knobs<I, K>(parent_keys: I) -> Result<(), TrustcRouteError>
where
    I: IntoIterator<Item = K>,
    K: AsRef<OsStr>,
{
    let vars = trust_mc_metadata::engine_args::set_engine_env_knobs(parent_keys);
    if vars.is_empty() { Ok(()) } else { Err(TrustcRouteError::EngineEnvKnobs { vars }) }
}

#[cfg(test)]
#[path = "trustc_route_tests.rs"]
mod tests;
