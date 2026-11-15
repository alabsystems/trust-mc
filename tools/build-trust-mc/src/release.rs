// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The RELEASE bundle (`targo --unverified bundle`) is cut on one Trust seal and
//! on nothing else (owner orders 2026-09-28/29: ALab systems build with Trust;
//! "NO STOCK RUST IN THE TOOLCHAIN FOR TRUST").
//!
//! [`admit`] decides that before the long build starts, by what the toolchain
//! IS rather than what it is called: the compiler reports a Trust identity
//! (`binary: trustc`, a `trust:` line, a 40-hex `commit-hash`), the Targo that
//! launched this tool lives in that compiler's own `bin/`, the seal ships the
//! `bin/targo` and `bin/trustc` an installed bundle runs (plus the read-only
//! `bin/rustc` version probe retained for existing bundle metadata), the checkout pins
//! `channel = "trust"`, no rustup selection (`RUSTUP_TOOLCHAIN`) names another
//! toolchain, and no wrapper or `CARGO_BUILD_RUSTC` ([`COMPILER_OVERRIDES`])
//! would run another program in the compiler's place. The admitted seal is what
//! the bundle records: `rust-toolchain-version` is the channel (`trust`,
//! [`toolchain_name`]), `rustc-version` is the seal's `bin/rustc --version` (the
//! line `trust-mc setup --use-local-toolchain` checks,
//! [`ReleaseSeal::installed_rustc_version`]) and [`SEAL_RECORD`] names the seal
//! itself — its commit, its numbered build, its `librustc_driver` and that
//! driver's sha256 ([`ReleaseSeal::record`]).
//!
//! The release build also keeps the build host out of the shipped bytes:
//! [`ReleaseSeal::remap_flags`] are `--remap-path-prefix` flags for `$HOME`,
//! `$CARGO_HOME`, the sibling-checkout root, the seal root and the std sources,
//! and [`RELEASE_BUNDLE_ENV`] tells `trust-mc-compiler/build.rs` and
//! `trust-mc-driver/build.rs` to bake no absolute path to the build seal (the
//! installed bundle reaches it through its `toolchain` link).

use crate::dev_std::{DevCompiler, StdSource, require_rustc_dev};
use crate::keyed::{CompilerIdentity, TRUST_SRC_COMPONENT, derive_identity, run_capture};
use anyhow::{Context, Result, bail, format_err};
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The channel a release bundle is built on, and the only `RUSTUP_TOOLCHAIN` it
/// accepts. What it records in `rust-toolchain-version`.
pub(crate) const TRUST_CHANNEL: &str = "trust";
/// The bundle file naming the seal the bundle was cut on ([`ReleaseSeal::record`]).
pub(crate) const SEAL_RECORD: &str = "trust-seal";
const SEAL_RECORD_SCHEMA: &str = "trust-mc-release-seal/1";
/// Set (to `1`) in the environment of the release build's cargo. The build
/// scripts of trust-mc-compiler and trust-mc-driver then bake no absolute path
/// to the build seal: no `-rpath <seal>/lib` (the bundle keeps
/// `@loader_path/../toolchain/lib`) and no `MC_DRIVER_BUILD_SYSROOT` (an
/// installed bundle runs its own `toolchain/bin/targo`). No `TRUST_` prefix:
/// authenticated Targo reserves that namespace.
pub(crate) const RELEASE_BUNDLE_ENV: &str = "MC_RELEASE_BUNDLE";
/// Where an installed bundle, and the release build's own sysroot, link the
/// seal (`trust-mc setup --use-local-toolchain <seal>` makes the same link).
pub(crate) const TOOLCHAIN_LINK: &str = "toolchain";

/// A Trust seal admitted to cut the release bundle.
#[derive(Debug)]
pub(crate) struct ReleaseSeal {
    pub(crate) compiler: DevCompiler,
    /// `commit-hash:` of `trustc -vV`, 40 lowercase hex.
    pub(crate) commit: String,
    /// `trust:` of `trustc -vV`.
    pub(crate) trust: String,
    /// `host:` of `trustc -vV`.
    pub(crate) host: String,
    /// The seal's driver identity (PROVENANCE's, else the installed driver's sha256).
    pub(crate) identity: CompilerIdentity,
}

/// What [`admit`] judges, as plain values so each refusal is testable.
pub(crate) struct Launch<'a> {
    /// `<compiler> -vV`.
    pub(crate) verbose: &'a str,
    /// The cargo that launched this tool (`$CARGO`), when known.
    pub(crate) cargo: Option<&'a Path>,
    /// `RUSTUP_TOOLCHAIN`, when set and non-empty.
    pub(crate) rustup_toolchain: Option<&'a str>,
    /// `channel` of the checkout's `rust-toolchain.toml`.
    pub(crate) pinned_channel: Option<&'a str>,
    /// `<sysroot>/PROVENANCE`, when the seal ships one.
    pub(crate) provenance: Option<&'a str>,
    /// Each [`COMPILER_OVERRIDES`] variable that is set, with its value.
    pub(crate) overrides: &'a [(&'static str, String)],
}

/// Environment variables under which cargo runs something other than the
/// admitted compiler for the units it builds (a wrapper, or another `rustc`).
/// A release bundle is compiled by the seal's own compiler, so each is refused.
pub(crate) const COMPILER_OVERRIDES: [&str; 5] = [
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
];

/// The toolchain name a release bundle records in `rust-toolchain-version`:
/// always [`TRUST_CHANNEL`]. A `RUSTUP_TOOLCHAIN` that names anything else
/// (`nightly-2025-12-03`, `stable`) and a checkout pinned to another channel are
/// refused — such a bundle would send its consumers to a stock toolchain.
pub(crate) fn toolchain_name(
    rustup_toolchain: Option<&str>,
    pinned_channel: Option<&str>,
) -> Result<&'static str> {
    if let Some(selected) = rustup_toolchain.filter(|tc| !tc.is_empty())
        && selected != TRUST_CHANNEL
    {
        bail!(
            "RUSTUP_TOOLCHAIN={selected}: a trust-mc release bundle is cut on the Trust \
             toolchain only (`{TRUST_CHANNEL}`), never on another toolchain. Unset \
             RUSTUP_TOOLCHAIN and run the seal's own targo: \
             <seal>/bin/targo --unverified bundle"
        );
    }
    match pinned_channel {
        Some(TRUST_CHANNEL) => Ok(TRUST_CHANNEL),
        Some(other) => bail!(
            "rust-toolchain.toml pins channel `{other}`: a trust-mc release bundle is cut \
             only from a checkout that pins `channel = \"{TRUST_CHANNEL}\"`"
        ),
        None => bail!("rust-toolchain.toml names no channel; a release bundle needs `trust`"),
    }
}

fn verbose_field<'a>(verbose: &'a str, name: &str) -> Option<&'a str> {
    verbose.lines().find_map(|line| line.strip_prefix(name)).map(str::trim)
}

fn is_lower_hex(text: &str, len: usize) -> bool {
    text.len() == len && text.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn canonical(path: &Path) -> PathBuf {
    path.canonicalize().unwrap_or_else(|_| path.to_path_buf())
}

/// The seal programs an installed bundle runs through its `toolchain` link.
// rustc is retained only for the existing read-only bundle version comparison.
const INSTALLED_NAMES: [&str; 3] = ["targo", "trustc", "rustc"];

fn installed_tool(sysroot: &Path, name: &str) -> PathBuf {
    sysroot.join("bin").join(format!("{name}{}", std::env::consts::EXE_SUFFIX))
}

/// Admit `compiler` to cut a release bundle, or refuse naming why.
pub(crate) fn admit(compiler: DevCompiler, launch: &Launch<'_>) -> Result<ReleaseSeal> {
    toolchain_name(launch.rustup_toolchain, launch.pinned_channel)?;
    if let Some((name, value)) = launch.overrides.first() {
        bail!(
            "{name}={value}: cargo would run it in place of the seal's compiler, and a \
             trust-mc release bundle is compiled by the seal's own compiler only. Unset \
             {name} and run <seal>/bin/targo --unverified bundle"
        );
    }
    let shown = compiler.rustc.display().to_string();
    let binary = verbose_field(launch.verbose, "binary:");
    let trust = verbose_field(launch.verbose, "trust:").filter(|t| !t.is_empty());
    let (Some("trustc"), Some(trust)) = (binary, trust) else {
        bail!(
            "{shown} is not a Trust compiler: `-vV` reports binary `{}` and {} (a Trust \
             seal reports `binary: trustc` and a `trust:` line). A trust-mc release bundle \
             is cut on a Trust seal only: <seal>/bin/targo --unverified bundle",
            binary.unwrap_or("<none>"),
            if trust.is_some() { "a `trust:` line" } else { "no `trust:` line" }
        );
    };
    let commit = verbose_field(launch.verbose, "commit-hash:").unwrap_or_default();
    if !is_lower_hex(commit, 40) {
        bail!("{shown} reports commit-hash `{commit}`; a release names a full 40-hex commit");
    }
    let host = verbose_field(launch.verbose, "host:")
        .filter(|h| !h.is_empty())
        .ok_or_else(|| format_err!("{shown} -vV has no host: line"))?;

    // Every nested build runs the launching cargo: it must be this seal's own.
    let seal_bin = canonical(&compiler.sysroot.join("bin"));
    let Some(cargo) = launch.cargo else {
        bail!(
            "no launching cargo (`$CARGO` is unset): run the release build through the \
             seal's targo, <seal>/bin/targo --unverified bundle"
        );
    };
    let cargo_bin = cargo.parent().map(canonical);
    if cargo_bin.as_deref() != Some(seal_bin.as_path()) {
        bail!(
            "the launching cargo {} is not the seal's own ({}): every nested build of a \
             release bundle runs the cargo of the compiler it links, so launch it as \
             {}/targo --unverified bundle",
            cargo.display(),
            seal_bin.display(),
            seal_bin.display()
        );
    }
    // argv[0] selects the frontend persona: the compatibility cargo next to
    // Targo is not an authorized launcher even when its bytes are identical.
    if cargo.file_name()
        != Some(std::ffi::OsStr::new(&format!("targo{}", std::env::consts::EXE_SUFFIX)))
    {
        bail!(
            "the launching frontend {} is not named targo: use {}/targo --unverified bundle",
            cargo.display(),
            seal_bin.display()
        );
    }
    // An installed bundle runs the seal through its `toolchain` link under these
    // names: `toolchain/bin/targo` with RUSTC=`toolchain/bin/trustc`
    // (trust-mc-driver/src/session/cargo.rs), and `trust-mc setup
    // --use-local-toolchain` matches `bin/rustc --version` against the bundle's
    // `rustc-version`. A seal without them cannot run what it cut.
    for name in INSTALLED_NAMES {
        let path = installed_tool(&compiler.sysroot, name);
        if !path.is_file() {
            bail!(
                "{} does not exist: an installed trust-mc bundle runs the seal it was cut on \
                 as `toolchain/bin/{name}`, so the seal must ship it",
                path.display()
            );
        }
    }
    require_rustc_dev(&compiler)?;
    let identity = derive_identity(&compiler.sysroot, Some(commit), launch.provenance)?;
    Ok(ReleaseSeal {
        commit: commit.to_string(),
        trust: trust.to_string(),
        host: host.to_string(),
        identity,
        compiler,
    })
}

/// [`admit`] for this process: `-vV` of `compiler`, `$CARGO`, `$RUSTUP_TOOLCHAIN`,
/// `rust-toolchain.toml` under `repo_root`, and the seal's PROVENANCE.
pub(crate) fn admit_this_launch(compiler: DevCompiler, repo_root: &Path) -> Result<ReleaseSeal> {
    let verbose = run_capture(
        Command::new(&compiler.rustc).arg("-vV"),
        &format!("{} -vV", compiler.rustc.display()),
    )?;
    let cargo = std::env::var_os("CARGO").filter(|c| !c.is_empty()).map(PathBuf::from);
    let rustup = std::env::var("RUSTUP_TOOLCHAIN").ok();
    let pin = repo_root.join("rust-toolchain.toml");
    let pin_text =
        fs::read_to_string(&pin).with_context(|| format!("cannot read {}", pin.display()))?;
    let pinned = crate::pinned_channel(&pin_text);
    let provenance = fs::read_to_string(compiler.sysroot.join("PROVENANCE")).ok();
    let overrides: Vec<(&'static str, String)> = COMPILER_OVERRIDES
        .iter()
        .filter_map(|name| std::env::var(name).ok().filter(|v| !v.is_empty()).map(|v| (*name, v)))
        .collect();
    admit(
        compiler,
        &Launch {
            verbose: &verbose,
            cargo: cargo.as_deref(),
            rustup_toolchain: rustup.as_deref(),
            pinned_channel: pinned.as_deref(),
            provenance: provenance.as_deref(),
            overrides: &overrides,
        },
    )
}

/// The inputs of [`ReleaseSeal::remap_flags`] that come from the build host.
pub(crate) struct HostPaths {
    /// `$HOME`.
    pub(crate) home: Option<PathBuf>,
    /// `$CARGO_HOME`, else `$HOME/.cargo`: registry and git sources.
    pub(crate) cargo_home: Option<PathBuf>,
    /// The directory holding this checkout and its `../ay`, `../trust-ir` siblings.
    pub(crate) source_root: PathBuf,
}

impl HostPaths {
    pub(crate) fn of_this_host(repo_root: &Path) -> Self {
        let home = std::env::var_os("HOME").filter(|h| !h.is_empty()).map(PathBuf::from);
        let cargo_home = std::env::var_os("CARGO_HOME")
            .filter(|h| !h.is_empty())
            .map(PathBuf::from)
            .or_else(|| home.as_ref().map(|h| h.join(".cargo")));
        HostPaths {
            home,
            cargo_home,
            source_root: repo_root.parent().unwrap_or(repo_root).to_path_buf(),
        }
    }
}

impl ReleaseSeal {
    /// `<seal>/bin/rustc`: only the read-only version comparison retained for
    /// existing bundle metadata. Installed compilations run Targo and trustc.
    pub(crate) fn installed_rustc(&self) -> PathBuf {
        installed_tool(&self.compiler.sysroot, "rustc")
    }

    /// What the bundle records in `rustc-version`: `--version` of
    /// [`Self::installed_rustc`], the line `trust-mc setup --use-local-toolchain
    /// <seal>` reads back from `<seal>/bin/rustc` to admit the seal. A Trust seal
    /// answers by the name it is run as (`trustc` appends ` (trustc <ver>)`), so
    /// recording the `trustc` spelling made setup refuse the very seal that cut
    /// the bundle.
    pub(crate) fn installed_rustc_version(&self) -> Result<String> {
        let rustc = self.installed_rustc();
        run_capture(
            Command::new(&rustc).arg("--version"),
            &format!("{} --version", rustc.display()),
        )
    }

    /// The `library/` the verification and playback sysroots are built from: the
    /// seal's own rust-src when it ships one (always, explicitly, so cargo cannot
    /// pick another), else the checkout sources prepared for the compiler's commit.
    pub(crate) fn std_library(&self, source: &StdSource, prepared: Option<&Path>) -> PathBuf {
        match (source, prepared) {
            (_, Some(prepared)) => prepared.to_path_buf(),
            _ => self.compiler.sysroot.join(TRUST_SRC_COMPONENT).join("library"),
        }
    }

    /// `--remap-path-prefix` flags for every unit of the release build. Ordered
    /// general to specific: rustc applies the LAST matching prefix, so the std
    /// sources win over the seal root, the seal and checkouts over `$HOME`.
    /// A path is remapped under its spelling and its canonical form, since cargo
    /// and rustc spell some of them each way.
    ///
    /// - `$HOME` -> `~`, the catch-all;
    /// - `$CARGO_HOME` -> `/cargo` (registry and git dependency sources);
    /// - the sibling-checkout root -> `/src` (`/src/trust-mc`, `/src/ay`, ...);
    /// - the seal root -> `/trust/<commit>`;
    /// - the directory holding `std_library` -> `/rustc/<commit>`, the spelling
    ///   rustc gives std sources (`library/core/src/...` under it), naming the
    ///   seal's own commit.
    pub(crate) fn remap_flags(&self, host: &HostPaths, std_library: &Path) -> Result<Vec<String>> {
        let std_root = std_library.parent().unwrap_or(std_library);
        let mut pairs: Vec<(&Path, String)> = Vec::new();
        if let Some(home) = &host.home {
            pairs.push((home, "~".to_string()));
        }
        if let Some(cargo_home) = &host.cargo_home {
            pairs.push((cargo_home, "/cargo".to_string()));
        }
        pairs.push((&host.source_root, "/src".to_string()));
        pairs.push((&self.compiler.sysroot, format!("/trust/{}", self.commit)));
        pairs.push((std_root, format!("/rustc/{}", self.commit)));
        let mut flags = Vec::new();
        for (from, to) in pairs {
            let mut spellings = vec![from.to_path_buf()];
            let real = canonical(from);
            if real != from {
                spellings.push(real);
            }
            for spelling in spellings {
                let spelled = spelling.to_str().ok_or_else(|| {
                    format_err!("{} is not UTF-8; it cannot be remapped", spelling.display())
                })?;
                if spelled.is_empty() || spelled == "/" {
                    continue;
                }
                let flag = format!("--remap-path-prefix={spelled}={to}");
                if !flags.contains(&flag) {
                    flags.push(flag);
                }
            }
        }
        Ok(flags)
    }

    /// The numbered seal build: the sysroot's directory name when it is a number
    /// (an atpkg store build, `.../store/trust/<N>`).
    pub(crate) fn build(&self) -> Option<String> {
        let name = self.compiler.sysroot.file_name()?.to_str()?;
        (!name.is_empty() && name.bytes().all(|b| b.is_ascii_digit())).then(|| name.to_string())
    }

    /// The text of [`SEAL_RECORD`]: which seal cut the bundle, by identity, with no
    /// build-host path.
    pub(crate) fn record(&self, std_source: &str) -> String {
        let id = &self.identity;
        let seal = self
            .compiler
            .sysroot
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        format!(
            "schema={SEAL_RECORD_SCHEMA}\n\
             channel={TRUST_CHANNEL}\n\
             compiler={version}\n\
             commit={commit}\n\
             trust={trust}\n\
             host={host}\n\
             seal={seal}\n\
             build={build}\n\
             driver={driver}\n\
             driver_sha256={sha}\n\
             key={key}\n\
             key_source={key_source}\n\
             provenance_class={class}\n\
             std_source={std_source}\n",
            version = self.compiler.version,
            commit = self.commit,
            trust = self.trust,
            host = self.host,
            build = self.build().as_deref().unwrap_or("none"),
            driver = id.driver_name,
            sha = id.driver_sha256,
            key = id.key,
            key_source = id.key_source.as_str(),
            class = id.provenance_class.as_deref().unwrap_or("none"),
        )
    }

    /// Link `<sysroot dir>/toolchain` to the seal, as an installed bundle does, so
    /// the release trust-mc-compiler (rpath `@loader_path/../toolchain/lib` only)
    /// loads the seal's `librustc_driver` while it builds the libraries.
    pub(crate) fn link_toolchain(&self, sysroot_dir: &Path) -> Result<()> {
        let link = sysroot_dir.join(TOOLCHAIN_LINK);
        if fs::symlink_metadata(&link).is_ok() {
            fs::remove_file(&link).with_context(|| format!("cannot replace {}", link.display()))?;
        }
        fs::create_dir_all(sysroot_dir)?;
        #[cfg(unix)]
        std::os::unix::fs::symlink(&self.compiler.sysroot, &link).with_context(|| {
            format!("cannot link {} -> {}", link.display(), self.compiler.sysroot.display())
        })?;
        Ok(())
    }

    /// Environment for the release build's cargo: [`RELEASE_BUNDLE_ENV`].
    pub(crate) fn cargo_env(&self) -> Vec<(String, OsString)> {
        vec![(RELEASE_BUNDLE_ENV.to_string(), OsString::from("1"))]
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "a panicking assertion is the point in tests")]
mod tests {
    use super::*;
    use crate::keyed::KeySource;

    const COMMIT: &str = "7d5533b2bb9c9417bc09c27f1acd9d0b808f8f15";
    const TRUST_VV: &str = "rustc 1.99.0-dev (7d5533b2b 2026-09-23) (trustc 0.1.0)\n\
        binary: trustc\n\
        commit-hash: 7d5533b2bb9c9417bc09c27f1acd9d0b808f8f15\n\
        commit-date: 2026-09-23\n\
        host: aarch64-apple-darwin\n\
        release: 1.99.0-dev\n\
        trust: 0.1.0\n\
        LLVM version: 22.1.2\n";
    /// What the frozen comparison nightly reports (measured, nightly-2025-12-03).
    const STOCK_VV: &str = "rustc 1.93.0-nightly (646a3f8c1 2025-12-02)\n\
        binary: rustc\n\
        commit-hash: 646a3f8c15baefb98dc6e0c1c1ba3356db702d2a\n\
        commit-date: 2025-12-02\n\
        host: aarch64-apple-darwin\n\
        release: 1.93.0-nightly\n\
        LLVM version: 21.1.5\n";

    /// A seal directory with `bin/{targo,trustc,cargo,rustc}` and one driver
    /// under both `lib/` and `lib/rustlib/<host>/lib/`.
    fn seal(name: &str) -> PathBuf {
        let root = std::env::temp_dir()
            .join(format!("build-trust-mc-release-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        let seal = root.join("store/trust/10042");
        let lib = seal.join("lib/rustlib/aarch64-apple-darwin/lib");
        fs::create_dir_all(seal.join("bin")).unwrap();
        fs::create_dir_all(&lib).unwrap();
        for bin in ["targo", "trustc", "cargo", "rustc"] {
            fs::write(seal.join("bin").join(bin), "").unwrap();
        }
        let driver =
            format!("librustc_driver-ea44686a6eaf5d13.{}", crate::sysroot::lib_extension());
        fs::write(seal.join("lib").join(&driver), b"driver").unwrap();
        fs::write(lib.join(&driver), b"driver").unwrap();
        seal
    }

    fn compiler(seal: &Path) -> DevCompiler {
        DevCompiler {
            rustc: seal.join("bin/trustc"),
            version: TRUST_VV.lines().next().unwrap().to_string(),
            commit: Some(COMMIT.to_string()),
            sysroot: seal.to_path_buf(),
        }
    }

    fn launch<'a>(verbose: &'a str, cargo: &'a Path) -> Launch<'a> {
        Launch {
            verbose,
            cargo: Some(cargo),
            rustup_toolchain: None,
            pinned_channel: Some("trust"),
            provenance: None,
            overrides: &[],
        }
    }

    #[test]
    fn a_trust_seal_launched_by_its_own_targo_is_admitted_and_stamped() {
        let seal = seal("admit");
        let targo = seal.join("bin/targo");
        let admitted = admit(compiler(&seal), &launch(TRUST_VV, &targo)).unwrap();
        assert_eq!(admitted.commit, COMMIT);
        assert_eq!(admitted.build().as_deref(), Some("10042"));
        assert_eq!(admitted.identity.key_source, KeySource::DriverDylibSha256);
        let record = admitted.record("seal-rust-src");
        for line in [
            "schema=trust-mc-release-seal/1",
            "channel=trust",
            "commit=7d5533b2bb9c9417bc09c27f1acd9d0b808f8f15",
            "trust=0.1.0",
            "build=10042",
            "seal=10042",
            "std_source=seal-rust-src",
        ] {
            assert!(record.lines().any(|l| l == line), "missing `{line}` in\n{record}");
        }
        assert!(record.contains("driver=librustc_driver-ea44686a6eaf5d13."), "{record}");
        assert!(!record.contains(seal.to_str().unwrap()), "no build-host path: {record}");
        // RUSTUP_TOOLCHAIN=trust (a rustup proxy chose the channel) is the same toolchain.
        let mut via_rustup = launch(TRUST_VV, &targo);
        via_rustup.rustup_toolchain = Some("trust");
        admit(compiler(&seal), &via_rustup).unwrap();
        let _ = fs::remove_dir_all(seal.ancestors().nth(3).unwrap());
    }

    /// The defect: `bundle_toolchain_name` stamped whatever `RUSTUP_TOOLCHAIN`
    /// said, so a bundle cut with the frozen nightly selected recorded
    /// `nightly-2025-12-03` and sent every consumer to a stock toolchain.
    #[test]
    fn a_stock_rustup_selection_is_refused() {
        for stock in ["nightly-2025-12-03", "nightly-2025-12-03-aarch64-apple-darwin", "stable"] {
            let error = toolchain_name(Some(stock), Some("trust")).unwrap_err().to_string();
            assert!(error.contains(&format!("RUSTUP_TOOLCHAIN={stock}")), "{error}");
            assert!(!error.contains("rustup toolchain install"), "no stock remedy: {error}");
        }
        assert_eq!(toolchain_name(None, Some("trust")).unwrap(), "trust");
        assert_eq!(toolchain_name(Some(""), Some("trust")).unwrap(), "trust");
        assert_eq!(toolchain_name(Some("trust"), Some("trust")).unwrap(), "trust");
        let legacy = toolchain_name(None, Some("nightly-2025-12-03")).unwrap_err().to_string();
        assert!(legacy.contains("pins channel `nightly-2025-12-03`"), "{legacy}");
        assert!(toolchain_name(None, None).is_err());

        let seal = seal("rustup");
        let targo = seal.join("bin/targo");
        let mut selected = launch(TRUST_VV, &targo);
        selected.rustup_toolchain = Some("nightly-2025-12-03");
        assert!(admit(compiler(&seal), &selected).is_err());
        let _ = fs::remove_dir_all(seal.ancestors().nth(3).unwrap());
    }

    #[test]
    fn a_stock_compiler_is_refused_whatever_it_is_called() {
        let seal = seal("stock");
        let targo = seal.join("bin/targo");
        let error = admit(compiler(&seal), &launch(STOCK_VV, &targo)).unwrap_err().to_string();
        assert!(error.contains("is not a Trust compiler"), "{error}");
        assert!(error.contains("binary `rustc`"), "{error}");
        // A compiler calling itself trustc without a Trust version is not one either.
        let renamed = STOCK_VV.replace("binary: rustc", "binary: trustc");
        let error = admit(compiler(&seal), &launch(&renamed, &targo)).unwrap_err().to_string();
        assert!(error.contains("no `trust:` line"), "{error}");
        let short = TRUST_VV.replace(COMMIT, "7d5533b2b");
        let error = admit(compiler(&seal), &launch(&short, &targo)).unwrap_err().to_string();
        assert!(error.contains("full 40-hex commit"), "{error}");
        let _ = fs::remove_dir_all(seal.ancestors().nth(3).unwrap());
    }

    /// A wrapper or a `CARGO_BUILD_RUSTC` would run another program in place of
    /// the admitted compiler for every unit: refused, naming the variable.
    #[test]
    fn a_compiler_override_in_the_environment_is_refused() {
        let seal = seal("override");
        let targo = seal.join("bin/targo");
        for name in COMPILER_OVERRIDES {
            let overrides = [(name, "/opt/stock/bin/rustc".to_string())];
            let mut overridden = launch(TRUST_VV, &targo);
            overridden.overrides = &overrides;
            let error = admit(compiler(&seal), &overridden).unwrap_err().to_string();
            assert!(error.contains(&format!("{name}=/opt/stock/bin/rustc")), "{error}");
        }
        let _ = fs::remove_dir_all(seal.ancestors().nth(3).unwrap());
    }

    #[test]
    fn a_cargo_outside_the_seal_is_refused() {
        let seal = seal("cargo");
        let stock = seal.ancestors().nth(3).unwrap().join("rustup/toolchains/nightly/bin");
        fs::create_dir_all(&stock).unwrap();
        fs::write(stock.join("cargo"), "").unwrap();
        let error = admit(compiler(&seal), &launch(TRUST_VV, &stock.join("cargo")))
            .unwrap_err()
            .to_string();
        assert!(error.contains("is not the seal's own"), "{error}");
        let mut unset = launch(TRUST_VV, &stock);
        unset.cargo = None;
        assert!(admit(compiler(&seal), &unset).unwrap_err().to_string().contains("$CARGO"));
        let _ = fs::remove_dir_all(seal.ancestors().nth(3).unwrap());
    }

    #[test]
    fn the_same_seals_compatibility_cargo_is_not_a_release_launcher() {
        let seal = seal("cargo-persona");
        let error = admit(compiler(&seal), &launch(TRUST_VV, &seal.join("bin/cargo")))
            .unwrap_err()
            .to_string();
        assert!(error.contains("not named targo"), "{error}");
        let _ = fs::remove_dir_all(seal.ancestors().nth(3).unwrap());
    }

    /// Installed builds need canonical Trust names; the compatibility rustc
    /// remains necessary only for the existing read-only version comparison.
    #[test]
    fn a_seal_without_the_names_an_install_runs_is_refused() {
        for missing in INSTALLED_NAMES {
            let seal = seal(&format!("missing-{missing}"));
            fs::remove_file(seal.join("bin").join(missing)).unwrap();
            let targo = seal.join("bin/targo");
            let error = admit(compiler(&seal), &launch(TRUST_VV, &targo)).unwrap_err().to_string();
            assert!(error.contains(&format!("`toolchain/bin/{missing}`")), "{error}");
            let _ = fs::remove_dir_all(seal.ancestors().nth(3).unwrap());
        }
    }

    /// Regression: the bundle recorded `trustc --version` in `rustc-version`
    /// (`... (trustc 0.1.0)`), but `trust-mc setup --use-local-toolchain <seal>`
    /// compares it with `<seal>/bin/rustc --version`, which the same Trust binary
    /// answers without the suffix, so setup refused the seal that cut the bundle.
    /// The recorded line is the installed `rustc`'s.
    #[cfg(unix)]
    #[test]
    fn rustc_version_is_the_line_setup_reads_back_from_the_installed_rustc() {
        use std::os::unix::fs::PermissionsExt;
        let seal = seal("installed-rustc");
        let bin = seal.join("bin");
        let installed = "rustc 1.99.0-dev (7d5533b2b 2026-09-23)";
        for (name, line) in
            [("trustc", format!("{installed} (trustc 0.1.0)")), ("rustc", installed.to_string())]
        {
            let path = bin.join(name);
            fs::write(&path, format!("#!/bin/sh\necho '{line}'\n")).unwrap();
            fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
        }
        let admitted = admit(compiler(&seal), &launch(TRUST_VV, &bin.join("targo"))).unwrap();
        assert_eq!(admitted.installed_rustc(), bin.join("rustc"));
        assert_eq!(admitted.installed_rustc_version().unwrap(), format!("{installed}\n"));
        let _ = fs::remove_dir_all(seal.ancestors().nth(3).unwrap());
    }

    #[test]
    fn remap_flags_go_general_to_specific_and_name_the_seal_commit() {
        let seal = seal("remap");
        let targo = seal.join("bin/targo");
        let admitted = admit(compiler(&seal), &launch(TRUST_VV, &targo)).unwrap();
        let host = HostPaths {
            home: Some("$HOME".into()),
            cargo_home: Some("$HOME/.cargo".into()),
            source_root: "$HOME/src".into(),
        };
        let library = admitted.std_library(&StdSource::Sysroot, None);
        assert_eq!(library, seal.join("lib/rustlib/src/rust/library"));
        let flags = admitted.remap_flags(&host, &library).unwrap();
        let seal_str = seal.to_str().unwrap();
        let expected_head = [
            "--remap-path-prefix=$HOME=~".to_string(),
            "--remap-path-prefix=$HOME/.cargo=/cargo".to_string(),
            "--remap-path-prefix=$HOME/src=/src".to_string(),
            format!("--remap-path-prefix={seal_str}=/trust/{COMMIT}"),
        ];
        assert_eq!(&flags[..4], &expected_head);
        // The std root is last (it wins), possibly followed by its canonical spelling.
        let std_flag =
            format!("--remap-path-prefix={seal_str}/lib/rustlib/src/rust=/rustc/{COMMIT}");
        let std_at = flags.iter().position(|f| *f == std_flag).expect("std sources remapped");
        assert!(flags[std_at..].iter().all(|f| f.ends_with(&format!("=/rustc/{COMMIT}"))));
        // Prepared checkout sources are remapped the same way.
        let prepared = Path::new("/r/target/build-libs/std-src/c/library");
        let checkout = StdSource::Checkout("/trust".into());
        assert_eq!(admitted.std_library(&checkout, Some(prepared)), prepared);
        let flags = admitted.remap_flags(&host, prepared).unwrap();
        assert_eq!(
            flags.last().unwrap(),
            &format!("--remap-path-prefix=/r/target/build-libs/std-src/c=/rustc/{COMMIT}")
        );
        let _ = fs::remove_dir_all(seal.ancestors().nth(3).unwrap());
    }

    #[test]
    fn the_toolchain_link_points_at_the_seal_and_is_replaced() {
        let seal = seal("link");
        let targo = seal.join("bin/targo");
        let admitted = admit(compiler(&seal), &launch(TRUST_VV, &targo)).unwrap();
        let sysroot = seal.ancestors().nth(3).unwrap().join("target/trust-mc");
        fs::create_dir_all(&sysroot).unwrap();
        #[cfg(unix)]
        std::os::unix::fs::symlink("/elsewhere", sysroot.join(TOOLCHAIN_LINK)).unwrap();
        admitted.link_toolchain(&sysroot).unwrap();
        assert_eq!(fs::read_link(sysroot.join(TOOLCHAIN_LINK)).unwrap(), seal);
        assert_eq!(admitted.cargo_env(), vec![("MC_RELEASE_BUNDLE".to_string(), "1".into())]);
        let _ = fs::remove_dir_all(seal.ancestors().nth(3).unwrap());
    }
}
