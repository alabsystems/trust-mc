// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Which compiler `build-dev` (and `bundle`) builds trust-mc with, and where its
//! `-Z build-std` library builds read the standard-library sources.
//!
//! `build-dev` rebuilds std with the trust-mc-compiler driver, so cargo needs the
//! library sources of the exact compiler commit the driver links. A toolchain
//! that ships them (`lib/rustlib/src/rust/library`: rustup's `rust-src`, or a
//! Trust seal's `trust-src`) serves them as `-Z build-std` always did. A Trust
//! seal that ships none -- seal 9192 has no `lib/rustlib/src` -- is served the
//! way `build-keyed --trust-checkout` is (keyed.rs): `library/` and the paths it
//! resolves outside itself are extracted by `git archive` from a trust checkout
//! at the compiler's own `commit-hash`, and cargo reads them through
//! `__CARGO_TESTS_ONLY_SRC_ROOT`. Nothing is taken from another revision: a
//! checkout without that commit is refused, and after the binaries are built the
//! driver itself must report the same commit.

use crate::keyed::{TRUST_SRC_COMPONENT, materialize_sources, require_commit, run_capture};
use crate::sysroot::trust_mc_repo_root;
use anyhow::{Context, Result, bail, format_err};
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Environment spelling of `build-dev --trust-checkout`, for gate scripts that run
/// a bare `targo --unverified build-dev`.
pub(crate) const TRUST_CHECKOUT_ENV: &str = "TRUST_MC_TRUST_CHECKOUT";
/// Records which commit and tree an extracted source directory holds.
const STAMP: &str = ".build-dev-std-source";

/// The compiler cargo builds trust-mc with, as it reports itself.
#[derive(Debug)]
pub(crate) struct DevCompiler {
    /// What was run (`$RUSTC`, or the trustc beside the launching `$CARGO`).
    pub(crate) rustc: PathBuf,
    /// First line of `-vV`.
    pub(crate) version: String,
    /// `commit-hash:` of `-vV`, when the compiler reports one.
    pub(crate) commit: Option<String>,
    /// `--print sysroot`.
    pub(crate) sysroot: PathBuf,
}

impl DevCompiler {
    /// Where a toolchain that ships its library sources keeps them.
    fn sysroot_library(&self) -> PathBuf {
        self.sysroot.join(TRUST_SRC_COMPONENT).join("library")
    }

    fn sysroot_ships_library(&self) -> bool {
        self.sysroot_library().join("Cargo.lock").is_file()
    }
}

/// Run `rustc -vV` and `rustc --print sysroot`.
pub(crate) fn probe_compiler(rustc: &OsStr) -> Result<DevCompiler> {
    let shown = Path::new(rustc).display().to_string();
    let verbose = run_capture(Command::new(rustc).arg("-vV"), &format!("{shown} -vV"))?;
    let probe = crate::keyed::parse_verbose_version(&verbose)?;
    let sysroot = run_capture(
        Command::new(rustc).args(["--print", "sysroot"]),
        &format!("{shown} --print sysroot"),
    )?;
    let sysroot = PathBuf::from(sysroot.trim());
    if !sysroot.is_dir() {
        bail!("{shown} reports a sysroot that does not exist: {}", sysroot.display());
    }
    Ok(DevCompiler {
        rustc: PathBuf::from(rustc),
        version: probe.version,
        commit: probe.commit_hash,
        sysroot,
    })
}

/// trust-mc-compiler is a rustc driver (`#![feature(rustc_private)]`), so the
/// toolchain must carry `librustc_driver` (rustc-dev). A Trust seal ships it as
/// part of the seal; a missing one means a damaged seal, not a component to add.
/// This replaces a `rustup component list` probe: nothing here depends on rustup.
pub(crate) fn require_rustc_dev(compiler: &DevCompiler) -> Result<()> {
    let rustlib = compiler.sysroot.join("lib/rustlib");
    let has_driver = fs::read_dir(&rustlib).is_ok_and(|triples| {
        triples.flatten().any(|triple| {
            fs::read_dir(triple.path().join("lib")).is_ok_and(|files| {
                files
                    .flatten()
                    .any(|file| file.file_name().to_string_lossy().starts_with("librustc_driver"))
            })
        })
    });
    if !has_driver {
        bail!(
            "{} ({}) has no librustc_driver under {}: trust-mc-compiler is a rustc driver and \
             links the compiler's internal crates (rustc-dev). The Trust seal ships them; \
             check it with `aterm pkg doctor` (repair: `aterm pkg repair`).",
            compiler.rustc.display(),
            compiler.version,
            rustlib.display()
        );
    }
    Ok(())
}

/// Where `-Z build-std` reads the standard-library sources.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum StdSource {
    /// The toolchain's own `lib/rustlib/src/rust/library`.
    Sysroot,
    /// A trust git checkout that contains the compiler's commit.
    Checkout(PathBuf),
}

/// The checkouts `build-dev` may take the sources from, most explicit first.
#[derive(Debug, Default)]
pub(crate) struct CheckoutCandidates {
    /// `--trust-checkout`.
    pub(crate) flag: Option<PathBuf>,
    /// `TRUST_MC_TRUST_CHECKOUT`.
    pub(crate) env: Option<PathBuf>,
    /// The trust superproject this repository is a submodule of, if any.
    pub(crate) superproject: Option<PathBuf>,
}

impl CheckoutCandidates {
    /// `flag`, the environment and the superproject of this repository.
    pub(crate) fn discover(flag: Option<&Path>) -> Self {
        CheckoutCandidates {
            flag: flag.map(Path::to_path_buf),
            env: std::env::var_os(TRUST_CHECKOUT_ENV)
                .filter(|value| !value.is_empty())
                .map(PathBuf::from),
            superproject: superproject_of(&trust_mc_repo_root()),
        }
    }
}

/// `git rev-parse --show-superproject-working-tree`: `first-party/trust-mc` in a
/// trust checkout answers with that checkout.
fn superproject_of(repo: &Path) -> Option<PathBuf> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(["rev-parse", "--show-superproject-working-tree"])
        .output()
        .ok()
        .filter(|output| output.status.success())?;
    let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
    (!path.is_empty()).then(|| PathBuf::from(path))
}

/// Choose the source. An explicit checkout (flag, then environment) wins and must
/// hold the commit; otherwise the sysroot's own sources; otherwise the
/// superproject when it holds the commit. `holds_commit` is injected so the
/// order is testable without git.
pub(crate) fn choose_std_source(
    compiler: &DevCompiler,
    candidates: &CheckoutCandidates,
    holds_commit: &dyn Fn(&Path, &str) -> Result<()>,
) -> Result<StdSource> {
    let explicit = candidates
        .flag
        .as_ref()
        .map(|path| (path, "--trust-checkout"))
        .or_else(|| candidates.env.as_ref().map(|path| (path, TRUST_CHECKOUT_ENV)));
    if let Some((checkout, origin)) = explicit {
        let commit = required_commit(compiler)?;
        holds_commit(checkout, commit).with_context(|| {
            format!("{origin} {} cannot supply the library sources", checkout.display())
        })?;
        return Ok(StdSource::Checkout(checkout.clone()));
    }
    if compiler.sysroot_ships_library() {
        return Ok(StdSource::Sysroot);
    }
    let mut tried = String::new();
    if let (Some(superproject), Some(commit)) = (&candidates.superproject, &compiler.commit) {
        match holds_commit(superproject, commit) {
            Ok(()) => return Ok(StdSource::Checkout(superproject.clone())),
            Err(error) => {
                tried = format!(
                    "\nThe trust superproject {} was tried and refused: {error:#}",
                    superproject.display()
                );
            }
        }
    }
    bail!(
        "{} ({}) ships no standard-library sources ({} is missing), and `-Z build-std` \
         needs them to rebuild std with trust-mc-compiler.{tried}\n\
         Name a trust checkout that contains the compiler's commit {}:\n    \
         targo --unverified build-dev --trust-checkout <trust checkout>\n\
         (or set {TRUST_CHECKOUT_ENV}); `--skip-libs` builds only the binaries.",
        compiler.rustc.display(),
        compiler.version,
        compiler.sysroot_library().join("Cargo.lock").display(),
        compiler.commit.as_deref().unwrap_or("<the compiler reports no commit-hash>"),
    )
}

fn required_commit(compiler: &DevCompiler) -> Result<&str> {
    compiler.commit.as_deref().ok_or_else(|| {
        format_err!(
            "{} ({}) reports no commit-hash in `-vV`, so no checkout revision can be matched \
             to it",
            compiler.rustc.display(),
            compiler.version
        )
    })
}

/// `holds_commit` for [`choose_std_source`]: the top level of a git checkout that
/// contains `commit`.
pub(crate) fn checkout_holds_commit(checkout: &Path, commit: &str) -> Result<()> {
    require_commit(checkout, commit).map(drop)
}

/// Refuse unless the built driver reports the commit the sources were chosen for:
/// std rebuilt from another commit's sources would not be the std the driver's
/// own compiler expects.
pub(crate) fn require_driver_commit(compiler: &DevCompiler, driver: &Path) -> Result<()> {
    let expected = required_commit(compiler)?;
    let verbose =
        run_capture(Command::new(driver).arg("-vV"), &format!("{} -vV", driver.display()))?;
    let reported = crate::keyed::parse_verbose_version(&verbose)?.commit_hash;
    if reported.as_deref() != Some(expected) {
        bail!(
            "{} reports commit {}, but the std sources were chosen for {expected} ({}); \
             build trust-mc and its library with one toolchain",
            driver.display(),
            reported.as_deref().unwrap_or("<none>"),
            compiler.rustc.display()
        );
    }
    Ok(())
}

/// Make the chosen sources available. Returns the directory to hand cargo as
/// `__CARGO_TESTS_ONLY_SRC_ROOT`, or `None` when the sysroot serves them.
///
/// A checkout's sources are extracted once per commit into
/// `target/build-libs/std-src/<commit>` and reused while the stamp names the same
/// commit and tree, so an unchanged std is not rebuilt on every `build-dev`.
pub(crate) fn prepare_std_source(
    source: &StdSource,
    compiler: &DevCompiler,
    cargo: &OsStr,
) -> Result<Option<PathBuf>> {
    let StdSource::Checkout(checkout) = source else {
        return Ok(None);
    };
    let commit = required_commit(compiler)?;
    let tree = require_commit(checkout, commit)?;
    let src = trust_mc_repo_root().join("target/build-libs/std-src").join(commit);
    let stamp = stamp_text(commit, &tree);
    let library = src.join("library");
    if fs::read_to_string(src.join(STAMP)).is_ok_and(|text| text == stamp)
        && library.join("Cargo.lock").is_file()
    {
        println!("-- std sources: {} at {commit} (reused {})", checkout.display(), src.display());
        return Ok(Some(library));
    }
    let tree_record =
        materialize_sources(Path::new(cargo), &compiler.rustc, checkout, commit, &src)?;
    fs::write(src.join(STAMP), &stamp)
        .with_context(|| format!("cannot write {}", src.join(STAMP).display()))?;
    println!("-- std sources: {}", tree_record.describe());
    Ok(Some(library))
}

fn stamp_text(commit: &str, tree: &str) -> String {
    format!("commit={commit}\ntree={tree}\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    const COMMIT: &str = "321aaeda75478038420d97830f14724c33c8dc39";

    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir()
            .join(format!("build-trust-mc-dev-std-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn compiler(sysroot: &Path, commit: Option<&str>) -> DevCompiler {
        DevCompiler {
            rustc: sysroot.join("bin/trustc"),
            version: "rustc 1.99.0-dev (321aaeda7 2026-09-17)".to_string(),
            commit: commit.map(str::to_string),
            sysroot: sysroot.to_path_buf(),
        }
    }

    fn ship_library(sysroot: &Path) {
        let library = sysroot.join(TRUST_SRC_COMPONENT).join("library");
        fs::create_dir_all(&library).unwrap();
        fs::write(library.join("Cargo.lock"), "").unwrap();
    }

    fn holds(ok: &'static [&'static str]) -> impl Fn(&Path, &str) -> Result<()> {
        move |path: &Path, commit: &str| {
            assert_eq!(commit, COMMIT);
            if ok.iter().any(|p| Path::new(p) == path) {
                Ok(())
            } else {
                bail!("{} does not contain {commit}", path.display())
            }
        }
    }

    #[test]
    fn a_sysroot_that_ships_its_sources_needs_no_checkout() {
        let sysroot = scratch("ships");
        ship_library(&sysroot);
        let chosen = choose_std_source(
            &compiler(&sysroot, Some(COMMIT)),
            &CheckoutCandidates { superproject: Some("/trust".into()), ..Default::default() },
            &holds(&["/trust"]),
        )
        .unwrap();
        assert_eq!(chosen, StdSource::Sysroot);
    }

    #[test]
    fn an_explicit_checkout_wins_and_must_hold_the_commit() {
        let sysroot = scratch("explicit");
        ship_library(&sysroot);
        let flag = CheckoutCandidates {
            flag: Some("/flag".into()),
            env: Some("/env".into()),
            superproject: None,
        };
        let chosen =
            choose_std_source(&compiler(&sysroot, Some(COMMIT)), &flag, &holds(&["/flag"]))
                .unwrap();
        assert_eq!(chosen, StdSource::Checkout("/flag".into()));

        let env = CheckoutCandidates { env: Some("/env".into()), ..Default::default() };
        let chosen =
            choose_std_source(&compiler(&sysroot, Some(COMMIT)), &env, &holds(&["/env"])).unwrap();
        assert_eq!(chosen, StdSource::Checkout("/env".into()));

        // A named checkout without the commit is refused, never passed over.
        let error =
            choose_std_source(&compiler(&sysroot, Some(COMMIT)), &flag, &holds(&[])).unwrap_err();
        assert!(format!("{error:#}").contains("--trust-checkout /flag"), "{error:#}");
    }

    #[test]
    fn a_seal_without_sources_falls_to_the_superproject_holding_the_commit() {
        let sysroot = scratch("superproject");
        let candidates =
            CheckoutCandidates { superproject: Some("/trust".into()), ..Default::default() };
        let chosen =
            choose_std_source(&compiler(&sysroot, Some(COMMIT)), &candidates, &holds(&["/trust"]))
                .unwrap();
        assert_eq!(chosen, StdSource::Checkout("/trust".into()));
    }

    #[test]
    fn no_source_at_all_is_refused_with_the_fix() {
        let sysroot = scratch("none");
        let candidates =
            CheckoutCandidates { superproject: Some("/trust".into()), ..Default::default() };
        let error = choose_std_source(&compiler(&sysroot, Some(COMMIT)), &candidates, &holds(&[]))
            .unwrap_err()
            .to_string();
        assert!(error.contains("--trust-checkout <trust checkout>"), "{error}");
        assert!(error.contains(TRUST_CHECKOUT_ENV), "{error}");
        assert!(error.contains(COMMIT), "{error}");
        assert!(error.contains("/trust was tried and refused"), "{error}");
        assert!(!error.contains("rustup"), "no stock remedy: {error}");
    }

    #[test]
    fn a_compiler_without_a_commit_cannot_be_matched_to_a_checkout() {
        let sysroot = scratch("nocommit");
        let flag = CheckoutCandidates { flag: Some("/flag".into()), ..Default::default() };
        let error =
            choose_std_source(&compiler(&sysroot, None), &flag, &holds(&["/flag"])).unwrap_err();
        assert!(error.to_string().contains("reports no commit-hash"), "{error}");
    }

    #[test]
    fn rustc_dev_is_found_in_the_sysroot_itself() {
        let sysroot = scratch("rustcdev");
        assert!(require_rustc_dev(&compiler(&sysroot, Some(COMMIT))).is_err());
        let lib = sysroot.join("lib/rustlib/aarch64-apple-darwin/lib");
        fs::create_dir_all(&lib).unwrap();
        fs::write(lib.join("librustc_driver-6fb93c367b721e46.dylib"), "").unwrap();
        require_rustc_dev(&compiler(&sysroot, Some(COMMIT))).unwrap();
    }

    #[test]
    fn the_stamp_names_commit_and_tree() {
        assert_eq!(stamp_text("c", "t"), "commit=c\ntree=t\n");
    }
}
