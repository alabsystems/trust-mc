// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Installation detection and path resolution.
//!
//! Determines whether trust-mc is running from a development repo or a release bundle,
//! and provides paths to compiler binaries, sysroot libraries, and toolchain info.
//!
//! Zero coupling to `KaniSession` or process execution. Uses `std::path`, `std::env`, `anyhow`.

use super::trustc_route::TrustcRouteError;
use crate::args::compiler_route::{CompilerRouteArgs, CompilerRouteKind};
use anyhow::{Context, Result, bail};
use std::ffi::OsString;
use std::path::{Path, PathBuf};

const TRUST_MC_SYSROOT_ENV_VAR: &str = "TRUST_MC_SYSROOT";
/// The canonical trustc of the Trustc route, when `--trustc` is not given.
pub(crate) const TRUST_MC_TRUSTC_ENV_VAR: &str = "TRUST_MC_TRUSTC";
/// The backend dylib of the Trustc route, when `--backend-dylib` is not given.
pub(crate) const TRUST_MC_BACKEND_DYLIB_ENV_VAR: &str = "TRUST_MC_BACKEND_DYLIB";

/// Which compiler builds the crates under verification (T1-D1).
///
/// Both routes feed the same file-based pipeline (kani-metadata.json, `.smt2`,
/// `.vc.json`, `run_ay`); they differ only in the program that runs and its flags.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CompilerRoute {
    /// `trust-mc-compiler --kani-compiler`, resolved from [`InstallType`] at the
    /// point of use so lanes that never compile do not need it installed.
    DevCli,
    /// Canonical `trustc -Zcodegen-backend=<backend> -Ztrust-verify=off` against
    /// the Kani library of `key_dir`, the KEY directory `TRUST_MC_SYSROOT` names.
    /// All three paths are canonical. On this route a `TRUST_MC_SYSROOT` layout
    /// needs no `bin/trust-mc-compiler`.
    Trustc { trustc: PathBuf, backend: PathBuf, key_dir: PathBuf },
}

impl CompilerRoute {
    pub(crate) fn resolve(args: &CompilerRouteArgs) -> Result<Self, TrustcRouteError> {
        Self::resolve_with(args, |name| std::env::var_os(name))
    }

    /// [`Self::resolve`] with the environment injected. Flags win over the
    /// environment, an empty variable counts as unset, and the DevCli route
    /// reads nothing at all. The identity preflight is not run here.
    pub(crate) fn resolve_with(
        args: &CompilerRouteArgs,
        env: impl Fn(&str) -> Option<OsString>,
    ) -> Result<Self, TrustcRouteError> {
        if args.compiler_route == CompilerRouteKind::DevCli {
            return Ok(CompilerRoute::DevCli);
        }
        let from_env = |name: &str| env(name).filter(|value| !value.is_empty()).map(PathBuf::from);
        let trustc = required_trustc(args, &from_env)?;
        let backend =
            args.backend_dylib.clone().or_else(|| from_env(TRUST_MC_BACKEND_DYLIB_ENV_VAR)).ok_or(
                TrustcRouteError::MissingInput {
                    what: "backend dylib",
                    flag: Some("--backend-dylib"),
                    env: TRUST_MC_BACKEND_DYLIB_ENV_VAR,
                },
            )?;
        let key_dir = required_key_dir(&from_env)?;
        Ok(CompilerRoute::Trustc {
            trustc: canonical_route_path("trustc", &trustc, false)?,
            backend: canonical_route_path("backend dylib", &backend, false)?,
            key_dir: canonical_route_path("KEY directory", &key_dir, true)?,
        })
    }
}

/// The compiler route of concrete playback.
///
/// Playback builds a real test executable and never loads the engine backend, so
/// its Trustc form has no backend dylib: `--backend-dylib` is refused at argument
/// validation and `TRUST_MC_BACKEND_DYLIB` is never read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PlaybackRoute {
    /// trust-mc-compiler without `--kani-compiler`.
    DevCli,
    /// Canonical trustc against the playback library of `key_dir`.
    Trustc { trustc: PathBuf, key_dir: PathBuf },
}

impl PlaybackRoute {
    pub(crate) fn resolve(args: &CompilerRouteArgs) -> Result<Self, TrustcRouteError> {
        Self::resolve_with(args, |name| std::env::var_os(name))
    }

    /// [`Self::resolve`] with the environment injected, under the same rules as
    /// [`CompilerRoute::resolve_with`] minus the backend.
    pub(crate) fn resolve_with(
        args: &CompilerRouteArgs,
        env: impl Fn(&str) -> Option<OsString>,
    ) -> Result<Self, TrustcRouteError> {
        if args.compiler_route == CompilerRouteKind::DevCli {
            return Ok(PlaybackRoute::DevCli);
        }
        let from_env = |name: &str| env(name).filter(|value| !value.is_empty()).map(PathBuf::from);
        let trustc = required_trustc(args, &from_env)?;
        let key_dir = required_key_dir(&from_env)?;
        Ok(PlaybackRoute::Trustc {
            trustc: canonical_route_path("trustc", &trustc, false)?,
            key_dir: canonical_route_path("KEY directory", &key_dir, true)?,
        })
    }

    /// As [`CompilerRoute::library_folder`].
    pub(crate) fn library_folder(&self, subdir: &str) -> Result<PathBuf> {
        match self {
            PlaybackRoute::DevCli => {
                library_folder_with_sysroot(subdir, trust_mc_sysroot().as_deref())
            }
            PlaybackRoute::Trustc { key_dir, .. } => {
                library_folder_with_sysroot(subdir, Some(key_dir))
            }
        }
    }
}

/// The cargo `cargo locate-project` runs on the Trustc route, before any session
/// exists (`args_toml`): the seal cargo in the directory of the canonical trustc,
/// which the preflight later requires to be `<sysroot>/bin`, with the route's cargo
/// environment. `locate-project` compiles nothing, so no preflight runs here.
pub(crate) fn trustc_route_locate_cargo(args: &CompilerRouteArgs) -> Result<std::process::Command> {
    Ok(trustc_route_locate_cargo_with(args, std::env::vars_os().collect())?)
}

/// [`trustc_route_locate_cargo`] with the environment passed in.
pub(crate) fn trustc_route_locate_cargo_with(
    args: &CompilerRouteArgs,
    env: Vec<(OsString, OsString)>,
) -> Result<std::process::Command, TrustcRouteError> {
    use super::trustc_route::{
        apply_env_edits, refuse_rustc_wrappers, seal_cargo_in, trustc_cargo_env,
    };
    refuse_rustc_wrappers(env.iter().map(|(key, value)| (key, value)))?;
    let from_env = |name: &str| {
        env.iter()
            .find(|(key, _)| key.as_os_str() == std::ffi::OsStr::new(name))
            .map(|(_, value)| value.clone())
            .filter(|value| !value.is_empty())
            .map(PathBuf::from)
    };
    let trustc = canonical_route_path("trustc", &required_trustc(args, &from_env)?, false)?;
    let sysroot =
        trustc.parent().and_then(Path::parent).ok_or_else(|| TrustcRouteError::BadPath {
            what: "trustc",
            path: trustc.clone(),
            detail: "is not in a <sysroot>/bin directory".to_string(),
        })?;
    let mut cmd = std::process::Command::new(seal_cargo_in(sysroot)?);
    apply_env_edits(&mut cmd, trustc_cargo_env(&trustc, env.into_iter().map(|(key, _)| key)));
    Ok(cmd)
}

fn required_trustc(
    args: &CompilerRouteArgs,
    from_env: &impl Fn(&str) -> Option<PathBuf>,
) -> Result<PathBuf, TrustcRouteError> {
    args.trustc.clone().or_else(|| from_env(TRUST_MC_TRUSTC_ENV_VAR)).ok_or(
        TrustcRouteError::MissingInput {
            what: "trustc binary",
            flag: Some("--trustc"),
            env: TRUST_MC_TRUSTC_ENV_VAR,
        },
    )
}

fn required_key_dir(
    from_env: &impl Fn(&str) -> Option<PathBuf>,
) -> Result<PathBuf, TrustcRouteError> {
    from_env(TRUST_MC_SYSROOT_ENV_VAR).ok_or(TrustcRouteError::MissingInput {
        what: "KEY directory",
        flag: None,
        env: TRUST_MC_SYSROOT_ENV_VAR,
    })
}

impl CompilerRoute {
    /// The Kani library folder `subdir` (`lib`, `no_core/lib`, `playback/lib`) this
    /// route compiles against. On Trustc it is under the canonical KEY directory the
    /// preflight checked, never re-read from `TRUST_MC_SYSROOT`: a relative value
    /// resolves against whatever directory cargo runs rustc in, which need not be
    /// the KEY the preflight accepted. DevCli keeps `TRUST_MC_SYSROOT` or the install.
    pub(crate) fn library_folder(&self, subdir: &str) -> Result<PathBuf> {
        match self {
            CompilerRoute::DevCli => {
                library_folder_with_sysroot(subdir, trust_mc_sysroot().as_deref())
            }
            CompilerRoute::Trustc { key_dir, .. } => {
                library_folder_with_sysroot(subdir, Some(key_dir))
            }
        }
    }
}

fn canonical_route_path(
    what: &'static str,
    path: &Path,
    directory: bool,
) -> Result<PathBuf, TrustcRouteError> {
    let bad = |detail: String| TrustcRouteError::BadPath { what, path: path.to_path_buf(), detail };
    let canonical = path.canonicalize().map_err(|error| bad(error.to_string()))?;
    match (directory, canonical.is_dir()) {
        (true, false) => Err(bad("is not a directory".to_string())),
        (false, true) => Err(bad("is a directory, not a file".to_string())),
        _ => Ok(canonical),
    }
}

/// Represents where we detected trust_mc, with helper methods for using that information to find critical paths
pub(crate) enum InstallType {
    /// We're operating in a a checked out repo that's been built locally.
    /// The path here is to the root of the repo.
    DevRepo(PathBuf),
    /// We're operating from a release bundle (made with `build-trust-mc release`).
    /// The path here to where this release bundle has been unpacked.
    Release(PathBuf),
}

impl InstallType {
    pub(crate) fn new() -> Result<Self> {
        let sysroot = trust_mc_sysroot();
        Self::new_with_sysroot(sysroot.as_deref())
    }

    fn new_with_sysroot(sysroot: Option<&Path>) -> Result<Self> {
        if let Some(sysroot) = sysroot {
            return Ok(InstallType::Release(sysroot.to_path_buf()));
        }

        let path = bin_folder()?;
        if let Some(root) = dev_repo_root_from_bin_dir(&path) {
            Ok(InstallType::DevRepo(root))
        } else if path.ends_with("bin") {
            Ok(InstallType::Release(
                path.parent().expect("bin directory should have a parent").to_path_buf(),
            ))
        } else {
            bail!(
                "Unable to determine installation location. {} doesn't look typical",
                path.display()
            )
        }
    }

    pub(crate) fn kani_compiler(&self) -> Result<PathBuf> {
        match self {
            Self::DevRepo(_) => {
                // Use bin_folder to hide debug/release differences.
                let path = bin_folder()?.join("trust-mc-compiler");
                expect_path(path)
            }
            Self::Release(release) => {
                let path = release.join("bin/trust-mc-compiler");
                expect_path(path)
            }
        }
    }
}

/// Return the path for the folder where the current executable is located.
fn bin_folder() -> Result<PathBuf> {
    let exe = std::env::current_exe().context("Cannot determine current executable location")?;
    let dir = exe.parent().context("Executable isn't in a directory")?.to_owned();
    Ok(dir)
}

fn dev_repo_root_from_bin_dir(path: &Path) -> Option<PathBuf> {
    if path.ends_with("target/trust-mc/bin") {
        return path.parent()?.parent()?.parent().map(Path::to_path_buf);
    }

    let profile = path.file_name()?.to_str()?;
    if profile != "debug" && profile != "release" {
        return None;
    }

    let parent = path.parent()?;
    let parent_name = parent.file_name()?.to_str()?;
    if parent_name == "target" {
        return parent.parent().map(Path::to_path_buf);
    }

    if parent_name.starts_with("worker_") {
        let target_dir = parent.parent()?;
        if target_dir.file_name()?.to_str()? == "target" {
            return target_dir.parent().map(Path::to_path_buf);
        }
    }

    let target_dir = parent.parent()?;
    if target_dir.file_name()?.to_str()? == "target" {
        return target_dir.parent().map(Path::to_path_buf);
    }

    None
}

pub(super) fn trust_mc_sysroot() -> Option<PathBuf> {
    std::env::var_os(TRUST_MC_SYSROOT_ENV_VAR).map(PathBuf::from)
}

pub(super) fn release_cargo_path(root: &Path) -> PathBuf {
    root.join("toolchain").join("bin").join("targo")
}

fn sysroot_override_subdir(sysroot: Option<&Path>, subdir: &str) -> Result<Option<PathBuf>> {
    let Some(sysroot) = sysroot else {
        return Ok(None);
    };
    let path = sysroot.join(subdir);
    if path.exists() {
        Ok(Some(path))
    } else {
        bail!(
            "{TRUST_MC_SYSROOT_ENV_VAR} set to {} but {} does not exist",
            sysroot.display(),
            path.display()
        );
    }
}

/// Return the path for the folder where the pre-compiled rust libraries are located.
pub(crate) fn lib_folder() -> Result<PathBuf> {
    let sysroot = trust_mc_sysroot();
    library_folder_with_sysroot("lib", sysroot.as_deref())
}

// Keep the process-environment read at the public boundary. Tests inject the
// override here instead of mutating process-global state shared with other tests.
fn library_folder_with_sysroot(subdir: &str, sysroot: Option<&Path>) -> Result<PathBuf> {
    if let Some(path) = sysroot_override_subdir(sysroot, subdir)? {
        return Ok(path);
    }
    let install = InstallType::new_with_sysroot(sysroot)?;
    match install {
        InstallType::DevRepo(root) => Ok(root.join("target/trust-mc").join(subdir)),
        InstallType::Release(root) => Ok(root.join(subdir)),
    }
}

/// The sysroot of the toolchain that built this driver (`build.rs`: `$RUSTC
/// --print sysroot`). `build-dev` builds trust-mc-compiler in the same cargo
/// invocation, so this is the toolchain the compiler links, and its `bin/cargo`
/// is the cargo DevCli runs (`session/cargo.rs`). `None` when the build script
/// could not ask the compiler; nothing then substitutes another toolchain.
pub(crate) fn build_toolchain_sysroot() -> Option<PathBuf> {
    option_env!("MC_DRIVER_BUILD_SYSROOT").filter(|sysroot| !sysroot.is_empty()).map(PathBuf::from)
}

/// A quick helper to say "hey, we expected this thing to be here but it's not!"
fn expect_path(path: PathBuf) -> Result<PathBuf> {
    if path.exists() {
        Ok(path)
    } else {
        bail!(
            "Unable to find {}. Looked for {}",
            path.file_name().map(|n| n.to_string_lossy()).unwrap_or_default(),
            path.display()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{
        CompilerRoute, InstallType, PlaybackRoute, TRUST_MC_BACKEND_DYLIB_ENV_VAR,
        TRUST_MC_SYSROOT_ENV_VAR, TRUST_MC_TRUSTC_ENV_VAR, dev_repo_root_from_bin_dir,
        library_folder_with_sysroot,
    };
    use crate::args::compiler_route::{CompilerRouteArgs, CompilerRouteKind};
    use crate::session::trustc_route::TrustcRouteError;
    use std::ffi::OsString;
    use std::path::{Path, PathBuf};
    use tempfile::TempDir;

    struct RouteFixture {
        tmp: TempDir,
        trustc: PathBuf,
        backend: PathBuf,
        key_dir: PathBuf,
    }

    fn route_fixture() -> RouteFixture {
        let tmp = TempDir::new().unwrap();
        let bin = tmp.path().join("Application Support/store/trust/8571/bin");
        let key_dir = tmp.path().join("keyed/driver-948b36c62eacc5d1");
        std::fs::create_dir_all(&bin).unwrap();
        std::fs::create_dir_all(key_dir.join("codegen-backends")).unwrap();
        let trustc = bin.join("trustc");
        let backend = key_dir.join("codegen-backends/librustc_codegen_trust_mc.dylib");
        std::fs::write(&trustc, "").unwrap();
        std::fs::write(&backend, "").unwrap();
        RouteFixture { tmp, trustc, backend, key_dir }
    }

    fn trustc_args(trustc: Option<&Path>, backend: Option<&Path>) -> CompilerRouteArgs {
        CompilerRouteArgs {
            compiler_route: CompilerRouteKind::Trustc,
            trustc: trustc.map(Path::to_path_buf),
            backend_dylib: backend.map(Path::to_path_buf),
        }
    }

    fn env_of(pairs: Vec<(&'static str, PathBuf)>) -> impl Fn(&str) -> Option<OsString> {
        move |name| {
            pairs.iter().find(|(key, _)| *key == name).map(|(_, value)| value.clone().into())
        }
    }

    #[test]
    fn compiler_route_dev_cli_is_the_default_and_reads_no_environment() {
        let args = CompilerRouteArgs {
            compiler_route: CompilerRouteKind::default(),
            trustc: None,
            backend_dylib: None,
        };
        let route = CompilerRoute::resolve_with(&args, |name: &str| -> Option<OsString> {
            panic!("the DevCli route read {name}")
        })
        .unwrap();
        assert_eq!(route, CompilerRoute::DevCli);
    }

    #[test]
    fn compiler_route_trustc_prefers_flags_over_environment_and_canonicalizes() {
        let f = route_fixture();
        let relative_backend =
            f.key_dir.join("codegen-backends/../codegen-backends/librustc_codegen_trust_mc.dylib");
        let env = env_of(vec![
            (TRUST_MC_TRUSTC_ENV_VAR, PathBuf::from("/nonexistent/trustc")),
            (TRUST_MC_BACKEND_DYLIB_ENV_VAR, PathBuf::from("/nonexistent/backend.dylib")),
            (TRUST_MC_SYSROOT_ENV_VAR, f.key_dir.clone()),
        ]);
        let route = CompilerRoute::resolve_with(
            &trustc_args(Some(&f.trustc), Some(&relative_backend)),
            env,
        )
        .unwrap();
        assert_eq!(
            route,
            CompilerRoute::Trustc {
                trustc: f.trustc.canonicalize().unwrap(),
                backend: f.backend.canonicalize().unwrap(),
                key_dir: f.key_dir.canonicalize().unwrap(),
            }
        );
    }

    #[test]
    fn compiler_route_trustc_falls_back_to_the_environment() {
        let f = route_fixture();
        let env = env_of(vec![
            (TRUST_MC_TRUSTC_ENV_VAR, f.trustc.clone()),
            (TRUST_MC_BACKEND_DYLIB_ENV_VAR, f.backend.clone()),
            (TRUST_MC_SYSROOT_ENV_VAR, f.key_dir.clone()),
        ]);
        let route = CompilerRoute::resolve_with(&trustc_args(None, None), env).unwrap();
        assert!(matches!(route, CompilerRoute::Trustc { .. }));
    }

    #[test]
    fn compiler_route_playback_needs_no_backend_and_never_reads_its_variable() {
        let f = route_fixture();
        let key_dir = f.key_dir.clone();
        let trustc = f.trustc.clone();
        let env = move |name: &str| -> Option<OsString> {
            match name {
                TRUST_MC_TRUSTC_ENV_VAR => Some(trustc.clone().into()),
                TRUST_MC_SYSROOT_ENV_VAR => Some(key_dir.clone().into()),
                other => panic!("playback read {other}"),
            }
        };
        let route = PlaybackRoute::resolve_with(&trustc_args(None, None), env).unwrap();
        assert_eq!(
            route,
            PlaybackRoute::Trustc {
                trustc: f.trustc.canonicalize().unwrap(),
                key_dir: f.key_dir.canonicalize().unwrap(),
            }
        );
        std::fs::create_dir_all(f.key_dir.join("playback/lib")).unwrap();
        assert_eq!(
            route.library_folder("playback/lib").unwrap(),
            f.key_dir.canonicalize().unwrap().join("playback/lib")
        );
        assert!(matches!(
            PlaybackRoute::resolve_with(
                &trustc_args(Some(&f.trustc), None),
                env_of(vec![(TRUST_MC_SYSROOT_ENV_VAR, PathBuf::new())])
            ),
            Err(TrustcRouteError::MissingInput { env: TRUST_MC_SYSROOT_ENV_VAR, .. })
        ));
        let dev_cli = CompilerRouteArgs {
            compiler_route: CompilerRouteKind::DevCli,
            trustc: None,
            backend_dylib: None,
        };
        assert_eq!(
            PlaybackRoute::resolve_with(&dev_cli, |name: &str| -> Option<OsString> {
                panic!("the DevCli playback route read {name}")
            })
            .unwrap(),
            PlaybackRoute::DevCli
        );
    }

    #[test]
    fn compiler_route_trustc_names_each_missing_input() {
        let f = route_fixture();
        let missing = |args: CompilerRouteArgs, env: Vec<(&'static str, PathBuf)>| {
            match CompilerRoute::resolve_with(&args, env_of(env)) {
                Err(TrustcRouteError::MissingInput { env, .. }) => env,
                other => panic!("expected MissingInput, got {other:?}"),
            }
        };
        let sysroot = vec![(TRUST_MC_SYSROOT_ENV_VAR, f.key_dir.clone())];
        assert_eq!(
            missing(trustc_args(None, Some(&f.backend)), sysroot.clone()),
            TRUST_MC_TRUSTC_ENV_VAR
        );
        assert_eq!(
            missing(trustc_args(Some(&f.trustc), None), sysroot),
            TRUST_MC_BACKEND_DYLIB_ENV_VAR
        );
        assert_eq!(
            missing(
                trustc_args(Some(&f.trustc), Some(&f.backend)),
                vec![(TRUST_MC_SYSROOT_ENV_VAR, PathBuf::new())]
            ),
            TRUST_MC_SYSROOT_ENV_VAR
        );
    }

    #[test]
    fn compiler_route_trustc_refuses_paths_that_are_absent_or_the_wrong_kind() {
        let f = route_fixture();
        let sysroot = || env_of(vec![(TRUST_MC_SYSROOT_ENV_VAR, f.key_dir.clone())]);
        let absent = f.tmp.path().join("absent.dylib");
        assert!(matches!(
            CompilerRoute::resolve_with(&trustc_args(Some(&f.trustc), Some(&absent)), sysroot()),
            Err(TrustcRouteError::BadPath { what: "backend dylib", .. })
        ));
        assert!(matches!(
            CompilerRoute::resolve_with(
                &trustc_args(Some(&f.key_dir), Some(&f.backend)),
                sysroot()
            ),
            Err(TrustcRouteError::BadPath { what: "trustc", .. })
        ));
        assert!(matches!(
            CompilerRoute::resolve_with(
                &trustc_args(Some(&f.trustc), Some(&f.backend)),
                env_of(vec![(TRUST_MC_SYSROOT_ENV_VAR, f.backend.clone())])
            ),
            Err(TrustcRouteError::BadPath { what: "KEY directory", .. })
        ));
    }

    #[test]
    fn compiler_route_trustc_key_layout_needs_no_trust_mc_compiler() {
        let f = route_fixture();
        std::fs::create_dir_all(f.key_dir.join("lib")).unwrap();
        assert!(!f.key_dir.join("bin/trust-mc-compiler").exists());
        assert!(matches!(
            InstallType::new_with_sysroot(Some(&f.key_dir)).unwrap(),
            InstallType::Release(root) if root == f.key_dir
        ));
        assert_eq!(
            library_folder_with_sysroot("lib", Some(&f.key_dir)).unwrap(),
            f.key_dir.join("lib")
        );
    }

    #[test]
    fn compiler_route_trustc_library_folders_come_from_the_canonical_key() {
        let f = route_fixture();
        for subdir in ["lib", "no_core/lib", "playback/lib"] {
            std::fs::create_dir_all(f.key_dir.join(subdir)).unwrap();
        }
        let key_dir = f.key_dir.canonicalize().unwrap();
        let route = CompilerRoute::Trustc {
            trustc: f.trustc.canonicalize().unwrap(),
            backend: f.backend.canonicalize().unwrap(),
            key_dir: key_dir.clone(),
        };
        for subdir in ["lib", "no_core/lib", "playback/lib"] {
            assert_eq!(route.library_folder(subdir).unwrap(), key_dir.join(subdir));
        }
        std::fs::remove_dir_all(key_dir.join("playback")).unwrap();
        let error = route.library_folder("playback/lib").unwrap_err().to_string();
        assert!(error.contains("does not exist"), "{error}");
    }

    #[test]
    fn detects_standard_cargo_dev_repo_root() {
        let root = dev_repo_root_from_bin_dir(Path::new("/repo/trust_mc/target/debug"))
            .expect("standard cargo debug path should resolve");
        assert_eq!(root, Path::new("/repo/trust_mc"));
    }

    #[test]
    fn detects_worker_debug_dev_repo_root() {
        let root = dev_repo_root_from_bin_dir(Path::new("/repo/trust_mc/target/worker_2/debug"))
            .expect("worker debug path should resolve");
        assert_eq!(root, Path::new("/repo/trust_mc"));
    }

    #[test]
    fn detects_worker_release_dev_repo_root() {
        let root = dev_repo_root_from_bin_dir(Path::new("/repo/trust_mc/target/worker_7/release"))
            .expect("worker release path should resolve");
        assert_eq!(root, Path::new("/repo/trust_mc"));
    }

    #[test]
    fn detects_custom_target_dir_dev_repo_root() {
        let root = dev_repo_root_from_bin_dir(Path::new("/repo/trust_mc/target/user/release"))
            .expect("custom target dir should resolve");
        assert_eq!(root, Path::new("/repo/trust_mc"));
    }

    #[test]
    fn trust_mc_sysroot_override_resolves_all_library_roots() {
        let temp = TempDir::new().expect("temp dir should be created");
        std::fs::create_dir_all(temp.path().join("lib")).expect("lib dir should exist");
        std::fs::create_dir_all(temp.path().join("playback/lib"))
            .expect("playback lib dir should exist");
        std::fs::create_dir_all(temp.path().join("no_core/lib"))
            .expect("no_core lib dir should exist");
        assert_eq!(
            library_folder_with_sysroot("lib", Some(temp.path()))
                .expect("override lib should resolve"),
            temp.path().join("lib")
        );
        assert_eq!(
            library_folder_with_sysroot("playback/lib", Some(temp.path()))
                .expect("override playback lib should resolve"),
            temp.path().join("playback/lib")
        );
        assert_eq!(
            library_folder_with_sysroot("no_core/lib", Some(temp.path()))
                .expect("override no_core lib should resolve"),
            temp.path().join("no_core/lib")
        );

        match InstallType::new_with_sysroot(Some(temp.path()))
            .expect("override install type should resolve")
        {
            InstallType::Release(root) => assert_eq!(root, temp.path()),
            InstallType::DevRepo(root) => {
                panic!("expected release-style sysroot override, got dev repo {}", root.display())
            }
        }
    }

    #[test]
    fn trust_mc_sysroot_override_rejects_missing_lib_dir() {
        let temp = TempDir::new().expect("temp dir should be created");

        let err = library_folder_with_sysroot("lib", Some(temp.path()))
            .expect_err("missing override lib dir should error");
        let message = err.to_string();
        assert!(message.contains("TRUST_MC_SYSROOT"), "unexpected error: {message}");
        assert!(
            message.contains("does not exist"),
            "missing-path error should mention missing dir: {message}"
        );
    }
}
