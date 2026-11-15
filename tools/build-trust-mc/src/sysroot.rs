// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module has all the logic to build trust-mc's sysroot folder.
//! In this folder, you can find the following folders:
//! - `bin/`: Where all trust-mc binaries will be located.
//! - `lib/`: trust-mc libraries as well as rust standard libraries.
//!
//! Rustc expects the sysroot to have a specific folder layout:
//! `{SYSROOT}/rustlib/<target-triplet>/lib/<libraries>`
//!
//! Note: We don't cross-compile. Target is the same as the host.

use crate::watchdog::Watchdog;
use crate::{AutoRun, cp};
use anyhow::{Context, Result, bail, format_err};
use cargo_metadata::{Artifact, Message, TargetKind};
use std::ffi::{OsStr, OsString};
use std::fs;
use std::io::BufReader;
use std::path::{Path, PathBuf};
use std::process::{ChildStdout, Command, Stdio};
use std::sync::OnceLock;

/// Packages of the verification and playback library sets.
pub(crate) const VERIFICATION_PACKAGES: [&str; 3] = ["std", "kani", "kani_macros"];
/// Packages of the no_core library set.
pub(crate) const NO_CORE_PACKAGES: [&str; 2] = ["kani_core", "kani_macros"];
/// Cargo arguments of the no_core library set.
pub(crate) const NO_CORE_CARGO_ARGS: [&str; 2] =
    ["--features=kani_macros/no_core", "--features=kani_core/no_core"];
/// Feature argument of the playback library set.
pub(crate) const PLAYBACK_FEATURES: &str =
    "--features=std/concrete_playback,kani/concrete_playback";

macro_rules! path_buf {
    // The arguments are expressions that can be pushed to the PathBuf.
    ($base_path:expr, $($extra_path:expr),+) => {{
        let mut path_buf = PathBuf::from($base_path);
        $(path_buf.push($extra_path);)+
        path_buf
    }};
}

#[cfg(target_os = "linux")]
pub(crate) fn lib_extension() -> &'static str {
    "so"
}

#[cfg(target_os = "macos")]
pub(crate) fn lib_extension() -> &'static str {
    "dylib"
}

/// Returns the path to trust-mc sysroot. I.e.: folder where we store pre-compiled binaries and
/// libraries.
pub(crate) fn trust_mc_sysroot() -> PathBuf {
    trust_mc_repo_root().join("target/trust-mc")
}

/// Return the repository root containing the `tools/build-trust-mc` package.
///
/// Build paths are derived from Cargo's authenticated package metadata instead
/// of project-controlled `TRUST_*` environment entries. Authenticated Targo
/// deliberately rejects those entries because they share the namespace used
/// by verification-authority controls.
pub(crate) fn trust_mc_repo_root() -> PathBuf {
    let mut root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    root.pop();
    root.pop();
    root
}

/// The trust-mc library sources (`kani`, `kani_core`, `kani_macros`, `std`).
fn trust_mc_library_root() -> PathBuf {
    trust_mc_repo_root().join("library")
}

/// Returns the path to where trust-mc and std pre-compiled libraries are stored.
pub(crate) fn trust_mc_sysroot_lib() -> PathBuf {
    path_buf!(trust_mc_sysroot(), "lib")
}

/// Returns the path to where trust-mc libraries for concrete playback is kept.
pub(crate) fn trust_mc_playback_lib() -> PathBuf {
    path_buf!(trust_mc_sysroot(), "playback/lib")
}

/// Returns the path to where trust-mc libraries for no_core is kept.
pub(crate) fn trust_mc_no_core_lib() -> PathBuf {
    path_buf!(trust_mc_sysroot(), "no_core/lib")
}

/// Returns the path to where trust-mc's pre-compiled binaries are stored.
fn trust_mc_sysroot_bin() -> PathBuf {
    path_buf!(trust_mc_sysroot(), "bin")
}

/// Returns the build target
pub(crate) fn build_target() -> &'static str {
    env!("TARGET")
}

/// The cargo for nested builds of this workspace. `targo --unverified run`
/// exports `CARGO` as the absolute path of the Targo that launched this tool
/// (measured on seal 9192: `<seal>/bin/targo`). Run any other way, the build
/// tool is `targo` -- never a bare `cargo`, which on an ALab host is not the
/// Trust toolchain at all.
pub(crate) fn launching_cargo() -> OsString {
    std::env::var_os("CARGO").filter(|cargo| !cargo.is_empty()).unwrap_or_else(|| "targo".into())
}

/// The compiler of the toolchain that launched this tool: `$RUSTC` when set,
/// else the compiler beside the launching `$CARGO` (a Trust seal's `trustc`),
/// else `trustc` from PATH. Never a bare `rustc` looked up on PATH.
pub(crate) fn toolchain_rustc() -> OsString {
    if let Some(rustc) = std::env::var_os("RUSTC").filter(|rustc| !rustc.is_empty()) {
        return rustc;
    }
    toolchain_rustc_beside(std::env::var_os("CARGO").as_deref())
}

fn toolchain_rustc_beside(cargo: Option<&OsStr>) -> OsString {
    let bin = cargo.map(Path::new).and_then(Path::parent).filter(|b| !b.as_os_str().is_empty());
    if let Some(bin) = bin {
        // `trustc` first: a Trust seal ships both names for one binary. A
        // `rustc` beside a cargo with no `trustc` is that toolchain's own
        // compiler -- STOCK-AS-ORACLE: only the frozen
        // Kani-comparison lane (rust-toolchain.legacy.toml) launches this tool
        // from a stock cargo; the Trust lane never reaches this name.
        for name in ["trustc", "rustc"] {
            let candidate = bin.join(format!("{name}{}", std::env::consts::EXE_SUFFIX));
            if candidate.is_file() {
                return candidate.into_os_string();
            }
        }
    }
    OsString::from("trustc")
}

/// A `Command` for a nested build by `cargo`, with Targo's lane named.
///
/// `targo --unverified build-dev` runs this tool with `CARGO` set to Targo
/// itself, and Targo does not propagate its lane to a recursive `$CARGO`
/// ("recursive `$CARGO` invocations must select their own lane"): a nested
/// bare `targo build` refuses with "refuses to create an implicitly unverified
/// artifact" (measured on seal 9192). So a nested Targo is given
/// `--unverified` explicitly -- `build-dev` makes no proof claim, see
/// [`select_unverified_lane`]. Stock cargo takes no lane and gets no flag.
pub(crate) fn nested_cargo(cargo: &OsStr) -> Command {
    let mut cmd = Command::new(cargo);
    if Path::new(cargo).file_stem().is_some_and(|stem| stem == "targo") {
        cmd.arg("--unverified");
    }
    cmd
}

/// Which compiler and cargo a library build uses, and with what flags.
pub(crate) struct LibToolchain {
    pub(crate) cargo: OsString,
    pub(crate) rustc: PathBuf,
    pub(crate) target_dir: PathBuf,
    /// Added to the Kani base rustflags of every target unit.
    pub(crate) target_rustflags: Vec<String>,
    /// `host.rustflags` for build scripts and proc-macros.
    pub(crate) host_rustflags: Vec<String>,
    pub(crate) env: Vec<(String, OsString)>,
    pub(crate) env_remove: Vec<String>,
}

impl LibToolchain {
    /// The `build-dev` lane: the trust-mc-compiler driver as RUSTC.
    fn dev(compiler_path: &Path) -> Self {
        LibToolchain {
            cargo: launching_cargo(),
            rustc: compiler_path.to_path_buf(),
            target_dir: trust_mc_repo_root().join("target/build-libs"),
            target_rustflags: Vec::new(),
            host_rustflags: vec!["--cfg=kani".to_string(), "--cfg=kani_sysroot".to_string()],
            env: Vec::new(),
            env_remove: Vec::new(),
        }
    }
}

/// What the RELEASE build adds to every cargo it spawns (`release.rs`): the
/// `--remap-path-prefix` flags that keep build-host paths out of the shipped
/// bytes, and the environment that tells the binaries' build scripts it is a
/// release (`MC_RELEASE_BUNDLE`). `None` everywhere is the development build.
#[derive(Debug, Default)]
pub(crate) struct ReleaseFlags {
    /// Added to every unit's rustflags, host units included.
    pub(crate) rustflags: Vec<String>,
    pub(crate) env: Vec<(String, OsString)>,
}

impl ReleaseFlags {
    /// Extend `cmd`'s `CARGO_ENCODED_RUSTFLAGS` (the value already set on `cmd`,
    /// else the inherited one) with [`Self::rustflags`], and set [`Self::env`].
    pub(crate) fn apply(&self, cmd: &mut Command) {
        let set_on_cmd = cmd
            .get_envs()
            .find(|(key, _)| *key == "CARGO_ENCODED_RUSTFLAGS")
            .and_then(|(_, value)| value.map(|v| v.to_string_lossy().into_owned()));
        let existing = set_on_cmd.or_else(|| std::env::var("CARGO_ENCODED_RUSTFLAGS").ok());
        let mut flags: Vec<String> = existing
            .filter(|value| !value.is_empty())
            .map(|value| value.split('\x1f').map(str::to_string).collect())
            .unwrap_or_default();
        for flag in &self.rustflags {
            if !flags.contains(flag) {
                flags.push(flag.clone());
            }
        }
        if !flags.is_empty() {
            cmd.env("CARGO_ENCODED_RUSTFLAGS", flags.join("\x1f"));
        }
        for (key, value) in &self.env {
            cmd.env(key, value);
        }
    }
}

/// The cargo variable naming the std sources `-Z build-std` reads instead of
/// `<sysroot>/lib/rustlib/src/rust/library` (see `dev_std.rs`, and `build-keyed`,
/// which sets it the same way).
pub(crate) const STD_SRC_ROOT_ENV: &str = "__CARGO_TESTS_ONLY_SRC_ROOT";

/// Which std libraries accompany a library set under `<lib>/rustlib/<triple>/lib`.
pub(crate) enum StdLibs<'a> {
    /// None (the no_core set).
    None,
    /// Every non-trust-mc library artifact (the `build-dev` lane).
    AllNonTrustMc,
    /// Library artifacts cargo built for the target triple, i.e. under
    /// `<target_dir>/<triple>/`. That is std's whole closure, including its
    /// crates.io dependencies, and excludes host-only proc-macro dependencies
    /// (syn, quote, heck, strum), which cargo builds under `<target_dir>/debug`.
    TargetUnits(&'a Path),
    /// A symlink to the compiler's prebuilt std directory.
    LinkPrebuilt(&'a Path),
}

/// Build the `lib/` folder and `lib-playback/` for the new sysroot.
/// - The `lib/` folder contains the sysroot for verification.
/// - The `lib-playback/` folder contains the sysroot used for playback.
///
/// `std_src_root` is the extracted `library/` the `-Z build-std` builds read
/// (`dev_std::prepare_std_source`); `None` leaves them on the sysroot's own.
/// A release build names it always (the seal's own rust-src when it ships one),
/// and its `release` flags reach every unit, host units included.
pub(crate) fn build_lib(
    bin_folder: &Path,
    std_src_root: Option<&Path>,
    release: Option<&ReleaseFlags>,
) -> Result<()> {
    let mut toolchain = LibToolchain::dev(&bin_folder.join("trust-mc-compiler"));
    // Remove any inherited value: only the source chosen for this compiler counts.
    toolchain.env_remove.push(STD_SRC_ROOT_ENV.to_string());
    if let Some(release) = release {
        toolchain.target_rustflags.extend(release.rustflags.iter().cloned());
        toolchain.host_rustflags.extend(release.rustflags.iter().cloned());
        toolchain.env.extend(release.env.iter().cloned());
    }
    build_no_core_lib(&toolchain)?;
    if let Some(root) = std_src_root {
        toolchain.env.push((STD_SRC_ROOT_ENV.to_string(), root.as_os_str().to_owned()));
    }
    build_verification_lib(&toolchain)?;
    build_playback_lib(&toolchain)
}

/// Build the `lib/` folder for the new sysroot used during verification.
/// This will include trust-mc's libraries as well as the standard libraries compiled with --emit-mir.
fn build_verification_lib(toolchain: &LibToolchain) -> Result<()> {
    let extra_args =
        ["-Z", "build-std=panic_abort,std,test", "--config", "profile.dev.panic=\"abort\""];
    let compiler_args = ["--kani-compiler", "-Cllvm-args=--ignore-global-asm --build-std"];
    let artifacts =
        build_trust_mc_lib(toolchain, &VERIFICATION_PACKAGES, &extra_args, &compiler_args)?;
    copy_artifacts(&artifacts, &trust_mc_sysroot_lib(), &StdLibs::AllNonTrustMc)
}

/// Build the `lib-playback/` folder that will be used during counter example playback.
/// This will include trust-mc's libraries compiled with `concrete-playback` feature enabled.
fn build_playback_lib(toolchain: &LibToolchain) -> Result<()> {
    let extra_args = [PLAYBACK_FEATURES, "-Z", "build-std=std,test"];
    let artifacts = build_trust_mc_lib(toolchain, &VERIFICATION_PACKAGES, &extra_args, &[])?;
    copy_artifacts(&artifacts, &trust_mc_playback_lib(), &StdLibs::AllNonTrustMc)
}

/// Build the no core library folder that will be used during std verification.
fn build_no_core_lib(toolchain: &LibToolchain) -> Result<()> {
    let artifacts = build_trust_mc_lib(toolchain, &NO_CORE_PACKAGES, &NO_CORE_CARGO_ARGS, &[])?;
    copy_artifacts(&artifacts, &trust_mc_no_core_lib(), &StdLibs::None)
}

/// Render strings as a TOML array for a `--config key=[...]` argument.
pub(crate) fn toml_string_array(items: &[String]) -> String {
    let quoted: Vec<String> = items
        .iter()
        .map(|item| format!("\"{}\"", item.replace('\\', "\\\\").replace('"', "\\\"")))
        .collect();
    format!("[{}]", quoted.join(", "))
}

pub(crate) fn build_trust_mc_lib(
    toolchain: &LibToolchain,
    packages: &[&str],
    extra_cargo_args: &[&str],
    extra_rustc_args: &[&str],
) -> Result<Vec<Artifact>> {
    // Run cargo build with -Z build-std
    let target = build_target();
    let target_dir = toolchain
        .target_dir
        .to_str()
        .ok_or_else(|| format_err!("trust-mc build path is not valid UTF-8"))?;
    let host_rustflags = format!("host.rustflags={}", toml_string_array(&toolchain.host_rustflags));
    let args = [
        "build",
        "-Z",
        "unstable-options",
        "--target-dir",
        target_dir,
        "-Z",
        "target-applies-to-host",
        "-Z",
        "host-config",
        "--profile",
        "dev",
        // Disable debug assertions for now as a mitigation for
        // https://github.com/model-checking/kani/issues/1740
        "--config",
        "profile.dev.debug-assertions=false",
        "--config",
        &host_rustflags,
        "--target",
        target,
        "--message-format",
        "json-diagnostic-rendered-ansi",
    ];
    let mut rustc_args: Vec<&str> = vec![
        "--cfg=kani",
        "--cfg=kani_sysroot",
        "-Z",
        "always-encode-mir",
        "-Z",
        "mir-enable-passes=-RemoveStorageMarkers",
        // Disable MIR inlining to preserve HashMap/BigInt call boundaries (Part of #798)
        "-Z",
        "inline-mir=no",
    ];
    rustc_args.extend(toolchain.target_rustflags.iter().map(String::as_str));
    rustc_args.extend_from_slice(extra_rustc_args);
    let mut command = nested_cargo(&toolchain.cargo);
    command.current_dir(trust_mc_repo_root());
    for var in &toolchain.env_remove {
        command.env_remove(var);
    }
    command.env("CARGO_ENCODED_RUSTFLAGS", rustc_args.join("\x1f")).env("RUSTC", &toolchain.rustc);
    for (key, value) in &toolchain.env {
        command.env(key, value);
    }
    command
        .args(args)
        .args(packages.iter().copied().flat_map(|pkg| ["-p", pkg]))
        .args(extra_cargo_args);
    let what = format!("cargo build -p {}", packages.join(" -p "));
    run_cargo_collecting_artifacts(&mut command, &what)
}

/// Run a `cargo build --message-format=json…` command under the cargo-build
/// [`Watchdog`] and return the artifacts it reports; `what` names the build in
/// errors.
fn run_cargo_collecting_artifacts(command: &mut Command, what: &str) -> Result<Vec<Artifact>> {
    command.stdout(Stdio::piped());
    let watchdog = Watchdog::cargo_build()?;
    println!("-- {}", crate::render_command(command).to_string_lossy());
    let mut cmd = command
        .spawn()
        .with_context(|| format!("failed to run {}", Path::new(command.get_program()).display()))?;

    // Collect the build artifacts on a thread, so the watchdog bounds the whole
    // build rather than only the wait after cargo's stdout closes.
    let stdout =
        cmd.stdout.take().context("cargo build must be spawned with Stdio::piped stdout")?;
    let collector = std::thread::spawn(move || build_artifacts(stdout));

    let exit_status = watchdog.wait(cmd, what)?;
    let artifacts = collector
        .join()
        .map_err(|_| format_err!("the cargo message reader panicked unexpectedly"))??;
    if !exit_status.success() {
        bail!("build failed: {what} exited with {exit_status}");
    }
    Ok(artifacts)
}

/// Copy all the artifacts to their correct place to generate a valid sysroot.
pub(crate) fn copy_artifacts(
    artifacts: &[Artifact],
    sysroot_lib: &Path,
    std_libs: &StdLibs<'_>,
) -> Result<()> {
    // Create sysroot folder.
    if sysroot_lib.exists() {
        fs::remove_dir_all(sysroot_lib)
            .with_context(|| format!("cannot clear {}", sysroot_lib.display()))?;
    }
    fs::create_dir_all(sysroot_lib)?;

    //  Copy trust-mc libraries into sysroot top folder.
    copy_libs(artifacts, sysroot_lib, is_trust_mc_lib)?;

    //  Copy standard libraries into rustlib/<target>/lib/ folder.
    let std_path = path_buf!(&sysroot_lib, "rustlib", build_target(), "lib");
    match std_libs {
        StdLibs::None => {}
        StdLibs::AllNonTrustMc => {
            fs::create_dir_all(&std_path)?;
            copy_libs(artifacts, &std_path, |a| is_rust_lib(a) && !is_trust_mc_lib(a))?;
        }
        StdLibs::TargetUnits(target_dir) => {
            fs::create_dir_all(&std_path)?;
            let target_units = target_dir.join(build_target());
            copy_libs(artifacts, &std_path, |a| {
                is_rust_lib(a)
                    && !is_trust_mc_lib(a)
                    && is_target_unit(a.filenames.iter().map(|f| f.as_std_path()), &target_units)
            })?;
        }
        StdLibs::LinkPrebuilt(prebuilt) => {
            if !prebuilt.is_dir() {
                bail!("prebuilt std directory {} does not exist", prebuilt.display());
            }
            let parent = std_path.parent().expect("rustlib/<triple>/lib has a parent");
            fs::create_dir_all(parent)?;
            #[cfg(unix)]
            std::os::unix::fs::symlink(prebuilt, &std_path).with_context(|| {
                format!("cannot link {} -> {}", std_path.display(), prebuilt.display())
            })?;
        }
    }
    Ok(())
}

/// Whether every output file of an artifact lies under `<target_dir>/<triple>`.
pub(crate) fn is_target_unit<'p>(
    mut filenames: impl Iterator<Item = &'p Path>,
    target_units: &Path,
) -> bool {
    let mut any = false;
    let all = filenames.all(|file| {
        any = true;
        file.starts_with(target_units)
    });
    any && all
}

/// Check if an artifact is a rust library that can be used by rustc on further crates compilations.
/// This inspects the kind of targets that this artifact originates from.
fn is_rust_lib(artifact: &Artifact) -> bool {
    artifact.target.kind.iter().any(|kind| match kind {
        TargetKind::Lib | TargetKind::RLib | TargetKind::ProcMacro => true,
        TargetKind::Bin
        | TargetKind::DyLib
        | TargetKind::CDyLib
        | TargetKind::StaticLib
        | TargetKind::CustomBuild => false,
        _ => false,
    })
}

/// Return whether this a trust-mc library.
/// For a given artifact, check if this is a library or proc_macro, and whether its source is
/// one of trust-mc's own libraries under `library/`. (Not merely under the repository root:
/// keyed std sources are extracted under `target/`, which is inside the repository.)
fn is_trust_mc_lib(artifact: &Artifact) -> bool {
    is_rust_lib(artifact) && artifact.target.src_path.starts_with(trust_mc_library_root())
}

/// Copy the library files from the artifacts that match the given `predicate`.
/// This function will iterate over the list of artifacts generated by the compiler, it will
/// filter the artifacts according to the given predicate. For the artifacts that satisfy the
/// predicate, it will copy the following files to the `target` folder.
///  - `rlib`: Store metadata for future codegen and executable code for concrete executions.
///  - shared library which are used for proc_macros.
fn copy_libs<P>(artifacts: &[Artifact], target: &Path, mut predicate: P) -> Result<()>
where
    P: FnMut(&Artifact) -> bool,
{
    if !target.is_dir() {
        bail!("Expected a folder, but found {}", target.display());
    }
    for artifact in artifacts.iter().filter(|&x| predicate(x)) {
        for lib in artifact.filenames.iter().filter(|path| {
            path.extension() == Some("rlib") || path.extension() == Some(lib_extension())
        }) {
            cp(lib.as_std_path(), target)
                .with_context(|| format!("failed to copy {lib} to {}", target.display()))?;
        }
    }
    Ok(())
}

/// Collect all the artifacts generated by Cargo build.
/// This will also include libraries that didn't need to be rebuild.
fn build_artifacts(cargo_stdout: ChildStdout) -> Result<Vec<Artifact>> {
    let reader = BufReader::new(cargo_stdout);
    let mut artifacts = Vec::new();
    for message in Message::parse_stream(reader) {
        match message.context("failed to parse cargo build message")? {
            Message::CompilerMessage(msg) => {
                // Print message as cargo would.
                println!("{msg}");
            }
            Message::CompilerArtifact(artifact) => artifacts.push(artifact),
            // BuildScriptExecuted, BuildFinished and the non-exhaustive rest.
            _ => {}
        }
    }
    Ok(artifacts)
}

/// Build trust-mc binaries with the extra arguments provided and return the path to the binaries folder.
/// Extra arguments to be given to `cargo build` while building trust-mc's binaries.
/// Note that the following arguments are always provided:
/// ```bash
/// cargo build --bins --lib -p trust-mc-compiler -p trust-mc-driver -p trust-mc-backend \
///   --features trust-mc-compiler/ay --message-format=json-render-diagnostics
/// ```
/// The ay feature is always enabled to ensure AY backend support is available.
/// One invocation, so feature resolution is shared and the engine rlib and the
/// AY stack compile once: the binaries go to `$MC_BUILD_SYSROOT/bin/` and
/// `librustc_codegen_trust_mc.dylib` to `$MC_BUILD_SYSROOT/codegen-backends/`.
/// Select the UNVERIFIED lane for a cargo this tool spawns.
///
/// `build-dev` produces a development bundle and makes no proof claim; the
/// verified lane is `targo trust`, which this tool never stands in for. Until
/// seal 9178 that was implicit — a bare `rustc` compiled without verification
/// by default, and the bundle build logged "compiled WITHOUT Trust
/// verification — 0 obligations checked". **9178 flipped that default**, and
/// the same `cargo build-dev` then failed inside third-party dependencies
/// (`colorchoice`, `unicode-ident`, `shlex`, `proc-macro2`, …) with "Trust
/// strict verification failed", because a lane was never selected.
///
/// Relying on a compiler default was the defect; a spawned cargo has to say
/// which lane it is in. Targo cannot say it for us: it does not propagate its
/// lane to nested `$CARGO` invocations ("recursive `$CARGO` invocations must
/// select their own lane"), and `build_lib` already sets this variable for the
/// keyed library build for the same reason.
///
/// An existing value is extended, never replaced, so a caller that already
/// chose a posture keeps it. When unset, the `.cargo/config.toml` rustflags
/// this shadows are all `-A` allow-lints, so nothing but warning volume moves.
/// Whether the compiler the cargo we spawn will drive understands
/// `-Ztrust-verify` at all.
///
/// The frozen Kani-lane toolchain (`rust-toolchain.legacy.toml`,
/// `nightly-2025-12-03`) does not: it refuses the flag with `error: unknown
/// unstable option: 'trust-verify'` while merely *learning about the target*,
/// so selecting the lane unconditionally killed `cargo build-dev` on the one
/// toolchain that lane is documented to run on — before a single crate
/// compiled. Selecting a lane is only meaningful on a compiler that has lanes;
/// a compiler with no verifier is already in the unverified one.
///
/// Probed once, from `-Zhelp`, on the same compiler cargo will pick
/// ([`toolchain_rustc`]). A compiler that cannot be probed is treated as a
/// Trust compiler, so the seal-9178 behaviour stands wherever the answer is
/// unknown. The `false` answer exists only for the frozen stock-nightly
/// comparison lane (STOCK-AS-ORACLE, kept by the owner's ruling of
/// 2026-09-29).
fn spawned_rustc_knows_trust_verify() -> bool {
    static KNOWS: OnceLock<bool> = OnceLock::new();
    *KNOWS.get_or_init(|| match Command::new(toolchain_rustc()).arg("-Zhelp").output() {
        Ok(out) if out.status.success() => {
            let text = String::from_utf8_lossy(&out.stdout);
            text.contains("trust-verify=")
        }
        _ => true,
    })
}

fn select_unverified_lane(cmd: &mut Command, release: Option<&ReleaseFlags>) {
    select_unverified_lane_when(cmd, spawned_rustc_knows_trust_verify());
    if let Some(release) = release {
        release.apply(cmd);
    }
}

/// [`select_unverified_lane`] with the capability decided by the caller, so the
/// tests exercise both compilers without owning either.
fn select_unverified_lane_when(cmd: &mut Command, compiler_has_lanes: bool) {
    const OFF: &str = "-Ztrust-verify=off";
    if !compiler_has_lanes {
        return;
    }
    let value = match std::env::var("CARGO_ENCODED_RUSTFLAGS") {
        Ok(existing) if existing.split('\x1f').any(|flag| flag == OFF) => existing,
        Ok(existing) if !existing.is_empty() => format!("{existing}\x1f{OFF}"),
        _ => OFF.to_string(),
    };
    cmd.env("CARGO_ENCODED_RUSTFLAGS", value);
}

pub(crate) fn build_bin<T: AsRef<OsStr>>(
    extra_args: &[T],
    release: Option<&ReleaseFlags>,
) -> Result<PathBuf> {
    const BIN_PACKAGES: [&str; 2] = ["trust-mc-compiler", "trust-mc-driver"];
    const BACKEND_PACKAGE: &str = "trust-mc-backend";
    let out_dir = trust_mc_sysroot_bin();
    let backend_dir = trust_mc_sysroot().join("codegen-backends");
    let mut cmd = nested_cargo(&launching_cargo());
    select_unverified_lane(&mut cmd, release);
    cmd.arg("build").args(extra_args).args([
        "--bins",
        "--lib",
        "-p",
        BIN_PACKAGES[0],
        "-p",
        BIN_PACKAGES[1],
        "-p",
        BACKEND_PACKAGE,
        "--features",
        "trust-mc-compiler/ay",
        "--message-format=json-render-diagnostics",
    ]);
    let artifacts =
        run_cargo_collecting_artifacts(&mut cmd, "cargo build of the trust-mc binaries")
            .context("Failed to build binaries.")?;

    fs::create_dir_all(&out_dir)?;
    fs::create_dir_all(&backend_dir)?;
    let mut backends = 0;
    for artifact in &artifacts {
        // Targets of the named package, whose sources live under its directory.
        let from =
            |name: &str| artifact.target.src_path.starts_with(trust_mc_repo_root().join(name));
        if artifact.target.kind.contains(&TargetKind::Bin)
            && BIN_PACKAGES.iter().any(|name| from(name))
            && let Some(exe) = &artifact.executable
        {
            cp(exe.as_std_path(), &out_dir)?;
        }
        if artifact.target.kind.contains(&TargetKind::CDyLib) && from(BACKEND_PACKAGE) {
            for lib in artifact.filenames.iter().filter(|f| f.extension() == Some(lib_extension()))
            {
                cp(lib.as_std_path(), &backend_dir)?;
                check_backend_dylib_is_relocatable(
                    &backend_dir.join(lib.file_name().unwrap_or("")),
                )?;
                backends += 1;
            }
        }
    }
    if backends != 1 {
        bail!("expected cargo to report one {BACKEND_PACKAGE} cdylib, found {backends}");
    }
    Ok(out_dir)
}

/// The backend dylib is dlopened by a compiler that already loaded its
/// `librustc_driver`: it must carry no rpath (dyld could resolve
/// `@rpath/librustc_driver-*` to a second copy), and no build-host path may
/// ship inside it. Fails closed when the inspection tool is unavailable.
#[cfg(target_os = "macos")]
fn check_backend_dylib_is_relocatable(dylib: &Path) -> Result<()> {
    let run = |args: &[&str]| -> Result<String> {
        let out = Command::new("otool")
            .args(args)
            .arg(dylib)
            .output()
            .map_err(|e| format_err!("cannot run otool on {}: {e}", dylib.display()))?;
        if !out.status.success() {
            bail!("otool {} {} failed", args.join(" "), dylib.display());
        }
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    };
    let rpaths = run(&["-l"])?.lines().filter(|l| l.trim() == "cmd LC_RPATH").count();
    if rpaths != 0 {
        bail!("{} carries {rpaths} LC_RPATH load command(s); it must carry none", dylib.display());
    }
    // `otool -D` prints the file name, then the install name.
    let ids = run(&["-D"])?;
    if let Some(id) = ids.lines().skip(1).find(|l| l.starts_with('/')) {
        bail!("{} has an absolute install name {id}; expected @rpath/…", dylib.display());
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn check_backend_dylib_is_relocatable(dylib: &Path) -> Result<()> {
    let out = Command::new("readelf")
        .args(["-d"])
        .arg(dylib)
        .output()
        .map_err(|e| format_err!("cannot run readelf on {}: {e}", dylib.display()))?;
    if !out.status.success() {
        bail!("readelf -d {} failed", dylib.display());
    }
    let dynamic = String::from_utf8_lossy(&out.stdout);
    if dynamic.contains("(RPATH)") || dynamic.contains("(RUNPATH)") {
        bail!("{} carries an RPATH/RUNPATH; it must carry none", dylib.display());
    }
    Ok(())
}

/// Build tool binaries with the extra arguments provided.
/// At present, the only tool we build for the bundle is `trust-mc-cov`, but this
/// could include other tools in the future.
pub(crate) fn build_tools<T: AsRef<OsStr>>(
    extra_args: &[T],
    release: Option<&ReleaseFlags>,
) -> Result<()> {
    let args = ["-p", "trust-mc-cov"];
    let mut tools_cmd = nested_cargo(&launching_cargo());
    select_unverified_lane(&mut tools_cmd, release);
    tools_cmd
        .arg("build")
        .args(extra_args)
        .args(args)
        .run_with_watchdog(Watchdog::cargo_build()?)
        .context("Failed to build tool binaries.")?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The lane is SELECTED, never inherited from a compiler default — that
    /// default changed under us when the Trust seal moved 8595 -> 9178.
    #[test]
    fn unverified_lane_is_selected_and_never_replaces_an_existing_posture() {
        let seen = |cmd: &Command| {
            cmd.get_envs()
                .find(|(k, _)| *k == "CARGO_ENCODED_RUSTFLAGS")
                .and_then(|(_, v)| v)
                .map(|v| v.to_string_lossy().into_owned())
        };

        // Nothing set: the lane is stated outright.
        let mut cmd = Command::new("cargo");
        // SAFETY: single-threaded test process.
        unsafe { std::env::remove_var("CARGO_ENCODED_RUSTFLAGS") };
        select_unverified_lane_when(&mut cmd, true);
        assert_eq!(seen(&cmd).as_deref(), Some("-Ztrust-verify=off"));

        // A compiler with no verification lanes (the frozen Kani-lane nightly)
        // is given NO flag: it rejects `-Ztrust-verify` outright, which failed
        // `cargo build-dev` before it compiled anything.
        let mut cmd = Command::new("cargo");
        select_unverified_lane_when(&mut cmd, false);
        assert_eq!(seen(&cmd), None);

        // A caller's posture is EXTENDED, not clobbered.
        unsafe { std::env::set_var("CARGO_ENCODED_RUSTFLAGS", "-Cdebuginfo=2") };
        let mut cmd = Command::new("cargo");
        select_unverified_lane_when(&mut cmd, true);
        assert_eq!(seen(&cmd).as_deref(), Some("-Cdebuginfo=2\u{1f}-Ztrust-verify=off"));

        // Already selected: not stated twice.
        unsafe { std::env::set_var("CARGO_ENCODED_RUSTFLAGS", "-Ztrust-verify=off") };
        let mut cmd = Command::new("cargo");
        select_unverified_lane_when(&mut cmd, true);
        assert_eq!(seen(&cmd).as_deref(), Some("-Ztrust-verify=off"));
        unsafe { std::env::remove_var("CARGO_ENCODED_RUSTFLAGS") };
    }

    /// The release flags extend the lane the command already selected (never
    /// replace it) and are not repeated.
    #[test]
    fn release_flags_extend_the_selected_lane() {
        let release = ReleaseFlags {
            rustflags: vec!["--remap-path-prefix=$HOME=~".to_string()],
            env: vec![("MC_RELEASE_BUNDLE".to_string(), "1".into())],
        };
        let mut cmd = Command::new("targo");
        cmd.env("CARGO_ENCODED_RUSTFLAGS", "-Ztrust-verify=off");
        release.apply(&mut cmd);
        release.apply(&mut cmd);
        let env = |key: &str| {
            cmd.get_envs()
                .find(|(k, _)| *k == key)
                .and_then(|(_, v)| v)
                .map(|v| v.to_string_lossy().into_owned())
        };
        assert_eq!(
            env("CARGO_ENCODED_RUSTFLAGS").as_deref(),
            Some("-Ztrust-verify=off\u{1f}--remap-path-prefix=$HOME=~")
        );
        assert_eq!(env("MC_RELEASE_BUNDLE").as_deref(), Some("1"));
    }

    /// A nested Targo names its lane; a nested stock cargo is left alone.
    #[test]
    fn nested_targo_names_the_unverified_lane() {
        let args = |cargo: &str| {
            nested_cargo(OsStr::new(cargo))
                .get_args()
                .map(|a| a.to_string_lossy().into_owned())
                .collect::<Vec<_>>()
        };
        assert_eq!(args("/seal/bin/targo"), ["--unverified"]);
        assert_eq!(args("targo"), ["--unverified"]);
        assert_eq!(args("/seal/bin/targo.exe"), ["--unverified"]);
        assert!(args("/seal/bin/cargo").is_empty());
        assert!(args("cargo").is_empty());
        // A name that merely contains "targo" is not Targo.
        assert!(args("/x/bin/targo-tippy").is_empty());
    }

    /// The compiler probed is the launching toolchain's own -- trustc on a seal --
    /// and with nothing to go on it is `trustc`, never a PATH `rustc`.
    #[test]
    fn toolchain_rustc_is_the_launching_toolchains_compiler() {
        let exe = std::env::consts::EXE_SUFFIX;
        let root = std::env::temp_dir()
            .join(format!("build-trust-mc-toolchain-rustc-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        let seal = root.join("seal/bin");
        let stock = root.join("stock/bin");
        fs::create_dir_all(&seal).unwrap();
        fs::create_dir_all(&stock).unwrap();
        for (dir, names) in
            [(&seal, &["targo", "trustc", "rustc"][..]), (&stock, &["cargo", "rustc"])]
        {
            for name in names {
                fs::write(dir.join(format!("{name}{exe}")), "").unwrap();
            }
        }
        let beside = |cargo: &Path| toolchain_rustc_beside(Some(cargo.as_os_str()));
        assert_eq!(beside(&seal.join("targo")), seal.join(format!("trustc{exe}")));
        assert_eq!(beside(&stock.join("cargo")), stock.join(format!("rustc{exe}")));
        assert_eq!(beside(&root.join("empty/bin/targo")), OsString::from("trustc"));
        assert_eq!(toolchain_rustc_beside(Some(OsStr::new("targo"))), OsString::from("trustc"));
        assert_eq!(toolchain_rustc_beside(None), OsString::from("trustc"));
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn std_closure_is_what_cargo_built_for_the_target_triple() {
        let target_dir = Path::new("/r/target/build-libs/keyed/driver-948b36c62eacc5d1");
        let units = target_dir.join("aarch64-apple-darwin");
        let hashbrown = units.join("debug/deps/libhashbrown-1.rlib");
        let syn = target_dir.join("debug/deps/libsyn-2.rlib");
        assert!(is_target_unit([hashbrown.as_path()].into_iter(), &units));
        assert!(!is_target_unit([syn.as_path()].into_iter(), &units));
        assert!(!is_target_unit([hashbrown.as_path(), syn.as_path()].into_iter(), &units));
        assert!(!is_target_unit(std::iter::empty(), &units));
    }

    #[test]
    fn host_rustflags_render_as_a_toml_array() {
        let flags = vec!["--cfg=kani".to_string(), "-Ztrust-verify=off".to_string()];
        assert_eq!(toml_string_array(&flags), "[\"--cfg=kani\", \"-Ztrust-verify=off\"]");
        assert_eq!(toml_string_array(&["a\"b".to_string()]), "[\"a\\\"b\"]");
    }
}

#[cfg(test)]
mod std_shim_prelude_tests {
    /// The Kani std shim that `build-dev` and `build-keyed` copy into every sysroot.
    fn shim_source() -> String {
        let path = super::trust_mc_repo_root().join("library/std/src/lib.rs");
        std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()))
    }

    /// The names of the `#[macro_export] macro_rules!` items the shim defines.
    fn exported_macros(src: &str) -> Vec<String> {
        let lines: Vec<&str> = src.lines().map(str::trim).collect();
        lines
            .windows(2)
            .filter(|w| w[0] == "#[macro_export]")
            .filter_map(|w| w[1].strip_prefix("macro_rules! "))
            .map(|rest| rest.trim_end_matches('{').trim().to_string())
            .collect()
    }

    /// The comma-separated identifiers between `open` and the next `close`.
    fn list_after<'a>(src: &'a str, open: &str, close: &str) -> Vec<&'a str> {
        let start = src.find(open).unwrap_or_else(|| panic!("shim has no `{open}`")) + open.len();
        let end = start + src[start..].find(close).expect("unterminated list");
        src[start..end].split(',').map(str::trim).filter(|s| !s.is_empty()).collect()
    }

    /// Toolchains whose std prelude exports `assert!`, `panic!` and friends as
    /// items (Trust 8571) inject `extern crate std` without `#[macro_use]`, so a
    /// crate reaches a macro only through `std::prelude::rust_20xx::*`. An
    /// override missing from the shim's prelude modules is silently replaced by
    /// std's own: `assert!` then expands to `core::panicking::panic_fmt` and the
    /// check loses its property (measured on the Trustc route, 2026-09-12).
    #[test]
    fn every_macro_override_is_in_every_edition_prelude() {
        let src = shim_source();
        let macros = exported_macros(&src);
        for expected in ["assert", "assert_eq", "panic", "println", "unreachable"] {
            assert!(macros.iter().any(|m| m == expected), "shim no longer overrides `{expected}`");
        }
        let prelude = &src[src.find("pub mod prelude {").expect("shim has no prelude module")..];
        // The grouped list, plus any override re-exported on a line of its own
        // (`assert` is, so its lint allow does not cover the others).
        let mut reexported = list_after(prelude, "pub use crate::{", "};");
        reexported.extend(prelude.lines().filter_map(|line| {
            line.trim().strip_prefix("pub use crate::")?.strip_suffix(';').filter(|name| {
                !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            })
        }));
        for name in &macros {
            if name == "panic" {
                // `panic` is also a std module; the prelude takes only the macro.
                assert!(
                    prelude.contains("pub use super::panic_macro_only::panic;"),
                    "the shim prelude does not re-export the `panic` override"
                );
            } else {
                assert!(
                    reexported.contains(&name.as_str()),
                    "the shim prelude does not re-export the `{name}` override: {reexported:?}"
                );
            }
        }
        let editions = list_after(prelude, "kani_prelude!(", ");");
        for edition in ["v1", "rust_2015", "rust_2018", "rust_2021", "rust_2024"] {
            assert!(
                editions.contains(&edition),
                "the shim declares no `prelude::{edition}`, so crates of that edition bypass \
                 every override: {editions:?}"
            );
        }
    }
}
