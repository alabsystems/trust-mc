// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::args::VerificationArgs;
use crate::call_cargo::output::cargo_message_format_arg;
use crate::call_cargo::targets::{
    VerificationTarget, filter_features_for_package, package_targets,
};
use crate::call_single_file::{LibConfig, ambient_rustflags};
use crate::project::Artifact;
use crate::session::trustc_route;
use crate::session::{
    CompilerRoute, DEFAULT_TOOL_TIMEOUT_SECS, KaniSession, resolve_cargo_path, wait_with_timeout,
};
use crate::util;
use crate::util::args::{CargoArg, CommandWrapper as _, KaniArg, PassTo, RustcArg};
use anyhow::{Context, Result, bail};
use cargo_metadata::{CrateType, Metadata, MetadataCommand, Package, PackageId, Target};
use std::collections::HashMap;
use std::ffi::OsString;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::mpsc;
use std::time::Duration;
use tracing::{debug, trace};
use trust_mc_metadata::{ArtifactType, CompilerArtifactStub};

mod output;
#[cfg(test)]
mod route_tests;
mod targets;
#[cfg(test)]
mod tests;
pub(crate) use output::{cargo_config_args, trustc_cargo_config_args};

/// The outputs of kani-compiler being invoked via cargo on a project.
pub(crate) struct CargoOutputs {
    /// The target profile directory shared by all compiled units.
    /// Artifact paths come from compiler messages and harness metadata; Targo
    /// places them in per-unit directories without creating `debug/deps`.
    pub outdir: PathBuf,
    /// The kani-metadata.json files written by kani-compiler.
    pub metadata: Vec<Artifact>,
    /// Recording the cargo metadata from the build
    pub cargo_metadata: Metadata,
}

impl KaniSession {
    /// Create a new cargo library in the given path.
    ///
    /// Since we cannot create a new workspace with `cargo init --lib`, we create the dummy
    /// crate manually. =( See <https://github.com/rust-lang/cargo/issues/8365>.
    ///
    /// Without setting up a new workspace, cargo init will modify the workspace where this is
    /// running. See <https://github.com/model-checking/kani/issues/3574> for details.
    pub(crate) fn cargo_init_lib(&self, path: &Path) -> Result<()> {
        let toml_path = path.join("Cargo.toml");
        if toml_path.exists() {
            bail!("Cargo.toml already exists in {}", path.display());
        }

        // Create folder for library
        fs::create_dir_all(path.join("src"))?;

        // Create dummy crate and write dummy body
        let lib_path = path.join("src/lib.rs");
        fs::write(&lib_path, "pub fn dummy() {}")?;

        // Create Cargo.toml
        fs::write(
            &toml_path,
            r#"[package]
name = "dummy"
version = "0.1.0"

[lib]
crate-type = ["lib"]

[workspace]
"#,
        )?;
        Ok(())
    }

    pub(crate) fn cargo_build_std(
        &self,
        std_path: &Path,
        krate_path: &Path,
    ) -> Result<Vec<Artifact>> {
        let lib_path = self.route.library_folder("no_core/lib")?;
        let mut rustc_args = self.kani_rustc_flags(LibConfig::new_no_core(lib_path)?);

        // In theory, these could be passed just to the local crate rather than all crates,
        // but the `cargo build` command we use for building `std` doesn't allow you to pass `rustc`
        // arguments, so we have to pass them through the environment variable instead.
        let mut std_flags = self.route_check_version_flags();
        std_flags.extend(self.kani_compiler_local_flags());
        rustc_args.push(self.encode_kani_args(&std_flags));

        // Ignore global assembly, since `compiler_builtins` has some.
        rustc_args.push(
            self.encode_kani_args(&[KaniArg::from("--ignore-global-asm"), self.reachability_arg()]),
        );

        let mut cargo_args: Vec<CargoArg> = vec!["build".into()];
        cargo_args.append(&mut self.route_cargo_config_args());

        // Configuration needed to parse cargo compilation status.
        cargo_args.push("--message-format".into());
        cargo_args.push(cargo_message_format_arg(self.args.common_args.message_format).into());
        cargo_args.push("-Z".into());
        cargo_args.push("build-std=panic_abort,core,std".into());

        if self.args.common_args.verbose {
            cargo_args.push("-v".into());
        }

        // We need this suffix push because of https://github.com/rust-lang/cargo/pull/14370
        // which removes the library suffix from the build-std command
        let mut full_path = std_path.to_path_buf();
        full_path.push("library");

        // Since we are verifying the standard library, we set the reachability to all crates.
        // The std-verification build runs from `krate_path`, so that is where cargo
        // reads its `[env]` table from.
        self.refuse_cargo_env_table(Some(krate_path))?;
        let mut cmd = self.cargo_command(None)?;
        cmd.pass_cargo_args(&cargo_args)
            .current_dir(krate_path)
            .env("RUSTC", self.compiler_program()?)
            .pass_rustc_args(&rustc_args, PassTo::AllCrates)
            .env("CARGO_TERM_PROGRESS_WHEN", "never")
            .env("__CARGO_TESTS_ONLY_SRC_ROOT", full_path.as_os_str());
        self.apply_route_env(&mut cmd);

        Ok(self
            .with_backend_recheck(|| self.run_build(cmd, None))?
            .into_iter()
            .filter_map(|artifact| {
                if artifact.target.crate_types.contains(&CrateType::Lib)
                    || artifact.target.crate_types.contains(&CrateType::RLib)
                {
                    map_kani_artifact(artifact)
                } else {
                    None
                }
            })
            .collect())
    }

    /// The cargo `--target` and host-configuration arguments of this route: Kani's on
    /// DevCli ([`cargo_config_args`]), and on Trustc the same with host units given
    /// the route's host posture ([`trustc_cargo_config_args`]).
    pub(crate) fn route_cargo_config_args(&self) -> Vec<CargoArg> {
        match self.route {
            CompilerRoute::DevCli => cargo_config_args(),
            CompilerRoute::Trustc { .. } => trustc_cargo_config_args(),
        }
    }

    /// Build the shared cargo arguments for verification (excludes per-package features).
    fn cargo_build_args(&self, target_dir: PathBuf) -> Vec<CargoArg> {
        let mut cargo_args: Vec<CargoArg> = vec!["rustc".into()];
        if let Some(path) = &self.args.cargo.manifest_path {
            cargo_args.push("--manifest-path".into());
            cargo_args.push(path.into());
        }
        if self.args.cargo.locked {
            cargo_args.push("--locked".into());
        }
        if self.args.cargo.all_features {
            cargo_args.push("--all-features".into());
        }
        if self.args.cargo.no_default_features {
            cargo_args.push("--no-default-features".into());
        }
        // Note: We do NOT add --features here globally. Features are filtered
        // per-package in cargo_build to handle workspaces where packages don't
        // all declare the same features. This matches cargo's behavior.

        cargo_args.append(&mut self.route_cargo_config_args());

        cargo_args.push("--target-dir".into());
        cargo_args.push(target_dir.into());

        cargo_args.push("--message-format".into());
        cargo_args.push(cargo_message_format_arg(self.args.common_args.message_format).into());

        if self.args.tests {
            cargo_args.push("--profile".into());
            cargo_args.push("test".into());
        }

        if self.args.common_args.verbose {
            cargo_args.push("-v".into());
        }
        cargo_args
    }

    /// Calls `cargo_build` to generate verification artifacts in `target_dir`
    pub(crate) fn cargo_build(&mut self, keep_going: bool) -> Result<CargoOutputs> {
        let build_target = env!("TARGET"); // see build.rs
        let metadata = self.cargo_metadata(build_target)?;
        // Before any compile: a cargo `[env]` table would set variables on every
        // rustc after the launcher's edits (Trustc route only; a probe, not a compile).
        self.refuse_cargo_env_table(None)?;
        let default_target_dir: PathBuf = metadata.target_directory.as_std_path().to_owned();
        let target_dir = self
            .args
            .target_dir
            .as_ref()
            .unwrap_or(&default_target_dir)
            .join(self.kani_target_namespace()?);
        let outdir = target_dir.join(build_target).join("debug");

        if self.args.force_build && target_dir.exists() {
            fs::remove_dir_all(&target_dir)?;
        }

        let rustc_args = self.cargo_build_rustc_args(
            self.route.library_folder("lib")?,
            ambient_rustflags().as_deref(),
        )?;

        let cargo_args = self.cargo_build_args(target_dir);
        let requested_features = self.args.cargo.features();

        // Arguments passed only to the target package (not dependencies).
        // See https://doc.rust-lang.org/cargo/commands/cargo-rustc.html
        let local_kani_arg = self.cargo_build_local_kani_arg();

        let mut found_target = false;
        let packages = self.packages_to_verify(&self.args, &metadata)?;
        let mut artifacts = vec![];
        let mut failed_targets = vec![];
        for package in packages {
            let pkg_features = filter_features_for_package(&requested_features, package);

            for verification_target in package_targets(&self.args, package) {
                let cargo = self.cargo_command(Some(verification_target.target().name.clone()))?;
                let cmd = self.cargo_build_command(
                    cargo,
                    &cargo_args,
                    &package.id.to_string(),
                    &pkg_features,
                    &verification_target,
                    &rustc_args,
                    local_kani_arg.clone(),
                )?;

                let built =
                    self.run_build_target(cmd, verification_target.target(), Some(&metadata));
                // Outside the match: `keep_going` must never absorb a changed backend.
                self.recheck_trustc_backend()?;
                match built {
                    Err(err) => {
                        if keep_going {
                            let target_str = format!("{verification_target}");
                            util::error(&format_args!("Failed to compile {target_str}"));
                            failed_targets.push(target_str);
                        } else {
                            return Err(err);
                        }
                    }
                    Ok(Some(artifact)) => artifacts.push(artifact),
                    Ok(None) => {}
                }
                found_target = true;
            }
        }

        if !found_target {
            bail!("No supported targets were found.");
        }

        Ok(CargoOutputs { outdir, metadata: artifacts, cargo_metadata: metadata })
    }

    /// The command that builds one verification target: `cargo` (from
    /// [`Self::cargo_command`]) with the shared cargo arguments, the package, its
    /// features and target, then `RUSTC` set to this route's compiler (the Trustc
    /// route prints its marker here, once per compile), `rustc_args` for every crate
    /// through `CARGO_ENCODED_RUSTFLAGS`, which cargo applies to target units only,
    /// and `local_kani_arg` for the selected target alone.
    #[allow(clippy::too_many_arguments)]
    fn cargo_build_command(
        &self,
        mut cargo: Command,
        cargo_args: &[CargoArg],
        package_id: &str,
        pkg_features: &[String],
        verification_target: &VerificationTarget,
        rustc_args: &[RustcArg],
        local_kani_arg: RustcArg,
    ) -> Result<Command> {
        cargo.pass_cargo_args(cargo_args).args(["-p", package_id]);

        if !pkg_features.is_empty() {
            cargo.arg(format!("--features={}", pkg_features.join(",")));
        }

        cargo
            .args(verification_target.to_args())
            .arg("--")
            .env("RUSTC", self.compiler_program()?)
            .pass_rustc_args(rustc_args, PassTo::AllCrates)
            .pass_rustc_arg(local_kani_arg, PassTo::OnlyLocalCrate)
            .env("RUSTC_BOOTSTRAP", "1")
            .env("RUST_BACKTRACE", "1")
            .env("CARGO_TERM_PROGRESS_WHEN", "never");
        self.apply_route_env(&mut cargo);
        Ok(cargo)
    }

    /// The rustc arguments `cargo_build` passes to every crate (through
    /// `CARGO_ENCODED_RUSTFLAGS`), as a pure function of the session.
    pub(crate) fn cargo_build_rustc_args(
        &self,
        lib_path: PathBuf,
        rustflags: Option<&str>,
    ) -> Result<Vec<RustcArg>> {
        let mut rustc_args = self.kani_rustc_flags_with(LibConfig::new(lib_path)?, rustflags);
        rustc_args.push(self.encode_kani_args(&self.kani_compiler_dependency_flags()));
        Ok(rustc_args)
    }

    /// The engine arguments `cargo_build` passes only to the target package.
    pub(crate) fn cargo_build_local_kani_arg(&self) -> RustcArg {
        let mut kani_pkg_args = vec![self.reachability_arg()];
        kani_pkg_args.extend(self.kani_compiler_local_flags());
        self.encode_kani_args(&kani_pkg_args)
    }

    pub(crate) fn cargo_metadata(&self, build_target: &str) -> Result<Metadata> {
        let cmd = self.cargo_metadata_command_on(build_target, std::env::vars_os().collect())?;
        self.exec_cargo_metadata(cmd)
    }

    /// The `cargo metadata` command, with the driver's environment passed in.
    /// DevCli runs the pinned toolchain's cargo. Trustc refuses a rustc wrapper, an
    /// engine knob or a route-owned `RUSTFLAGS` token named in that environment
    /// (`trustc_route::refuse_cargo_route_env`), establishes the identity, and runs
    /// the seal's own cargo
    /// with the route's cargo environment (`trustc_route::trustc_cargo_env`): the
    /// `--filter-platform` query asks `RUSTC` for target information.
    fn cargo_metadata_command_on(
        &self,
        build_target: &str,
        env: Vec<(OsString, OsString)>,
    ) -> Result<MetadataCommand> {
        let mut cmd = MetadataCommand::new();

        match self.route {
            CompilerRoute::DevCli => {
                // Use Kani's toolchain when running `cargo metadata`
                let cargo_resolution = resolve_cargo_path()?;
                cmd.cargo_path(&cargo_resolution.metadata_path);
                for (key, value) in cargo_resolution.toolchain_env() {
                    cmd.env(key, value);
                }
            }
            CompilerRoute::Trustc { .. } => {
                trustc_route::refuse_cargo_route_env(&env)?;
                let identity = self.trustc_identity()?;
                cmd.cargo_path(identity.seal_cargo()?);
                let keys = env.into_iter().map(|(key, _)| key);
                for (key, value) in trustc_route::trustc_cargo_env(&identity.trustc, keys) {
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
        }

        // restrict metadata command to host platform. References:
        // https://github.com/rust-lang/rust-analyzer/issues/6908
        // https://github.com/rust-lang/rust-analyzer/pull/6912
        let mut metadata_options = vec![String::from("--filter-platform"), build_target.to_owned()];
        if self.args.cargo.locked {
            metadata_options.push(String::from("--locked"));
        }
        cmd.other_options(metadata_options);

        // Set a --manifest-path if we're given one
        if let Some(path) = &self.args.cargo.manifest_path {
            cmd.manifest_path(path);
        }
        // Pass down features enables, which may affect dependencies or build metadata
        // (multiple calls to features are ok with cargo_metadata:)
        if self.args.cargo.all_features {
            cmd.features(cargo_metadata::CargoOpt::AllFeatures);
        }
        if self.args.cargo.no_default_features {
            cmd.features(cargo_metadata::CargoOpt::NoDefaultFeatures);
        }
        let features = self.args.cargo.features();
        if !features.is_empty() {
            cmd.features(cargo_metadata::CargoOpt::SomeFeatures(features));
        }
        Ok(cmd)
    }

    /// Run `cmd` under the tool timeout.
    fn exec_cargo_metadata(&self, cmd: MetadataCommand) -> Result<Metadata> {
        // Use timeout protection (#997)
        // MetadataCommand doesn't have built-in timeout, so we run it in a thread
        let timeout = self.tool_timeout().unwrap_or(Duration::from_secs(DEFAULT_TOOL_TIMEOUT_SECS));
        let (tx, rx) = mpsc::channel();

        std::thread::spawn(move || {
            let result = cmd.exec();
            let _ = tx.send(result);
        });

        match rx.recv_timeout(timeout) {
            Ok(result) => result.context("Failed to get cargo metadata."),
            Err(mpsc::RecvTimeoutError::Timeout) => {
                bail!(
                    "cargo metadata timed out after {:.1}s. Use --tool-timeout to increase the limit.",
                    timeout.as_secs_f64()
                )
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                bail!("cargo metadata thread panicked unexpectedly")
            }
        }
    }

    /// Run cargo and collect any error found.
    /// We also collect the metadata file generated during compilation if any for the given target.
    fn run_build_target(
        &self,
        cargo_cmd: Command,
        target: &Target,
        metadata: Option<&Metadata>,
    ) -> Result<Option<Artifact>> {
        /// This used to be `rustc_artifact == *target`, but it
        /// started to fail after the `cargo` change in
        /// <https://github.com/rust-lang/cargo/pull/12783>
        ///
        /// We should revisit this check after a while to see if
        /// it's not needed anymore or it can be restricted to
        /// certain cases.
        /// Upstream: <https://github.com/model-checking/kani/issues/3111>
        fn same_target(t1: &Target, t2: &Target) -> bool {
            (t1 == t2)
                || (t1.name.replace('-', "_") == t2.name.replace('-', "_")
                    && t1.kind == t2.kind
                    && t1.src_path == t2.src_path
                    && t1.edition == t2.edition
                    && t1.doctest == t2.doctest
                    && t1.test == t2.test
                    && t1.doc == t2.doc)
        }

        let compile_start = std::time::Instant::now();
        let artifacts = self.run_build(cargo_cmd, metadata)?;
        if std::env::var("TIME_COMPILER").is_ok() {
            // conditionally print the compilation time for debugging & use by `compile-timer`
            // doesn't just use the existing `--debug` flag because the number of prints significantly affects performance
            writeln!(
                std::io::stdout(),
                "BUILT {} IN {:?}μs",
                target.name,
                compile_start.elapsed().as_micros()
            )?;
        }
        debug!(?artifacts, "run_build_target");

        // We generate kani specific artifacts only for the build target. The build target is
        // always the last artifact generated in a build, and all the other artifacts are related
        // to dependencies or build scripts.
        Ok(artifacts.into_iter().rev().find_map(|artifact| {
            if same_target(&artifact.target, target) { map_kani_artifact(artifact) } else { None }
        }))
    }

    /// Check that all package names are present in the workspace, otherwise return which aren't.
    fn to_package_ids<'a>(
        &self,
        package_names: &'a [String],
    ) -> Result<HashMap<PackageId, &'a str>> {
        package_names
            .iter()
            .map(|pkg| {
                let mut cmd = self.cargo_query_command()?;
                cmd.arg("pkgid");
                if let Some(path) = &self.args.cargo.manifest_path {
                    cmd.arg("--manifest-path");
                    cmd.arg(path);
                }
                cmd.arg(pkg);
                // Use timeout protection for cargo pkgid (#995)
                let mut process = self.run_piped(cmd)?;
                // Take stdout before wait_with_timeout moves the process
                let stdout = process.stdout.take();
                let timeout =
                    self.tool_timeout().unwrap_or(Duration::from_secs(DEFAULT_TOOL_TIMEOUT_SECS));
                let result = wait_with_timeout(process, timeout, "cargo pkgid")?;
                if !result.success() {
                    bail!("Failed to retrieve information for `{pkg}`");
                }

                let mut reader =
                    BufReader::new(stdout.context("failed to capture cargo pkgid stdout")?);
                let mut line = String::new();
                reader.read_line(&mut line)?;
                trace!(package_id=?line, "package_ids");
                Ok((PackageId { repr: line.trim().to_string() }, pkg.as_str()))
            })
            .collect()
    }

    /// Extract the packages that should be verified.
    ///
    /// The result is built following these rules (mimicking cargo, see
    /// https://github.com/rust-lang/cargo/blob/master/src/cargo/core/workspace.rs):
    /// - If `--package <pkg>` is given, return the list of packages selected.
    /// - If `--exclude <pkg>` is given, return the list of packages not excluded.
    /// - If `--workspace` is given, return the list of workspace members.
    /// - Else obtain the set of packages from cargo's default_workspace_members (i.e., if
    ///   `default-members` is specified in Cargo.toml, use that list; else if a root package is
    ///   specified use that; else use all members).
    ///
    /// In addition, if either `--package <pkg>` or `--exclude <pkg>` is given,
    /// validate that `<pkg>` is a package name in the workspace, or return an error
    /// otherwise.
    fn packages_to_verify<'b>(
        &self,
        args: &VerificationArgs,
        metadata: &'b Metadata,
    ) -> Result<Vec<&'b Package>> {
        debug!(package_selection=?args.cargo.package, package_exclusion=?args.cargo.exclude, workspace=args.cargo.workspace, "packages_to_verify args");
        let packages = if !args.cargo.package.is_empty() {
            let pkg_ids = self.to_package_ids(&args.cargo.package)?;
            let filtered: Vec<_> = metadata
                .workspace_packages()
                .into_iter()
                .filter(|pkg| pkg_ids.contains_key(&pkg.id))
                .collect();
            if filtered.len() < args.cargo.package.len() {
                // Some packages specified in `--package` were not found in the workspace.
                let outer: Vec<_> = metadata
                    .packages
                    .iter()
                    .filter_map(|pkg| pkg_ids.get(&pkg.id).copied())
                    .collect();
                bail!(
                    "The following specified packages were not found in this workspace: `{}`",
                    outer.join("`,")
                );
            }
            filtered
        } else if !args.cargo.exclude.is_empty() {
            // should be ensured by argument validation
            assert!(args.cargo.workspace);
            let pkg_ids = self.to_package_ids(&args.cargo.exclude)?;
            metadata
                .workspace_packages()
                .into_iter()
                .filter(|pkg| !pkg_ids.contains_key(&pkg.id))
                .collect()
        } else if args.cargo.workspace {
            metadata.workspace_packages()
        } else {
            metadata.workspace_default_packages()
        };
        trace!(?packages, "packages_to_verify result");
        Ok(packages)
    }
}

/// Extract Kani artifact that might've been generated from a given rustc artifact.
/// Not every rustc artifact will map to a kani artifact, hence the `Option<>`.
///
/// Unfortunately, we cannot always rely on the messages to get the path for the original artifact
/// that `rustc` produces. So we hack the content of the output path to point to the original
/// metadata file. See <https://github.com/model-checking/kani/issues/2234> for more details.
fn map_kani_artifact(rustc_artifact: cargo_metadata::Artifact) -> Option<Artifact> {
    debug!(?rustc_artifact, "map_kani_artifact");
    if rustc_artifact.target.is_custom_build() {
        // We don't verify custom builds.
        return None;
    }
    let result = rustc_artifact.filenames.iter().find_map(|path| {
        if path.extension() == Some("rmeta") {
            let file_stem = path.file_stem()?.strip_prefix("lib")?;
            let parent = path.parent().map(|p| p.as_std_path().to_path_buf()).unwrap_or_default();
            let mut meta_path = parent.join(file_stem);
            meta_path.set_extension(ArtifactType::Metadata);
            trace!(rmeta=?path, kani_meta=?meta_path.display(), "map_kani_artifact");

            // This will check if the file exists and we just skip if it doesn't.
            Artifact::try_new(&meta_path, ArtifactType::Metadata).ok()
        } else if path.extension() == Some("rlib") {
            // We skip `rlib` files since we should also generate a `rmeta`.
            trace!(rlib=?path, "map_kani_artifact");
            None
        } else {
            // For all the other cases we write the path of the metadata into the output file.
            // The compiler should always write a valid stub into the artifact file, however the
            // kani-metadata file only exists if there were valid targets.
            trace!(artifact=?path, "map_kani_artifact");
            let input_file = File::open(path).ok()?;
            let stub: CompilerArtifactStub = serde_json::from_reader(input_file).ok()?;
            Artifact::try_new(&stub.metadata_path, ArtifactType::Metadata).ok()
        }
    });
    debug!(?result, "map_kani_artifact");
    result
}
