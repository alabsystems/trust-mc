// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Validation logic for trust-mc CLI arguments: `ValidateArgs` impls, conflict checks, path checks.

use std::path::Path;

use clap::{error::Error, error::ErrorKind};
use trust_mc_metadata::{ChcStepMode, ChcTrackLevel};

use crate::args::common::{CommonArgs, UnstableFeature};
use crate::args::harnesses_validation::validate_harnesses_shortcut;
use crate::args::solver::{AYChcAutoInvariantsMode, AYChcEngine, AYChcProofCoreMode};
use crate::args::{CargoKaniArgs, CargoKaniSubcommand, ConcretePlaybackMode, OutputFormat};
use crate::args::{StandaloneArgs, StandaloneSubcommand, VerificationArgs};
use crate::util::warning;

/// Trait used to perform extra validation after parsing.
pub(crate) trait ValidateArgs {
    /// Perform post-parsing validation but do not abort.
    fn validate(&self) -> Result<(), Error>;
}

/// Validate a set of arguments and ensure they are in a valid state.
/// This method will abort execution with a user friendly error message if the state is invalid.
pub(crate) fn check_is_valid<T>(command: &T)
where
    T: clap::Parser + ValidateArgs,
{
    if let Err(error) = command.validate() {
        error.format(&mut T::command()).exit();
    }
}

/// First step in two-phase stabilization.
/// When an unstable feature is first stabilized, print this warning that `-Z {feature}` has no effect.
/// This warning should last for one release only; in the next trust-mc release, remove it.
pub(crate) fn print_stabilized_feature_warning(
    verbosity: &CommonArgs,
    feature: UnstableFeature,
    version: &str,
) {
    if !verbosity.quiet {
        warning(&format_args!(
            "The `{feature}` feature has been stable since {version} and no longer requires {} to enable",
            feature.as_argument_string()
        ))
    }
}

/// Utility function to error out on arguments that are invalid Cargo specific.
///
/// We currently define a bunch of cargo specific arguments as part of the overall arguments,
/// however, they are invalid in the trust-mc standalone usage. Explicitly check them for now.
/// Inherited workaround from upstream Kani argument separation.
/// Upstream: <https://github.com/model-checking/kani/issues/1831>
fn check_no_cargo_opt(is_set: bool, name: &str) -> Result<(), Error> {
    if is_set {
        Err(Error::raw(
            ErrorKind::UnknownArgument,
            format!("argument `{name}` cannot be used with standalone trust-mc."),
        ))
    } else {
        Ok(())
    }
}

impl ValidateArgs for StandaloneArgs {
    fn validate(&self) -> Result<(), Error> {
        self.verify_opts.validate()?;

        match &self.command {
            Some(StandaloneSubcommand::VerifyStd(args)) => args.validate()?,
            Some(StandaloneSubcommand::List(args)) => args.validate()?,
            Some(StandaloneSubcommand::Autoharness(args)) => args.validate()?,
            // Fix #816: Invoke PlaybackArgs validation
            Some(StandaloneSubcommand::Playback(args)) => args.validate()?,
            None => {}
        }
        validate_harnesses_shortcut(
            self.list_harnesses,
            self.command.is_some(),
            self.verify_opts.common_args.quiet,
            self.verify_opts.trust_vc_bundle.is_some(),
        )?;

        // Cargo target arguments.
        check_no_cargo_opt(self.verify_opts.target.all_targets, "--all-targets")?;
        check_no_cargo_opt(!self.verify_opts.target.bench.is_empty(), "--bench")?;
        check_no_cargo_opt(self.verify_opts.target.benches, "--benches")?;
        check_no_cargo_opt(self.verify_opts.target.bins, "--bins")?;
        check_no_cargo_opt(self.verify_opts.target.lib, "--lib")?;
        check_no_cargo_opt(!self.verify_opts.target.bin.is_empty(), "--bin")?;
        check_no_cargo_opt(!self.verify_opts.target.example.is_empty(), "--example")?;
        check_no_cargo_opt(self.verify_opts.target.examples, "--examples")?;
        check_no_cargo_opt(!self.verify_opts.target.test.is_empty(), "--test")?;
        // Cargo common arguments.
        check_no_cargo_opt(self.verify_opts.cargo.all_features, "--all-features")?;
        check_no_cargo_opt(self.verify_opts.cargo.no_default_features, "--no-default-features")?;
        check_no_cargo_opt(!self.verify_opts.cargo.features().is_empty(), "--features / -F")?;
        check_no_cargo_opt(!self.verify_opts.cargo.package.is_empty(), "--package / -p")?;
        check_no_cargo_opt(!self.verify_opts.cargo.exclude.is_empty(), "--exclude")?;
        check_no_cargo_opt(self.verify_opts.cargo.workspace, "--workspace")?;
        check_no_cargo_opt(self.verify_opts.cargo.manifest_path.is_some(), "--manifest-path")?;
        if self.input.is_some() && self.verify_opts.trust_vc_bundle.is_some() {
            return Err(Error::raw(
                ErrorKind::ArgumentConflict,
                "argument `input` cannot be used together with `--trust-vc-bundle`.",
            ));
        }
        if self.command.is_none()
            && self.input.is_none()
            && self.verify_opts.trust_vc_bundle.is_none()
        {
            return Err(Error::raw(
                ErrorKind::MissingRequiredArgument,
                "standalone mode requires an input file or `--trust-vc-bundle <PATH>`.",
            ));
        }
        if let Some(input) = &self.input
            && !input.is_file()
        {
            return Err(Error::raw(
                ErrorKind::InvalidValue,
                format!(
                    "Invalid argument: Input invalid. `{}` is not a regular file.",
                    input.display()
                ),
            ));
        }
        Ok(())
    }
}

impl<T> ValidateArgs for Option<T>
where
    T: ValidateArgs,
{
    fn validate(&self) -> Result<(), Error> {
        self.as_ref().map_or(Ok(()), |inner| inner.validate())
    }
}

impl ValidateArgs for CargoKaniSubcommand {
    fn validate(&self) -> Result<(), Error> {
        match self {
            CargoKaniSubcommand::Autoharness(autoharness) => autoharness.validate(),
            CargoKaniSubcommand::Playback(playback) => playback.validate(),
            CargoKaniSubcommand::List(list) => list.validate(),
        }
    }
}

impl ValidateArgs for CargoKaniArgs {
    fn validate(&self) -> Result<(), Error> {
        self.verify_opts.validate()?;
        self.command.validate()?;
        validate_harnesses_shortcut(
            self.list_harnesses,
            self.command.is_some(),
            self.verify_opts.common_args.quiet,
            self.verify_opts.trust_vc_bundle.is_some(),
        )?;
        Ok(())
    }
}

impl ValidateArgs for VerificationArgs {
    fn validate(&self) -> Result<(), Error> {
        self.common_args.validate()?;
        self.validate_unstable_features()?;
        self.validate_conflicting_options()?;
        self.validate_chc_options()?;
        self.validate_deprecated_obsolete()?;
        self.validate_cbmc_only_flags()?;

        // Bespoke validations that don't fit into any of the categories above.
        if let Some(randomize_layout) = self.randomize_layout
            && self.concrete_playback.is_some()
        {
            let random_seed = if let Some(seed) = randomize_layout {
                format!(" -Z layout-seed={seed}")
            } else {
                String::new()
            };

            println!(
                "Using concrete playback with --randomize-layout.\n\
                The produced tests will have to be played with the same rustc arguments:\n\
                -Z randomize-layout{random_seed}"
            );
        }

        if let Some(out_dir) = &self.target_dir
            && out_dir.exists()
            && !out_dir.is_dir()
        {
            return Err(Error::raw(
                ErrorKind::InvalidValue,
                format!(
                    "Invalid argument: `--target-dir` argument `{}` is not a directory",
                    out_dir.display()
                ),
            ));
        }

        if let Some(out_file) = &self.sarif
            && out_file.exists()
            && out_file.is_dir()
        {
            return Err(Error::raw(
                ErrorKind::InvalidValue,
                format!(
                    "Invalid argument: `--sarif` argument `{}` is a directory",
                    out_file.display()
                ),
            ));
        }

        if let Some(out_file) = &self.proof_summary_json
            && out_file.exists()
            && out_file.is_dir()
        {
            return Err(Error::raw(
                ErrorKind::InvalidValue,
                format!(
                    "Invalid argument: `--proof-summary-json` argument `{}` is a directory",
                    out_file.display()
                ),
            ));
        }

        Ok(())
    }
}

impl VerificationArgs {
    /// Check that each unstable option has its requisite `-Z` feature enabled.
    fn validate_unstable_features(&self) -> Result<(), Error> {
        self.common_args.check_unstable(
            self.concrete_playback.is_some(),
            "concrete-playback",
            UnstableFeature::ConcretePlayback,
        )?;
        self.common_args.check_unstable(!self.c_lib.is_empty(), "c-lib", UnstableFeature::CFfi)?;
        self.common_args.check_unstable(
            self.no_codegen,
            "no-codegen",
            UnstableFeature::UnstableOptions,
        )?;
        self.common_args.check_unstable(
            self.extra_pointer_checks,
            "extra-pointer-checks",
            UnstableFeature::UnstableOptions,
        )?;
        self.common_args.check_unstable(
            self.ignore_global_asm,
            "ignore-global-asm",
            UnstableFeature::UnstableOptions,
        )?;
        self.common_args.check_unstable(
            self.no_restrict_vtable,
            "no-restrict-vtable",
            UnstableFeature::RestrictVtable,
        )?;
        self.common_args.check_unstable(
            self.coverage,
            "coverage",
            UnstableFeature::SourceCoverage,
        )?;
        self.common_args.check_unstable(
            self.output_into_files,
            "output-into-files",
            UnstableFeature::UnstableOptions,
        )?;
        self.common_args.check_unstable(
            self.harness_timeout.is_some(),
            "harness-timeout",
            UnstableFeature::UnstableOptions,
        )?;
        self.common_args.check_unstable(
            self.no_assert_contracts,
            "no-assert-contracts",
            UnstableFeature::FunctionContracts,
        )?;
        self.common_args.check_unstable(
            self.prove_safety_only,
            "prove-safety-only",
            UnstableFeature::UnstableOptions,
        )?;
        // Note: backend=ay is no longer unstable - it's the sole backend
        Ok(())
    }

    /// Check for general argument conflicts (non-CHC).
    fn validate_conflicting_options(&self) -> Result<(), Error> {
        if self.common_args.quiet && self.concrete_playback == Some(ConcretePlaybackMode::Print) {
            return Err(Error::raw(
                ErrorKind::ArgumentConflict,
                "Conflicting options: --concrete-playback=print and --quiet.",
            ));
        }
        if self.concrete_playback.is_some() && self.output_format == OutputFormat::Old {
            return Err(Error::raw(
                ErrorKind::ArgumentConflict,
                "Conflicting options: --concrete-playback isn't compatible with \
                --output-format=old.",
            ));
        }
        if self.concrete_playback.is_some() && self.jobs().will_multithread() {
            return Err(Error::raw(
                ErrorKind::ArgumentConflict,
                "Conflicting options: --concrete-playback isn't compatible with --jobs specifying multiple threads.",
            ));
        }
        if self.jobs().will_multithread() && self.output_format != OutputFormat::Terse {
            return Err(Error::raw(
                ErrorKind::ArgumentConflict,
                "Conflicting options: --jobs requires `--output-format=terse`",
            ));
        }
        if self.sarif.is_some() && self.output_format == OutputFormat::Old {
            return Err(Error::raw(
                ErrorKind::ArgumentConflict,
                "Conflicting options: --sarif isn't compatible with --output-format=old.",
            ));
        }
        if self.sarif.is_some() && self.only_codegen {
            return Err(Error::raw(
                ErrorKind::ArgumentConflict,
                "Conflicting options: --sarif isn't compatible with --only-codegen.",
            ));
        }
        Ok(())
    }

    /// Validate AY/CHC-specific option interactions.
    ///
    /// Most CHC sub-options require `--ay-chc` to be set. This function checks
    /// all such dependencies and validates transform names.
    fn validate_chc_options(&self) -> Result<(), Error> {
        self.validate_chc_requires_ay_chc()?;
        self.validate_chc_feature_gates()?;
        self.validate_chc_transforms()?;
        Ok(())
    }

    /// Check that CHC sub-options requiring `--ay-chc` are only used with it.
    fn validate_chc_requires_ay_chc(&self) -> Result<(), Error> {
        /// Return an error if `active` is true but `--ay-chc` was not provided.
        fn require_chc(active: bool, option: &str, ay_chc: bool) -> Result<(), Error> {
            if active && !ay_chc {
                return Err(Error::raw(
                    ErrorKind::ArgumentConflict,
                    format!("The `--{option}` option requires `--ay-chc`."),
                ));
            }
            Ok(())
        }

        require_chc(self.ay_chc_transform, "ay-chc-transform", self.ay_chc)?;
        require_chc(
            self.ay_chc_auto_invariants != AYChcAutoInvariantsMode::Off,
            "ay-chc-auto-invariants` option (non-off",
            self.ay_chc,
        )?;
        require_chc(
            self.ay_chc_proof_core != AYChcProofCoreMode::Off,
            "ay-chc-proof-core` option (non-off",
            self.ay_chc,
        )?;
        require_chc(self.ay_chc_debug, "ay-chc-debug", self.ay_chc)?;
        require_chc(
            self.ay_chc_track != ChcTrackLevel::Mem,
            "ay-chc-track` option (non-default",
            self.ay_chc,
        )?;
        require_chc(
            self.ay_chc_step != ChcStepMode::Auto,
            "ay-chc-step` option (non-default",
            self.ay_chc,
        )?;
        require_chc(self.ay_chc_int_lift, "ay-chc-int-lift", self.ay_chc)?;
        require_chc(self.ay_chc_skip_verify, "ay-chc-skip-verify", self.ay_chc)?;
        require_chc(self.ay_wide_mem, "ay-wide-mem`/`--wide-mem", self.ay_chc)?;
        require_chc(
            self.ay_chc_engine != AYChcEngine::Auto,
            "ay-chc-engine` option (non-auto",
            self.ay_chc,
        )?;
        require_chc(self.ay_chc_no_retry, "ay-chc-no-retry", self.ay_chc)?;
        require_chc(self.ay_chc_bounded_unroll, "ay-chc-bounded-unroll", self.ay_chc)?;
        require_chc(self.export_chc_comp.is_some(), "export-chc-comp", self.ay_chc)?;
        Ok(())
    }

    /// Check CHC feature-gate requirements (e.g., native build).
    fn validate_chc_feature_gates(&self) -> Result<(), Error> {
        if self.ay_chc_auto_invariants != AYChcAutoInvariantsMode::Off
            && !cfg!(feature = "ay-chc-native")
        {
            return Err(Error::raw(
                ErrorKind::ArgumentConflict,
                "The `--ay-chc-auto-invariants` option (non-off) requires a `ay-chc-native` build.",
            ));
        }
        Ok(())
    }

    /// Validate CHC transform flag dependencies and transform name values.
    fn validate_chc_transforms(&self) -> Result<(), Error> {
        if !self.ay_chc_transforms.is_empty() && !self.ay_chc_transform {
            return Err(Error::raw(
                ErrorKind::ArgumentConflict,
                "The `--ay-chc-transforms` option requires `--ay-chc-transform`.",
            ));
        }
        let valid_transforms = ["inline", "scalarize", "split-ite", "split-or", "all"];
        for transform in &self.ay_chc_transforms {
            if !valid_transforms.contains(&transform.as_str()) {
                return Err(Error::raw(
                    ErrorKind::InvalidValue,
                    format!(
                        "Invalid transform `{}`. Valid transforms: {}",
                        transform,
                        valid_transforms.join(", ")
                    ),
                ));
            }
        }
        Ok(())
    }

    /// Check for deprecated/obsolete options or stabilized unstable flags.
    fn validate_deprecated_obsolete(&self) -> Result<(), Error> {
        if self.restrict_vtable {
            return Err(Error::raw(
                ErrorKind::ValueValidation,
                format!(
                    "The restrict-vtable option is obsolete. Use `{}` instead.",
                    UnstableFeature::RestrictVtable.as_argument_string()
                ),
            ));
        }
        Ok(())
    }
}

pub(crate) fn validate_std_path(std_path: &Path) -> Result<(), Error> {
    if !std_path.exists() {
        Err(Error::raw(
            ErrorKind::InvalidValue,
            format!(
                "Invalid argument: `<STD_PATH>` argument `{}` does not exist",
                std_path.display()
            ),
        ))
    } else if !std_path.is_dir() {
        Err(Error::raw(
            ErrorKind::InvalidValue,
            format!(
                "Invalid argument: `<STD_PATH>` argument `{}` is not a directory",
                std_path.display()
            ),
        ))
    } else {
        let full_path = std_path.canonicalize()?;
        let dir = full_path.file_stem().ok_or_else(|| {
            Error::raw(
                ErrorKind::InvalidValue,
                format!(
                    "Invalid argument: `<STD_PATH>` path `{}` has no file stem",
                    full_path.display()
                ),
            )
        })?;
        if dir != "library" {
            Err(Error::raw(
                ErrorKind::InvalidValue,
                format!(
                    "Invalid argument: Expected `<STD_PATH>` to point to the `library` folder \
                containing the standard library crates.\n\
                Found `{}` folder instead",
                    dir.to_string_lossy()
                ),
            ))
        } else {
            Ok(())
        }
    }
}
