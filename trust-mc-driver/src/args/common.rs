// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Define arguments that should be common to all subcommands in trust_mc.
use crate::args::{ValidateArgs, print_stabilized_feature_warning};
use clap::{ValueEnum, error::Error, error::ErrorKind};
use std::sync::atomic::{AtomicBool, Ordering};
pub(crate) use trust_mc_metadata::{EnabledUnstableFeatures, UnstableFeature};

/// Process-global mirror of `--quiet`, for the output sites that cannot reach
/// the parsed arguments.
///
/// `--quiet` is documented as "print nothing but the exit code and requested
/// artifacts", yet the `[AY:*]` marker lines went to stdout through bare
/// `println!` / `solver_stdout!` calls, so a quiet run still printed
/// `[AY:PROOF] CHC verification: ...` and `[AY:CTREX_CAT:Genuine]`. Most of
/// those sites do have a `&KaniSession` and are gated on it directly; the CHC
/// portfolio's `solver_stdout!` sites do not — several fire from free
/// functions (`classify_unknown`, `bail_unknown_if_deadline_exhausted`, ...)
/// that never see the arguments. Threading a flag through all of them would be
/// a large, mechanical, merge-hostile change for a display-only decision, so
/// the flag is mirrored here instead: the driver is one process per
/// invocation, and [`set_quiet_output`] is called once before any harness runs.
///
/// It defaults to `false`, so any path that never sets it — unit tests, the
/// library target — keeps the exact pre-existing output. Only the WRITE is
/// suppressed; every verdict, classification and exit code is unchanged.
static QUIET_OUTPUT: AtomicBool = AtomicBool::new(false);

/// Mirror `--quiet` into [`QUIET_OUTPUT`]. Called once from
/// `HarnessRunner::check_all_harnesses`, before any solver output can happen.
pub(crate) fn set_quiet_output(quiet: bool) {
    QUIET_OUTPUT.store(quiet, Ordering::Relaxed);
}

/// Whether `--quiet` was requested. See [`QUIET_OUTPUT`].
pub(crate) fn quiet_output() -> bool {
    QUIET_OUTPUT.load(Ordering::Relaxed)
}

/// Message formats available for subcommand output.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, ValueEnum, strum_macros::Display)]
#[strum(serialize_all = "kebab-case")]
pub(crate) enum MessageFormat {
    /// Print diagnostic messages in a user friendly format.
    #[default]
    Human,
    /// Print diagnostic messages in JSON format.
    Json,
}

/// Common trust-mc arguments that we expect to be included in most subcommands.
#[derive(Debug, clap::Args)]
#[clap(next_help_heading = "Common Options")]
pub(crate) struct CommonArgs {
    /// Produce full debug information
    #[arg(long)]
    pub debug: bool,
    /// Produces no output, just an exit code and requested artifacts; overrides --verbose
    #[arg(long, short, conflicts_with_all(["debug", "verbose"]))]
    pub quiet: bool,
    /// Output processing stages and commands, along with minor debug information
    #[arg(long, short, default_value_if("debug", "true", Some("true")))]
    pub verbose: bool,
    /// Enable usage of unstable options
    #[arg(long, hide = true)]
    pub enable_unstable: bool,

    /// We no longer support dry-run. Use `--verbose` to see the commands being printed during
    /// trust-mc execution.
    #[arg(long, hide = true)]
    pub dry_run: bool,

    /// Enable an unstable feature.
    #[clap(flatten)]
    pub unstable_features: EnabledUnstableFeatures,

    /// Control diagnostic output format: 'human' for readable text, 'json' for machine-parseable.
    #[arg(long, default_value = "human")]
    pub message_format: MessageFormat,
}

impl ValidateArgs for CommonArgs {
    fn validate(&self) -> Result<(), Error> {
        if self.dry_run {
            return Err(Error::raw(
                ErrorKind::ValueValidation,
                "The `--dry-run` option is obsolete. Use --verbose instead.",
            ));
        }
        if self.enable_unstable {
            return Err(Error::raw(
                ErrorKind::ValueValidation,
                "The `--enable-unstable` option is obsolete. Enable the appropriate unstable feature(s) with `-Z {feature}` instead.",
            ));
        }

        // Warn if a deprecated unstable feature is enabled.
        for feature in self.unstable_features.iter() {
            let stabilization_version = feature.stabilization_version();
            if let Some(version) = stabilization_version {
                print_stabilized_feature_warning(self, *feature, version);
            }
        }

        Ok(())
    }
}

impl CommonArgs {
    pub(crate) fn check_unstable(
        &self,
        enabled: bool,
        argument: &str,
        required: UnstableFeature,
    ) -> Result<(), Error> {
        if enabled && !self.unstable_features.contains(required) {
            return Err(Error::raw(
                ErrorKind::MissingRequiredArgument,
                format!(
                    "The `--{argument}` option is unstable and requires `{}` to be used.",
                    required.as_argument_string()
                ),
            ));
        }
        Ok(())
    }
}

/// The verbosity level to be used in trust_mc.
pub(crate) trait Verbosity {
    /// Whether we should be quiet.
    fn quiet(&self) -> bool;
    /// Whether we should be verbose.
    /// Note that `debug == true` must imply `verbose() == true`.
    fn verbose(&self) -> bool;
    /// Whether any verbosity was selected.
    fn is_set(&self) -> bool;
}

impl Verbosity for CommonArgs {
    fn quiet(&self) -> bool {
        self.quiet
    }

    fn verbose(&self) -> bool {
        self.verbose || self.debug
    }

    fn is_set(&self) -> bool {
        self.quiet || self.verbose || self.debug
    }
}
