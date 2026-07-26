// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Module that define trust_mc's command line interface. This includes all subcommands.

pub(crate) mod autoharness_args;
pub(crate) mod cargo;
pub(crate) mod common;
mod harnesses_validation;
pub(crate) mod list_args;
pub(crate) mod playback_args;
pub(crate) mod solver;
mod std_args;
mod validation;
mod verification;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_ay_chc;

// Re-export solver/type definitions so external consumers see them at args::<Type>.
#[allow(unused_imports)] // AYChcEngine used only by tests_ay_chc
pub(crate) use self::solver::{
    AYChcAutoInvariantsMode, AYChcEngine, AYChcProofCoreMode, AYSolver, Backend,
    ConcretePlaybackMode, NumThreads, OutputFormat, Timeout,
};
// Re-export validation items at args::<item>.
pub(crate) use self::validation::{
    ValidateArgs, check_is_valid, print_stabilized_feature_warning, validate_std_path,
};
// Re-export verification args at args::<Type>.
pub(crate) use self::verification::VerificationArgs;

use self::common::*;
pub(crate) use trust_mc_metadata::{ChcStepMode, ChcTrackLevel};

use std::path::PathBuf;

#[derive(Debug, clap::Parser)]
#[command(
    version,
    name = "trust-mc",
    about = "Verify a single Rust crate. For more information, see https://github.com/alabsystems/trust-mc",
    args_override_self = true,
    subcommand_negates_reqs = true,
    subcommand_precedence_over_arg = true,
    args_conflicts_with_subcommands = true
)]
pub(crate) struct StandaloneArgs {
    /// Rust file to verify
    pub input: Option<PathBuf>,

    /// List contracts and harnesses.
    #[arg(long = "harnesses")]
    pub list_harnesses: bool,

    /// Print authority evidence only when the linked AY build exactly matches the clean pinned commit.
    #[arg(long)]
    pub version_authority: bool,

    #[command(flatten)]
    pub verify_opts: VerificationArgs,

    #[command(subcommand)]
    pub command: Option<StandaloneSubcommand>,

    #[arg(long, hide = true)]
    pub crate_name: Option<String>,
}

/// trust-mc takes optional subcommands to request specialized behavior.
/// When no subcommand is provided, there is an implied verification subcommand.
#[derive(Debug, clap::Subcommand)]
pub(crate) enum StandaloneSubcommand {
    /// Create and run harnesses automatically for eligible functions. Implies -Z function-contracts and -Z loop-contracts.
    Autoharness(Box<autoharness_args::StandaloneAutoharnessArgs>),
    /// List contracts and harnesses.
    List(Box<list_args::StandaloneListArgs>),
    /// Execute concrete playback testcases of a local crate.
    Playback(Box<playback_args::KaniPlaybackArgs>),
    /// Verify the rust standard library.
    VerifyStd(Box<std_args::VerifyStdArgs>),
}

#[derive(Debug, clap::Parser)]
#[command(
    version,
    name = "cargo-trust-mc",
    about = "Verify a Rust crate. For more information, see https://github.com/alabsystems/trust-mc",
    args_override_self = true
)]
pub(crate) struct CargoKaniArgs {
    #[command(subcommand)]
    pub command: Option<CargoKaniSubcommand>,

    /// List contracts and harnesses.
    #[arg(long = "harnesses")]
    pub list_harnesses: bool,

    /// Print authority evidence only when the linked AY build exactly matches the clean pinned commit.
    #[arg(long)]
    pub version_authority: bool,

    #[command(flatten)]
    pub verify_opts: VerificationArgs,
}

/// cargo-trust-mc takes optional subcommands to request specialized behavior
#[derive(Debug, clap::Subcommand)]
pub(crate) enum CargoKaniSubcommand {
    /// Create and run harnesses automatically for eligible functions. Implies -Z function-contracts and -Z loop-contracts.
    /// See https://model-checking.github.io/kani/reference/experimental/autoharness.html for documentation.
    Autoharness(Box<autoharness_args::CargoAutoharnessArgs>),

    /// List contracts and harnesses.
    List(Box<list_args::CargoListArgs>),

    /// Execute concrete playback testcases of a local package.
    Playback(Box<playback_args::CargoPlaybackArgs>),
}
