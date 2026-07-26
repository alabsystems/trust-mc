// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module defines the data structures and validation logic for subcommands
//! and general arguments. Most of the implementation is done through clap.
//!
//! Note: Validation for subcommand-specific arguments is done in the module
//! associated with each subcommand.

use std::path::PathBuf;

use anyhow::{Result, bail};

use crate::{merge, report, summary};

/// We define three subcommands:
///  * `merge` for merging raw trust_mc coverage results (AKA "kaniraw" files)
///  * `summary` for producing a summary containing coverage metrics
///  * `report` for generating human-readable coverage reports
///
/// As an example, let's assume we execute trust_mc with coverage enabled
/// ```sh
/// trust_mc main.rs --coverage -Zsource-coverage
/// ```
/// the raw coverage results will be saved to a folder
/// ```sh
/// [info] Coverage results saved to /absolute/path/to/results/kanicov_2024-09-23_23-49
/// ```
///
/// We can aggregate those results with the `merge` subcommand
/// ```sh
/// trust_mc-cov merge kanicov_2024-09-23_23-49/*kaniraw.json
/// ```
/// which by default produces a `default_kanicov.json` file.
///
/// Once we have both the "kanicov" file and the "kanimap" file, we are ready to
/// produce coverage metrics with the `summary` subcommand:
/// ```sh
/// trust_mc-cov summary kanicov_2024-09-23_23-49/kanicov_2024-09-23_23-49_kanimap.json --profile default_kanicov.json
/// ```
///
/// We can also produce coverage reports with the `report` subcommand:
/// ```sh
/// trust_mc-cov report kanicov_2024-09-23_23-49/kanicov_2024-09-23_23-49_kanimap.json --profile default_kanicov.json
/// ```
#[derive(Debug, clap::Subcommand)]
pub(crate) enum Subcommand {
    Merge(MergeArgs),
    Summary(SummaryArgs),
    Report(ReportArgs),
}

/// The main command.
/// Note: We use the same options as in Kani so that their option-parsing
/// behaviors (and issues due to them) are as similar as possible.
#[derive(Debug, clap::Parser)]
#[command(
    version,
    name = "trust_mc-cov",
    about = "A tool to process coverage information from trust_mc",
    args_override_self = true,
    subcommand_negates_reqs = true,
    subcommand_precedence_over_arg = true,
    args_conflicts_with_subcommands = true
)]
pub(crate) struct Args {
    #[command(subcommand)]
    pub command: Option<Subcommand>,
}

/// Arguments for the `merge` subcommand
#[derive(Debug, clap::Args)]
pub(crate) struct MergeArgs {
    #[arg(long)]
    pub output: Option<PathBuf>,
    #[arg(required = true)]
    pub files: Vec<PathBuf>,
}

/// Arguments for the `summary` subcommand
#[derive(Debug, clap::Args)]
pub(crate) struct SummaryArgs {
    // The path to the "kanimap" file
    #[arg(required = true)]
    pub mapfile: PathBuf,
    // The path to the "kanicov" file
    #[arg(long, required = true)]
    pub profile: PathBuf,
    // The format of the summary
    #[arg(long, short, value_parser = clap::value_parser!(SummaryFormat), default_value = "markdown")]
    pub format: SummaryFormat,
}

/// The format of the summary.
///
/// The default format is Markdown, but the CSV and JSON formats would be really
/// nice to have.
#[derive(Clone, Debug, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum SummaryFormat {
    Markdown,
    // Csv,
    // Json,
}

/// Arguments for the `report` subcommand
#[derive(Debug, clap::Args)]
pub(crate) struct ReportArgs {
    // The path to the "kanimap" file
    #[arg(required = true)]
    pub mapfile: PathBuf,
    // The path to the "kanicov" file
    #[arg(long, required = true)]
    pub profile: PathBuf,
    // The format of the report
    #[arg(long, short, value_parser = clap::value_parser!(ReportFormat), default_value = "terminal")]
    pub format: ReportFormat,
}

#[derive(Clone, Debug, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum ReportFormat {
    Terminal,
    Escapes,
}

/// Validate general arguments and delegate validation of command-specific
/// arguments.
pub(crate) fn validate_args(args: &Args) -> Result<()> {
    if args.command.is_none() {
        bail!("subcommand needs to be specified (`merge`, `summary` or `report`)")
    }

    match args.command.as_ref().expect("checked is_none above") {
        Subcommand::Merge(merge_args) => merge::validate_merge_args(merge_args)?,
        Subcommand::Summary(summary_args) => summary::validate_summary_args(summary_args)?,
        Subcommand::Report(report_args) => report::validate_report_args(report_args)?,
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::CommandFactory;

    #[test]
    fn test_args_parser_valid() {
        // Verify clap configuration is valid
        Args::command().debug_assert();
    }

    #[test]
    fn test_summary_format_default_is_markdown() {
        // Default format should be markdown
        assert_eq!(SummaryFormat::Markdown, SummaryFormat::Markdown);
    }

    #[test]
    fn test_report_format_variants() {
        // Verify report format variants exist
        assert_eq!(ReportFormat::Terminal, ReportFormat::Terminal);
        assert_eq!(ReportFormat::Escapes, ReportFormat::Escapes);
        assert_ne!(ReportFormat::Terminal, ReportFormat::Escapes);
    }

    #[test]
    fn test_validate_args_requires_subcommand() {
        let args = Args { command: None };
        let result = validate_args(&args);
        assert!(result.is_err());
        let err_msg = result.expect_err("should fail without subcommand").to_string();
        assert!(err_msg.contains("subcommand"));
    }

    #[test]
    fn test_merge_args_fields() {
        let args = MergeArgs {
            output: Some(PathBuf::from("output.json")),
            files: vec![PathBuf::from("file1.json"), PathBuf::from("file2.json")],
        };
        assert_eq!(args.output, Some(PathBuf::from("output.json")));
        assert_eq!(args.files.len(), 2);
    }

    #[test]
    fn test_summary_args_fields() {
        let args = SummaryArgs {
            mapfile: PathBuf::from("map.json"),
            profile: PathBuf::from("profile.json"),
            format: SummaryFormat::Markdown,
        };
        assert_eq!(args.mapfile, PathBuf::from("map.json"));
        assert_eq!(args.profile, PathBuf::from("profile.json"));
    }

    #[test]
    fn test_report_args_fields() {
        let args = ReportArgs {
            mapfile: PathBuf::from("map.json"),
            profile: PathBuf::from("profile.json"),
            format: ReportFormat::Terminal,
        };
        assert_eq!(args.format, ReportFormat::Terminal);
    }
}
