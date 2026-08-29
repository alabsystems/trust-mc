// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use clap::Parser;
use replacement_audit::progress::{ProgressConfig, run};
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

#[derive(Debug, Parser)]
#[command(
    name = "replacement-progress",
    about = "Report progress toward trust_mc's 100% Kani replacement accounting target"
)]
struct Args {
    #[arg(
        long,
        value_name = "INVENTORY_JSON",
        default_value = "tests/trust-mc/replacement-harness-inventory.json",
        help = "Mixed replacement accounting inventory"
    )]
    inventory: PathBuf,

    #[arg(
        long,
        value_name = "INVENTORY_JSON",
        default_value = "tests/trust-mc/replacement-harness-inventory.proof.json",
        help = "Proof-quality replacement subset inventory"
    )]
    proof_inventory: PathBuf,

    #[arg(
        long,
        value_name = "CLOSURE_JSON",
        default_value = "tests/trust-mc/non-proof-closure.json",
        help = "Checked closure for non-PROOF mixed-inventory rows"
    )]
    non_proof_closure: PathBuf,

    #[arg(
        long,
        value_name = "REPORT_JSON",
        help = "Optional schema-v2 compiletest per-harness report to score against the proof inventory; full reports are accepted and may be repeated for shards/focused lanes"
    )]
    report: Vec<PathBuf>,

    #[arg(
        long,
        value_name = "COMMIT",
        help = "Require report commit to match this 40-character trust_mc commit; defaults to the current git HEAD when available"
    )]
    expected_commit: Option<String>,

    #[arg(
        long,
        value_name = "PIN",
        help = "Require report ay_pin to match this 40-character AY commit; defaults to the pinned AY rev in Cargo.toml when available"
    )]
    expected_ay_pin: Option<String>,

    #[arg(
        long,
        value_name = "DIGEST",
        help = "Require report tree_fingerprint to match this 64-character digest"
    )]
    expected_tree_fingerprint: Option<String>,

    #[arg(
        long,
        value_name = "REPO_ROOT",
        default_value = ".",
        help = "Repository root used to derive current git HEAD, tree state, and pinned AY rev"
    )]
    repo_root: PathBuf,

    #[arg(
        long,
        help = "Exit nonzero unless the supplied report and closure establish complete replacement accounting"
    )]
    require_complete: bool,
}

fn main() -> ExitCode {
    match run(&Args::parse().into()) {
        Ok(outcome) => {
            write_lines(&outcome.lines, io::stdout().lock());
            if outcome.complete || !outcome.require_complete {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
        Err(err) => {
            let mut stderr = io::stderr().lock();
            let _ = writeln!(stderr, "replacement-progress: {err}");
            ExitCode::FAILURE
        }
    }
}

fn write_lines(lines: &[String], mut writer: impl Write) {
    for line in lines {
        let _ = writeln!(writer, "{line}");
    }
}

impl From<Args> for ProgressConfig {
    fn from(args: Args) -> Self {
        Self {
            inventory: args.inventory,
            proof_inventory: args.proof_inventory,
            non_proof_closure: args.non_proof_closure,
            reports: args.report,
            expected_commit: args.expected_commit,
            expected_ay_pin: args.expected_ay_pin,
            expected_tree_fingerprint: args.expected_tree_fingerprint,
            repo_root: args.repo_root,
            require_complete: args.require_complete,
        }
    }
}
