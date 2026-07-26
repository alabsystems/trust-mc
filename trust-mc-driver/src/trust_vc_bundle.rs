// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Direct MergeBundle verification entry point.

use std::fs;
use std::path::Path;

use anyhow::{Context, Result};
use tempfile::NamedTempFile;
use trust_mc_metadata::{HarnessAttributes, HarnessKind, HarnessMetadata};
use trust_mc_trust_vc_ingest::ingest_bundle;

use crate::harness_runner::HarnessResult;
use crate::session::KaniSession;

pub(crate) fn verify_trust_vc_bundle(session: KaniSession, bundle_path: &Path) -> Result<()> {
    let bundle_json = fs::read_to_string(bundle_path)
        .with_context(|| format!("failed to read trust_vc bundle {}", bundle_path.display()))?;
    let unit = ingest_bundle(&bundle_json)
        .with_context(|| format!("failed to ingest trust_vc bundle {}", bundle_path.display()))?;
    let program = unit
        .to_program()
        .with_context(|| format!("failed to build SMT program for {}", unit.source_id))?;

    let mut temp_smt = NamedTempFile::new().context("failed to allocate temporary SMT file")?;
    use std::io::Write;
    temp_smt
        .write_all(program.to_string().as_bytes())
        .context("failed to write trust_vc SMT program")?;

    let harness = synthetic_bundle_harness(&unit.source_id, bundle_path);
    let deadline = crate::deadline::Deadline::for_harness(session.args.harness_timeout);
    let result = session.run_ay(temp_smt.path(), &harness, 0, deadline)?;
    session.process_output(&result, &harness, 0)?;

    let results = [HarnessResult { harness: &harness, result }];
    // Exactly one synthetic harness — the zero-harness success-with-note
    // path must never trigger here.
    session.print_final_summary(&results, 1)
}

fn synthetic_bundle_harness(source_id: &str, bundle_path: &Path) -> HarnessMetadata {
    HarnessMetadata {
        pretty_name: source_id.to_string(),
        mangled_name: source_id.to_string(),
        crate_name: "trust_vc_bundle".to_string(),
        original_file: bundle_path.display().to_string(),
        original_start_line: 0,
        original_end_line: 0,
        model_file: bundle_path.to_path_buf(),
        attributes: HarnessAttributes::new(HarnessKind::Proof),
        contract: None,
        has_loop_contracts: false,
        is_automatically_generated: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn synthetic_bundle_harness_uses_source_id_and_path() {
        let harness = synthetic_bundle_harness(
            "trust_vc::examples::arith::lemma_sum_nonneg",
            Path::new("/tmp/bundle.json"),
        );
        assert_eq!(harness.pretty_name, "trust_vc::examples::arith::lemma_sum_nonneg");
        assert_eq!(harness.original_file, "/tmp/bundle.json");
        assert!(matches!(harness.attributes.kind, HarnessKind::Proof));
    }
}
