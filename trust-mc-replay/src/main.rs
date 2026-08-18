// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Standalone obligation-REPLAY harness.
//!
//! Problem: the native verifier (ay-chc / trust-mc) is statically linked INTO
//! `trustc` (a rustc driver), so any verifier change forces a 26-minute
//! `./x.py build --stage 2 targo targo-trust` before you can see its effect.
//! That glacial loop is a soundness risk.
//!
//! Fix: the verifier logic can be exercised on a SERIALIZED obligation without
//! going through rustc at all. The compiler already serializes the exact
//! `trust_ir::NativeVerificationBundle` it feeds to the verifier when
//! `TRUST_DUMP_NATIVE_BUNDLE=<dir>` is set (see
//! `compiler/rustc_mir_transform/src/trust_verify.rs`). This harness loads that
//! JSON and runs the SAME private exact-module native path the driver runs:
//!
//!   solve_bundle_native_proof_grade(bundle)
//!     -> validate complete TrustIr module + proof-authority profile
//!     -> freshly translate obligations (trust-mc-trust-bmc)
//!     -> solve typed CHC/PDR requests
//!     -> mint and re-check live, non-serializable exact-module authority
//!
//! Because it is a leaf binary, `cargo build -p trust-mc-replay` finishes in
//! seconds, so you can edit ay-chc / trust-mc and re-check a real obligation
//! immediately.
//! The resulting authority covers the exact dumped TrustIr module. As in the
//! compiler integration, a source-level claim additionally needs the compiler's
//! private source-to-module binding; serialized replay output is not authority.
//!
//! Usage:
//!   1. ONCE: capture a faithful bundle with the existing stage-2 toolchain
//!        TRUST_DUMP_NATIVE_BUNDLE=/tmp/bundles \
//!          <stage2>/targo-trust trust check path/to/proof.rs
//!      -> writes /tmp/bundles/native_bundle_<fn>.json
//!   2. ITERATE (seconds each):
//!        cargo build -p trust-mc-replay
//!        trust-mc-replay /tmp/bundles/native_bundle_<fn>.json

use std::path::Path;
use std::time::{Duration, Instant};

use anyhow::{Context, Result, anyhow};
use trust_mc_core::ChcPdrSolveOptions;
use trust_mc_driver::NativeTrustIrChcPdrRunner;

fn main() -> Result<()> {
    let mut args = std::env::args().skip(1);
    let path =
        args.next().context("usage: trust-mc-replay <native_bundle_*.json> [timeout_secs]")?;
    // Optional wall-clock cap (default 60s) so a regression that makes the lane
    // diverge fails fast instead of hanging the iteration loop.
    let timeout_secs: u64 = args
        .next()
        .map(|s| s.parse())
        .transpose()
        .context("timeout_secs must be an integer")?
        .unwrap_or(60);

    let json =
        std::fs::read_to_string(&path).with_context(|| format!("failed to read bundle {path}"))?;

    // Faithful, round-trippable input: the exact serde-serialized bundle the
    // compiler handed the verifier. No lossy Debug-string re-parsing.
    let load_start = Instant::now();
    let bundle: trust_ir::NativeVerificationBundle = serde_json::from_str(&json)
        .with_context(|| format!("failed to deserialize NativeVerificationBundle from {path}"))?;
    println!(
        "loaded bundle {} (schema v{}, {} request(s)) in {:?}",
        short_name(&path),
        bundle.schema_version,
        bundle.requests.len(),
        load_start.elapsed()
    );

    let options = ChcPdrSolveOptions::default().with_timeout(Duration::from_secs(timeout_secs));
    let runner = NativeTrustIrChcPdrRunner::with_solve_options(options);

    // Run the authoritative bundle boundary, not the generic public typed
    // solver. The latter intentionally returns only a reject-only candidate;
    // it cannot establish that the submitted CHC faithfully represents this
    // exact TrustIr module.
    let solve_start = Instant::now();
    let evidence = runner
        .solve_bundle_native_proof_grade(&bundle)
        .map_err(|e| anyhow!("native exact-module replay failed: {e}"))?;
    let elapsed = solve_start.elapsed();

    let proved = evidence.obligations.len();
    let not_proved = evidence.not_proved.len();
    let refuted = evidence.refuted.len();
    println!("replayed {} obligation(s) in {elapsed:?}\n", proved + not_proved + refuted);

    for (i, solved) in evidence.obligations.iter().enumerate() {
        // Recompute the private mutation-bound seal at the point where this
        // harness labels the row proved. The serialized transport beside it is
        // diagnostic only and cannot recreate this borrowed capability.
        let authority = solved.verification.authorized_native_proof().map_err(|e| {
            anyhow!(
                "bundle runner returned row {} without live exact-module authority: {e}",
                solved.translated.obligation.obligation_id
            )
        })?;
        let obligation = &solved.translated.obligation;
        println!(
            "[{i}] {} :: {}\n     route={:?}  verdict=PROVED [exact-module authority: {:?}]",
            obligation.function_name,
            obligation.obligation_id,
            solved.verification.route,
            authority.candidate().proof_kind,
        );
    }

    for (offset, unresolved) in evidence.not_proved.iter().enumerate() {
        let i = proved + offset;
        let obligation = &unresolved.translated.obligation;
        println!(
            "[{i}] {} :: {}\n     verdict=NOT-PROVED [{}]",
            obligation.function_name, obligation.obligation_id, unresolved.reason
        );
    }

    for (offset, row) in evidence.refuted.iter().enumerate() {
        let i = proved + not_proved + offset;
        let obligation = &row.translated.obligation;
        // A witnessed refutation is dev-loop diagnostics here; the compiler's
        // consumer independently revalidates the witness before any verdict.
        println!(
            "[{i}] {} :: {}\n     verdict=REFUTED (witnessed; consumer revalidation required)",
            obligation.function_name, obligation.obligation_id
        );
    }

    println!(
        "\nsummary: {proved} proved (live exact-module authority), {not_proved} not-proved, {refuted} refuted (witnessed), {} total",
        proved + not_proved + refuted
    );

    // Non-zero exit if nothing received live exact-module authority, so scripts
    // cannot accidentally gate on generic public candidate bytes.
    if proved == 0 {
        std::process::exit(2);
    }
    Ok(())
}

fn short_name(path: &str) -> &str {
    Path::new(path).file_name().and_then(|s| s.to_str()).unwrap_or(path)
}
