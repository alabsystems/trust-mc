// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Direct AY backend entrypoint for CHC integration.

use std::path::Path;

use crate::property_model::Property;
use crate::session::KaniSession;
use crate::verification_result::{FailedProperties, VerificationStatus};
use trust_mc_metadata::HarnessMetadata;

macro_rules! solver_stdout {
    ($($arg:tt)*) => {{
        // Honor `--quiet` ("no output, just an exit code and requested
        // artifacts"): this macro used to write straight to stdout, so a quiet
        // run still printed `[AY:PROOF] CHC verification: ...` and the other
        // solver markers. The gate lives in the macro rather than at the ~70
        // call sites because several of them are free functions with no
        // `&KaniSession` in reach. Only the WRITE is skipped — the verdict and
        // the exit code are untouched — and with `--quiet` absent the bytes
        // are identical to before, which is what `scripts/ay-compiletest.sh`
        // parses.
        if !crate::args::common::quiet_output() {
            use std::io::Write;
            let stdout = std::io::stdout();
            let mut handle = stdout.lock();
            let _ = writeln!(handle, $($arg)*);
        }
    }};
}

impl KaniSession {
    /// Try to run AY solver using direct linking (no subprocess).
    ///
    /// This method uses AY's native Rust API directly, eliminating the need for
    /// subprocess spawning and text file I/O. Only available with ay-direct feature.
    ///
    /// The in-process solve is budgeted with
    /// `min(tool_timeout, deadline.remaining())` — previously this path was
    /// hardwired to the 600s default tool timeout regardless of the harness
    /// budget.
    ///
    /// Returns (status, failed_properties, properties) on success.
    pub(in crate::call_ay) fn try_ay_direct(
        &self,
        smt_file: &Path,
        _harness: &HarnessMetadata,
        deadline: crate::deadline::Deadline,
    ) -> anyhow::Result<(VerificationStatus, FailedProperties, Vec<Property>)> {
        if self.args.common_args.verbose {
            solver_stdout!("[AY-direct] Using direct AY linking (no subprocess)");
        }

        let smt_content = std::fs::read_to_string(smt_file)
            .map_err(|e| anyhow::anyhow!("Failed to read SMT file: {e}"))?;

        let timeout = match self.tool_timeout() {
            Some(tool_timeout) => deadline.clamp(tool_timeout),
            // Tool timeout explicitly disabled (--tool-timeout=0): the
            // per-harness deadline still bounds the in-process solve.
            None => deadline.remaining(),
        };
        crate::ay_direct::run_ay_direct_with_timeout(
            &smt_content,
            self.args.common_args.verbose,
            timeout,
        )
    }
}
