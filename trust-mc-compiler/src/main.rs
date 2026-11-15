// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The `trust-mc-compiler` binary: the embedded rustc driver of the frozen
//! Kani-compatibility lane.
//!
//! The engine is the `trust_mc_engine` rlib (package `trust-mc-engine`, whose
//! sources are the rest of this directory). Canonical trustc reaches the same
//! engine through `librustc_codegen_trust_mc.dylib` (package
//! `trust-mc-backend`). This file keeps only what is specific to the binary:
//! the hidden version probe.
#![feature(rustc_private)]
extern crate rustc_driver;

use std::env;

/// Embedded git SHA captured at build time by `build.rs`. Falls back to
/// `unknown-sha` on tarball/non-git builds; the shim treats that as
/// "skip staleness check". See `scripts/cargo-trust_mc`.
const TRUST_MC_GIT_SHA: &str = env!("TRUST_MC_GIT_SHA");
/// "1" when `build.rs` detected uncommitted changes, else "0".
const TRUST_MC_GIT_DIRTY: &str = env!("TRUST_MC_GIT_DIRTY");

/// Main function. Answer the version probe, or run the compiler.
fn main() {
    // Intercept the machine-readable version probe BEFORE rustc argument
    // parsing. Consumed by `scripts/cargo-trust_mc` to compare embedded SHA
    // against the repo's HEAD.
    //
    // Output format (single line, matches trust_mc-driver):
    //   trust_mc-version-sha sha=<sha> dirty=<0|1> version=<pkg-version>
    //
    // This is a hidden flag — do not document in user-facing help.
    if env::args().any(|arg| arg == "--trust_mc-version-sha") {
        println!(
            "trust_mc-version-sha sha={} dirty={} version={}",
            TRUST_MC_GIT_SHA,
            TRUST_MC_GIT_DIRTY,
            env!("CARGO_PKG_VERSION")
        );
        return;
    }

    trust_mc_engine::run_driver(env::args().collect());
}
