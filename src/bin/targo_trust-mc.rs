// Copyright Kani Contributors
// Modifications Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use anyhow::Result;

fn main() -> Result<()> {
    // Trust-native installed surface: `targo trust-mc ...` dispatches to this
    // binary (targo-trust-mc), matching the targo-<x> subcommand family.
    // The tool-internal proxy/argv identity intentionally stays `cargo-trust-mc`
    // (a PRIVATE compat protocol, like the retired kani / cargo-kani identities)
    // so trust-mc-driver's invocation-identity parsing and the staleness shim
    // keep recognizing it. See src/bin/cargo_trust-mc.rs (the back-compat twin).
    trust_mc::proxy("cargo-trust-mc")
}
