// Copyright Kani Contributors
// Modifications Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The `trust-mc` front door: a friendly wrapper around `trust-mc-driver`.
//!
//! It answers `--version`, `--help`, `example` and `doctor` with nothing
//! installed, verifies a single `.rs` file with no project setup, and turns a
//! missing engine, sysroot or solver into the exact command that fixes it.
//! All verification is done by the engine — see `src/frontend.rs`.
//!
//! `cargo-trust-mc` keeps using the historical `trust_mc::proxy` path.

use std::process::ExitCode;

fn main() -> ExitCode {
    trust_mc::front_door()
}
