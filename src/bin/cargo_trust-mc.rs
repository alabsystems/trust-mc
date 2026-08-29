// Copyright Kani Contributors
// Modifications Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::process::ExitCode;

fn main() -> ExitCode {
    trust_mc::cargo_proxy("cargo-trust-mc")
}
