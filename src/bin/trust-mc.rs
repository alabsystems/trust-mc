// Copyright Kani Contributors
// Modifications Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use anyhow::Result;

fn main() -> Result<()> {
    trust_mc::proxy("trust-mc")
}
