// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Define a benchmark with a "slow" cover used to ensure package targets are correctly picked.

#[cfg(kani)]
mod verify {
    #[kani::proof]
    fn slow_harness() {
        kani::cover!(true, "Cover bench `slow`");
    }
}

fn main() {
    // Do nothing
}
