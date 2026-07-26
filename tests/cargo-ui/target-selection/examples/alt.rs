// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Define an example with an "alt" cover used to ensure package targets are correctly picked.

#[cfg(kani)]
mod verify {
    #[kani::proof]
    fn alt_harness() {
        kani::cover!(true, "Cover example `alt`");
    }
}

fn main() {
    // Do nothing
}
