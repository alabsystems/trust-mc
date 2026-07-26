// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// compile-flags: --edition 2018

use kani::shadow::ShadowMem;

#[kani::proof]
fn main() {
    let _shadow: Option<ShadowMem<bool>> = None;
}
