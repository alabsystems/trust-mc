// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This test documents a coverage replacement gap: the return in `get` should be
//! `UNCOVERED`, but the current coverage pipeline reports the whole function as
//! `COVERED`. Coverage is outside the current 100% replacement claim until this
//! is fixed; see <https://github.com/model-checking/kani/issues/3441>.

fn get(s: &[i16], index: usize) -> i16 {
    s[index]
}

#[kani::proof]
fn main() {
    get(&[7, -83, 19], 15);
}
