// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Copy before in-place generation. Playback must panic at "guarded input bug",
//! never at a byte-count mismatch, missing input, or leftover-input assertion.

#[inline(never)]
fn inactive_input() -> u16 {
    kani::any()
}

#[inline(never)]
fn active_input() -> u8 {
    kani::any()
}

#[kani::proof]
fn guarded_inputs() {
    let branch: bool = kani::any();
    kani::assume(!branch);
    if branch {
        assert!(inactive_input() != 99);
    }
    let value = active_input();
    assert!(value != 7, "guarded input bug");
}
