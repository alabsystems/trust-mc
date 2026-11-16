// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

// Real shadow instrumentation must be observed as well as the semantic result.
// kani-flags: -Z uninit-checks
#[kani::proof]
pub fn canonical_shadow_unchanged_safe() {
    let values = vec![3u64];
    let pointer = values.as_ptr();
    assert!(unsafe { *pointer } == 3);
}
#[kani::proof]
pub fn canonical_shadow_unchanged_bug() {
    let values = vec![3u64];
    let pointer = values.as_ptr();
    assert!(unsafe { *pointer } == 9);
}
