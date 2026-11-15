// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! T1 step S10, the M4 `Vec` case: a harness that reaches into `std` rather
//! than staying inside the harness crate, run against the parity library the
//! KEY carries (`-Zbuild-std=panic_abort,std,test`, `profile.dev.panic=abort`,
//! `-Zinline-mir=no`, `-Zmir-enable-passes=-RemoveStorageMarkers`,
//! `-Ztrust-verify=off`).
//!
//! Expected on the Trustc route: `VERIFICATION:- SUCCESSFUL` in both lanes,
//! with the assertion below reported as a SUCCESS check.
//!
//! **Measured, and it corrects the premise this fixture was asked for.** S10
//! asked for "a Vec push/len harness that needs MIR-encoded std". This one does
//! not need it. `Vec::new`, `Vec::push` and `Vec::len` are generic, so rustc
//! ships their MIR in `std`'s metadata whatever the std was built with, and
//! measured on seal 8595 the same file decides the same way against a
//! `--std prebuilt` (smoke) KEY: `SUCCESSFUL` here and `FAILED` for the
//! negative probe that asserts `v.len() == 3`. Both KEYs also log the same two
//! `Stdlib function MIR unavailable` warnings for `Vec`/`RawVec` drop glue. So
//! this harness demonstrates that std library code is modeled and the length is
//! real (the negative probe is what rules out a vacuous pass); it does NOT
//! discriminate parity from smoke. Counted rows still need the parity library —
//! that is T1-D5, which rests on the library's MIR shape (panic, inlining,
//! storage markers), not on this harness.

#[kani::proof]
fn vec_push_len_counts_both_pushes() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let mut v: Vec<u8> = Vec::new();
    v.push(a);
    v.push(b);
    assert!(v.len() == 2, "the vector holds both pushes");
}
