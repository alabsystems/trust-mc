// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! T1 engine-flag case: the loop runs ten times but the harness unwinds it only
//! three, and the assertion after the loop is false. With unwinding checks on
//! (the default) the bound is reported: VERIFICATION:- FAILED on the unwinding
//! assertion. With `--no-unwinding-checks` the cut-off path is pruned and the
//! false assertion is unreachable, so the run reports SUCCESSFUL. The smoke uses
//! it to prove that an engine flag smuggled through `RUSTFLAGS -Cllvm-args` is
//! refused on the Trustc route rather than silently honored.

#[kani::proof]
#[kani::unwind(3)]
fn loop_runs_past_its_unwind_bound() {
    let mut i: u32 = 0;
    while i < 10 {
        i += 1;
    }
    assert!(i < 10, "the loop ran to 10");
}
