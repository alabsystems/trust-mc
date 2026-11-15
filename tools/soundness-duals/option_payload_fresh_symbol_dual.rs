// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// A counterexample that reads an unconstrained value must not be certified
// Genuine.
//
// `LocalKey::with` reaches the thread local through `Option<&T>`. For
// `T = bool` the Option datatype holds a Bool, while the payload arrives as a
// pointer, so `coerce_option_payload_expr` substitutes a fresh symbol. The site
// recorded only `aggregate_encoding_gap`, which no verdict reads. On main an
// unrelated translation drop in the same harness (the zero-sized `?` residual
// of `ok_or(AccessError)?`) kept the counterexample uncertified; once
// 7427e34c5 encoded that residual exactly, "assertion failed: b" on a true
// thread local was certified Genuine (kani/ThreadLocalRef/main.rs test_bool).
// The fresh payload is now recorded as an identified sound havoc: proofs are
// unaffected, and a counterexample that reads it is demoted.
//
// The u32 twins do not reach that fallback: the value is read from memory
// behind the accessor's pointer, which is not modelled either. The safe one is
// still certified Genuine (known red); the bug one guards the missed-bug side.
//
// Oracles, each confirmed with Kani 0.67.0 (kani-src at the corpus rev):
//   safe_thread_local_bool   SUCCESSFUL
//   bug_thread_local_bool    FAILED
//   safe_thread_local_u32    SUCCESSFUL
//   bug_thread_local_u32_ne  FAILED

thread_local! {
    static ON: bool = true;
    static OFF: bool = false;
    static SEVEN: u32 = 7;
}

#[kani::proof]
fn safe_thread_local_bool() {
    ON.with(|&b| {
        assert!(b);
    });
}

#[kani::proof]
fn bug_thread_local_bool() {
    OFF.with(|&b| {
        assert!(b); // FALSE
    });
}

#[kani::proof]
fn safe_thread_local_u32() {
    SEVEN.with(|&v| {
        assert!(v == 7);
    });
}

#[kani::proof]
fn bug_thread_local_u32_ne() {
    SEVEN.with(|&v| {
        assert!(v != 7); // FALSE: v == 7
    });
}
