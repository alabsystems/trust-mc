// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: --harness test_missing_stubbing_flag
// Test that Kani complains when use_stub_set is used without the stubbing feature enabled

fn some_function() {}

fn replacement_function() {}

kani::stub_set!(stub_set_without_flag, stub(some_function, replacement_function),);

#[kani::proof]
#[kani::use_stub_set(stub_set_without_flag)]
fn test_missing_stubbing_flag() {}
