// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z quantifiers

#[kani::proof]
fn typed_bounded_quantifiers_harness() {
    let target: u64 = 3;
    kani::assert(kani::forall!(|i: u64 in (0, 4)| i < 4), "typed forall u64");
    kani::assert(kani::exists!(|i: u64 in (0, 4)| i == target), "typed exists u64");
}
