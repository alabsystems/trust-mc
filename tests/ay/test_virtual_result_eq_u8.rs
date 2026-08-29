// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Regression guard for #3964: virtual aggregate returns must bridge back into
// typed memory before predicate helpers read the returned value by reference.
// Keep this on a plain struct so it isolates the virtual bridge from the
// separate enum-payload memory mirroring work in #3963.
//
// kani-expect: PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).

#[derive(Clone, Copy, PartialEq, Eq)]
struct Pair {
    left: u8,
    right: u8,
}

trait ProviderTrait {
    fn get(&self) -> Pair;
}

struct OnlyPair;

impl ProviderTrait for OnlyPair {
    fn get(&self) -> Pair {
        Pair { left: 1, right: 2 }
    }
}

fn probe_virtual_aggregate_eq() {
    let provider: &dyn ProviderTrait = &OnlyPair;
    let result = provider.get();
    assert!(result == Pair { left: 1, right: 2 });
}

#[kani::proof]
fn check_virtual_aggregate_eq() {
    probe_virtual_aggregate_eq();
}
