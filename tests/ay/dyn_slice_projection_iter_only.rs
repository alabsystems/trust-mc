// kani-expect: PROOF
// NOTE: 1 harness(es) CTREX→UNKNOWN (solver nondeterminism).
// kani-flags: --default-unwind 3
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Part of #4006: isolate the iterator half of dyn slice projection.
//!
//! This localizer keeps the known iterator-unsoundness lane separate from the
//! metadata-only residual.

trait Wrapper<T: ?Sized> {
    fn inner(&self) -> &T;
}

struct Concrete<'a, T: ?Sized> {
    inner: &'a T,
}

impl<T: ?Sized> Wrapper<T> for Concrete<'_, T> {
    fn inner(&self) -> &T {
        self.inner
    }
}

#[kani::proof]
fn check_iter_only() {
    let original: Concrete<[u8]> = Concrete { inner: &[1u8, 2u8] };
    let wrapper = &original as &dyn Wrapper<[u8]>;
    let mut sum = 0u8;

    for next in wrapper.inner() {
        sum += next;
    }

    assert_eq!(sum, 3);
}

fn main() {
    check_iter_only();
}
