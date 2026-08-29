// kani-expect: PROOF
// kani-flags: --default-unwind 3
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Part of #4006: isolate the metadata half of dyn slice projection.
//!
//! This localizer strips out iterator lowering so current-head measurements stay
//! focused on the remaining wide-ref metadata residual.

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
fn check_metadata_only() {
    let original: Concrete<[u8]> = Concrete { inner: &[1u8, 2u8] };
    let wrapper = &original as &dyn Wrapper<[u8]>;

    assert_eq!(std::mem::size_of_val(wrapper), 16);
    assert_eq!(std::mem::size_of_val(&wrapper.inner()), 16);
    assert_eq!(std::mem::size_of_val(wrapper.inner()), 2);
    assert_eq!(wrapper.inner().len(), 2);
}

fn main() {
    check_metadata_only();
}
