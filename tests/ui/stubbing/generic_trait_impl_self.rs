// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// kani-flags: --harness unsupported_harness -Z stubbing
// This test documents that trait methods from generic impls are currently
// unsupported as stubbing targets (Part of #2217).

#![allow(dead_code)]

trait Describe {
    fn tag(&self) -> usize;
}

struct Wrapper<T>(T);

impl<T> Describe for Wrapper<T> {
    fn tag(&self) -> usize {
        let _ = &self.0;
        0
    }
}

fn stub_tag<T>(_receiver: &Wrapper<T>) -> usize {
    7
}

#[kani::proof]
#[kani::stub(<Wrapper<u8> as Describe>::tag, stub_tag)]
#[kani::stub(<Wrapper<bool> as Describe>::tag, stub_tag)]
fn unsupported_harness() {}
