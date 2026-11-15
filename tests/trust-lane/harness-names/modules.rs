// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Harnesses at the crate root and in nested modules. Kani reports them by their
//! crate-relative path (`top`, `first::check`, `second::inner::check_inner`), and
//! `--harness` / `--exact` match that path. Trust's `Instance::name` prints the crate name
//! in front (`modules::first::check`); both compiler routes must report and match the Kani
//! form.

#[kani::proof]
fn top() {
    assert!(1u8.wrapping_add(1) == 2, "top");
}

mod first {
    #[kani::proof]
    fn check() {
        assert!(2u8.wrapping_add(2) == 4, "first check");
    }
}

mod second {
    #[kani::proof]
    fn check() {
        assert!(3u8.wrapping_add(3) == 6, "second check");
    }

    mod inner {
        #[kani::proof]
        fn check_inner() {
            assert!(4u8.wrapping_add(4) == 8, "inner check");
        }
    }
}
