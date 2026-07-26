// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// Required so we can use kani_macros attributes.
#![feature(register_tool)]
#![register_tool(kanitool)]
#![register_tool(trust_mctool)]
// Used for rustc_diagnostic_item.
// Note: We could use a kanitool attribute instead.
#![feature(rustc_attrs)]
// Used to model simd.
#![feature(repr_simd)]
#![feature(generic_const_exprs)]
#![allow(incomplete_features)]
// Features used for tests only.
#![cfg_attr(test, feature(core_intrinsics, portable_simd))]
// Required for `rustc_diagnostic_item` and `core_intrinsics`
#![allow(internal_features)]
// Required for implementing memory predicates.
#![feature(layout_for_ptr)]
#![feature(ptr_metadata)]
#![feature(f16)]
#![feature(f128)]
#![feature(convert_float_to_int)]
#![feature(sized_hierarchy)]

// Allow us to use `kani::` to access crate features.
extern crate self as kani;

pub mod arbitrary;
pub mod bounded_arbitrary;
#[cfg(feature = "concrete_playback")]
mod concrete_playback;
pub mod futures;
pub mod hashmap;
pub mod invariant;
pub mod iter;
pub mod shadow;
pub mod vec;

#[cfg(feature = "concrete_playback")]
pub use concrete_playback::concrete_playback_run;
pub use invariant::Invariant;

#[cfg(not(feature = "concrete_playback"))]
/// Compile-compatibility stub for generated concrete-playback tests in
/// ordinary verification builds.
///
/// This keeps `kani::concrete_playback_run(...)` nameable when generated
/// `#[test]` items remain in source, but it is not executable concrete
/// playback and will panic if called outside playback mode.
pub fn concrete_playback_run<F: Fn()>(_: Vec<Vec<u8>>, _: F) {
    unreachable!("Concrete playback does not work during verification")
}

pub use futures::{RoundRobin, block_on, block_on_with_spawn, spawn, yield_now};

// Kani proc macros must be in a separate crate
pub use kani_macros::*;

// Declare common Kani API such as assume, assert
// Expands the Kani API surface including the generated model set from
// kani_core::generate_models!(). This macro-expanded set includes
// SimdBitmaskModel and all other KaniModel variants, discovered by the
// compiler via #[kanitool::fn_marker] attributes. trust_mc does NOT use
// upstream Kani's #[rustc_diagnostic_item = "KaniModelSimdBitmask"]
// lookup; instead, the generic fn_marker pipeline handles SIMD bitmask
// routing identically to all other Kani models. See #4122.
kani_core::kani_lib!(kani);

// Used to bind `core::assert` to a different name to avoid possible name conflicts if a
// crate uses `extern crate std as core`. See
// https://github.com/model-checking/kani/issues/1949 and https://github.com/model-checking/kani/issues/2187
#[doc(hidden)]
#[cfg(not(feature = "concrete_playback"))]
pub use core::assert as __kani__workaround_core_assert;

#[macro_export]
macro_rules! cover {
    () => {
        kani::cover(true, "cover location");
    };
    ($cond:expr $(,)?) => {
        kani::cover($cond, concat!("cover condition: ", stringify!($cond)));
    };
    ($cond:expr, $msg:literal) => {
        kani::cover($cond, $msg);
    };
}

/// `implies!(premise => conclusion)` means that if the `premise` is true, so
/// must be the `conclusion`.
///
/// This simply expands to `!premise || conclusion` and is intended to make checks more readable,
/// as the concept of an implication is more natural to think about than its expansion.
#[macro_export]
macro_rules! implies {
    ($premise:expr => $conclusion:expr) => {
        !($premise) || ($conclusion)
    };
}

pub(crate) use kani_macros::unstable_feature as unstable;

pub mod contracts;
