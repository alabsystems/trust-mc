// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Routing for the stdlib gaps the tokio reachability scan reported. Each
// method here was first probed with a tiny harness to answer "does the Call
// survive to codegen, or is it MIR-inlined first?"; only the survivors got a
// stub. The deliberately UNSTUBBED entry (`Option::unwrap_or_default`) is
// pinned too, so a future arm cannot quietly replace the exact inlined body.

use super::{StubKind, StubRegistry, lookup};

#[test]
fn string_from_utf8_and_into_bytes_route_to_string_stubs() {
    assert_eq!(lookup("std::string::String::from_utf8"), Some(StubKind::StringFromUtf8));
    assert_eq!(lookup("alloc::string::String::from_utf8"), Some(StubKind::StringFromUtf8));
    assert_eq!(lookup("std::string::String::into_bytes"), Some(StubKind::StringIntoBytes));
    assert_eq!(lookup("alloc::string::String::into_bytes"), Some(StubKind::StringIntoBytes));
    // The lossy / unchecked siblings keep their own arms — `extract_method_name`
    // is exact, so "from_utf8" cannot swallow them.
    assert_eq!(
        lookup("std::string::String::from_utf8_lossy"),
        Some(StubKind::StringFromUtf8Lossy)
    );
    assert_eq!(lookup("std::string::String::from_utf8_unchecked"), Some(StubKind::StringFrom));
    // `core::str::from_utf8` is a different function with a different Ok type.
    assert_eq!(lookup("core::str::converts::from_utf8"), Some(StubKind::StrFromUtf8));
}

#[test]
fn vec_new_in_is_vec_new() {
    assert_eq!(lookup("std::vec::Vec::<T, A>::new_in"), Some(StubKind::VecNew));
    assert_eq!(
        StubRegistry::lookup_vec_suffix("alloc::vec::Vec::<u8>::new_in"),
        Some(StubKind::VecNew)
    );
    // RawVec::new_in stays RawVec's own stub (exclusive category before Vec).
    assert_eq!(lookup("alloc::raw_vec::RawVec::<T, A>::new_in"), Some(StubKind::RawVecNewIn));
}

#[test]
fn result_expect_err_shares_the_unwrap_err_stub() {
    assert_eq!(
        lookup("std::result::Result::<T, E>::expect_err"),
        Some(StubKind::ResultUnwrapErr)
    );
    assert_eq!(
        StubRegistry::lookup_result_suffix("core::result::Result::<u8, u8>::expect_err"),
        Some(StubKind::ResultUnwrapErr)
    );
    // Not confused with `expect` / `unwrap_err` / `unwrap`.
    assert_eq!(lookup("std::result::Result::<T, E>::expect"), Some(StubKind::ResultExpect));
    assert_eq!(
        lookup("std::result::Result::<T, E>::unwrap_err"),
        Some(StubKind::ResultUnwrapErr)
    );
    assert_eq!(lookup("std::result::Result::<T, E>::unwrap"), Some(StubKind::ResultUnwrap));
}

#[test]
fn option_unwrap_or_default_is_deliberately_unstubbed() {
    // The inline pass keeps the Call; the BMC mini-inliner runs the real body
    // (`T::default()` comes from MIR). A stub would have to invent defaults.
    assert_eq!(lookup("std::option::Option::<T>::unwrap_or_default"), None);
    assert_eq!(
        StubRegistry::lookup_option_suffix("core::option::Option::<u8>::unwrap_or_default"),
        None
    );
}

#[test]
fn unreachable_unchecked_is_a_panic_obligation() {
    assert_eq!(lookup("core::hint::unreachable_unchecked"), Some(StubKind::PanicError));
    assert_eq!(lookup("std::hint::unreachable_unchecked"), Some(StubKind::PanicError));
}

#[test]
fn slice_repeat_routes_the_slice_method_only() {
    // `str::repeat` lowers to `self.as_bytes().repeat(n)`: the CHC lane sees the
    // slice method under both spellings the compiler prints.
    assert_eq!(lookup("std::slice::<impl [T]>::repeat"), Some(StubKind::SliceRepeat));
    assert_eq!(lookup("alloc::std::slice::<impl [u8]>::repeat"), Some(StubKind::SliceRepeat));
    // Other items named `repeat` are different functions and stay unrouted here.
    assert_ne!(lookup("std::iter::repeat"), Some(StubKind::SliceRepeat));
    assert_ne!(lookup("std::iter::repeat::<u8>"), Some(StubKind::SliceRepeat));
    assert_ne!(lookup("alloc::str::<impl str>::repeat"), Some(StubKind::SliceRepeat));
}
