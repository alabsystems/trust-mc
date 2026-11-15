// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! T1 cargo pair: a proc-macro dependency. Cargo compiles it for the host, so on
//! the Trustc route it must reach trustc with the host posture (`--cfg=kani_host`,
//! `-Ztrust-verify=off`) and never with the engine backend or engine arguments: a
//! proc-macro built by the backend is no loadable dylib, and LLVM rejects the
//! engine's `-Cllvm-args`.

extern crate proc_macro;

use proc_macro::TokenStream;

#[cfg(not(kani_host))]
compile_error!("pair-macros is a host unit: it must be compiled with --cfg=kani_host");

/// `sum_limit!(N)` expands to `pub const SUM_LIMIT: u8 = N;`.
#[proc_macro]
pub fn sum_limit(input: TokenStream) -> TokenStream {
    format!("pub const SUM_LIMIT: u8 = {input};").parse().expect("a u8 literal")
}
