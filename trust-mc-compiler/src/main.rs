// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This is the main entry point to our compiler driver. This code accepts a few options that
//! can be used to configure AY CHC/SMT codegen as well as all other flags supported by rustc.
//!
//! Like miri, clippy, and other tools developed on the top of rustc, we rely on the
//! rustc_private feature and a specific version of rustc.
#![feature(extern_types)]
#![recursion_limit = "256"]
#![feature(box_patterns)]
#![feature(rustc_private)]
#![feature(more_qualified_paths)]
#![feature(iter_intersperse)]
#![feature(f128)]
#![feature(f16)]
#![feature(non_exhaustive_omitted_patterns_lint)]
#![feature(cfg_version)]
#![feature(mpmc_channel)]
// Once the `stable` branch is at 1.86 or later, remove this line, since float_next_up_down is stabilized
#![cfg_attr(not(version("1.86")), feature(float_next_up_down))]
#![feature(try_blocks)]
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_codegen_ssa;
extern crate rustc_const_eval;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_public;
extern crate rustc_public_bridge;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
// We can't add this directly as a dependency because we need the version to match rustc
extern crate tempfile;

mod args;
/// Restricted C front-end for `--c-lib` translation units (`-Z c-ffi`).
#[cfg(feature = "ay")]
mod c_ffi;
#[cfg(feature = "ay")]
mod codegen_ay;
mod intrinsics;
mod kani_compiler;
mod kani_middle;
mod kani_queries;
mod session;

use rustc_driver::{TimePassesCallbacks, run_compiler};
use std::env;

/// Embedded git SHA captured at build time by `build.rs`. Falls back to
/// `unknown-sha` on tarball/non-git builds; the shim treats that as
/// "skip staleness check". See `scripts/cargo-trust_mc`.
const TRUST_MC_GIT_SHA: &str = env!("TRUST_MC_GIT_SHA");
/// "1" when `build.rs` detected uncommitted changes, else "0".
const TRUST_MC_GIT_DIRTY: &str = env!("TRUST_MC_GIT_DIRTY");

/// Main function. Configure arguments and run the compiler.
fn main() {
    session::init_panic_hook();

    // Intercept the machine-readable version probe BEFORE rustc argument
    // parsing. Consumed by `scripts/cargo-trust_mc` to compare embedded SHA
    // against the repo's HEAD.
    //
    // Output format (single line, matches trust_mc-driver):
    //   trust_mc-version-sha sha=<sha> dirty=<0|1> version=<pkg-version>
    //
    // This is a hidden flag — do not document in user-facing help.
    if env::args().any(|arg| arg == "--trust_mc-version-sha") {
        println!(
            "trust_mc-version-sha sha={} dirty={} version={}",
            TRUST_MC_GIT_SHA,
            TRUST_MC_GIT_DIRTY,
            env!("CARGO_PKG_VERSION")
        );
        return;
    }

    let (kani_compiler, rustc_args) = is_kani_compiler(env::args().collect());

    // Configure and run compiler.
    if kani_compiler {
        kani_compiler::run(rustc_args);
    } else {
        let mut callbacks = TimePassesCallbacks::default();
        run_compiler(&rustc_args, &mut callbacks);
    }
}

/// Return whether we should run our flavour of the compiler, and which arguments to pass to rustc.
///
/// `trust_mc-driver` adds a `--kani-compiler` argument to run the Kani version of the compiler, which needs to be
/// filtered out before passing the arguments to rustc.
/// All other Kani arguments are today located inside `--llvm-args`.
///
/// This function returns `true` for rustc invocations that originate from our rustc / cargo rustc invocations in `trust_mc-driver`.
/// It returns `false` for rustc invocations that cargo adds in the process of executing the `trust_mc-driver` rustc command.
/// For example, if we are compiling a crate that has a build.rs file, cargo will compile and run that build script
/// (c.f. <https://doc.rust-lang.org/cargo/reference/build-scripts.html#life-cycle-of-a-build-script>).
/// The build script should be compiled with normal rustc, not the Kani compiler.
fn is_kani_compiler(args: Vec<String>) -> (bool, Vec<String>) {
    assert!(!args.is_empty(), "Arguments should always include executable name");
    const KANI_COMPILER: &str = "--kani-compiler";
    let mut has_kani_compiler = false;
    let new_args = args
        .into_iter()
        .filter(|arg| {
            if arg == KANI_COMPILER {
                has_kani_compiler = true;
                false
            } else {
                true
            }
        })
        .collect();
    (has_kani_compiler, new_args)
}
