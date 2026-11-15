// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The trust-mc engine: MIR -> AY verification conditions, as a rustc_private
//! rlib (package `trust-mc-engine`).
//!
//! Two front doors share this crate:
//!
//! * [`run_driver`] is the embedded rustc driver behind the `trust-mc-compiler`
//!   binary (the frozen Kani-compatibility lane). It runs
//!   `rustc_driver::run_compiler` with trust-mc's callbacks.
//! * [`make_backend`] returns the codegen backend that the
//!   `librustc_codegen_trust_mc` cdylib hands to canonical trustc through
//!   `-Zcodegen-backend=<path>`.
//!
//! Like miri, clippy, and other tools developed on the top of rustc, we rely on the
//! rustc_private feature and a specific version of rustc.
#![feature(extern_types)]
#![recursion_limit = "256"]
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
#[cfg(all(trust_toolchain, version("1.101")))]
extern crate rustc_attr_ir;
extern crate rustc_codegen_ssa;
extern crate rustc_const_eval;
#[cfg(all(trust_toolchain, version("1.101")))]
extern crate rustc_crate_store;
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
#[cfg(all(trust_toolchain, version("1.101")))]
extern crate rustc_structures;
extern crate rustc_target;
// We can't add this directly as a dependency because we need the version to match rustc
extern crate tempfile;

// Declared first, with #[macro_use], so `rvalue_use!` and `mir_span!` are in
// textual scope in every module below. See the module docs for the
// dual-toolchain contract.
#[macro_use]
mod rustc_compat;

mod args;
/// Restricted C front-end for `--c-lib` translation units (`-Z c-ffi`).
#[cfg(feature = "ay")]
mod c_ffi;
#[cfg(feature = "ay")]
mod callee_body;
#[cfg(feature = "ay")]
mod codegen_ay;
mod intrinsics;
mod kani_compiler;
mod kani_middle;
mod kani_queries;
mod session;

use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_driver::{TimePassesCallbacks, run_compiler};

/// The trust-mc codegen backend, as `__rustc_codegen_backend` returns it.
///
/// Installs trust-mc's panic hook (it chains to the hook it replaces, so a
/// panic inside trustc still reaches trustc's ICE reporter) and returns the AY
/// backend.
///
/// The backend parses its arguments from `-C llvm-args` in
/// `CodegenBackend::init`, so the embedded binary and trustc share one parse.
#[cfg(feature = "ay")]
pub fn make_backend() -> Box<dyn CodegenBackend> {
    session::init_panic_hook();
    Box::new(codegen_ay::AYCodegenBackend::new())
}

/// The compiler a backend dylib was built against, as its `build.rs` baked it,
/// and the check that compares it with the compiler that loaded the dylib.
pub struct BackendIdentity {
    /// `commit-hash:` of the rustc that built the dylib.
    pub rustc_commit: &'static str,
    /// Basename of the `librustc_driver` the dylib links.
    pub driver: &'static str,
    /// `artifact_driver_sha256` from the building sysroot's PROVENANCE; empty
    /// when that toolchain has none.
    pub driver_sha256: &'static str,
    /// Compare the baked identity with the loading session. `Err` carries a
    /// message naming both sides.
    #[cfg(not(all(trust_toolchain, version("1.101"))))]
    pub verify: fn(&rustc_session::Session) -> Result<(), String>,
    #[cfg(all(trust_toolchain, version("1.101")))]
    pub verify: fn(&rustc_session::EarlySession) -> Result<(), String>,
}

/// [`make_backend`] for a dylib that must refuse to run inside any compiler
/// but the one it was built against: `CodegenBackend::init` runs
/// `identity.verify` before anything else and makes a mismatch fatal.
#[cfg(feature = "ay")]
pub fn make_backend_with_identity(identity: BackendIdentity) -> Box<dyn CodegenBackend> {
    session::init_panic_hook();
    Box::new(codegen_ay::AYCodegenBackend::with_identity(identity))
}

/// Fallback backend. It will trigger an error if no backend has been enabled.
#[cfg(not(feature = "ay"))]
pub fn make_backend() -> Box<dyn CodegenBackend> {
    compile_error!("No backend is available. Enable the `ay` feature.");
}

/// Run the embedded trust-mc rustc driver over `args` (`args[0]` is the
/// executable name).
///
/// `trust-mc-driver` adds `--kani-compiler` to select trust-mc's flavour of the
/// compiler; every other invocation (build scripts cargo compiles along the
/// way) runs plain rustc.
pub fn run_driver(args: Vec<String>) {
    session::init_panic_hook();

    let (kani_compiler, rustc_args) = is_kani_compiler(args);

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
