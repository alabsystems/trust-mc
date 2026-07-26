// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module defines all compiler extensions that form the Kani compiler.
//!
//! The [KaniCompiler] can be used across multiple rustc driver runs ([`rustc_driver::run_compiler`]),
//! which is used to implement stubs.
//!
//! In the first run, [KaniCompiler::config] will implement the compiler configuration and it will
//! also collect any stubs that may need to be applied. This method will be a no-op for any
//! subsequent runs. The [KaniCompiler] will parse options that are passed via `-C llvm-args`.
//!
//! If no stubs need to be applied, the compiler will proceed to generate AY verification conditions, and it won't
//! need any extra runs. However, if stubs are required, we will have to restart the rustc driver
//! in order to apply the stubs. For the subsequent runs, we add the stub configuration to
//! `-C llvm-args`.

use crate::args::Arguments;
#[cfg(feature = "ay")]
use crate::codegen_ay::AYCodegenBackend;
use crate::kani_middle::check_crate_items;
use crate::kani_queries::QUERY_DB;
use crate::session::init_session;
use clap::Parser;
use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_driver::{Callbacks, Compilation, run_compiler};
use rustc_interface::Config;
use rustc_middle::ty::TyCtxt;
use rustc_public::rustc_internal;
use rustc_session::config::ErrorOutputType;
use tracing::debug;

/// Run the Kani flavour of the compiler.
/// This may require multiple runs of the rustc driver ([`rustc_driver::run_compiler`]).
pub(crate) fn run(args: Vec<String>) {
    let mut kani_compiler = KaniCompiler::new();
    kani_compiler.run(args);
}

/// Configure and return the AY backend that generates SMT-LIB2 verification conditions.
#[cfg(feature = "ay")]
fn backend(args: Arguments) -> Box<dyn CodegenBackend> {
    QUERY_DB.with(|db| db.borrow_mut().set_args(args));
    Box::new(AYCodegenBackend::new())
}

/// Fallback backend. It will trigger an error if no backend has been enabled.
#[cfg(not(feature = "ay"))]
fn backend(_args: Arguments) -> Box<dyn CodegenBackend> {
    compile_error!("No backend is available. Enable the `ay` feature.");
}

/// This object controls the compiler behavior.
///
/// It is responsible for initializing the query database, as well as controlling the compiler
/// state machine.
struct KaniCompiler {}

impl KaniCompiler {
    /// Create a new [KaniCompiler] instance.
    fn new() -> KaniCompiler {
        KaniCompiler {}
    }

    /// Compile the current crate with the given arguments.
    ///
    /// Since harnesses may have different attributes that affect compilation, Kani compiler can
    /// actually invoke the rust compiler multiple times.
    fn run(&mut self, args: Vec<String>) {
        debug!(?args, "run_compilation_session");
        run_compiler(&args, self);
    }
}

/// Use default function implementations.
impl Callbacks for KaniCompiler {
    /// Configure the [KaniCompiler] `self` object during initialization.
    fn config(&mut self, config: &mut Config) {
        // `trust_mc-driver` passes the `trust_mc-compiler` specific arguments through llvm-args,
        // so parse directly from borrowed strings and avoid cloning the full argument vector.
        let args = Arguments::parse_from(
            std::iter::once("trust_mc-compiler")
                .chain(config.opts.cg.llvm_args.iter().map(String::as_str)),
        );
        init_session(&args, matches!(config.opts.error_format, ErrorOutputType::Json { .. }));

        // Capture args in the closure so they're available when the backend is created
        // (potentially on a different thread).
        config.make_codegen_backend = Some(Box::new({
            let args = args;
            move |_cfg, _| backend(args)
        }));
    }

    /// After analysis, we check the crate items for Kani API misuse or configuration issues.
    fn after_analysis(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'_>,
    ) -> Compilation {
        rustc_internal::run(tcx, || {
            let ignore_global_asm = QUERY_DB.with(|db| db.borrow().args().ignore_global_asm);
            check_crate_items(tcx, ignore_global_asm);
        })
        .expect("failed to run crate item check");
        Compilation::Continue
    }
}
