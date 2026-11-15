// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The rustc driver callbacks of the embedded `trust-mc-compiler` binary.
//!
//! [KaniCompiler] runs one [`rustc_driver::run_compiler`] session. Stubbing is a
//! MIR transform inside the backend (`kani_middle::transform`), so there are no
//! driver restarts.
//!
//! The backend it installs is the one canonical trustc loads from
//! `librustc_codegen_trust_mc.dylib` ([`crate::make_backend`]): the engine
//! arguments are parsed once from `-C llvm-args` in `CodegenBackend::init`, and
//! `check_crate_items` runs at the top of `codegen_crate`. What stays here is
//! what only an embedded driver needs: rustc's own logger, and the crate-items
//! check for sessions that never reach codegen.

use crate::kani_middle::check_crate_items;
use crate::kani_queries::{QUERY_DB, claim_crate_items_check};
use crate::session::init_embedded_rustc_logger;
use rustc_driver::{Callbacks, Compilation, run_compiler};
use rustc_interface::Config;
use rustc_middle::ty::TyCtxt;
use rustc_public::rustc_internal;
use tracing::debug;

/// Run the Kani flavour of the compiler.
pub(crate) fn run(args: Vec<String>) {
    let mut kani_compiler = KaniCompiler::new();
    kani_compiler.run(args);
}

/// This object controls the compiler behavior.
struct KaniCompiler {}

impl KaniCompiler {
    /// Create a new [KaniCompiler] instance.
    fn new() -> KaniCompiler {
        KaniCompiler {}
    }

    /// Compile the current crate with the given arguments.
    fn run(&mut self, args: Vec<String>) {
        debug!(?args, "run_compilation_session");
        run_compiler(&args, self);
    }
}

/// Use default function implementations.
impl Callbacks for KaniCompiler {
    /// Install rustc's logger and the trust-mc backend factory.
    fn config(&mut self, config: &mut Config) {
        init_embedded_rustc_logger();

        #[cfg(not(trust_toolchain))]
        {
            config.make_codegen_backend = Some(Box::new(|_cfg, _| crate::make_backend()));
        }
        // Trust: the factory receives the constructed `&Session` instead of
        // `(&Options, &Target)`. Neither closure reads its parameters.
        #[cfg(trust_toolchain)]
        {
            config.make_codegen_backend = Some(Box::new(|_sess| crate::make_backend()));
        }
    }

    /// Check the crate items here only when this session will not reach
    /// `codegen_crate`, which otherwise runs the check (see
    /// [`claim_crate_items_check`]). rustc skips codegen under exactly this
    /// condition (`rustc_interface::passes::start_codegen`).
    fn after_analysis(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'_>,
    ) -> Compilation {
        let skips_codegen = tcx.sess.opts.unstable_opts.no_codegen
            || !tcx.sess.opts.output_types.should_codegen();
        if skips_codegen && claim_crate_items_check() {
            rustc_internal::run(tcx, || {
                let ignore_global_asm = QUERY_DB.with(|db| db.borrow().args().ignore_global_asm);
                check_crate_items(tcx, ignore_global_asm);
            })
            .expect("failed to run crate item check");
        }
        Compilation::Continue
    }
}
