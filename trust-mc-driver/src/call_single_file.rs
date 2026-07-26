// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use anyhow::{Context, Result};
use std::path::PathBuf;
use trust_mc_metadata::UnstableFeature;

use crate::session::KaniSession;
use crate::util::args::{KaniArg, RustcArg};

pub(crate) struct LibConfig {
    args: Vec<RustcArg>,
}

/// Convert a path to a UTF-8 string, returning an error if the path is not valid UTF-8.
fn path_to_str(path: &std::path::Path) -> Result<&str> {
    path.to_str().with_context(|| format!("Path is not valid UTF-8: {}", path.display()))
}

impl LibConfig {
    pub(crate) fn new(path: PathBuf) -> Result<LibConfig> {
        let sysroot = path.parent().context("Library path has no parent directory")?;
        let kani_std_rlib = path.join("libstd.rlib");
        let kani_std_wrapper = format!("noprelude:std={}", path_to_str(&kani_std_rlib)?);
        let args = vec![
            RustcArg::from("--sysroot"),
            RustcArg::from(path_to_str(sysroot)?),
            RustcArg::from("-L"),
            RustcArg::from(path_to_str(&path)?),
            RustcArg::from("--extern"),
            RustcArg::from("kani"),
            RustcArg::from("--extern"),
            RustcArg::from(kani_std_wrapper.as_str()),
        ];
        Ok(LibConfig { args })
    }

    pub(crate) fn new_no_core(path: PathBuf) -> Result<LibConfig> {
        Ok(LibConfig {
            args: vec![
                RustcArg::from("-L"),
                RustcArg::from(path_to_str(&path)?),
                RustcArg::from("--extern"),
                RustcArg::from("kani_core"),
            ],
        })
    }
}

impl KaniSession {
    /// Create a compiler option that represents the reachability mode.
    pub(crate) fn reachability_arg(&self) -> KaniArg {
        format!("--reachability={}", self.reachability_mode()).into()
    }

    /// The `kani-compiler`-specific arguments that should be passed when building all crates,
    /// including dependencies.
    pub(crate) fn kani_compiler_dependency_flags(&self) -> Vec<KaniArg> {
        let mut flags = vec![check_version()];

        if self.args.ignore_global_asm {
            flags.push("--ignore-global-asm".into());
        }

        flags
    }

    /// The `kani-compiler`-specific arguments that should be passed only to the local crate
    /// being compiled.
    pub(crate) fn kani_compiler_local_flags(&self) -> Vec<KaniArg> {
        let mut flags: Vec<KaniArg> = vec![];

        if self.args.common_args.debug {
            flags.push("--log-level=debug".into());
        } else if self.args.common_args.verbose {
            // Print the symtab command being invoked.
            flags.push("--log-level=info".into());
        } else {
            flags.push("--log-level=warn".into());
        }

        if self.args.restrict_vtable() {
            flags.push("--restrict-vtable-fn-ptrs".into());
        }
        if self.args.assertion_reach_checks() {
            flags.push("--assertion-reach-checks".into());
        }

        if self.args.is_stubbing_enabled() {
            flags.push("--enable-stubbing".into());
        }

        if self.args.coverage {
            flags.push("--coverage-checks".into());
        }

        if self.args.common_args.unstable_features.contains(UnstableFeature::ValidValueChecks) {
            flags.push("--ub-check=validity".into())
        }

        if self.args.common_args.unstable_features.contains(UnstableFeature::UninitChecks) {
            // Automatically enable shadow memory, since the version of uninitialized memory checks
            // without non-determinism depends on it.
            flags.push("-Z ghost-state".into());
            flags.push("--ub-check=uninit".into());
        }

        if self.args.no_assert_contracts {
            flags.push("--no-assert-contracts".into());
        }

        if self.args.list_metadata_only {
            flags.push("--list-metadata-only".into());
        }

        for harness in &self.args.harnesses {
            flags.push(format!("--harness {harness}").into());
        }

        if self.args.exact {
            flags.push("--exact".into());
        }

        if let Some(args) = &self.autoharness_compiler_flags {
            flags.extend(args.iter().cloned().map(KaniArg::from));
        }

        if self.args.prove_safety_only {
            flags.push("--prove-safety-only".into());
        }

        // Pass AY-specific options to compiler (backend is determined at compile time via features)
        use crate::args::Backend;
        if self.args.backend == Backend::AY {
            // Pass loop unwinding configuration for AY bounded loop unrolling.
            if let Some(default_unwind) = self.args.default_unwind {
                flags.push(format!("--default-unwind {default_unwind}").into());
            }
            if let Some(unwind) = self.args.unwind {
                flags.push(format!("--unwind {unwind}").into());
            }

            if self.args.ay_chc_debug {
                flags.push("--ay-chc-debug".into());
            }

            // Pass check toggles that affect unwinding assertions.
            if self.args.checks.no_default_checks {
                flags.push("--no-default-checks".into());
            }
            if self.args.checks.no_memory_safety_checks {
                flags.push("--no-memory-safety-checks".into());
            }
            if self.args.checks.no_overflow_checks {
                flags.push("--no-overflow-checks".into());
            }
            if self.args.checks.no_undefined_function_checks {
                flags.push("--no-undefined-function-checks".into());
            }
            if self.args.checks.no_unwinding_checks {
                flags.push("--no-unwinding-checks".into());
            }

            // Pass emit_bmc flag to use abstract IR emission path.
            if self.args.ay_emit_bmc {
                flags.push("--ay-emit-bmc".into());
            }

            // Pass CHC flag to use Horn clause mode.
            if self.args.ay_chc {
                flags.push("--ay-chc".into());
            }

            // Pass logic override if specified (#952).
            if let Some(ref logic) = self.args.ay_logic {
                flags.push(format!("--ay-logic={}", logic).into());
            }

            // Pass CHC track level if non-default (#768, #2214).
            // Default is now Mem (Part of #2214).
            use crate::args::ChcTrackLevel;
            match self.args.ay_chc_track {
                ChcTrackLevel::Reg => flags.push("--ay-chc-track=reg".into()),
                ChcTrackLevel::Ptr => flags.push("--ay-chc-track=ptr".into()),
                ChcTrackLevel::Mem => {} // Default, don't pass
            }

            // Pass CHC step mode if non-default (#112).
            use crate::args::ChcStepMode;
            match self.args.ay_chc_step {
                ChcStepMode::Large => flags.push("--ay-chc-step=large".into()),
                ChcStepMode::Small => flags.push("--ay-chc-step=small".into()),
                ChcStepMode::Auto => {} // Default, don't pass
            }

            // Pass int-lift flag if enabled (#112 Direction 2).
            if self.args.ay_chc_int_lift {
                flags.push("--ay-chc-int-lift".into());
            }

            // Pass CHC bounded unroll flag if enabled.
            if self.args.ay_chc_bounded_unroll {
                flags.push("--ay-chc-bounded-unroll".into());
            }

            // Pass wide memory model flag if enabled (#1678).
            if self.args.ay_wide_mem {
                flags.push("--ay-wide-mem".into());
            }

            // Pass extra pointer checks flag if enabled (#3176).
            if self.args.extra_pointer_checks {
                flags.push("--extra-pointer-checks".into());
            }
        }

        flags.extend(self.args.common_args.unstable_features.as_arguments().map(KaniArg::from));

        flags
    }

    /// This function generates all rustc configurations required by our AY codegen.
    pub(crate) fn kani_rustc_flags(&self, lib_config: LibConfig) -> Vec<RustcArg> {
        let mut flags: Vec<_> = base_rustc_flags(lib_config);
        // Default: panic=abort eliminates unwind paths. When ay_panic_unwind is
        // enabled, use panic=unwind to preserve cleanup blocks for verifying
        // Drop impls during panic unwinding. Part of #3301.
        if self.args.coverage {
            flags.extend_from_slice(
                &["-C", "instrument-coverage", "-Z", "no-profiler-runtime"].map(RustcArg::from),
            );
        }
        let panic_strategy = if self.args.ay_panic_unwind { "panic=unwind" } else { "panic=abort" };
        flags.extend_from_slice(
            &[
                "-C",
                panic_strategy,
                "-C",
                "symbol-mangling-version=v0",
                "-Z",
                "panic_abort_tests=yes",
                "-Z",
                "mir-enable-passes=-RemoveStorageMarkers",
                // Disable MIR inlining to preserve HashMap/BigInt call boundaries (Part of #798)
                "-Z",
                "inline-mir=no",
                "--check-cfg=cfg(kani)",
                // Do not invoke the linker since the compiler will not generate real object files
                "-Clinker=echo",
            ]
            .map(RustcArg::from),
        );

        if self.args.no_codegen {
            flags.push("-Z".into());
            flags.push("no-codegen".into());
        }

        if let Some(seed_opt) = self.args.randomize_layout {
            flags.push("-Z".into());
            flags.push("randomize-layout".into());
            if let Some(seed) = seed_opt {
                flags.push("-Z".into());
                flags.push(format!("layout-seed={seed}").into());
            }
        }

        if self.args.coverage {
            flags.push("-Zmir-enable-passes=-SingleUseConsts".into());
        }

        if self.args.prove_safety_only {
            flags.push("-C".into());
            flags.push("debug-assertions=off".into());
        }

        // This argument will select the Kani flavour of the compiler. It will be removed before
        // rustc driver is invoked.
        flags.push("--kani-compiler".into());

        flags
    }
}

/// Common flags used for compiling user code for verification and playback flow.
pub(crate) fn base_rustc_flags(lib_config: LibConfig) -> Vec<RustcArg> {
    let mut flags = [
        "-C",
        "overflow-checks=on",
        "-Z",
        "unstable-options",
        "-Z",
        "trim-diagnostic-paths=no",
        "-Z",
        "human_readable_cgu_names",
        "-Z",
        "always-encode-mir",
        "--cfg=kani",
        "--cfg=trust_mc",
        "-Z",
        "crate-attr=feature(register_tool)",
        "-Z",
        "crate-attr=register_tool(kanitool)",
        "-Z",
        "crate-attr=register_tool(trust_mctool)",
    ]
    .map(RustcArg::from)
    .to_vec();

    flags.extend(lib_config.args);

    // e.g. compiletest will set 'compile-flags' here and we should pass those down to rustc
    // and we fail in `tests/kani/Match/match_bool.rs`
    if let Ok(str) = std::env::var("RUSTFLAGS") {
        flags.extend(str.split(' ').map(RustcArg::from));
    }

    flags
}

/// Function that returns a `--check-version` argument to be added to the compiler flags.
/// This is really just used to force the compiler to recompile everything from scratch when a user
/// upgrades Kani. Cargo currently ignores the codegen backend version.
/// See <https://github.com/model-checking/kani/issues/2140> for more context.
fn check_version() -> KaniArg {
    format!("--check-version={}", env!("CARGO_PKG_VERSION")).into()
}
