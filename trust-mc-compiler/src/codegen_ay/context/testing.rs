// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Test infrastructure for AY codegen context.
//!
//! Provides helpers that spin up a minimal rustc session for unit tests.
//! Extracted from context.rs as part of #2093.

use ay_bindings::AYProgram;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CompilerError, run_with_tcx};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use tempfile::TempDir;
use trust_mc_core::bmc::BmcVc;

use super::{AYConfig, AYCtx, HeapState};
use crate::kani_queries::QueryDb;

/// The standard library's own `libc` (design trust-mc-reds-final §7.1, E3).
/// The sysroot ships two `liblibc` crates: std's (an rlib) and an rmeta-only
/// copy the compiler's own crates were built against, so a test source's
/// `extern crate libc` is ambiguous (E0464) unless it is named. std's is the
/// one with an rlib. The sysroot is the one the running `librustc_driver`
/// belongs to. Zero rlibs or more than one is refused rather than guessed.
///
/// Where std's metadata lives depends on how that sysroot was built, so the
/// file that names the crate does too:
/// - Trust seal: std's rlib holds only a metadata stub (its metadata is split
///   out, as `-Z embed-metadata=no` does) and the full metadata is the
///   `.rmeta` beside it with the same file stem. That `.rmeta` names the
///   crate: rustc refuses a stub rlib as an `--extern` ("only metadata stub
///   found for `rlib` dependency"), even with the `.rmeta` beside it.
/// - Stock sysroot (the frozen `nightly-2025-12-03` oracle lane): the
///   metadata is embedded in the rlib and no `.rmeta` of that stem ships, so
///   the rlib names the crate itself.
///
/// The choice cannot load the wrong crate: the other `liblibc` has a
/// different stem, and an rlib whose metadata is only a stub is refused by
/// rustc, so the compile fails instead.
fn sysroot_std_libc() -> PathBuf {
    let sysroot = rustc_session::config::Sysroot::new(None);
    let lib = rustc_session::filesearch::make_target_lib_path(
        sysroot.path(),
        rustc_session::config::host_tuple(),
    );
    let mut rlibs: Vec<PathBuf> = fs::read_dir(&lib)
        .unwrap_or_else(|err| panic!("read the sysroot target libdir {}: {err}", lib.display()))
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| {
            path.extension().is_some_and(|ext| ext == "rlib")
                && path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.starts_with("liblibc-"))
        })
        .collect();
    assert_eq!(
        rlibs.len(),
        1,
        "expected exactly one std liblibc rlib in {}, found {rlibs:?}",
        lib.display()
    );
    let rlib = rlibs.pop().expect("one rlib");
    let rmeta = rlib.with_extension("rmeta");
    if rmeta.is_file() { rmeta } else { rlib }
}

pub(in crate::codegen_ay) fn with_test_ay_ctx_for_source<F>(source: &str, callback: F)
where
    F: for<'tcx> FnOnce(AYCtx<'tcx, 'static>) + Send,
{
    with_test_ay_ctx_for_source_with_edition(source, "2024", callback);
}

pub(in crate::codegen_ay) fn with_test_ay_ctx_for_source_with_edition<F>(
    source: &str,
    edition: &str,
    callback: F,
) where
    F: for<'tcx> FnOnce(AYCtx<'tcx, 'static>) + Send,
{
    with_test_ay_ctx_for_source_with_edition_and_rustc_flags(source, edition, &[], callback);
}

/// Compile a real separate dependency and observe the caller with the linked compiler.
/// The fixed extern alias supplies source syntax only, never definition authority.
pub(in crate::codegen_ay) fn with_test_ay_ctx_for_external_source<F>(
    dependency_source: &str,
    caller_source: &str,
    rustc_flags: &[&str],
    callback: F,
) where
    F: for<'tcx> FnOnce(AYCtx<'tcx, 'static>) + Send,
{
    use std::sync::{
        Arc,
        atomic::{AtomicBool, AtomicU64, Ordering},
    };
    static CRATE_COUNTER: AtomicU64 = AtomicU64::new(0);
    let directory = TempDir::new().expect("external query dependency directory");
    let name = format!("external_vec_lookalike_{}", CRATE_COUNTER.fetch_add(1, Ordering::SeqCst));
    let source = directory.path().join("dependency.rs");
    let output = directory.path().join("out");
    fs::write(&source, dependency_source).expect("write real external dependency");
    fs::create_dir(&output).expect("dependency output directory");
    struct EmitDependency;
    impl rustc_driver::Callbacks for EmitDependency {}
    let mut arguments = vec![
        "rustc".to_owned(),
        source.to_string_lossy().into_owned(),
        "--crate-type=rlib".to_owned(),
        format!("--crate-name={name}"),
        "--out-dir".to_owned(),
        output.to_string_lossy().into_owned(),
        "--edition=2024".to_owned(),
        "-Cpanic=abort".to_owned(),
        "-Zalways-encode-mir".to_owned(),
        "-Zinline-mir=no".to_owned(),
    ];
    // Both crates must use the same sysroot and configuration when a control
    // observes the bundled standard library's actual private MIR.
    arguments.extend(rustc_flags.iter().map(|flag| (*flag).to_owned()));
    let result = rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(&arguments, &mut EmitDependency)
    });
    assert!(result.is_ok(), "external dependency compilation failed");
    let rlib = output.join(format!("lib{name}.rlib"));
    assert!(rlib.is_file(), "external dependency must emit its real rlib");
    // Trust may split metadata from its rlib. Use the real emitted sibling,
    // as context/testing.rs already does for sysroot dependencies.
    let rmeta = rlib.with_extension("rmeta");
    let metadata = if rmeta.is_file() { &rmeta } else { &rlib };
    let dependency = format!("external_vec_lookalike={}", metadata.display());
    let completed = Arc::new(AtomicBool::new(false));
    let callback_completed = Arc::clone(&completed);
    let mut flags = vec!["--extern", dependency.as_str(), "-Cpanic=abort", "-Zinline-mir=no"];
    flags.extend_from_slice(rustc_flags);
    with_test_ay_ctx_for_source_with_rustc_flags(caller_source, &flags, move |ctx| {
        callback(ctx);
        callback_completed.store(true, Ordering::SeqCst);
    });
    assert!(
        completed.load(Ordering::SeqCst),
        "actual external-definition classification callback must complete"
    );
}

/// [`with_test_ay_ctx_for_source`] with extra `rustc` flags appended.
///
/// The default context compiles at `-C opt-level=0`, which turns debug
/// assertions and overflow checks ON: every `a + b` gets an `Assert`
/// terminator and every `*p` a null/alignment check. A test that wants the
/// bare STATEMENT (`-C overflow-checks=off`, `-C debug-assertions=off`) — the
/// shape `--prove-safety-only` compiles, and the shape core's own MIR takes —
/// passes those flags here.
pub(in crate::codegen_ay) fn with_test_ay_ctx_for_source_with_rustc_flags<F>(
    source: &str,
    rustc_flags: &[&str],
    callback: F,
) where
    F: for<'tcx> FnOnce(AYCtx<'tcx, 'static>) + Send,
{
    with_test_ay_ctx_for_source_with_edition_and_rustc_flags(source, "2024", rustc_flags, callback);
}

pub(in crate::codegen_ay) fn with_test_ay_ctx_for_source_with_edition_and_rustc_flags<F>(
    source: &str,
    edition: &str,
    rustc_flags: &[&str],
    callback: F,
) where
    F: for<'tcx> FnOnce(AYCtx<'tcx, 'static>) + Send,
{
    fn with_tcx<F>(source: &str, edition: &str, rustc_flags: &[&str], callback: F)
    where
        F: for<'tcx> FnOnce(TyCtxt<'tcx>) + Send,
    {
        use std::sync::atomic::{AtomicU64, Ordering};
        static CRATE_COUNTER: AtomicU64 = AtomicU64::new(0);

        let temp_dir = TempDir::new().expect("create temp dir");
        let src_path: PathBuf = temp_dir.path().join("lib.rs");
        fs::write(&src_path, source).expect("write test source");

        // #1267: Use unique crate name and output directory per test to avoid
        // parallel compilation conflicts when multiple tests run simultaneously.
        let unique_id = CRATE_COUNTER.fetch_add(1, Ordering::SeqCst);
        let crate_name = format!("testcrate_{unique_id}");
        let out_dir = temp_dir.path().join("out");
        fs::create_dir_all(&out_dir).expect("create output dir");

        let mut args = vec![
            "rustc".to_string(),
            src_path.to_string_lossy().into_owned(),
            "--crate-type=lib".to_string(),
            "--out-dir".to_string(),
            out_dir.to_string_lossy().into_owned(),
            format!("--edition={edition}"),
            "-C".to_string(),
            "opt-level=0".to_string(),
        ];
        // An explicit name lets identity regressions compile a user crate
        // called core/std. Its unique temporary output directory still
        // isolates it from concurrent fixtures and the real sysroot crate.
        if !rustc_flags.iter().any(|flag| flag.starts_with("--crate-name=")) {
            args.push(format!("--crate-name={crate_name}"));
        }
        args.extend(rustc_flags.iter().map(|flag| (*flag).to_string()));
        if source.contains("extern crate libc") {
            args.push("--extern".to_string());
            args.push(format!("libc={}", sysroot_std_libc().display()));
        }
        // rustc compiles on a thread of its own; the compilation records its
        // diagnostics into the registry of the test that started it, so the
        // test reads them inside the callback and after it alike, and no
        // concurrent test reads or drains them.
        let counters = crate::codegen_ay::chc::compilation_counters();
        let result = run_with_tcx!(&args, |tcx| {
            let _counters = crate::codegen_ay::chc::enter_compilation_counters(counters);
            callback(tcx);
            std::ops::ControlFlow::<(), ()>::Continue(())
        });
        assert!(
            result.is_ok() || matches!(result, Err(CompilerError::Skipped)),
            "rustc_public run failed: {result:?}"
        );
    }

    with_tcx(source, edition, rustc_flags, |tcx| {
        let config = AYConfig::default();
        let mut program = if config.use_chc {
            AYProgram::horn()
        } else {
            let mut prog = AYProgram::new();
            prog.set_logic(&config.logic);
            prog
        };
        if config.produce_models {
            program.produce_models();
        }
        let mut bmc_vc = BmcVc::new();
        bmc_vc.query.produce_model = config.produce_models;
        bmc_vc.query.logic = Some(config.select_logic(false).to_owned());
        let ctx: AYCtx<'_, 'static> = AYCtx {
            obligation_free_body_by_fn: std::collections::HashMap::new(),
            std_abstraction: crate::kani_middle::std_abstraction::StdAbstraction::resolve(tcx),
            tcx,
            queries: QueryDb::default(),
            config,
            program,
            bmc_vc,
            chc_vc: None,
            var_map: HashMap::new(),
            memory: None,
            symbolic_memory_stores: HashMap::new(),
            heap_state: HeapState::default(),
            shadow_mem: super::shadow_mem_ctx::BmcShadowMemState::default(),
            name_counter: 0,
            label_counter: 0,
            property_counter: 0,
            current_fn: None,
            inline_frame_salt: None,
            inline_frame_salt_counter: 0,
            unsupported_constructs: FxHashMap::default(),

            transformer: None,
            property_violations: Vec::new(),
            assumption_context: None,
            any_vars: Vec::new(),
            cover_properties: Vec::new(),
            cover_metadata: Vec::new(),
            coverage_properties: Vec::new(),
            coverage_metadata: Vec::new(),
            chc_local_to_state_idx: HashMap::new(),
            bmc_mini_inline_stack: Vec::new(),
            bmc_root_fn_name: None,
            initial_memory: None,
            global_alloc_addrs: std::collections::HashMap::new(),
            global_alloc_bytes: std::collections::HashSet::new(),
            alloc_views: HashMap::new(),
            alloc_roots: rustc_data_structures::fx::FxIndexMap::default(),
            alloc_views_poisoned: std::collections::HashSet::new(),
            alloc_phi_defs: HashMap::new(),
            shared_scalar_slices: HashMap::new(),
        };
        callback(ctx);
    });
}

pub(in crate::codegen_ay) fn with_test_ay_ctx<F>(callback: F)
where
    F: for<'tcx> FnOnce(AYCtx<'tcx, 'static>) + Send,
{
    const TEST_SOURCE: &str = r#"
pub fn add(a: u32, b: u32) -> u32 { a + b }
"#;

    with_test_ay_ctx_for_source(TEST_SOURCE, callback);
}
