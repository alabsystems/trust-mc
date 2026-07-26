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
    fn with_tcx<F>(source: &str, edition: &str, callback: F)
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

        let args = vec![
            "rustc".to_string(),
            src_path.to_string_lossy().into_owned(),
            "--crate-type=lib".to_string(),
            format!("--crate-name={crate_name}"),
            "--out-dir".to_string(),
            out_dir.to_string_lossy().into_owned(),
            format!("--edition={edition}"),
            "-C".to_string(),
            "opt-level=0".to_string(),
        ];
        let result = run_with_tcx!(&args, |tcx| {
            callback(tcx);
            std::ops::ControlFlow::<(), ()>::Continue(())
        });
        assert!(
            result.is_ok() || matches!(result, Err(CompilerError::Skipped)),
            "rustc_public run failed: {result:?}"
        );
    }

    with_tcx(source, edition, |tcx| {
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
