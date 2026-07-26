// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(clippy::unwrap_used)]

use super::{check_referenced_type_unstable_features, referenced_unstable_type_defs};
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::rustc_internal;
use rustc_public::{CompilerError, CrateDef, run_with_tcx};
use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use tempfile::TempDir;

const FN_PTR_UNSTABLE_SOURCE: &str = r#"
#![feature(register_tool)]
#![register_tool(kanitool)]
#![allow(dead_code)]

#[kanitool::unstable(feature = "nested-types", issue = 1, reason = "test-only unstable type")]
pub struct UnstableStruct;

fn takes_unstable(_: UnstableStruct) {}

pub fn probe_fn_ptr() {
    let _fp: fn(UnstableStruct) = takes_unstable;
}
"#;

const EXTERNAL_GENERIC_UNSTABLE_LIB_SOURCE: &str = r#"
#![feature(register_tool)]
#![register_tool(kanitool)]
#![allow(dead_code)]

#[kanitool::unstable(feature = "nested-types", issue = 1, reason = "test-only unstable type")]
pub struct ExternalGeneric<T>(pub T);
"#;

fn with_test_tcx_for_source<F>(source: &str, callback: F)
where
    F: for<'tcx> FnOnce(TyCtxt<'tcx>) + Send,
{
    static CRATE_COUNTER: AtomicU64 = AtomicU64::new(0);

    let temp_dir = TempDir::new().expect("create temp dir");
    let src_path: PathBuf = temp_dir.path().join("lib.rs");
    fs::write(&src_path, source).expect("write test source");

    let unique_id = CRATE_COUNTER.fetch_add(1, Ordering::SeqCst);
    let crate_name = format!("unstable_type_test_crate_{unique_id}");
    let out_dir = temp_dir.path().join("out");
    fs::create_dir_all(&out_dir).expect("create output dir");

    let args = vec![
        "rustc".to_string(),
        src_path.to_string_lossy().into_owned(),
        "--crate-type=lib".to_string(),
        format!("--crate-name={crate_name}"),
        "--out-dir".to_string(),
        out_dir.to_string_lossy().into_owned(),
        "--edition=2024".to_string(),
        "-C".to_string(),
        "opt-level=0".to_string(),
    ];
    let result = run_with_tcx!(&args, |tcx| {
        callback(tcx);
        std::ops::ControlFlow::<(), ()>::Continue(())
    });
    assert!(
        result.is_ok()
            || matches!(result, Err(CompilerError::Skipped) | Err(CompilerError::Failed)),
        "rustc_public run failed: {result:?}"
    );
}

fn with_test_tcx_for_external_generic_source<F>(callback: F)
where
    F: for<'tcx> FnOnce(TyCtxt<'tcx>) + Send,
{
    static CRATE_COUNTER: AtomicU64 = AtomicU64::new(0);

    let temp_dir = TempDir::new().expect("create temp dir");
    let unique_id = CRATE_COUNTER.fetch_add(1, Ordering::SeqCst);
    let helper_name = format!("unstable_generic_helper_{unique_id}");
    let helper_src_path: PathBuf = temp_dir.path().join("helper.rs");
    fs::write(&helper_src_path, EXTERNAL_GENERIC_UNSTABLE_LIB_SOURCE).expect("write helper source");
    let helper_out_dir = temp_dir.path().join("helper_out");
    fs::create_dir_all(&helper_out_dir).expect("create helper output dir");

    // Compile the helper with the same explicitly selected compiler as this
    // test binary.  Falling through to an unrelated `rustc` on PATH can
    // produce an rlib with a different metadata version and make this test
    // observe E0514 instead of the unstable-type diagnostic under test.
    let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let helper_status = Command::new(rustc)
        .arg(&helper_src_path)
        .arg("--crate-type=lib")
        .arg(format!("--crate-name={helper_name}"))
        .arg("--out-dir")
        .arg(&helper_out_dir)
        .arg("--edition=2024")
        .status()
        .expect("compile helper crate");
    assert!(helper_status.success(), "helper crate compilation failed");

    let helper_rlib = fs::read_dir(&helper_out_dir)
        .expect("read helper output dir")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .find(|path| path.extension().is_some_and(|ext| ext == "rlib"))
        .expect("helper rlib should exist");

    let src_path: PathBuf = temp_dir.path().join("lib.rs");
    let source = format!(
        r#"
extern crate {helper_name};

use {helper_name}::ExternalGeneric;

fn takes_unstable(_: ExternalGeneric<u32>) {{}}

pub fn probe_external_fn_ptr() {{
    let _fp: fn(ExternalGeneric<u32>) = takes_unstable;
}}
"#
    );
    fs::write(&src_path, source).expect("write harness source");

    let crate_name = format!("unstable_type_external_test_crate_{unique_id}");
    let out_dir = temp_dir.path().join("out");
    fs::create_dir_all(&out_dir).expect("create output dir");

    let args = vec![
        "rustc".to_string(),
        src_path.to_string_lossy().into_owned(),
        "--crate-type=lib".to_string(),
        format!("--crate-name={crate_name}"),
        "--out-dir".to_string(),
        out_dir.to_string_lossy().into_owned(),
        "--edition=2024".to_string(),
        "--extern".to_string(),
        format!("{helper_name}={}", helper_rlib.to_string_lossy()),
        "-C".to_string(),
        "opt-level=0".to_string(),
    ];
    let result = run_with_tcx!(&args, |tcx| {
        callback(tcx);
        std::ops::ControlFlow::<(), ()>::Continue(())
    });
    assert!(
        result.is_ok()
            || matches!(result, Err(CompilerError::Skipped) | Err(CompilerError::Failed)),
        "rustc_public run failed: {result:?}"
    );
}

fn find_instance_by_suffix(tcx: TyCtxt<'_>, suffix: &str) -> Instance {
    rustc_public::all_local_items()
        .into_iter()
        .find_map(|item| {
            let def_id = rustc_internal::internal(tcx, item.def_id());
            tcx.def_path_str(def_id)
                .ends_with(suffix)
                .then(|| Instance::try_from(item).ok())
                .flatten()
        })
        .expect("missing item with requested suffix")
}

#[test]
fn test_referenced_unstable_type_defs_descends_into_fn_ptr_signatures() {
    with_test_tcx_for_source(FN_PTR_UNSTABLE_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_fn_ptr");
        let body = instance.body().expect("probe_fn_ptr should have a body");
        let referenced_paths: Vec<_> = body
            .local_decls()
            .flat_map(|(_, local_decl)| referenced_unstable_type_defs(local_decl.ty))
            .map(|def_id| tcx.def_path_str(rustc_internal::internal(tcx, def_id)))
            .collect();

        assert!(
            referenced_paths.iter().any(|path| path.ends_with("UnstableStruct")),
            "expected fn-pointer nested type to be collected, got {referenced_paths:?}"
        );
    });
}

#[test]
fn test_check_referenced_type_unstable_features_reports_fn_ptr_nested_types() {
    let saw_error = AtomicBool::new(false);
    with_test_tcx_for_source(FN_PTR_UNSTABLE_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_fn_ptr");
        let body = instance.body().expect("probe_fn_ptr should have a body");
        let mut visited_defs = HashSet::new();

        for (_, local_decl) in body.local_decls() {
            check_referenced_type_unstable_features(tcx, local_decl.ty, &[], &mut visited_defs);
        }

        saw_error.store(tcx.dcx().has_errors().is_some(), Ordering::SeqCst);
    });

    assert!(saw_error.load(Ordering::SeqCst), "expected unstable fn-pointer type usage to error");
}

#[test]
fn test_referenced_unstable_type_defs_descends_into_external_generic_fn_ptr_signatures() {
    with_test_tcx_for_external_generic_source(|tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_external_fn_ptr");
        let body = instance.body().expect("probe_external_fn_ptr should have a body");
        let referenced_paths: Vec<_> = body
            .local_decls()
            .flat_map(|(_, local_decl)| referenced_unstable_type_defs(local_decl.ty))
            .map(|def_id| tcx.def_path_str(rustc_internal::internal(tcx, def_id)))
            .collect();

        assert!(
            referenced_paths.iter().any(|path| path.ends_with("ExternalGeneric")),
            "expected external generic fn-pointer type to be collected, got {referenced_paths:?}"
        );
    });
}

#[test]
fn test_check_referenced_type_unstable_features_reports_external_generic_fn_ptr_nested_types() {
    let saw_error = AtomicBool::new(false);
    with_test_tcx_for_external_generic_source(|tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_external_fn_ptr");
        let body = instance.body().expect("probe_external_fn_ptr should have a body");
        let mut visited_defs = HashSet::new();

        for (_, local_decl) in body.local_decls() {
            check_referenced_type_unstable_features(tcx, local_decl.ty, &[], &mut visited_defs);
        }

        saw_error.store(tcx.dcx().has_errors().is_some(), Ordering::SeqCst);
    });

    assert!(
        saw_error.load(Ordering::SeqCst),
        "expected unstable external generic fn-pointer type usage to error"
    );
}
