// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(clippy::unwrap_used)]

use super::reachability::{AbstractionBoundary, collect_reachable_items, filter_crate_items};
use super::transform::BodyTransformation;
use crate::codegen_ay::stubs::StubRegistry;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::{Instance, MonoItem};
use rustc_public::rustc_internal;
use rustc_public::{CompilerError, CrateDef, run_with_tcx};
use std::fs;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};
use tempfile::TempDir;

const REACHABILITY_COLLECTION_SOURCE: &str = r#"
#![allow(dead_code)]
use std::collections::HashMap;

fn local_add_one(x: u32) -> u32 { x + 1 }

pub fn reachability_probe() -> u32 {
    let mut map = HashMap::<u32, u32>::new();
    map.insert(1, 2);
    local_add_one(0)
}
"#;

const REACHABILITY_FILTER_SOURCE: &str = r#"
#![allow(dead_code)]

pub fn keep_alpha() -> u32 { 1 }
pub fn keep_beta() -> u32 { 2 }
pub fn drop_gamma() -> u32 { 3 }
pub fn generic_fn<T: Copy>(value: T) -> T { value }
"#;

const REACHABILITY_STABLE_ATOMIC_SOURCE: &str = r#"
#![allow(dead_code)]
use std::sync::atomic::{AtomicPtr, Ordering};

pub fn probe_atomic_ptr_new() -> bool {
    let mut value = 1i32;
    let atomic = AtomicPtr::new(&mut value);
    !atomic.load(Ordering::SeqCst).is_null()
}

pub fn probe_atomic_ptr_compare_exchange() -> bool {
    let mut current = 1i32;
    let mut next = 2i32;
    let atomic = AtomicPtr::new(&mut current);
    atomic.compare_exchange(
        &mut current,
        &mut next,
        Ordering::SeqCst,
        Ordering::SeqCst,
    )
    .is_ok()
}

pub fn probe_atomic_ptr_from_ptr_unstubbed() -> bool {
    let mut value = 1i32;
    let mut raw: *mut i32 = &mut value;
    let atomic = unsafe { AtomicPtr::from_ptr(&mut raw) };
    !atomic.load(Ordering::SeqCst).is_null()
}
"#;

const REACHABILITY_SLICE_CONTAINS_SOURCE: &str = r#"
#![allow(dead_code)]

pub fn probe_slice_contains(needle: char) -> bool {
    const DAYS: &[char] = &['M', 'T', 'W'];
    DAYS.contains(&needle)
}
"#;

struct TestAbstractionBoundary {
    stub_registry: StubRegistry,
    recorded_unstubbed: Mutex<Vec<String>>,
}

impl TestAbstractionBoundary {
    fn new() -> Self {
        Self { stub_registry: StubRegistry::new(), recorded_unstubbed: Mutex::new(Vec::new()) }
    }

    fn recorded_unstubbed_paths(&self) -> Vec<String> {
        self.recorded_unstubbed.lock().unwrap_or_else(std::sync::PoisonError::into_inner).clone()
    }
}

fn is_handler_backed_test_abstraction(path: &str) -> bool {
    crate::kani_middle::stable_atomic_policy::is_handler_backed_stable_atomic(path)
        || is_handler_backed_test_slice_contains(path)
}

fn is_handler_backed_test_slice_contains(path: &str) -> bool {
    if !path.ends_with("::contains") {
        return false;
    }

    (path.contains("slice::") || path.contains("<["))
        && !path.contains("HashMap")
        && !path.contains("BTreeMap")
        && !path.contains("BTreeSet")
        && !path.contains("HashSet")
        && !path.contains("Vec")
        && !path.contains("String")
}

impl AbstractionBoundary for TestAbstractionBoundary {
    fn has_explicit_stub(&self, path: &str) -> bool {
        self.stub_registry.has_stub(path)
    }

    fn has_handler_backed_abstraction(&self, path: &str) -> bool {
        is_handler_backed_test_abstraction(path)
    }

    fn record_unstubbed_abstraction(&self, path: &str) {
        self.recorded_unstubbed
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push(path.to_owned());
    }
}

fn with_test_tcx_for_source<F>(source: &str, callback: F)
where
    F: for<'tcx> FnOnce(TyCtxt<'tcx>) + Send,
{
    static CRATE_COUNTER: AtomicU64 = AtomicU64::new(0);
    let temp_dir = TempDir::new().expect("create temp dir");
    let src_path: PathBuf = temp_dir.path().join("lib.rs");
    fs::write(&src_path, source).expect("write test source");

    let unique_id = CRATE_COUNTER.fetch_add(1, Ordering::SeqCst);
    let crate_name = format!("reachability_test_crate_{unique_id}");
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
        result.is_ok() || matches!(result, Err(CompilerError::Skipped)),
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
fn test_collect_reachable_items_includes_local_functions_and_excludes_hashmap_boundary() {
    with_test_tcx_for_source(REACHABILITY_COLLECTION_SOURCE, |tcx| {
        let root = find_instance_by_suffix(tcx, "reachability_probe");
        let mut transformer = BodyTransformation::new_for_tests();
        let abstraction_boundary = TestAbstractionBoundary::new();

        let (items, _graph) = collect_reachable_items(
            tcx,
            &mut transformer,
            &[MonoItem::Fn(root)],
            &abstraction_boundary,
        );
        let collected_fn_names: Vec<_> = items
            .into_iter()
            .filter_map(|item| match item {
                MonoItem::Fn(instance) => Some(instance.name()),
                _ => None, // external enum: MonoItem
            })
            .collect();

        assert!(
            collected_fn_names.iter().any(|name| name.contains("reachability_probe")),
            "reachable set should include root function, got {collected_fn_names:?}"
        );
        assert!(
            collected_fn_names.iter().any(|name| name.contains("local_add_one")),
            "reachable set should include local helper, got {collected_fn_names:?}"
        );
        assert!(
            !collected_fn_names.iter().any(|name| name.contains("std::collections::HashMap::")),
            "reachable set should exclude direct HashMap method bodies past abstraction boundary, got {collected_fn_names:?}"
        );
    });
}

#[test]
fn test_filter_crate_items_retains_predicate_matches_and_excludes_others() {
    with_test_tcx_for_source(REACHABILITY_FILTER_SOURCE, |tcx| {
        let filtered = filter_crate_items(tcx, |_, instance| instance.name().contains("keep_"));
        let filtered_names: Vec<_> = filtered.into_iter().map(|instance| instance.name()).collect();

        assert!(
            filtered_names.iter().any(|name| name.contains("keep_alpha")),
            "predicate filter should keep keep_alpha, got {filtered_names:?}"
        );
        assert!(
            filtered_names.iter().any(|name| name.contains("keep_beta")),
            "predicate filter should keep keep_beta, got {filtered_names:?}"
        );
        assert!(
            !filtered_names.iter().any(|name| name.contains("drop_gamma")),
            "predicate filter should exclude drop_gamma, got {filtered_names:?}"
        );
        assert!(
            !filtered_names.iter().any(|name| name.contains("generic_fn")),
            "generic function should not appear in monomorphic crate-item filter, got {filtered_names:?}"
        );
    });
}

#[test]
fn test_collect_reachable_items_stable_atomic_ptr_new_skips_unstubbed_diagnostic() {
    with_test_tcx_for_source(REACHABILITY_STABLE_ATOMIC_SOURCE, |tcx| {
        let root = find_instance_by_suffix(tcx, "probe_atomic_ptr_new");
        let mut transformer = BodyTransformation::new_for_tests();
        let abstraction_boundary = TestAbstractionBoundary::new();

        let (items, _graph) = collect_reachable_items(
            tcx,
            &mut transformer,
            &[MonoItem::Fn(root)],
            &abstraction_boundary,
        );
        let collected_fn_names: Vec<_> = items
            .into_iter()
            .filter_map(|item| match item {
                MonoItem::Fn(instance) => Some(instance.name()),
                _ => None,
            })
            .collect();
        let recorded_unstubbed = abstraction_boundary.recorded_unstubbed_paths();

        assert!(
            collected_fn_names.iter().any(|name| name.contains("probe_atomic_ptr_new")),
            "reachable set should include the probe root, got {collected_fn_names:?}"
        );
        assert!(
            !collected_fn_names.iter().any(|name| name.contains("AtomicPtr")),
            "stable atomic handlers should stay abstract at reachability, got {collected_fn_names:?}"
        );
        assert!(
            recorded_unstubbed.is_empty(),
            "handler-backed stable atomic abstractions should not be recorded as unstubbed, got {recorded_unstubbed:?}"
        );
    });
}

#[test]
fn test_collect_reachable_items_stable_atomic_compare_exchange_skips_unstubbed_diagnostic() {
    with_test_tcx_for_source(REACHABILITY_STABLE_ATOMIC_SOURCE, |tcx| {
        let root = find_instance_by_suffix(tcx, "probe_atomic_ptr_compare_exchange");
        let mut transformer = BodyTransformation::new_for_tests();
        let abstraction_boundary = TestAbstractionBoundary::new();

        let (items, _graph) = collect_reachable_items(
            tcx,
            &mut transformer,
            &[MonoItem::Fn(root)],
            &abstraction_boundary,
        );
        let collected_fn_names: Vec<_> = items
            .into_iter()
            .filter_map(|item| match item {
                MonoItem::Fn(instance) => Some(instance.name()),
                _ => None,
            })
            .collect();
        let recorded_unstubbed = abstraction_boundary.recorded_unstubbed_paths();

        assert!(
            collected_fn_names
                .iter()
                .any(|name| name.contains("probe_atomic_ptr_compare_exchange")),
            "reachable set should include the compare_exchange probe, got {collected_fn_names:?}"
        );
        assert!(
            !collected_fn_names.iter().any(|name| name.contains("AtomicPtr")),
            "stable atomic compare_exchange should remain abstract at reachability, got {collected_fn_names:?}"
        );
        assert!(
            recorded_unstubbed.is_empty(),
            "handler-backed stable atomic compare_exchange should not be recorded as unstubbed, got {recorded_unstubbed:?}"
        );
    });
}

#[test]
fn test_collect_reachable_items_stable_atomic_from_ptr_records_unstubbed_diagnostic() {
    with_test_tcx_for_source(REACHABILITY_STABLE_ATOMIC_SOURCE, |tcx| {
        let root = find_instance_by_suffix(tcx, "probe_atomic_ptr_from_ptr_unstubbed");
        let mut transformer = BodyTransformation::new_for_tests();
        let abstraction_boundary = TestAbstractionBoundary::new();

        let (items, _graph) = collect_reachable_items(
            tcx,
            &mut transformer,
            &[MonoItem::Fn(root)],
            &abstraction_boundary,
        );
        let collected_fn_names: Vec<_> = items
            .into_iter()
            .filter_map(|item| match item {
                MonoItem::Fn(instance) => Some(instance.name()),
                _ => None,
            })
            .collect();
        let recorded_unstubbed = abstraction_boundary.recorded_unstubbed_paths();

        assert!(
            collected_fn_names
                .iter()
                .any(|name| name.contains("probe_atomic_ptr_from_ptr_unstubbed")),
            "reachable set should include the from_ptr probe root, got {collected_fn_names:?}"
        );
        assert!(
            recorded_unstubbed.iter().any(|path| path.contains("::from_ptr")),
            "backend-selectable stable atomic from_ptr should still report unstubbed at the phase-1 boundary, got {recorded_unstubbed:?}"
        );
        assert!(
            !recorded_unstubbed.iter().any(|path| path.contains("::load")),
            "stable atomic load should remain handler-backed even when from_ptr is not, got {recorded_unstubbed:?}"
        );
    });
}

#[test]
fn test_collect_reachable_items_slice_contains_skips_unstubbed_diagnostic() {
    with_test_tcx_for_source(REACHABILITY_SLICE_CONTAINS_SOURCE, |tcx| {
        let root = find_instance_by_suffix(tcx, "probe_slice_contains");
        let mut transformer = BodyTransformation::new_for_tests();
        let abstraction_boundary = TestAbstractionBoundary::new();

        let (items, _graph) = collect_reachable_items(
            tcx,
            &mut transformer,
            &[MonoItem::Fn(root)],
            &abstraction_boundary,
        );
        let collected_fn_names: Vec<_> = items
            .into_iter()
            .filter_map(|item| match item {
                MonoItem::Fn(instance) => Some(instance.name()),
                _ => None,
            })
            .collect();
        let recorded_unstubbed = abstraction_boundary.recorded_unstubbed_paths();

        assert!(
            collected_fn_names.iter().any(|name| name.contains("probe_slice_contains")),
            "reachable set should include the slice::contains probe root, got {collected_fn_names:?}"
        );
        assert!(
            !collected_fn_names.iter().any(|name| name.ends_with("::contains")),
            "slice::contains should stay abstract at reachability, got {collected_fn_names:?}"
        );
        assert!(
            recorded_unstubbed.is_empty(),
            "handler-backed slice::contains should not be recorded as unstubbed, got {recorded_unstubbed:?}"
        );
    });
}
