// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(clippy::unwrap_used)]

use super::reachability::{
    AbstractionBoundary, collect_reachable_items, filter_crate_items, harness_stub_replaces_body,
};
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

const REACHABILITY_DYN_COERCION_SOURCE: &str = r#"
#![allow(dead_code)]
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::Arc;

pub trait Shape { fn area(&self) -> u32; }
pub struct Square(pub u32);
impl Shape for Square { fn area(&self) -> u32 { self.0 * self.0 } }

pub fn probe_box_dyn() -> u32 { let b: Box<dyn Shape> = Box::new(Square(3)); b.area() }
pub fn probe_rc_dyn() -> u32 { let r: Rc<dyn Shape> = Rc::new(Square(3)); r.area() }
pub fn probe_arc_dyn() -> u32 { let a: Arc<dyn Shape> = Arc::new(Square(3)); a.area() }
pub fn probe_nonnull_slice() -> usize {
    let mut bytes = [1u8, 2, 3, 4];
    let whole: NonNull<[u8; 4]> = NonNull::from(&mut bytes);
    let slice: NonNull<[u8]> = whole;
    slice.len()
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

/// On Trust, `NonNull<T>` holds `pattern_type!(*const T is !null)`, so reachability walks
/// through a pattern type for every coercion below; it used to panic in
/// `coercion.rs` ("Expected a pointer") before collecting the vtable.
#[test]
fn test_collect_reachable_items_follows_smart_pointer_unsize_coercions() {
    with_test_tcx_for_source(REACHABILITY_DYN_COERCION_SOURCE, |tcx| {
        for (root_name, needs_vtable) in [
            ("probe_box_dyn", true),
            ("probe_rc_dyn", true),
            ("probe_arc_dyn", true),
            ("probe_nonnull_slice", false),
        ] {
            let root = find_instance_by_suffix(tcx, root_name);
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
                collected_fn_names.iter().any(|name| name.ends_with(root_name)),
                "{root_name}: reachable set should include the root, got {collected_fn_names:?}"
            );
            if needs_vtable {
                assert!(
                    collected_fn_names.iter().any(|name| name.contains("Shape>::area")),
                    "{root_name}: the coercion to dyn Shape should collect Square's vtable method, got {collected_fn_names:?}"
                );
            }
        }
    });
}

const HARNESS_STUB_SOURCE: &str = r#"
#![allow(dead_code)]
pub fn stubbed_original(x: u32) -> u32 { x + 1 }
pub fn stub_replacement(x: u32) -> u32 { x + 2 }
pub fn unrelated_fn(x: u32) -> u32 { x }
"#;

fn fn_def_of(instance: Instance) -> rustc_public::ty::FnDef {
    match instance.ty().kind() {
        rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)) => def,
        other => panic!("expected FnDef, got {other:?}"),
    }
}

/// A harness `#[kani::stub(from, to)]` whose sides both have a body replaces `from`'s body,
/// so reachability must collect it whatever `from`'s path says; nothing else is replaced.
#[test]
fn test_harness_stub_replaces_body_only_for_the_stubbed_function() {
    with_test_tcx_for_source(HARNESS_STUB_SOURCE, |tcx| {
        let original = find_instance_by_suffix(tcx, "stubbed_original");
        let replacement = find_instance_by_suffix(tcx, "stub_replacement");
        let unrelated = find_instance_by_suffix(tcx, "unrelated_fn");
        let mut stubs = crate::kani_middle::codegen_units::Stubs::default();
        assert!(!harness_stub_replaces_body(&stubs, original), "empty map replaces nothing");
        stubs.insert(fn_def_of(original), fn_def_of(replacement));
        assert!(harness_stub_replaces_body(&stubs, original));
        assert!(!harness_stub_replaces_body(&stubs, replacement), "the stub itself is not replaced");
        assert!(!harness_stub_replaces_body(&stubs, unrelated));
    });
}

/// Design 5 backstop (`loop_contract_reach.rs`): a register call reached through
/// non-local generic code, through a vtable, through a fn pointer, directly, and
/// not at all.
const LOOP_CONTRACT_REACH_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

#[inline(never)]
#[kanitool::fn_marker = "kani_register_loop_contract"]
fn kani_register_loop_contract<F: Fn() -> bool>(f: &F, transformed: usize) -> bool {
    transformed != 0 && f()
}

fn contracted(n: u32) -> u32 {
    let inv = || n < 100;
    if kani_register_loop_contract(&inv, 1) { n } else { 0 }
}

struct MyIter(u32);

impl Iterator for MyIter {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        if self.0 == 0 {
            return None;
        }
        self.0 = 0;
        Some(contracted(1))
    }
}

pub fn via_generic_code() -> usize {
    MyIter(1).count()
}

pub fn via_vtable() -> Option<u32> {
    let mut it = MyIter(1);
    let d: &mut dyn Iterator<Item = u32> = &mut it;
    d.next()
}

pub fn via_fn_pointer() -> Option<u32> {
    let f: fn(u32) -> u32 = contracted;
    Some(1u32).map(f)
}

pub fn direct_only() -> u32 {
    contracted(2)
}

pub fn unrelated() -> u32 {
    let v = [1u32, 2];
    v[0].wrapping_add(v[1])
}
"#;

/// Abstracts every function whose path contains one of the fragments, and
/// nothing else the test source reaches.
struct NamedBoundary(&'static [&'static str]);

impl AbstractionBoundary for NamedBoundary {
    fn has_explicit_stub(&self, path: &str) -> bool {
        self.0.iter().any(|fragment| path.contains(fragment))
    }

    fn has_handler_backed_abstraction(&self, _path: &str) -> bool {
        false
    }

    fn record_unstubbed_abstraction(&self, _path: &str) {}
}

fn loop_contract_reach_of(
    tcx: TyCtxt<'_>,
    root: &str,
    boundary: &dyn AbstractionBoundary,
) -> (Instance, std::sync::Arc<crate::kani_middle::loop_contract_reach::LoopContractReach>) {
    let root = find_instance_by_suffix(tcx, root);
    let mut transformer = BodyTransformation::new_for_tests();
    let (_items, graph) =
        collect_reachable_items(tcx, &mut transformer, &[MonoItem::Fn(root)], boundary);
    (root, graph.dyn_universe.loop_contract_reach().expect("the collector computes the reach"))
}

fn some_address_taken_fn_reaches(
    reach: &crate::kani_middle::loop_contract_reach::LoopContractReach,
) -> bool {
    reach.address_taken().any(|taken| reach.reaches(&taken) == Some(true))
}

#[test]
fn loop_contract_reach_follows_generic_code_vtables_and_fn_pointers() {
    with_test_tcx_for_source(LOOP_CONTRACT_REACH_SOURCE, |tcx| {
        let none = NamedBoundary(&[]);

        let (root, reach) = loop_contract_reach_of(tcx, "via_generic_code", &none);
        assert_eq!(
            reach.reaches(&root),
            Some(true),
            "`Iterator::count` over a local iterator reaches its `next`"
        );
        assert!(!some_address_taken_fn_reaches(&reach), "nothing's address is taken");

        let (root, reach) = loop_contract_reach_of(tcx, "via_vtable", &none);
        assert!(reach.any());
        assert_eq!(reach.reaches(&root), Some(true), "the vtable method is an edge");
        assert!(some_address_taken_fn_reaches(&reach), "`next` is a vtable method");

        let (_, reach) = loop_contract_reach_of(tcx, "via_fn_pointer", &none);
        assert!(some_address_taken_fn_reaches(&reach), "`contracted` is reified");

        let (root, reach) = loop_contract_reach_of(tcx, "direct_only", &none);
        assert_eq!(reach.reaches(&root), Some(true));
        assert!(!some_address_taken_fn_reaches(&reach), "a direct call takes no address");

        let (root, reach) = loop_contract_reach_of(tcx, "unrelated", &none);
        assert!(!reach.any());
        assert_eq!(reach.reaches(&root), Some(false), "read in full, nothing reached: clear");
    });
}

/// A function the collector abstracts is never followed, so a function whose
/// reach passes one gets no answer from the graph, never a false "clear".
#[test]
fn loop_contract_reach_does_not_clear_a_path_through_an_abstracted_function() {
    with_test_tcx_for_source(LOOP_CONTRACT_REACH_SOURCE, |tcx| {
        let count_abstracted = NamedBoundary(&["Iterator::count"]);
        let (root, reach) = loop_contract_reach_of(tcx, "via_generic_code", &count_abstracted);
        assert!(!reach.any(), "the register call sits past the abstracted `count`");
        assert_eq!(reach.reaches(&root), None, "the graph cannot say, so it must not say no");
    });
}

/// Probe functions for the standard-library abstraction set
/// (`std_abstraction.rs`): each calls the item its name describes.
const STD_ABSTRACTION_SOURCE: &str = r#"
#![allow(dead_code, deprecated)]
use std::alloc::{GlobalAlloc, Layout, System};
use std::borrow::Cow;
use std::collections::{BTreeMap, BinaryHeap, HashMap, HashSet, LinkedList, VecDeque};
use std::rc::Rc;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

pub struct Local(pub usize);
impl From<Vec<u8>> for Local {
    fn from(v: Vec<u8>) -> Self { Local(v.len()) }
}
mod elsewhere {
    impl From<Vec<u16>> for super::Local {
        fn from(v: Vec<u16>) -> Self { super::Local(v.len()) }
    }
}
mod named {
    pub fn fetch_update() -> u8 { 5 }
    pub fn renamed() -> u8 { 5 }
}
pub struct UserAlloc;
unsafe impl GlobalAlloc for UserAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 { unsafe { System.alloc(layout) } }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) { unsafe { System.dealloc(ptr, layout) } }
}
fn local_helper(x: u32) -> u32 { x + 1 }

pub fn vec_push(v: &mut Vec<u32>) { v.push(1) }
pub fn vec_clone(v: &Vec<u32>) -> Vec<u32> { v.clone() }
pub fn vec_into_iter_next(i: &mut std::vec::IntoIter<u32>) -> Option<u32> { i.next() }
pub fn string_from() -> String { String::from("a") }
pub fn cow_into_owned(c: Cow<'static, str>) -> String { c.into_owned() }
pub fn hash_map_new() -> HashMap<u32, u32> { HashMap::new() }
pub fn hash_map_entry(m: &mut HashMap<u32, u32>) { m.entry(1).or_insert(2); }
pub fn hash_set_contains(s: &HashSet<u32>) -> bool { s.contains(&1) }
pub fn btree_map_insert(m: &mut BTreeMap<u32, u32>) { m.insert(1, 2); }
pub fn btree_map_entry(m: &mut BTreeMap<u32, u32>) { m.entry(1).or_insert(2); }
pub fn vec_deque_push_back(d: &mut VecDeque<u32>) { d.push_back(1) }
pub fn linked_list_push_back(l: &mut LinkedList<u32>) { l.push_back(1) }
pub fn binary_heap_push(h: &mut BinaryHeap<u32>) { h.push(1) }
pub fn slice_iter(s: &[u32]) -> std::slice::Iter<'_, u32> { s.iter() }
pub fn slice_iter_next<'a>(i: &mut std::slice::Iter<'a, u32>) -> Option<&'a u32> { i.next() }
pub fn slice_to_vec(s: &[u32]) -> Vec<u32> { s.to_vec() }
pub fn atomic_load(a: &AtomicUsize) -> usize { a.load(Ordering::SeqCst) }
pub fn atomic_fetch_update(a: &AtomicUsize) -> Result<usize, usize> {
    a.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x + 1))
}
pub fn atomic_bool_debug(a: &AtomicBool, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    std::fmt::Debug::fmt(a, f)
}
pub fn fs_remove_file() -> std::io::Result<()> { std::fs::remove_file("x") }
pub fn mutex_lock(m: &Mutex<u32>) -> u32 { *m.lock().unwrap() }
pub fn range_next(r: &mut std::ops::Range<u32>) -> Option<u32> { r.next() }
pub fn option_vec_clone(o: &Option<Vec<u32>>) -> Option<Vec<u32>> { o.clone() }
pub fn box_clone(b: &Box<u32>) -> Box<u32> { b.clone() }
pub fn range_map_capturing_vec(v: Vec<u32>) -> u32 {
    (0..3u32).map(move |x| x + v.len() as u32).sum()
}
pub fn rc_from_vec(v: Vec<u8>) -> Rc<[u8]> { Rc::from(v) }
pub fn local_from_vec(v: Vec<u8>) -> Local { Local::from(v) }
pub fn local_from_vec_elsewhere(v: Vec<u16>) -> Local { Local::from(v) }
pub fn drop_in_place_vec(p: *mut Vec<u32>) { unsafe { std::ptr::drop_in_place(p) } }
pub fn i32_display(x: i32, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    std::fmt::Display::fmt(&x, f)
}
pub fn calls_local() -> u32 { local_helper(1) }
pub fn vec_push_fn_named_fetch_update() -> usize {
    let mut v = Vec::new();
    v.push(named::fetch_update);
    v.len()
}
pub fn vec_push_fn_renamed() -> usize {
    let mut v = Vec::new();
    v.push(named::renamed);
    v.len()
}
pub fn user_global_alloc(a: &UserAlloc) -> *mut u8 {
    unsafe { a.alloc(Layout::new::<u64>()) }
}
"#;

/// The same items through `extern crate alloc` in a `no_std` crate, where
/// they print by their `alloc::` paths: by `alloc::..` under `def_path_str`,
/// by `<crate>::alloc::..` under `Instance::name`.
const NO_STD_ABSTRACTION_SOURCE: &str = r#"
#![no_std]
#![allow(dead_code)]
extern crate alloc;
use alloc::borrow::Cow;
use alloc::collections::{BTreeMap, BTreeSet, LinkedList, VecDeque};
use alloc::string::String;
use alloc::vec::Vec;
use core::sync::atomic::{AtomicUsize, Ordering};
pub fn btree_map_insert(m: &mut BTreeMap<u32, u32>) { m.insert(1, 2); }
pub fn btree_map_entry(m: &mut BTreeMap<u32, u32>) { m.entry(1).or_insert(2); }
pub fn btree_map_iter_next<'a>(
    i: &mut alloc::collections::btree_map::Iter<'a, u32, u32>,
) -> Option<(&'a u32, &'a u32)> { i.next() }
pub fn btree_set_insert(s: &mut BTreeSet<u32>) -> bool { s.insert(1) }
pub fn vec_deque_push_back(d: &mut VecDeque<u32>) { d.push_back(1) }
pub fn vec_deque_rotate_left(d: &mut VecDeque<u32>) { d.rotate_left(1) }
pub fn vec_deque_iter_next<'a>(
    i: &mut alloc::collections::vec_deque::Iter<'a, u32>,
) -> Option<&'a u32> { i.next() }
pub fn linked_list_push_back(l: &mut LinkedList<u32>) { l.push_back(1) }
pub fn linked_list_split_off(l: &mut LinkedList<u32>) -> LinkedList<u32> { l.split_off(1) }
pub fn vec_push(v: &mut Vec<u32>) { v.push(1) }
pub fn vec_clone(v: &Vec<u32>) -> Vec<u32> { v.clone() }
pub fn vec_into_iter_next(i: &mut alloc::vec::IntoIter<u32>) -> Option<u32> { i.next() }
pub fn string_from() -> String { String::from("a") }
pub fn string_push(s: &mut String) { s.push('a') }
pub fn cow_into_owned(c: Cow<'static, str>) -> String { c.into_owned() }
pub fn slice_iter(s: &[u32]) -> core::slice::Iter<'_, u32> { s.iter() }
pub fn slice_to_vec(s: &[u32]) -> Vec<u32> { s.to_vec() }
pub fn atomic_load(a: &AtomicUsize) -> usize { a.load(Ordering::SeqCst) }
"#;

/// A `std` crate that also names `alloc` with `extern crate`, so `alloc`'s
/// own paths go through that item.
const STD_EXTERN_ALLOC_ABSTRACTION_SOURCE: &str = r#"
#![allow(dead_code)]
extern crate alloc;
use std::collections::BTreeMap;
pub fn btree_map_insert(m: &mut BTreeMap<u32, u32>) { m.insert(1, 2); }
pub fn vec_push(v: &mut Vec<u32>) { v.push(1) }
pub fn vec_clone(v: &Vec<u32>) -> Vec<u32> { v.clone() }
pub fn slice_to_vec(s: &[u32]) -> Vec<u32> { s.to_vec() }
pub fn alloc_vec_push(v: &mut alloc::vec::Vec<u32>) { v.push(1) }
"#;

/// Every direct callee of the local function `caller`, with the set's
/// decision for its definition (reachability) and for the instance (the
/// inline gate).
fn std_abstraction_decisions(
    tcx: TyCtxt<'_>,
    set: &crate::kani_middle::std_abstraction::StdAbstraction,
    caller: &str,
) -> Vec<(String, crate::kani_middle::std_abstraction::Abstraction, bool)> {
    use rustc_public::mir::{MirVisitor, Terminator, TerminatorKind, visit::Location};
    use rustc_public::ty::{RigidTy, TyKind};
    struct Callees(
        Vec<(rustc_public::ty::FnDef, rustc_public::ty::GenericArgs)>,
        Vec<rustc_public::mir::LocalDecl>,
    );
    impl MirVisitor for Callees {
        fn visit_terminator(&mut self, terminator: &Terminator, location: Location) {
            if let TerminatorKind::Call { func, .. } = &terminator.kind
                && let Ok(ty) = func.ty(&self.1)
                && let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind()
            {
                self.0.push((def, args));
            }
            self.super_terminator(terminator, location);
        }
    }
    let instance = rustc_public::all_local_items()
        .into_iter()
        .find_map(|item| {
            let path = tcx.def_path_str(rustc_internal::internal(tcx, item.def_id()));
            (path == caller).then(|| Instance::try_from(item).ok()).flatten()
        })
        .unwrap_or_else(|| panic!("no probe `{caller}`"));
    let body = instance.body().expect("probe body");
    let mut callees = Callees(Vec::new(), body.locals().to_vec());
    callees.visit_body(&body);
    callees
        .0
        .into_iter()
        .map(|(def, args)| {
            let callee = Instance::resolve(def, &args).expect("resolve callee");
            let def_id = rustc_internal::internal(tcx, callee.def.def_id());
            (
                callee.name(),
                set.decide_definition(tcx, def_id),
                set.abstracts_public_instance(tcx, callee),
            )
        })
        .collect()
}

/// The decision for the one callee of `caller` whose name contains `callee`:
/// `(definition, instance)`.
fn std_abstraction_decision(
    tcx: TyCtxt<'_>,
    set: &crate::kani_middle::std_abstraction::StdAbstraction,
    caller: &str,
    callee: &str,
) -> (crate::kani_middle::std_abstraction::Abstraction, bool) {
    let decisions = std_abstraction_decisions(tcx, set, caller);
    let mut matching = decisions.iter().filter(|(name, ..)| name.contains(callee));
    let (_, definition, instance) =
        matching.next().unwrap_or_else(|| panic!("`{caller}` calls no `{callee}`: {decisions:?}"));
    assert!(matching.next().is_none(), "`{caller}` calls `{callee}` twice: {decisions:?}");
    (*definition, *instance)
}

/// `(definition, instance)`, each `true` when abstracted.
fn std_abstraction_abstracts(
    tcx: TyCtxt<'_>,
    set: &crate::kani_middle::std_abstraction::StdAbstraction,
    caller: &str,
    callee: &str,
) -> (bool, bool) {
    let (definition, instance) = std_abstraction_decision(tcx, set, caller, callee);
    (definition.is_abstracted(), instance)
}

/// A definition of crate `krate` by its real path, private modules included.
fn sysroot_definition(tcx: TyCtxt<'_>, krate: &str, path: &[&str]) -> rustc_hir::def_id::DefId {
    let krate = *tcx
        .crates(())
        .iter()
        .find(|candidate| tcx.crate_name(**candidate).as_str() == krate)
        .unwrap_or_else(|| panic!("no crate `{krate}`"));
    path.iter().fold(krate.as_def_id(), |current, segment| {
        tcx.module_children(current)
            .iter()
            .filter(|child| child.reexport_chain.is_empty() && child.ident.as_str() == *segment)
            .find_map(|child| child.res.opt_def_id())
            .unwrap_or_else(|| panic!("no `{segment}` in `{}`", tcx.def_path_str(current)))
    })
}

/// Every anchor resolves against the sysroot the tests compile with and
/// prints as one of its former spellings: a toolchain that moves, renames or
/// re-exports one elsewhere fails here, where the former keyword scan only
/// logged at debug level.
#[test]
fn std_abstraction_every_anchor_prints_as_a_former_spelling() {
    for source in
        [STD_ABSTRACTION_SOURCE, NO_STD_ABSTRACTION_SOURCE, STD_EXTERN_ALLOC_ABSTRACTION_SOURCE]
    {
        with_test_tcx_for_source(source, |tcx| {
            let set = crate::kani_middle::std_abstraction::StdAbstraction::resolve(tcx);
            assert_eq!(set.failures(), &[] as &[String], "nothing fails closed");
        });
    }
}

/// The decisions the former spellings made in a `std` crate, on the items
/// themselves.
#[test]
fn std_abstraction_decides_what_the_spellings_decided() {
    with_test_tcx_for_source(STD_ABSTRACTION_SOURCE, |tcx| {
        let set = crate::kani_middle::std_abstraction::StdAbstraction::resolve(tcx);
        let both = (true, true);
        let neither = (false, false);
        let decide =
            |caller: &str, callee: &str| std_abstraction_abstracts(tcx, &set, caller, callee);

        // An inherent method prints through its type (`std::vec::Vec::<T>::push`).
        assert_eq!(decide("vec_push", "push"), both);
        assert_eq!(decide("hash_map_new", "new"), both);
        assert_eq!(decide("btree_map_insert", "insert"), both);
        assert_eq!(decide("vec_deque_push_back", "push_back"), both);
        assert_eq!(decide("linked_list_push_back", "push_back"), both);
        assert_eq!(decide("hash_set_contains", "contains"), both);
        assert_eq!(decide("cow_into_owned", "into_owned"), both);
        assert_eq!(decide("mutex_lock", "lock"), both);
        assert_eq!(decide("atomic_load", "load"), both);
        // An item of an anchored module (`std::collections::hash_map::Entry`,
        // `std::collections::btree_map::Entry`).
        assert_eq!(decide("hash_map_entry", "or_insert"), both);
        assert_eq!(decide("btree_map_entry", "or_insert"), both);
        assert_eq!(decide("fs_remove_file", "remove_file"), both);
        // A slice's inherent impl prints by its module (`core::slice::<impl [T]>::iter`).
        assert_eq!(decide("slice_iter", "iter"), both);
        assert_eq!(decide("slice_to_vec", "to_vec"), both);
        // A qualified path naming an anchored type or module.
        assert_eq!(decide("slice_iter_next", "next"), both);
        assert_eq!(decide("vec_clone", "clone"), both);
        assert_eq!(decide("vec_into_iter_next", "next"), both);
        assert_eq!(decide("string_from", "from"), both);
        assert_eq!(decide("atomic_bool_debug", "fmt"), both);
        assert_eq!(decide("rc_from_vec", "from"), both);
        // A user impl beside its type prints `<Local as From<Vec<u8>>>::from`, which
        // names `Vec`, so the user's own body is abstracted. Pinned for parity with
        // the spellings, not as policy: an unstubbed abstraction does not demote a
        // proof (`demotion.rs`), so whether it should be is an open question. The
        // same impl in another module prints by that module.
        assert_eq!(decide("local_from_vec", "from"), both);
        assert_eq!(decide("local_from_vec_elsewhere", "from"), neither);
        // `fetch_update` keeps its body (its closure must be dispatched), and so
        // does any instance whose printed arguments name one: the inline gate
        // printed `Vec::<fn() -> u8 {named::fetch_update}>::push`.
        assert_eq!(decide("atomic_fetch_update", "fetch_update"), neither);
        assert_eq!(decide("vec_push_fn_named_fetch_update", "push"), (true, false));
        assert_eq!(decide("vec_push_fn_renamed", "push"), both);
        // Not anchored.
        assert_eq!(decide("binary_heap_push", "push"), neither);
        assert_eq!(decide("range_next", "next"), neither);
        assert_eq!(decide("drop_in_place_vec", "drop_in_place"), neither);
        assert_eq!(decide("i32_display", "fmt"), neither);
        assert_eq!(decide("calls_local", "local_helper"), neither);
        // `<UserAlloc as std::alloc::GlobalAlloc>::alloc` contained the text
        // `std::alloc::Global`, which named `Global` only by accident; collected.
        assert_eq!(decide("user_global_alloc", "GlobalAlloc>::alloc"), neither);

        // A private helper of `std::collections::hash::map` prints by that private
        // path, which no spelling named.
        let map_entry =
            sysroot_definition(tcx, "std", &["collections", "hash", "map", "map_entry"]);
        assert_eq!(
            set.decide_definition(tcx, map_entry),
            crate::kani_middle::std_abstraction::Abstraction::Collected
        );
    });
}

/// The inline gate decides per instance, and an instance prints its
/// arguments: `<Option<Vec<u32>> as Clone>::clone` names `Vec`, the
/// definition `<Option<T> as Clone>::clone` does not. A default argument
/// (`Box<u32, Global>`) and a closure's captures are not printed, so they
/// abstract nothing.
#[test]
fn std_abstraction_decides_an_instance_by_the_arguments_it_prints() {
    with_test_tcx_for_source(STD_ABSTRACTION_SOURCE, |tcx| {
        let set = crate::kani_middle::std_abstraction::StdAbstraction::resolve(tcx);
        let decide =
            |caller: &str, callee: &str| std_abstraction_abstracts(tcx, &set, caller, callee);
        assert_eq!(decide("option_vec_clone", "clone"), (false, true));
        assert_eq!(decide("box_clone", "clone"), (false, false));
        assert_eq!(decide("range_map_capturing_vec", "::map::"), (false, false));
    });
}

/// In a `no_std` crate the spellings matched only the `alloc::` paths they
/// name: `VecDeque`, `LinkedList`, `BTreeMap`, `BTreeSet`, their entries and
/// `IntoIter` print by paths none of them names, so their bodies are
/// collected (no stub matches them either). Under `Instance::name` every
/// `alloc` path starts with the crate's own name, so only a qualified path,
/// which contained a spelling, abstracts at the inline gate.
#[test]
fn std_abstraction_decides_in_a_no_std_crate_what_the_spellings_decided() {
    with_test_tcx_for_source(NO_STD_ABSTRACTION_SOURCE, |tcx| {
        let set = crate::kani_middle::std_abstraction::StdAbstraction::resolve(tcx);
        let both = (true, true);
        let neither = (false, false);
        let definition_only = (true, false);
        let decide =
            |caller: &str, callee: &str| std_abstraction_abstracts(tcx, &set, caller, callee);

        assert_eq!(decide("btree_map_insert", "insert"), neither);
        assert_eq!(decide("btree_map_entry", "or_insert"), neither);
        assert_eq!(decide("btree_set_insert", "insert"), neither);
        assert_eq!(decide("vec_deque_push_back", "push_back"), neither);
        assert_eq!(decide("vec_deque_rotate_left", "rotate_left"), neither);
        assert_eq!(decide("linked_list_push_back", "push_back"), neither);
        assert_eq!(decide("linked_list_split_off", "split_off"), neither);
        assert_eq!(decide("vec_into_iter_next", "next"), neither);
        // `<alloc::collections::btree_map::Iter<..> as Iterator>::next` contained the
        // text `alloc::collections::btree` inside `btree_map`; collected.
        assert_eq!(decide("btree_map_iter_next", "next"), neither);
        assert_eq!(decide("vec_deque_iter_next", "next"), both);
        // Spelled `alloc::` paths: a plain path abstracts where it starts with one.
        assert_eq!(decide("vec_push", "push"), definition_only);
        assert_eq!(decide("string_push", "push"), definition_only);
        assert_eq!(decide("cow_into_owned", "into_owned"), definition_only);
        assert_eq!(decide("slice_to_vec", "to_vec"), definition_only);
        assert_eq!(decide("vec_clone", "clone"), both);
        assert_eq!(decide("string_from", "from"), both);
        // `core` is injected, so it prints as `core::` under both printers.
        assert_eq!(decide("slice_iter", "iter"), both);
        assert_eq!(decide("atomic_load", "load"), both);
    });
}

/// `extern crate alloc` in a `std` crate leaves the re-exported types on
/// their `std::` paths and puts `alloc`'s own behind the item.
#[test]
fn std_abstraction_decides_with_extern_crate_alloc_what_the_spellings_decided() {
    with_test_tcx_for_source(STD_EXTERN_ALLOC_ABSTRACTION_SOURCE, |tcx| {
        let set = crate::kani_middle::std_abstraction::StdAbstraction::resolve(tcx);
        let both = (true, true);
        let decide =
            |caller: &str, callee: &str| std_abstraction_abstracts(tcx, &set, caller, callee);
        assert_eq!(decide("btree_map_insert", "insert"), both);
        assert_eq!(decide("vec_push", "push"), both);
        assert_eq!(decide("alloc_vec_push", "push"), both);
        assert_eq!(decide("vec_clone", "clone"), both);
        assert_eq!(decide("slice_to_vec", "to_vec"), both);
    });
}

/// An anchor that does not resolve fails closed: its items are abstracted by
/// its former spellings over the printed text, and the decision says so.
#[test]
fn std_abstraction_fails_closed_by_the_spellings_of_an_unresolved_anchor() {
    use crate::kani_middle::std_abstraction::{Abstraction, StdAbstraction};
    with_test_tcx_for_source(STD_ABSTRACTION_SOURCE, |tcx| {
        let set = StdAbstraction::resolve_altered(tcx, &["std::fs", "alloc::vec::Vec"], &[]);
        assert_eq!(set.failures().len(), 2, "{:?}", set.failures());
        let decide =
            |caller: &str, callee: &str| std_abstraction_decision(tcx, &set, caller, callee);
        assert_eq!(decide("fs_remove_file", "remove_file"), (Abstraction::FailClosed, true));
        assert_eq!(decide("vec_push", "push"), (Abstraction::FailClosed, true));
        // A qualified path naming another anchor is not a failure.
        assert_eq!(decide("string_from", "from"), (Abstraction::Abstracted, true));
        assert_eq!(decide("calls_local", "local_helper"), (Abstraction::Collected, false));
    });
}

/// An anchor printed under the crate a spelling names, as none of them (a
/// re-export moved), fails closed: abstracted wherever it is named.
#[test]
fn std_abstraction_fails_closed_on_an_anchor_printed_as_no_spelling() {
    use crate::kani_middle::std_abstraction::{Abstraction, StdAbstraction};
    with_test_tcx_for_source(STD_ABSTRACTION_SOURCE, |tcx| {
        let set = StdAbstraction::resolve_altered(
            tcx,
            &[],
            &[("std::collections::HashMap", &["std::collections::Map"])],
        );
        assert_eq!(set.failures().len(), 1, "{:?}", set.failures());
        let decide =
            |caller: &str, callee: &str| std_abstraction_decision(tcx, &set, caller, callee);
        assert_eq!(decide("hash_map_new", "new"), (Abstraction::FailClosed, true));
        assert_eq!(decide("vec_push", "push"), (Abstraction::Abstracted, true));
    });
}

/// The former rule over text, used only to fail closed: a path that starts
/// with a spelling, or a qualified path that contains one, after a doubled
/// leading `std::` collapses (#4231).
#[test]
fn std_abstraction_matches_spellings_as_the_former_rule_did() {
    use crate::kani_middle::std_abstraction::matches_spelling;
    let spellings = ["std::fs", "std::vec::Vec"];
    assert!(matches_spelling("std::fs::remove_file", &spellings));
    assert!(matches_spelling("std::std::fs::remove_file", &spellings));
    assert!(matches_spelling("std::std::std::fs::remove_file", &spellings));
    assert!(matches_spelling("<std::vec::Vec<u8> as core::clone::Clone>::clone", &spellings));
    assert!(!matches_spelling("std::fsx::remove_file", &spellings));
    assert!(!matches_spelling("core::fs::remove_file", &spellings));
    assert!(!matches_spelling("core::ptr::drop_in_place::<std::vec::Vec<u8>>", &spellings));
}
