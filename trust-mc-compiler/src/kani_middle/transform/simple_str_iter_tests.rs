// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(clippy::unwrap_used)]

use super::*;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::{CompilerError, run_with_tcx};
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use tempfile::TempDir;

const SIMPLE_STR_ITER_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

struct KaniBytesIter {
    ptr: *const u8,
    len: usize,
}

impl KaniBytesIter {
    fn from_str(source: &str) -> Self {
        KaniBytesIter { ptr: source.as_ptr(), len: source.len() }
    }

    fn nth(&self, i: usize) -> u8 {
        unsafe { *self.ptr.wrapping_add(i) }
    }
}

struct KaniAsciiCharsIter {
    bytes: KaniBytesIter,
}

impl KaniAsciiCharsIter {
    fn from_str(source: &str) -> Self {
        KaniAsciiCharsIter { bytes: KaniBytesIter::from_str(source) }
    }

    fn nth(&self, i: usize) -> char {
        self.bytes.nth(i) as char
    }

    fn len(&self) -> usize {
        self.bytes.len
    }
}

#[doc(hidden)]
mod internal {
    #[kanitool::fn_marker = "StrBytesNthHelper"]
    pub fn kani_str_bytes_nth(source: &str, index: usize) -> Option<u8> {
        let iter = super::KaniBytesIter::from_str(source);
        if index < iter.len { Some(iter.nth(index)) } else { None }
    }

    #[kanitool::fn_marker = "StrCharsNthHelper"]
    pub fn kani_str_chars_nth(source: &str, index: usize) -> Option<char> {
        let iter = super::KaniAsciiCharsIter::from_str(source);
        if index < iter.len() { Some(iter.nth(index)) } else { None }
    }
}

struct MyStr {
    header_0: u8,
    header_1: u8,
    data: str,
}

impl MyStr {
    fn new(original: &mut String) -> &mut Self {
        let buf = original.get_mut(..).unwrap();
        assert!(buf.len() > 2);
        let unsized_len = buf.len() - 2;
        let ptr = std::ptr::slice_from_raw_parts_mut(buf.as_mut_ptr(), unsized_len);
        unsafe { &mut *(ptr as *mut Self) }
    }
}

fn probe_string() -> Option<char> {
    let s = "foo".to_string();
    s.chars().nth(1)
}

fn probe_bytes() -> Option<u8> {
    let v = vec![240u8, 159, 146, 150];
    let s = std::str::from_utf8(&v).unwrap();
    s.bytes().nth(0)
}

fn probe_chars_nth4() -> Option<char> {
    "abcdef".chars().nth(4)
}

fn probe_chars_nth2() -> Option<char> {
    "abcdef".chars().nth(2)
}

fn probe_bytes_nth4() -> Option<u8> {
    "abcdef".bytes().nth(4)
}

fn probe_projection() -> Option<char> {
    let mut buf = String::from("123456");
    let my_str = MyStr::new(&mut buf);
    my_str.data.chars().nth(0)
}
"#;

const MARKER_ONLY_HELPER_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod decoy {
    pub fn kani_str_bytes_nth(_source: &str, _index: usize) -> Option<u8> {
        Some(255)
    }

    pub fn kani_str_chars_nth(_source: &str, _index: usize) -> Option<char> {
        Some('x')
    }
}

mod marked {
    #[kanitool::fn_marker = "StrBytesNthHelper"]
    pub fn bridge_bytes(source: &str, index: usize) -> Option<u8> {
        source.as_bytes().get(index).copied()
    }

    #[kanitool::fn_marker = "StrCharsNthHelper"]
    pub fn bridge_chars(source: &str, index: usize) -> Option<char> {
        source.chars().nth(index)
    }
}

fn probe_marker_chars() -> Option<char> {
    let s = "foo".to_string();
    s.chars().nth(1)
}

fn probe_marker_bytes() -> Option<u8> {
    let s = "bar";
    s.bytes().nth(1)
}
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
    let crate_name = format!("simple_str_iter_test_crate_{unique_id}");
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
        "-Z".to_string(),
        "inline-mir=no".to_string(),
        "-Z".to_string(),
        "mir-opt-level=0".to_string(),
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

fn transform_probe_body(tcx: TyCtxt<'_>, suffix: &str) -> Body {
    let instance = find_instance_by_suffix(tcx, suffix);
    let body = instance.body().expect("probe should have a body");
    let mut pass = SimpleStrIterPass::new();
    let (changed, transformed) = pass.transform(tcx, body, instance);
    assert!(changed, "simple_str_iter pass should transform {suffix}");
    transformed
}

fn collect_call_names(body: &Body) -> Vec<String> {
    body.blocks
        .iter()
        .filter_map(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                return None;
            };
            let func_ty = func.ty(body.locals()).ok()?;
            let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)) =
                func_ty.kind()
            else {
                return None;
            };
            Some(def.name().clone())
        })
        .collect()
}

fn collect_call_paths(tcx: TyCtxt<'_>, body: &Body) -> Vec<String> {
    body.blocks
        .iter()
        .filter_map(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                return None;
            };
            let func_ty = func.ty(body.locals()).ok()?;
            let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)) =
                func_ty.kind()
            else {
                return None;
            };
            Some(tcx.def_path_str(rustc_internal::internal(tcx, def.def_id())))
        })
        .collect()
}

fn has_internal_helper_path(paths: &[String], helper_name: &str) -> bool {
    paths.iter().any(|path| {
        path.strip_suffix(helper_name)
            .is_some_and(|prefix| prefix == "internal::" || prefix.ends_with("::internal::"))
    })
}

fn collect_call_markers(body: &Body) -> Vec<String> {
    body.blocks
        .iter()
        .filter_map(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                return None;
            };
            let func_ty = func.ty(body.locals()).ok()?;
            let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)) =
                func_ty.kind()
            else {
                return None;
            };
            crate::kani_middle::attributes::fn_marker(def).map(|marker| marker.to_string())
        })
        .collect()
}

fn collect_local_type_strings(body: &Body) -> Vec<String> {
    body.local_decls().map(|(_, decl)| format!("{:?}", decl.ty)).collect()
}

#[test]
fn test_pass_creation() {
    let _pass = SimpleStrIterPass::new();
    assert!(matches!(SimpleStrIterPass::transformation_type(), TransformationType::Stubbing));
}

#[test]
fn test_transform_rewrites_string_chars_nth_to_helper() {
    with_test_tcx_for_source(SIMPLE_STR_ITER_SOURCE, |tcx| {
        let transformed = transform_probe_body(tcx, "probe_string");
        let local_ty_names = collect_local_type_strings(&transformed);
        let call_names = collect_call_names(&transformed);
        let call_paths = collect_call_paths(tcx, &transformed);
        let call_markers = collect_call_markers(&transformed);

        assert!(
            !local_ty_names.iter().any(|ty| ty.contains("str::Chars")),
            "transformed body should not keep Chars locals, got {local_ty_names:?}"
        );
        assert!(
            call_names.iter().any(|name| name.ends_with("kani_str_chars_nth")),
            "transformed body should call the chars helper, got {call_names:?}"
        );
        assert!(
            call_markers.iter().any(|marker| marker == CHARS_HELPER_MARKER),
            "transformed body should call the marker-tagged chars helper, got {call_markers:?}"
        );
        assert!(
            has_internal_helper_path(&call_paths, "kani_str_chars_nth"),
            "transformed body should call the internal chars helper path, got {call_paths:?}"
        );
        assert!(
            !call_names.iter().any(|name| name.ends_with("::chars") || name.ends_with("::nth")),
            "transformed body should not keep chars()/nth() calls, got {call_names:?}"
        );
    });
}

#[test]
fn test_transform_rewrites_bytes_nth_to_helper() {
    with_test_tcx_for_source(SIMPLE_STR_ITER_SOURCE, |tcx| {
        let transformed = transform_probe_body(tcx, "probe_bytes");
        let local_ty_names = collect_local_type_strings(&transformed);
        let call_names = collect_call_names(&transformed);
        let call_paths = collect_call_paths(tcx, &transformed);
        let call_markers = collect_call_markers(&transformed);

        assert!(
            !local_ty_names.iter().any(|ty| ty.contains("str::Bytes")),
            "transformed body should not keep Bytes locals, got {local_ty_names:?}"
        );
        assert!(
            call_names.iter().any(|name| name.ends_with("kani_str_bytes_nth")),
            "transformed body should call the bytes helper, got {call_names:?}"
        );
        assert!(
            call_markers.iter().any(|marker| marker == BYTES_HELPER_MARKER),
            "transformed body should call the marker-tagged bytes helper, got {call_markers:?}"
        );
        assert!(
            has_internal_helper_path(&call_paths, "kani_str_bytes_nth"),
            "transformed body should call the internal bytes helper path, got {call_paths:?}"
        );
        assert!(
            !call_names.iter().any(|name| name.ends_with("::bytes") || name.ends_with("::nth")),
            "transformed body should not keep bytes()/nth() calls, got {call_names:?}"
        );
    });
}

#[test]
fn test_transform_rewrites_projection_chars_nth_to_helper() {
    with_test_tcx_for_source(SIMPLE_STR_ITER_SOURCE, |tcx| {
        let transformed = transform_probe_body(tcx, "probe_projection");
        let local_ty_names = collect_local_type_strings(&transformed);
        let call_names = collect_call_names(&transformed);
        let call_paths = collect_call_paths(tcx, &transformed);
        let call_markers = collect_call_markers(&transformed);

        assert!(
            !local_ty_names.iter().any(|ty| ty.contains("str::Chars")),
            "transformed projection body should not keep Chars locals, got {local_ty_names:?}"
        );
        assert!(
            call_names.iter().any(|name| name.ends_with("kani_str_chars_nth")),
            "transformed projection body should call the chars helper, got {call_names:?}"
        );
        assert!(
            call_markers.iter().any(|marker| marker == CHARS_HELPER_MARKER),
            "transformed projection body should call the marker-tagged chars helper, got {call_markers:?}"
        );
        assert!(
            has_internal_helper_path(&call_paths, "kani_str_chars_nth"),
            "transformed projection body should call the internal chars helper path, got {call_paths:?}"
        );
        assert!(
            !call_names.iter().any(|name| name.ends_with("::chars") || name.ends_with("::nth")),
            "transformed projection body should not keep chars()/nth() calls, got {call_names:?}"
        );
    });
}

#[test]
fn test_transform_prefers_marker_tagged_helper_over_suffix_match() {
    with_test_tcx_for_source(MARKER_ONLY_HELPER_SOURCE, |tcx| {
        let transformed_chars = transform_probe_body(tcx, "probe_marker_chars");
        let char_call_names = collect_call_names(&transformed_chars);
        let char_call_markers = collect_call_markers(&transformed_chars);

        assert!(
            char_call_names.iter().any(|name| name.ends_with("bridge_chars")),
            "transformed body should call the marker-tagged chars bridge, got {char_call_names:?}"
        );
        assert!(
            !char_call_names.iter().any(|name| name == "kani_str_chars_nth"),
            "transformed body should not call the suffix-matched decoy chars helper, got {char_call_names:?}"
        );
        assert!(
            char_call_markers.iter().any(|marker| marker == CHARS_HELPER_MARKER),
            "transformed body should retain the chars helper marker, got {char_call_markers:?}"
        );

        let transformed_bytes = transform_probe_body(tcx, "probe_marker_bytes");
        let byte_call_names = collect_call_names(&transformed_bytes);
        let byte_call_markers = collect_call_markers(&transformed_bytes);

        assert!(
            byte_call_names.iter().any(|name| name.ends_with("bridge_bytes")),
            "transformed body should call the marker-tagged bytes bridge, got {byte_call_names:?}"
        );
        assert!(
            !byte_call_names.iter().any(|name| name == "kani_str_bytes_nth"),
            "transformed body should not call the suffix-matched decoy bytes helper, got {byte_call_names:?}"
        );
        assert!(
            byte_call_markers.iter().any(|marker| marker == BYTES_HELPER_MARKER),
            "transformed body should retain the bytes helper marker, got {byte_call_markers:?}"
        );
    });
}

#[test]
fn test_library_string_helper_boundary_stays_internal() {
    with_test_tcx_for_source(SIMPLE_STR_ITER_SOURCE, |_tcx| {
        assert!(
            find_helper_instance(BYTES_HELPER_MARKER).is_some(),
            "bytes helper marker should remain discoverable"
        );
        assert!(
            find_helper_instance(CHARS_HELPER_MARKER).is_some(),
            "chars helper marker should remain discoverable"
        );
    });

    let iter_string_source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../library/kani_core/src/iter_string.rs"
    ));
    let kani_core_lib_source =
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../library/kani_core/src/lib.rs"));

    assert!(
        !iter_string_source.contains("pub struct KaniBytesIter"),
        "KaniBytesIter should stay private to the string helper implementation"
    );
    assert!(
        !iter_string_source.contains("pub struct KaniAsciiCharsIter"),
        "KaniAsciiCharsIter should stay private to the string helper implementation"
    );
    assert!(
        kani_core_lib_source.matches("kani_core::generate_string_iter_internal!();").count() == 1,
        "kani_core should emit exactly one internal string helper block for the shipped kani module"
    );
    assert!(
        kani_core_lib_source.matches("kani_core::generate_string_iter_root_helpers!();").count()
            == 2,
        "only the core/std macro variants should retain root-level string helper entry points"
    );
}

/// `chars().nth(k)` runs `Chars::advance_by`, a loop of one pass per skipped
/// char, and Kani fails its unwinding assertion unless `k < U` (measured for
/// `k` in 0..=5, `U` in 1..=6). The helper has no loop, so under a declared
/// bound the rewrite dropped that failure: `chars().nth(4)` under
/// `#[kani::unwind(3)]` verified clean (walker fail-closed review 6 round 3,
/// finding 6). Under a bound only a constant `k < U` is rewritten; `bytes()`
/// (a slice index in std) and an unbounded unit are rewritten as before.
#[test]
fn test_chars_nth_rewrite_respects_the_declared_unwind() {
    with_test_tcx_for_source(SIMPLE_STR_ITER_SOURCE, |tcx| {
        let run = |suffix: &str, unwind: Option<u32>| {
            let instance = find_instance_by_suffix(tcx, suffix);
            let body = instance.body().expect("probe should have a body");
            SimpleStrIterPass::with_declared_unwind(unwind).transform(tcx, body, instance).0
        };
        assert!(!run("probe_chars_nth4", Some(3)), "k = 4 >= U = 3: the std call stays");
        assert!(run("probe_chars_nth2", Some(3)), "k = 2 < U = 3: rewritten");
        assert!(run("probe_chars_nth4", Some(5)), "k = 4 < U = 5: rewritten");
        assert!(run("probe_chars_nth4", None), "no declared bound: rewritten");
        assert!(run("probe_bytes_nth4", Some(3)), "bytes().nth is loop-free: rewritten");
    });
}

/// The pass starts at the unit's smallest bound and is re-keyed per harness
/// (`BodyTransformation::set_harness_declared_unwind`): a harness declaring
/// `unwind(8)` gets the rewrite of `chars().nth(4)` even when another harness
/// of the unit declares `unwind(3)` (walker fail-closed review 6 round 3,
/// `str_chars_nth_unwind_dual.rs` `n1_chars_nth_u8_safe`, which failed
/// against main's proof), and the next `unwind(3)` harness keeps the std call.
#[test]
fn test_chars_nth_rewrite_follows_the_harness_bound() {
    use crate::kani_middle::transform::TransformPass;
    with_test_tcx_for_source(SIMPLE_STR_ITER_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_chars_nth4");
        let mut pass = SimpleStrIterPass::with_declared_unwind(Some(3));
        let mut run = |pass: &mut SimpleStrIterPass| {
            let body = instance.body().expect("probe should have a body");
            pass.transform(tcx, body, instance).0
        };
        assert!(!run(&mut pass), "the unit's bound 3: the std call stays");
        pass.set_harness_declared_unwind(Some(8));
        assert!(run(&mut pass), "a harness with unwind(8): rewritten");
        pass.set_harness_declared_unwind(Some(3));
        assert!(!run(&mut pass), "the next harness with unwind(3): the std call stays");
        pass.set_harness_declared_unwind(None);
        assert!(run(&mut pass), "a harness with no bound: rewritten");
    });
}
