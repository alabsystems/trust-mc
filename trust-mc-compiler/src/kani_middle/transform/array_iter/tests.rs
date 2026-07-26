// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(clippy::unwrap_used)]

use super::*;
use crate::args::Arguments;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::{CompilerError, CrateDef, run_with_tcx};
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use tempfile::TempDir;

const ARRAY_ITER_NONCOPY_SOURCE: &str = r#"
#![allow(dead_code)]

struct NonCopy(u8);

fn probe_noncopy_array(array: [NonCopy; 3]) -> u8 {
    let mut sum = 0u8;
    for value in array {
        sum += value.0;
    }
    sum
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
    let crate_name = format!("array_iter_test_crate_{unique_id}");
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

fn transform_probe_body(tcx: TyCtxt<'_>) -> (Body, Place, BasicBlockIdx) {
    let instance = find_instance_by_suffix(tcx, "probe_noncopy_array");
    let body = instance.body().expect("probe_noncopy_array should have a body");
    let mut array_loops = find_array_for_loops(&body);
    assert_eq!(array_loops.len(), 1, "probe should contain exactly one array for-loop");
    let loop_info = array_loops.pop().expect("probe should contain an array for-loop");
    let mut pass = ArrayIterUnrollPass::new();
    let (changed, transformed) = pass.transform(tcx, body, instance);
    assert!(changed, "array_iter pass should transform the non-Copy array probe");
    (transformed, loop_info.array_place, loop_info.body_bb)
}

fn collect_call_type_strings(body: &Body) -> Vec<String> {
    body.blocks
        .iter()
        .filter_map(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                return None;
            };
            func.ty(body.locals()).ok().map(|ty| format!("{ty:?}"))
        })
        .collect()
}

fn has_constant_indexed_array_read(body: &Body, array_place: &Place, expected_offset: u64) -> bool {
    body.blocks.iter().any(|block| {
        block.statements.iter().any(|stmt| {
            let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                return false;
            };
            let place = match rvalue {
                Rvalue::Use(Operand::Copy(place)) | Rvalue::Use(Operand::Move(place)) => place,
                _ => return false,
            };
            place.local == array_place.local
                && place.projection.len() == array_place.projection.len() + 1
                && place.projection[..array_place.projection.len()] == array_place.projection[..]
                && matches!(
                    place.projection.last(),
                    Some(ProjectionElem::ConstantIndex { offset, .. }) if *offset == expected_offset
                )
        })
    })
}

#[test]
fn test_pass_creation() {
    let _pass = ArrayIterUnrollPass::new();
    assert!(matches!(ArrayIterUnrollPass::transformation_type(), TransformationType::Stubbing));
}

#[test]
fn test_pass_enabled_for_ay_chc_without_unstable_flag() {
    let mut args = Arguments::default();
    args.ay_chc = true;

    let mut query_db = QueryDb::default();
    query_db.set_args(args);

    let pass = ArrayIterUnrollPass::new();
    assert!(pass.is_enabled(&query_db));
}

#[test]
fn test_is_array_iter_infra_ty_name() {
    assert!(is_array_iter_infra_ty_name("std::array::IntoIter<i32, 3>"));
    assert!(is_array_iter_infra_ty_name("PolymorphicIter<i32>"));
    assert!(is_array_iter_infra_ty_name("std::ops::IndexRange"));
    assert!(is_array_iter_infra_ty_name("std::array::iter::iter_inner::IterInner<i32>"));
    assert!(!is_array_iter_infra_ty_name("Vec<i32>"));
    assert!(!is_array_iter_infra_ty_name("Range<usize>"));
    assert!(!is_array_iter_infra_ty_name("ManuallyDrop<String>"));
}

#[test]
fn test_is_array_iter_infra_call() {
    assert!(is_array_iter_infra_call("fn(IntoIter<i32>) -> Option<i32>"));
    assert!(is_array_iter_infra_call("fn(&mut Iter) -> Iterator::next"));
    assert!(is_array_iter_infra_call("fn(PolymorphicIter<i32>)"));
    assert!(is_array_iter_infra_call("fn(&mut IndexRange) -> IndexRange::next"));
    assert!(is_array_iter_infra_call("IndexRange::next_unchecked"));
    assert!(!is_array_iter_infra_call("fn(Vec<i32>) -> usize"));
    assert!(!is_array_iter_infra_call("fn(&str) -> bool"));
}

#[test]
fn test_transform_removes_array_iter_infrastructure_from_noncopy_probe() {
    with_test_tcx_for_source(ARRAY_ITER_NONCOPY_SOURCE, |tcx| {
        let (transformed, _, _) = transform_probe_body(tcx);
        let local_ty_names: Vec<_> = transformed
            .local_decls()
            .map(|(_, local_decl)| format!("{:?}", local_decl.ty))
            .collect();
        let call_type_strings = collect_call_type_strings(&transformed);

        assert!(
            !local_ty_names.iter().any(|ty| is_array_iter_infra_ty_name(ty)),
            "transformed body should not keep iterator carrier locals, got {local_ty_names:?}"
        );
        assert!(
            !call_type_strings.iter().any(|ty| is_array_iter_infra_call(ty)),
            "transformed body should not keep iterator infrastructure calls, got {call_type_strings:?}"
        );
    });
}

#[test]
fn test_transform_uses_constant_indexed_array_reads_for_noncopy_probe() {
    with_test_tcx_for_source(ARRAY_ITER_NONCOPY_SOURCE, |tcx| {
        let (transformed, array_place, _) = transform_probe_body(tcx);
        assert!(
            has_constant_indexed_array_read(&transformed, &array_place, 0)
                && has_constant_indexed_array_read(&transformed, &array_place, 1)
                && has_constant_indexed_array_read(&transformed, &array_place, 2),
            "transformed non-Copy array loop should read from the original array place via ConstantIndex projections"
        );
    });
}
