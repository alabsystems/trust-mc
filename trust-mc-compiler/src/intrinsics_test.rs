// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The float intrinsics Trust core spells differently from the frozen nightly core must reach
//! the same models: `f32::abs`, `f64::min` and `f32::max` are compiled against the toolchain's
//! own core, and the intrinsic each calls must classify and read as the nightly spelling on
//! both toolchains.

#![allow(clippy::unwrap_used)]

use super::{
    Intrinsic, callee_path_model_spelling, instance_path_model_spelling, intrinsic_model_name,
    is_modelled_renamed_intrinsic, nightly_float_intrinsic_name,
};
use crate::kani_middle::transform::TransformPass;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::Body;
use rustc_public::mir::TerminatorKind;
use rustc_public::mir::mono::Instance;
use rustc_public::rustc_internal;
use rustc_public::ty::{FloatTy, RigidTy, TyKind};
use rustc_public::{CompilerError, CrateDef, run_with_tcx};
use std::fs;
use std::sync::atomic::{AtomicU64, Ordering};
use tempfile::TempDir;

#[test]
fn trust_float_intrinsic_spellings_read_as_their_nightly_names() {
    let cases = [
        ("fabs", Some(FloatTy::F16), "fabsf16"),
        ("fabs", Some(FloatTy::F32), "fabsf32"),
        ("fabs", Some(FloatTy::F64), "fabsf64"),
        ("fabs", Some(FloatTy::F128), "fabsf128"),
        ("minimum_number_nsz_f16", None, "minnumf16"),
        ("minimum_number_nsz_f32", None, "minnumf32"),
        ("minimum_number_nsz_f64", None, "minnumf64"),
        ("minimum_number_nsz_f128", None, "minnumf128"),
        ("maximum_number_nsz_f16", None, "maxnumf16"),
        ("maximum_number_nsz_f32", None, "maxnumf32"),
        ("maximum_number_nsz_f64", None, "maxnumf64"),
        ("maximum_number_nsz_f128", None, "maxnumf128"),
    ];
    for (trust_name, float_ty, nightly_name) in cases {
        assert_eq!(nightly_float_intrinsic_name(trust_name, float_ty), Some(nightly_name));
    }
}

#[test]
fn float_intrinsics_trust_core_did_not_rename_keep_their_names() {
    for name in [
        "fabsf32",
        "fabsf64",
        "minnumf32",
        "maxnumf64",
        "minimumf32",
        "maximumf64",
        "copysignf64",
        "sqrtf32",
        "powif64",
        "fmaf32",
        "round_ties_even_f64",
        "fadd_fast",
        "frem_algebraic",
        "float_to_int_unchecked",
    ] {
        assert_eq!(nightly_float_intrinsic_name(name, Some(FloatTy::F32)), None, "{name}");
    }
    // `fabs` has no width of its own: without the float it is instantiated at it stays as is.
    assert_eq!(nightly_float_intrinsic_name("fabs", None), None);
}

const FLOAT_METHODS: &str = r#"
pub fn probe(x: f32, y: f64) -> (f32, f64, f64, f32) {
    (x.abs(), y.abs(), y.min(1.5), x.max(2.5))
}
"#;

fn with_test_tcx_for_source<F>(source: &str, callback: F)
where
    F: for<'tcx> FnOnce(TyCtxt<'tcx>) + Send,
{
    static CRATE_COUNTER: AtomicU64 = AtomicU64::new(0);
    let temp_dir = TempDir::new().expect("create temp dir");
    let src_path = temp_dir.path().join("lib.rs");
    fs::write(&src_path, source).expect("write test source");
    let crate_name =
        format!("intrinsics_test_crate_{}", CRATE_COUNTER.fetch_add(1, Ordering::SeqCst));
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

/// Every call terminator's resolved callee in `instance`'s body.
fn called_instances(instance: &Instance) -> Vec<Instance> {
    calls_in(&instance.body().expect("body"))
}

/// Every call terminator's resolved callee in `body`.
fn calls_in(body: &Body) -> Vec<Instance> {
    body.blocks
        .iter()
        .filter_map(|block| match &block.terminator.kind {
            TerminatorKind::Call { func, .. } => match func.ty(body.locals()).ok()?.kind() {
                TyKind::RigidTy(RigidTy::FnDef(def, args)) => Instance::resolve(def, &args).ok(),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

#[test]
fn std_float_methods_call_intrinsics_that_read_as_the_nightly_models() {
    with_test_tcx_for_source(FLOAT_METHODS, |tcx| {
        let probe = rustc_public::all_local_items()
            .into_iter()
            .find_map(|item| {
                let def_id = rustc_internal::internal(tcx, item.def_id());
                (tcx.def_path_str(def_id) == "probe")
                    .then(|| Instance::try_from(item).ok())
                    .flatten()
            })
            .expect("probe fn");
        let methods = called_instances(&probe);
        let expected = ["fabsf32", "fabsf64", "minnumf64", "maxnumf32"];
        assert_eq!(methods.len(), expected.len(), "calls in probe: {methods:?}");

        for (method, nightly_name) in methods.iter().zip(expected) {
            let intrinsics: Vec<_> = called_instances(method)
                .into_iter()
                .filter(|callee| callee.intrinsic_name().is_some())
                .collect();
            assert_eq!(intrinsics.len(), 1, "{}: intrinsic calls {intrinsics:?}", method.name());
            let intrinsic = &intrinsics[0];

            assert_eq!(intrinsic_model_name(intrinsic).as_deref(), Some(nightly_name));
            // On Trust the intrinsic is a renamed spelling; on the nightly it IS the nightly name.
            assert_eq!(
                is_modelled_renamed_intrinsic(intrinsic),
                cfg!(trust_toolchain),
                "{nightly_name}"
            );
            let classified = Intrinsic::from_instance(intrinsic);
            let expected_variant = match nightly_name {
                "fabsf32" => matches!(classified, Intrinsic::FabsF32),
                "fabsf64" => matches!(classified, Intrinsic::FabsF64),
                "minnumf64" => matches!(classified, Intrinsic::MinNumF64),
                "maxnumf32" => matches!(classified, Intrinsic::MaxNumF32),
                _ => unreachable!(),
            };
            assert!(expected_variant, "{nightly_name}: classified as {classified:?}");

            let def_path = tcx.def_path_str(rustc_internal::internal(tcx, intrinsic.def.def_id()));
            let TyKind::RigidTy(RigidTy::FnDef(def, args)) = intrinsic.ty().kind() else {
                panic!("intrinsic without an FnDef type: {intrinsic:?}")
            };
            let spelled = callee_path_model_spelling(def_path.clone(), def, &args);
            assert!(
                spelled.ends_with(&format!("::{nightly_name}")),
                "{def_path} should read as ...::{nightly_name}, got {spelled}"
            );
            assert_eq!(instance_path_model_spelling(def_path, intrinsic), spelled);
        }
    });
}

const HALF_AND_QUAD_MIN_MAX: &str = r#"
#![feature(f16, f128)]
pub fn probe(a: f16, b: f128) -> (f16, f16, f128, f128) {
    (a.min(0.5), a.max(0.5), b.min(0.5), b.max(0.5))
}
"#;

/// The f16/f128 min/max intrinsics are renamed too, and on Trust they are the ones whose
/// fallback body no engine models: the BMC mini-inliner executed `minimum_number_nsz_f16`'s body
/// and proved `(-0.0f16).min(0.0).is_sign_positive()`, which fails at run time. They must read
/// as renamed, so `AYCtx::body_or_instance_body` (and every other body fetch) refuses them.
#[test]
fn half_and_quad_min_max_intrinsics_are_renamed_intrinsics_with_no_reachable_body() {
    with_test_tcx_for_source(HALF_AND_QUAD_MIN_MAX, |tcx| {
        let probe = rustc_public::all_local_items()
            .into_iter()
            .find_map(|item| {
                let def_id = rustc_internal::internal(tcx, item.def_id());
                (tcx.def_path_str(def_id) == "probe")
                    .then(|| Instance::try_from(item).ok())
                    .flatten()
            })
            .expect("probe fn");
        let expected = ["minnumf16", "maxnumf16", "minnumf128", "maxnumf128"];
        let methods = called_instances(&probe);
        assert_eq!(methods.len(), expected.len(), "calls in probe: {methods:?}");
        for (method, nightly_name) in methods.iter().zip(expected) {
            let intrinsics: Vec<_> = called_instances(method)
                .into_iter()
                .filter(|callee| callee.intrinsic_name().is_some())
                .collect();
            assert_eq!(intrinsics.len(), 1, "{}: intrinsic calls {intrinsics:?}", method.name());
            let intrinsic = &intrinsics[0];
            assert_eq!(intrinsic_model_name(intrinsic).as_deref(), Some(nightly_name));
            assert_eq!(
                is_modelled_renamed_intrinsic(intrinsic),
                cfg!(trust_toolchain),
                "{nightly_name}"
            );
        }
    });
}

/// The inliner must leave the call to a renamed float intrinsic in place. On Trust,
/// `minimum_number_nsz_f64` and `maximum_number_nsz_f32` have fallback bodies; inlining one into
/// `f64::min` / `f32::max` replaced the minNum/maxNum model with a single deterministic choice
/// (measured: the BMC min/max duals decided on the Trustc route where the nightly model leaves
/// them undecided).
#[test]
fn the_inliner_keeps_renamed_float_intrinsics_as_calls_to_their_models() {
    with_test_tcx_for_source(FLOAT_METHODS, |tcx| {
        let probe = rustc_public::all_local_items()
            .into_iter()
            .find_map(|item| {
                let def_id = rustc_internal::internal(tcx, item.def_id());
                (tcx.def_path_str(def_id) == "probe")
                    .then(|| Instance::try_from(item).ok())
                    .flatten()
            })
            .expect("probe fn");
        let expected = ["fabsf32", "fabsf64", "minnumf64", "maxnumf32"];
        for (method, nightly_name) in called_instances(&probe).iter().zip(expected) {
            let body = method.body().expect("method body");
            let mut pass = FunctionInlinePass::new(InlineConfig {
                max_depth: 8,
                enabled: true,
                ..InlineConfig::default()
            });
            let (_, inlined) = pass.transform(tcx, body, *method);
            let model_calls: Vec<_> = calls_in(&inlined)
                .into_iter()
                .filter(|callee| intrinsic_model_name(callee).as_deref() == Some(nightly_name))
                .collect();
            assert_eq!(
                model_calls.len(),
                1,
                "{}: after inlining, the call to the {nightly_name} model must remain",
                method.name()
            );
        }
    });
}
