// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![cfg(trust_toolchain)]

use super::common::*;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::context::{AYCtx, with_test_ay_ctx_for_external_source};
use crate::codegen_ay::shared::string_identity::{
    is_native_string_adt, is_string_stub, string_stub_is_authorized,
};
use crate::codegen_ay::statement::StatementCodegen;
use crate::kani_middle::tuple_usage::TupleUsageAnalysis;
use rustc_public::mir::{Body, TerminatorKind};
use std::collections::HashMap;

fn context(callback: impl for<'tcx> FnOnce(AYCtx<'tcx, 'static>) + Send) {
    with_test_ay_ctx_for_external_source(
        include_str!("fixtures/external_string_identity_dependency.rs"),
        include_str!("fixtures/external_string_identity_caller.rs"),
        &[],
        callback,
    );
}

fn call(body: &Body) -> (&Operand, &[Operand], &Place, Option<usize>) {
    let calls: Vec<_> = body
        .blocks
        .iter()
        .filter_map(|block| {
            if let TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            {
                Some((func, args.as_slice(), destination, *target))
            } else {
                None
            }
        })
        .collect();
    assert_eq!(calls.len(), 1, "one actual call required: {body:#?}");
    calls[0]
}

fn classification(ctx: &mut AYCtx<'_, '_>, name: &str, expected: Option<StubKind>) {
    classification_in_lanes(ctx, name, expected, expected);
}

fn classification_in_lanes(
    ctx: &mut AYCtx<'_, '_>,
    name: &str,
    expected_chc: Option<StubKind>,
    expected_bmc: Option<StubKind>,
) {
    let instance = find_instance_by_suffix(ctx.tcx, name);
    let body = instance.callee_body().unwrap();
    let (func, _, _, _) = call(&body);
    let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
    assert_eq!(chc.detect_stub(func), expected_chc, "CHC {name}");
    assert_eq!(
        chc.detect_stub_with_locals(func, body.locals()),
        expected_chc,
        "CHC explicit locals {name}"
    );
    ctx.set_current_fn(instance);
    let bmc = StatementCodegen::new(ctx, &body, TupleUsageAnalysis::run(&body));
    assert_eq!(bmc.test_stdlib_registry_candidate(func), expected_bmc, "BMC {name}");
}

#[test]
fn actual_string_definitions_authorize_both_lanes_and_aliases() {
    context(|mut ctx| {
        let mut calls = 0;
        for prefix in ["standard", "alias", "reexport"] {
            for (method, kind) in [
                ("new", StubKind::StringNew),
                ("default", StubKind::StringNew),
                ("len", StubKind::StringLen),
                ("is_empty", StubKind::StringIsEmpty),
                ("as_str", StubKind::StringAsStr),
                ("deref", StubKind::StringAsStr),
                ("deref_mut", StubKind::StringAsStr),
            ] {
                classification(&mut ctx, &format!("{prefix}_{method}"), Some(kind));
                calls += 1;
            }
        }
        for (name, kind) in [
            ("standard_from", StubKind::StringFrom),
            ("standard_clone", StubKind::StringClone),
            ("standard_to_owned", StubKind::StringClone),
            // The real blanket ToString call uses the existing Display route.
            ("standard_to_string", StubKind::DisplayToString),
        ] {
            classification(&mut ctx, name, Some(kind));
            calls += 1;
        }
        // CHC specializes canonical str equality before its registry. BMC's
        // registry retains the existing general PartialEq candidate instead.
        classification_in_lanes(
            &mut ctx,
            "standard_str_eq",
            Some(StubKind::StringEq),
            Some(StubKind::PrimitivePartialEqEq),
        );
        let equality = find_instance_by_suffix(ctx.tcx, "standard_str_eq").callee_body().unwrap();
        assert!(string_stub_is_authorized(
            ctx.tcx,
            call(&equality).0,
            equality.locals(),
            StubKind::StringEq,
        ));
        calls += 1;
        assert_eq!(calls, 26);
        for (name, expected) in [("standard_cow", true), ("foreign_cow", false)] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.callee_body().unwrap();
            assert_eq!(
                string_stub_is_authorized(
                    ctx.tcx,
                    call(&body).0,
                    body.locals(),
                    StubKind::CowToString
                ),
                expected,
                "actual Cow precheck signature {name}"
            );
        }
        let body = find_instance_by_suffix(ctx.tcx, "identities").body().unwrap();
        assert_eq!(body.arg_locals().len(), 4);
        for (index, local) in body.arg_locals().iter().enumerate() {
            let TyKind::RigidTy(RigidTy::Adt(def, _)) = local.ty.kind() else {
                panic!("actual ADT")
            };
            assert_eq!(is_native_string_adt(ctx.tcx, def), index < 3);
            let sort = ChcCtx::translate_ty(local.ty).unwrap();
            if index < 3 {
                assert_eq!(sort.datatype_name(), Some(crate::codegen_ay::names::RUST_STRING_SORT));
            } else {
                assert_eq!(sort.datatype_sort().unwrap().constructors[0].fields.len(), 1);
            }
            assert_eq!(ChcCtx::detect_collection_type(local.ty).is_some(), index < 3);
        }
    });
}

#[test]
fn actual_external_string_and_early_prechecks_have_no_native_authority() {
    context(|mut ctx| {
        let foreign_new = find_instance_by_suffix(ctx.tcx, "foreign_new").callee_body().unwrap();
        let all_string_kinds = [
            StubKind::StringNew,
            StubKind::StringFrom,
            StubKind::StringFromRawParts,
            StubKind::StringLen,
            StubKind::StringIsEmpty,
            StubKind::StringPush,
            StubKind::StringPushStr,
            StubKind::StringClear,
            StubKind::StringClone,
            StubKind::StringTruncate,
            StubKind::StringFromUtf8Lossy,
            StubKind::StringEq,
            StubKind::StringContains,
            StubKind::StringStartsWith,
            StubKind::StringEndsWith,
            StubKind::StringIsAscii,
            StubKind::StringAsStr,
            StubKind::StringIntoBoxedStr,
            StubKind::StringFromUtf8,
            StubKind::StringIntoBytes,
            StubKind::SplitWhitespace,
            StubKind::SplitWhitespaceNext,
            StubKind::CowToString,
            StubKind::DisplayToString,
            StubKind::FmtFormat,
        ];
        assert_eq!(all_string_kinds.len(), 25);
        for kind in all_string_kinds {
            assert!(is_string_stub(kind));
            assert!(
                !string_stub_is_authorized(
                    ctx.tcx,
                    call(&foreign_new).0,
                    foreign_new.locals(),
                    kind
                ),
                "foreign origin cannot authorize {kind:?}"
            );
        }
        let mut calls = 0;
        for name in [
            "foreign_new",
            "foreign_default",
            "foreign_len",
            "foreign_is_empty",
            "foreign_deref",
            "foreign_trait_len",
            "foreign_trait_is_empty",
            "foreign_bounded",
            "foreign_cow",
            "indirect_len",
            "virtual_len",
        ] {
            classification(&mut ctx, name, None);
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.callee_body().unwrap();
            let (func, args, destination, target) = call(&body);
            if let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func.ty(body.locals()).unwrap().kind()
            {
                if !matches!(name, "foreign_default" | "foreign_deref" | "foreign_cow") {
                    assert!(
                        !rustc_internal::internal(ctx.tcx, def.def_id()).is_local(),
                        "actual external FnDef {name}"
                    );
                }
            }
            ctx.set_current_fn(instance);
            let mut bmc = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            assert!(
                bmc.test_string_dispatch_misses(func, args, destination, target),
                "actual pre-registry dispatch {name}"
            );
            calls += 1;
        }
        assert_eq!(calls, 11);
    });
}

#[test]
fn string_replacement_maps_deny_actual_queries_in_chc_and_bmc() {
    context(|mut ctx| {
        let native = find_instance_by_suffix(ctx.tcx, "standard_len");
        let body = native.callee_body().unwrap();
        let func = call(&body).0;
        let TyKind::RigidTy(RigidTy::FnDef(original, args)) =
            func.ty(body.locals()).unwrap().kind()
        else {
            panic!("actual native FnDef")
        };
        let actual_instance = rustc_public::mir::mono::Instance::resolve(original, &args).unwrap();
        let actual_id = rustc_internal::internal(ctx.tcx, actual_instance.def.def_id());
        let TyKind::RigidTy(RigidTy::FnDef(actual, _)) =
            rustc_internal::stable(ctx.tcx.type_of(actual_id)).value.kind()
        else {
            panic!("resolved native implementation must have an actual FnDef")
        };
        assert_eq!(rustc_internal::internal(ctx.tcx, actual.def_id()), actual_id);
        let foreign = find_instance_by_suffix(ctx.tcx, "foreign_trait_len").callee_body().unwrap();
        let TyKind::RigidTy(RigidTy::FnDef(original, args)) =
            call(&foreign).0.ty(foreign.locals()).unwrap().kind()
        else {
            panic!("actual replacement FnDef")
        };
        let replacement_instance =
            rustc_public::mir::mono::Instance::resolve(original, &args).unwrap();
        let replacement_id = rustc_internal::internal(ctx.tcx, replacement_instance.def.def_id());
        let TyKind::RigidTy(RigidTy::FnDef(replacement, _)) =
            rustc_internal::stable(ctx.tcx.type_of(replacement_id)).value.kind()
        else {
            panic!("resolved foreign implementation must have an actual FnDef")
        };
        assert_eq!(rustc_internal::internal(ctx.tcx, replacement.def_id()), replacement_id);
        {
            let _scope = crate::kani_middle::transform::UnitStubsTestScope::install(HashMap::from(
                [(actual, replacement)],
            ));
            for name in [
                "standard_new",
                "standard_default",
                "standard_len",
                "standard_is_empty",
                "standard_as_str",
                "standard_deref",
                "standard_deref_mut",
            ] {
                classification(&mut ctx, name, None);
            }
        }
        classification(&mut ctx, "standard_len", Some(StubKind::StringLen));
        assert!(!crate::kani_middle::transform::unit_has_stubs());
        let mut transformer =
            crate::kani_middle::transform::BodyTransformation::new_for_tests_with_stubs(
                HashMap::from([(actual, replacement)]),
            );
        let mut bmc_ctx = AYCtx::new(
            ctx.tcx,
            crate::kani_queries::QueryDb::default(),
            crate::codegen_ay::context::AYConfig { use_chc: false, ..Default::default() },
            &mut transformer,
        );
        assert!(bmc_ctx.unit_has_stubs());
        let mut calls = 0;
        for name in [
            "standard_new",
            "standard_default",
            "standard_len",
            "standard_is_empty",
            "standard_as_str",
            "standard_deref",
            "standard_deref_mut",
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.callee_body().unwrap();
            bmc_ctx.set_current_fn(instance);
            let bmc = StatementCodegen::new(&mut bmc_ctx, &body, TupleUsageAnalysis::run(&body));
            assert!(bmc.test_stdlib_registry_candidate(call(&body).0).is_none());
            calls += 1;
        }
        assert_eq!(calls, 7);
        assert!(is_string_stub(StubKind::StringNew));
    });
}

#[test]
fn actual_string_alias_models_are_boundaries_and_foreign_bodies_inline() {
    use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
    context(|ctx| {
        let mut native = 0;
        for prefix in ["standard", "alias", "reexport"] {
            for method in ["new", "default", "len", "is_empty", "as_str", "deref", "deref_mut"] {
                let name = format!("{prefix}_{method}");
                let instance = find_instance_by_suffix(ctx.tcx, &name);
                let body = instance.callee_body().unwrap();
                let (func, _, _, _) = call(&body);
                assert!(crate::codegen_ay::native_string_call_boundary(
                    ctx.tcx,
                    func,
                    body.locals()
                ));
                let mut requested = 0;
                let (_, kept) = FunctionInlinePass::new(InlineConfig::default())
                    .transform_with_body_provider(ctx.tcx, body, instance, |callee| {
                        requested += 1;
                        callee.callee_body()
                    });
                assert_eq!(requested, 0, "actual native boundary {name}");
                assert!(crate::codegen_ay::native_string_call_boundary(
                    ctx.tcx,
                    call(&kept).0,
                    kept.locals()
                ));
                // Actual attached BMC map state prevents model preservation,
                // even when the CHC replacement TLS is absent.
                assert!(!crate::kani_middle::transform::unit_has_stubs());
                if method == "default" {
                    let mut requested = 0;
                    FunctionInlinePass::new(InlineConfig::default())
                        .with_unit_stubs(true)
                        .transform_with_body_provider(ctx.tcx, kept, instance, |_callee| {
                            requested += 1;
                            None
                        });
                    assert_eq!(requested, 1, "actual map veto {name}");
                }
                native += 1;
            }
        }
        assert_eq!(native, 21);
        let mut foreign = 0;
        for name in ["foreign_new", "foreign_len", "foreign_is_empty"] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.callee_body().unwrap();
            assert!(!crate::codegen_ay::native_string_call_boundary(
                ctx.tcx,
                call(&body).0,
                body.locals()
            ));
            let mut requested = 0;
            let (changed, _) = FunctionInlinePass::new(InlineConfig::default())
                .transform_with_body_provider(ctx.tcx, body, instance, |callee| {
                    requested += 1;
                    callee.callee_body()
                });
            assert!(changed && requested > 0, "actual foreign body must inline {name}");
            foreign += 1;
        }
        assert_eq!(foreign, 3);
    });
}
