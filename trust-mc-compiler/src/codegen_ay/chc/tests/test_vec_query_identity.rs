// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Definition classification, with a real external dependency and actual MIR
//! call operands. These controls do not claim semantic Safe/Bug acceptance.
#![cfg(trust_toolchain)]

use super::common::*;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::context::AYCtx;
use crate::codegen_ay::shared::vec_query_identity::vec_query_stub_is_authorized;
use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::stubs::StubRegistry;
use crate::kani_middle::std_abstraction::{
    is_sysroot_alloc_definition, is_sysroot_alloc_definition_at, is_sysroot_core_definition_at,
};
use crate::kani_middle::tuple_usage::TupleUsageAnalysis;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{Body, TerminatorKind};
use std::collections::HashMap;

const DEPENDENCY: &str = include_str!("fixtures/external_vec_query_dependency.rs");
const SOURCE: &str = include_str!("fixtures/external_vec_query_caller.rs");
const QUERY_KINDS: [StubKind; 6] = [
    StubKind::VecLen,
    StubKind::VecCapacity,
    StubKind::VecIsEmpty,
    StubKind::VecAsPtr,
    StubKind::VecAsMutPtr,
    StubKind::VecAsSlice,
];
const METHODS: [(&str, StubKind); 9] = [
    ("len", StubKind::VecLen),
    ("capacity", StubKind::VecCapacity),
    ("is_empty", StubKind::VecIsEmpty),
    ("as_ptr", StubKind::VecAsPtr),
    ("as_mut_ptr", StubKind::VecAsMutPtr),
    ("as_slice", StubKind::VecAsSlice),
    ("as_mut_slice", StubKind::VecAsSlice),
    ("deref", StubKind::VecAsSlice),
    ("deref_mut", StubKind::VecAsSlice),
];

/// Reuse the project's linked-compiler external-crate pattern from
/// kani_middle/unstable_type_test.rs. No tool is spawned by a PATH name.
fn with_external_vec_query_ctx<F>(callback: F)
where
    F: for<'tcx> FnOnce(AYCtx<'tcx, 'static>) + Send,
{
    with_external_definition_ctx(DEPENDENCY, SOURCE, callback);
}

fn with_external_definition_ctx<F>(dependency_source: &str, caller_source: &str, callback: F)
where
    F: for<'tcx> FnOnce(AYCtx<'tcx, 'static>) + Send,
{
    crate::codegen_ay::context::with_test_ay_ctx_for_external_source(
        dependency_source,
        caller_source,
        &[],
        callback,
    );
}

#[test]
fn actual_external_rawvec_and_foreign_trait_ptr_have_no_native_authority() {
    with_external_definition_ctx(
        include_str!("fixtures/external_rawvec_field_dependency.rs"),
        include_str!("fixtures/external_rawvec_field_caller.rs"),
        |mut ctx| {
            let mut direct = 0;
            let mut indirect = 0;
            for name in ["external_rawvec_ptr", "external_trait_ptr", "indirect_ptr"] {
                let instance = find_instance_by_suffix(ctx.tcx, name);
                let body = instance.callee_body().expect("actual external caller MIR");
                let func = only_call(&body);
                if let TyKind::RigidTy(RigidTy::FnDef(def, _)) =
                    func.ty(body.locals()).unwrap().kind()
                {
                    assert!(
                        !rustc_internal::internal(ctx.tcx, def.def_id()).is_local(),
                        "actual external FnDef required"
                    );
                    direct += 1;
                } else {
                    assert_eq!(name, "indirect_ptr");
                    indirect += 1;
                }
                ctx.set_current_fn(instance);
                let codegen =
                    StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
                assert!(!codegen.test_native_rawvec_ptr_call(func), "{name}");
            }
            assert_eq!((direct, indirect), (2, 1));
            let instance = find_instance_by_suffix(ctx.tcx, "external_rawvec_field");
            let body = instance.callee_body().unwrap();
            ctx.set_current_fn(instance);
            let mut codegen =
                StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let mut fields = 0;
            for block in &body.blocks {
                for statement in &block.statements {
                    if let rustc_public::mir::StatementKind::Assign(
                        _,
                        rustc_public::mir::Rvalue::Ref(_, _, place),
                    ) = &statement.kind
                    {
                        assert!(codegen.test_native_vec_field_place(place).is_none());
                        fields += 1;
                    }
                }
            }
            assert!(fields > 0, "actual external field reference required");
        },
    );
}

fn only_call(body: &Body) -> &Operand {
    let calls: Vec<_> = body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator.kind {
            TerminatorKind::Call { func, .. } => Some(func),
            _ => None,
        })
        .collect();
    assert_eq!(calls.len(), 1, "probe must retain exactly one actual call: {body:#?}");
    calls[0]
}

fn resolved_call(body: &Body) -> (rustc_public::ty::FnDef, Instance) {
    let TyKind::RigidTy(RigidTy::FnDef(original, args)) =
        only_call(body).ty(body.locals()).expect("actual call type").kind()
    else {
        panic!("probe must carry an actual FnDef")
    };
    (original, Instance::resolve(original, &args).expect("resolved external call"))
}

/// Both real production candidate decisions must agree. BMC's test access calls
/// the same method used by its dispatcher, before unrelated family checks.
fn assert_classification(
    ctx: &mut AYCtx<'_, '_>,
    body: &Body,
    name: &str,
    expected: Option<StubKind>,
) {
    let func = only_call(body);
    let mut chc = ChcCtx::new(ctx.tcx, body, name, ChcConfig::default());
    assert_eq!(chc.detect_stub(func), expected, "CHC {name}");
    assert_eq!(
        chc.detect_stub_with_locals(func, body.locals()),
        expected,
        "CHC explicit locals {name}"
    );
    // Exercise the separate nested pure-query entry point with a value of
    // the actual receiver ADT. In particular the foreign trait impl has a
    // genuine Vec value, so a receiver-shape veto cannot satisfy this check.
    if let TyKind::RigidTy(RigidTy::FnDef(def, generics)) = func.ty(body.locals()).unwrap().kind()
        && let Ok(instance) = Instance::resolve(def, &generics)
        && !matches!(instance.kind, InstanceKind::Virtual { .. })
    {
        let path = ctx.tcx.def_path_str(rustc_internal::internal(ctx.tcx, instance.def.def_id()));
        if matches!(
            StubRegistry::new().lookup(&path),
            Some(StubKind::VecLen | StubKind::VecIsEmpty)
        ) {
            let args = body
                .blocks
                .iter()
                .find_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { args, .. } => Some(args),
                    _ => None,
                })
                .unwrap();
            let TyKind::RigidTy(RigidTy::Ref(_, owner, _)) =
                args[0].ty(body.locals()).unwrap().kind()
            else {
                panic!("query receiver reference")
            };
            let sort = ChcCtx::translate_ty(owner).expect("actual receiver ADT representation");
            let receiver = Expr::var(format!("{name}_receiver"), sort);
            let result = crate::codegen_ay::chc::call::inline_known_calls::inline_known_call_expr_for_callee_path(
                &mut chc, func, &path, &[receiver], args, body.locals(),
            );
            assert_eq!(result.is_some(), expected.is_some(), "nested pure-query boundary {name}");
        }
    }
    ctx.set_current_fn(find_instance_by_suffix(ctx.tcx, name));
    let bmc = StatementCodegen::new(ctx, body, TupleUsageAnalysis::run(body));
    assert_eq!(bmc.test_stdlib_registry_candidate(func), expected, "BMC {name}");
}

#[test]
fn test_external_vec_query_identity_classifies_real_definitions_in_both_lanes() {
    with_external_vec_query_ctx(|mut ctx| {
        let mut positive_calls = 0;
        let mut negative_calls = 0;
        for prefix in ["standard", "alias", "reexport"] {
            for (method, expected) in METHODS {
                let name = format!("{prefix}_{method}");
                let body = find_instance_by_suffix(ctx.tcx, &name).callee_body().unwrap();
                let (_, actual) = resolved_call(&body);
                let actual_id = rustc_internal::internal(ctx.tcx, actual.def.def_id());
                assert!(is_sysroot_alloc_definition(ctx.tcx, actual_id), "{name}");
                assert!(!actual_id.is_local(), "{name}");
                let path = ctx.tcx.def_path_str(actual_id);
                assert_eq!(StubRegistry::new().lookup(&path), Some(expected), "{name}: {path}");
                for candidate in QUERY_KINDS {
                    assert_eq!(
                        vec_query_stub_is_authorized(
                            ctx.tcx,
                            only_call(&body),
                            body.locals(),
                            candidate
                        ),
                        candidate == expected,
                        "exact category {name}: {candidate:?}"
                    );
                }
                assert_classification(&mut ctx, &body, &name, Some(expected));
                positive_calls += 1;
            }
        }
        assert_eq!(positive_calls, 27, "all aliases/reexports and nine actual query forms");

        for (method, expected) in METHODS.into_iter().take(6) {
            let name = format!("external_{method}");
            let body = find_instance_by_suffix(ctx.tcx, &name).callee_body().unwrap();
            let (_, actual) = resolved_call(&body);
            let actual_id = rustc_internal::internal(ctx.tcx, actual.def.def_id());
            assert!(!actual_id.is_local(), "dependency must have a real external CrateNum");
            assert!(!is_sysroot_alloc_definition(ctx.tcx, actual_id));
            assert!(!crate::codegen_ay::shared::callee_is_local_item(
                only_call(&body),
                body.locals()
            ));
            let path = ctx.tcx.def_path_str(actual_id);
            assert_eq!(
                StubRegistry::new().lookup(&path),
                Some(expected),
                "exercise the old candidate route: {path}"
            );
            assert!(!vec_query_stub_is_authorized(
                ctx.tcx,
                only_call(&body),
                body.locals(),
                expected
            ));
            assert_classification(&mut ctx, &body, &name, None);
            negative_calls += 1;
        }
        let foreign = find_instance_by_suffix(ctx.tcx, "foreign_trait_len").callee_body().unwrap();
        let (_, foreign_instance) = resolved_call(&foreign);
        let foreign_id = rustc_internal::internal(ctx.tcx, foreign_instance.def.def_id());
        let TyKind::RigidTy(RigidTy::FnDef(foreign_replacement, _)) =
            rustc_internal::stable(ctx.tcx.type_of(foreign_id)).value.kind()
        else {
            panic!("resolved foreign implementation must have an actual FnDef")
        };
        assert_eq!(rustc_internal::internal(ctx.tcx, foreign_replacement.def_id()), foreign_id);
        assert!(!foreign_id.is_local());
        assert!(!is_sysroot_alloc_definition(ctx.tcx, foreign_id));
        assert!(!crate::codegen_ay::shared::callee_is_local_item(
            only_call(&foreign),
            foreign.locals()
        ));
        let signature = foreign_instance.ty().kind().fn_sig().unwrap().skip_binder();
        let TyKind::RigidTy(RigidTy::Ref(_, owner, _)) = signature.inputs()[0].kind() else {
            panic!("foreign trait method receiver")
        };
        let TyKind::RigidTy(RigidTy::Adt(owner, _)) = owner.kind() else {
            panic!("foreign trait method must operate on an actual Vec owner")
        };
        assert!(is_sysroot_alloc_definition_at(
            ctx.tcx,
            rustc_internal::internal(ctx.tcx, owner.def_id()),
            &["vec", "Vec"]
        ));
        let path = ctx.tcx.def_path_str(foreign_id);
        assert_eq!(StubRegistry::new().lookup(&path), Some(StubKind::VecLen), "{path}");
        assert_classification(&mut ctx, &foreign, "foreign_trait_len", None);
        negative_calls += 1;
        assert_eq!(
            negative_calls, 7,
            "six external query categories plus foreign impl on real Vec"
        );

        // A generic adapter retains an actual core trait FnDef; the real
        // monomorphized callee body supplies concrete Vec arguments. Do not
        // manufacture a trait operand or accept a missing call as coverage.
        for (name, trait_name, method) in
            [("adapted_deref", "Deref", "deref"), ("adapted_deref_mut", "DerefMut", "deref_mut")]
        {
            let outer = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let (_, adapter) = resolved_call(&outer);
            let body = adapter.callee_body().expect("actual monomorphized generic adapter");
            let (original, actual) = resolved_call(&body);
            assert!(
                is_sysroot_core_definition_at(
                    ctx.tcx,
                    rustc_internal::internal(ctx.tcx, original.def_id()),
                    &["ops", "deref", trait_name, method]
                ),
                "adapter must retain the actual core trait definition"
            );
            assert!(is_sysroot_alloc_definition(
                ctx.tcx,
                rustc_internal::internal(ctx.tcx, actual.def.def_id())
            ));
            assert_classification(&mut ctx, &body, name, Some(StubKind::VecAsSlice));
        }

        let native_len = find_instance_by_suffix(ctx.tcx, "standard_len").callee_body().unwrap();
        let (native_len_def, _) = resolved_call(&native_len);
        {
            // This scope exercises CHC TLS. Its BMC checks also exercise the
            // shared predicate's defensive TLS refusal; the actual production
            // BMC transformer-map control below deliberately has no TLS scope.
            // Both methods have (&Vec<u64>) -> usize signatures. This is a
            // real replacement map, rather than a fabricated function token.
            let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(HashMap::from(
                [(native_len_def, foreign_replacement)],
            ));
            for (method, _) in METHODS.into_iter().take(6) {
                let name = format!("standard_{method}");
                // Read the original caller instance while the scope is active;
                // these call operands are genuine compiler MIR, not rewritten
                // to conceal which query permission is being checked.
                let body = find_instance_by_suffix(ctx.tcx, &name).body().unwrap();
                for candidate in QUERY_KINDS {
                    assert!(!vec_query_stub_is_authorized(
                        ctx.tcx,
                        only_call(&body),
                        body.locals(),
                        candidate
                    ));
                }
                assert_classification(&mut ctx, &body, &name, None);
            }
        }
        assert_classification(&mut ctx, &native_len, "standard_len", Some(StubKind::VecLen));

        // Production BMC carries replacements on AYCtx's transformer, without
        // installing the CHC walker TLS. One actual replacement must refuse all
        // six query categories, including calls not themselves in that map.
        assert!(!crate::kani_middle::transform::unit_has_stubs());
        for has_replacement in [false, true] {
            let map = if has_replacement {
                HashMap::from([(native_len_def, foreign_replacement)])
            } else {
                HashMap::new()
            };
            let mut transformer =
                crate::kani_middle::transform::BodyTransformation::new_for_tests_with_stubs(
                    map.clone(),
                );
            let mut bmc_ctx = AYCtx::new(
                ctx.tcx,
                crate::kani_queries::QueryDb::default(),
                crate::codegen_ay::context::AYConfig { use_chc: false, ..Default::default() },
                &mut transformer,
            );
            assert_eq!(bmc_ctx.unit_stub_map(), map, "actual attached transformer map");
            assert_eq!(bmc_ctx.unit_has_stubs(), has_replacement);
            let mut actual_calls = 0;
            for (method, category) in METHODS.into_iter().take(6) {
                let name = format!("standard_{method}");
                let instance = find_instance_by_suffix(ctx.tcx, &name);
                let body = instance.body().expect("actual compiler caller MIR");
                let func = only_call(&body);
                assert!(!crate::kani_middle::transform::unit_has_stubs(), "no CHC TLS");
                assert!(
                    vec_query_stub_is_authorized(ctx.tcx, func, body.locals(), category),
                    "canonical call remains authorized by the TLS-only predicate"
                );
                bmc_ctx.set_current_fn(instance);
                let bmc =
                    StatementCodegen::new(&mut bmc_ctx, &body, TupleUsageAnalysis::run(&body));
                assert_eq!(
                    bmc.test_stdlib_registry_candidate(func),
                    (!has_replacement).then_some(category),
                    "BMC actual unit map: {name}, replacement={has_replacement}"
                );
                actual_calls += 1;
            }
            assert_eq!(actual_calls, 6, "all actual query calls in each BMC map state");
            assert!(!crate::kani_middle::transform::unit_has_stubs());
        }

        let virtual_body = find_instance_by_suffix(ctx.tcx, "virtual_len").callee_body().unwrap();
        let (_, virtual_instance) = resolved_call(&virtual_body);
        assert!(matches!(virtual_instance.kind, InstanceKind::Virtual { .. }));
        for candidate in QUERY_KINDS {
            assert!(!vec_query_stub_is_authorized(
                ctx.tcx,
                only_call(&virtual_body),
                virtual_body.locals(),
                candidate
            ));
        }
        assert_classification(&mut ctx, &virtual_body, "virtual_len", None);

        let indirect = find_instance_by_suffix(ctx.tcx, "indirect_len").callee_body().unwrap();
        assert!(!matches!(
            only_call(&indirect).ty(indirect.locals()).unwrap().kind(),
            TyKind::RigidTy(RigidTy::FnDef(..))
        ));
        for candidate in QUERY_KINDS {
            assert!(!vec_query_stub_is_authorized(
                ctx.tcx,
                only_call(&indirect),
                indirect.locals(),
                candidate
            ));
        }
        assert_classification(&mut ctx, &indirect, "indirect_len", None);

        let generic = find_crate_item_by_suffix(ctx.tcx, "unresolved_len");
        let generic_id = rustc_internal::internal(ctx.tcx, generic.def_id());
        let TyKind::RigidTy(RigidTy::FnDef(def, _)) =
            rustc_internal::stable(ctx.tcx.type_of(generic_id)).value.kind()
        else {
            panic!("actual generic function definition")
        };
        let unresolved = def.callee_body().expect("actual generic definition body");
        let call_ty = only_call(&unresolved).ty(unresolved.locals()).unwrap();
        assert!(crate::codegen_ay::shared::mono_ty::has_unresolved_params(call_ty));
        for candidate in QUERY_KINDS {
            assert!(!vec_query_stub_is_authorized(
                ctx.tcx,
                only_call(&unresolved),
                unresolved.locals(),
                candidate
            ));
        }
        // The existing CHC/BMC path resolvers select an Instance before this
        // classification boundary. Do not send them an uninstantiated body or
        // pretend this generic definition is a concrete native call. The
        // shared predicate itself refuses it before Instance::resolve.
    });
}
