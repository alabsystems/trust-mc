// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use crate::codegen_ay::types::ptr_sort;
use rustc_public::CrateDef;
use rustc_public::CrateItem;
use rustc_public::mir::mono::Instance;
use rustc_public::rustc_internal;
use rustc_public::ty::{
    FnSig, GenericArgKind, GenericArgs, RigidTy, Ty, TyConst, TyConstKind, UintTy,
};
use std::sync::Arc;
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};

fn fn_sig_by_suffix(tcx: TyCtxt<'_>, suffix: &str) -> FnSig {
    let item = find_crate_item_by_suffix(tcx, suffix);
    let def_id = rustc_internal::internal(tcx, item.def_id());
    let fn_ty = rustc_internal::stable(tcx.type_of(def_id)).value;
    fn_ty.kind().fn_sig().expect("expected function signature").skip_binder()
}

fn find_crate_item_by_suffix(tcx: TyCtxt<'_>, suffix: &str) -> CrateItem {
    let matches: Vec<_> = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| {
            let def_id = rustc_internal::internal(tcx, item.def_id());
            let path = tcx.def_path_str(def_id);
            path == suffix || path.ends_with(&format!("::{suffix}"))
        })
        .collect();
    match matches.as_slice() {
        [] => panic!("missing item with suffix '{suffix}'"),
        [single] => *single,
        many => {
            let names: Vec<_> = many
                .iter()
                .map(|item| {
                    let def_id = rustc_internal::internal(tcx, item.def_id());
                    tcx.def_path_str(def_id)
                })
                .collect();
            panic!("ambiguous suffix '{suffix}': {} matches: {names:?}", many.len());
        }
    }
}

fn resolve_single_type_generic_instance_by_suffix(
    tcx: TyCtxt<'_>,
    suffix: &str,
    concrete_ty: Ty,
) -> Instance {
    let item = find_crate_item_by_suffix(tcx, suffix);
    let def_id = rustc_internal::internal(tcx, item.def_id());
    let fn_ty = rustc_internal::stable(tcx.type_of(def_id)).value;
    let rustc_public::ty::TyKind::RigidTy(RigidTy::FnDef(fn_def, _)) = fn_ty.kind() else {
        panic!("item '{suffix}' is not a function: {fn_ty:?}");
    };
    Instance::resolve(fn_def, &GenericArgs(vec![GenericArgKind::Type(concrete_ty)]))
        .expect("single-type generic instance should resolve")
}

fn resolve_single_const_generic_instance_by_suffix(
    tcx: TyCtxt<'_>,
    suffix: &str,
    concrete_len: u64,
) -> Instance {
    let item = find_crate_item_by_suffix(tcx, suffix);
    let def_id = rustc_internal::internal(tcx, item.def_id());
    let fn_ty = rustc_internal::stable(tcx.type_of(def_id)).value;
    let rustc_public::ty::TyKind::RigidTy(RigidTy::FnDef(fn_def, _)) = fn_ty.kind() else {
        panic!("item '{suffix}' is not a function: {fn_ty:?}");
    };
    Instance::resolve(
        fn_def,
        &GenericArgs(vec![GenericArgKind::Const(
            TyConst::try_from_target_usize(concrete_len)
                .expect("const generic length should fit in target usize"),
        )]),
    )
    .expect("single-const generic instance should resolve")
}

#[test]
fn test_push_late_state_var_pair_patches_existing_block_rules() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_late_pair(x: u32) -> u32 {
            if x > 0 { x + 1 } else { x }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_late_pair");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_late_pair", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let from_rel = Arc::clone(chc_ctx.block_relations.get(&0).expect("bb0 relation"));
        let to_rel = Arc::clone(chc_ctx.block_relations.get(&1).expect("bb1 relation"));
        let from_decl = chc_ctx
            .vc
            .relations
            .iter()
            .find(|rel| rel.name.as_str() == from_rel.as_ref())
            .expect("bb0 decl")
            .clone();
        let to_decl = chc_ctx
            .vc
            .relations
            .iter()
            .find(|rel| rel.name.as_str() == to_rel.as_ref())
            .expect("bb1 decl")
            .clone();
        let body_args: Vec<_> = from_decl
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(idx, sort)| Expr::var(format!("from_arg_{idx}"), sort.clone()))
            .collect();
        let head_args: Vec<_> = to_decl
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(idx, sort)| Expr::var(format!("head_arg_{idx}"), sort.clone()))
            .collect();
        chc_ctx.vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new(from_rel.as_ref(), body_args)),
                vec![Expr::bool_const(true)],
            ),
            RelationApp::new(to_rel.as_ref(), head_args),
        ));

        let body_arity_before =
            chc_ctx.vc.rules[0].body.relation.as_ref().expect("body relation").args.len();
        let head_arity_before = chc_ctx.vc.rules[0].head.args.len();
        let live_len_before =
            chc_ctx.state_var_mgr.live_state_indices.first().expect("live sets").len();
        let late_sort = Sort::array(ptr_sort(), Sort::bitvec(32));
        let late_expr = Expr::var("__late_region_i32", late_sort.clone());

        chc_ctx.push_late_state_var_pair(
            Arc::from("__late_region_i32"),
            "__late_region_i32__out",
            late_sort.clone(),
        );

        let body_rel = chc_ctx.vc.rules[0].body.relation.as_ref().expect("body relation");
        assert_eq!(body_rel.args.len(), body_arity_before + 1, "body arity should grow");
        assert_eq!(body_rel.args.last(), Some(&late_expr), "body should pass through late input");
        assert_eq!(
            chc_ctx.vc.rules[0].head.args.len(),
            head_arity_before + 1,
            "head arity should grow"
        );
        assert_eq!(
            chc_ctx.vc.rules[0].head.args.last(),
            Some(&late_expr),
            "head should pass through late input",
        );
        assert!(
            chc_ctx
                .state_var_mgr
                .live_state_indices
                .iter()
                .all(|live| live.len() == live_len_before + 1),
            "all live sets should include the late state var",
        );
        assert_eq!(
            chc_ctx
                .vc
                .relations
                .iter()
                .find(|rel| rel.name.as_str() == from_rel.as_ref())
                .expect("bb0 decl")
                .arg_sorts
                .last(),
            Some(&late_sort),
            "block relation decl should include late sort",
        );
        if let Some(error_rel) = chc_ctx.vc.relations.iter().find(|rel| rel.name == "error") {
            assert!(error_rel.arg_sorts.is_empty(), "error relation must remain nullary");
        }
    });
}

#[test]
fn test_push_late_collection_aux_var_patches_existing_block_rules() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_late_collection_aux(x: u32) -> u32 {
            if x > 0 { x + 1 } else { x }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_late_collection_aux");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_late_collection_aux", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let from_rel = Arc::clone(chc_ctx.block_relations.get(&0).expect("bb0 relation"));
        let to_rel = Arc::clone(chc_ctx.block_relations.get(&1).expect("bb1 relation"));
        let from_decl = chc_ctx
            .vc
            .relations
            .iter()
            .find(|rel| rel.name.as_str() == from_rel.as_ref())
            .expect("bb0 decl")
            .clone();
        let to_decl = chc_ctx
            .vc
            .relations
            .iter()
            .find(|rel| rel.name.as_str() == to_rel.as_ref())
            .expect("bb1 decl")
            .clone();
        let body_args: Vec<_> = from_decl
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(idx, sort)| Expr::var(format!("from_aux_arg_{idx}"), sort.clone()))
            .collect();
        let head_args: Vec<_> = to_decl
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(idx, sort)| Expr::var(format!("head_aux_arg_{idx}"), sort.clone()))
            .collect();
        chc_ctx.vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new(from_rel.as_ref(), body_args)),
                vec![Expr::bool_const(true)],
            ),
            RelationApp::new(to_rel.as_ref(), head_args),
        ));

        let body_arity_before =
            chc_ctx.vc.rules[0].body.relation.as_ref().expect("body relation").args.len();
        let live_len_before =
            chc_ctx.state_var_mgr.live_state_indices.first().expect("live sets").len();
        let late_sort = ptr_sort();
        let late_expr = Expr::var("__late_len", late_sort.clone());

        chc_ctx.push_late_collection_aux_var(
            Arc::from("__late_len"),
            "__late_len__out",
            late_sort.clone(),
        );

        let body_rel = chc_ctx.vc.rules[0].body.relation.as_ref().expect("body relation");
        assert_eq!(body_rel.args.len(), body_arity_before + 1, "body arity should grow");
        assert_eq!(body_rel.args.last(), Some(&late_expr), "body should pass through late input");
        assert_eq!(
            chc_ctx.vc.rules[0].head.args.last(),
            Some(&late_expr),
            "head should pass through late input",
        );
        assert!(
            chc_ctx
                .state_var_mgr
                .live_state_indices
                .iter()
                .all(|live| live.len() == live_len_before + 1),
            "all live sets should include the late collection aux var",
        );
        assert_eq!(
            chc_ctx
                .vc
                .relations
                .iter()
                .find(|rel| rel.name.as_str() == to_rel.as_ref())
                .expect("bb1 decl")
                .arg_sorts
                .last(),
            Some(&late_sort),
            "block relation decl should include late collection aux sort",
        );
        if let Some(error_rel) = chc_ctx.vc.relations.iter().find(|rel| rel.name == "error") {
            assert!(error_rel.arg_sorts.is_empty(), "error relation must remain nullary");
        }
    });
}

#[test]
fn test_refresh_block_relation_app_pads_late_state_var_via_reverse_map() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn probe_refresh_late_app(x: u32) -> u32 {
            if x > 0 { x + 1 } else { x }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_refresh_late_app");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_refresh_late_app", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let from_rel = Arc::clone(chc_ctx.block_relations.get(&0).expect("bb0 relation"));
        assert_eq!(
            chc_ctx.rel_name_to_bb.get(from_rel.as_ref()),
            Some(&0),
            "declare_block_relations should populate the reverse relation-name map",
        );

        let live_len_before =
            chc_ctx.state_var_mgr.live_state_indices.first().expect("live set for bb0").len();
        let stale_args: Vec<_> = chc_ctx.state_var_mgr.live_state_indices[0]
            .iter()
            .map(|&idx| {
                let (name, sort) = &chc_ctx.state_var_mgr.state_vars[idx];
                Expr::var(&**name, sort.clone())
            })
            .collect();
        assert_eq!(stale_args.len(), live_len_before, "stale app should match original arity");
        let stale_app = RelationApp::new(from_rel.as_ref(), stale_args);

        let late_sort = Sort::array(ptr_sort(), Sort::bitvec(32));
        chc_ctx.push_late_state_var_pair(
            Arc::from("__late_refresh_region"),
            "__late_refresh_region__out",
            late_sort.clone(),
        );

        let refreshed = chc_ctx.refresh_block_relation_app(&stale_app);
        let expected = Expr::var("__late_refresh_region", late_sort);
        assert_eq!(refreshed.name.as_str(), from_rel.as_ref(), "relation name should be preserved",);
        assert_eq!(
            refreshed.args.len(),
            live_len_before + 1,
            "refresh should append the missing late state var",
        );
        assert_eq!(
            refreshed.args.last(),
            Some(&expected),
            "refresh should append the concrete late input var rather than scanning for a block",
        );
    });
}

#[test]
fn test_resolve_body_ty_substitutes_const_generic_array_len() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn const_array_caller<const N: usize>(x: [u8; N]) -> [u8; N] {
            let y: [u8; N] = x;
            y
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance =
            resolve_single_const_generic_instance_by_suffix(ctx.tcx, "const_array_caller", 4);
        let body = instance.body().expect("resolved generic function body");
        let raw_input_ty = fn_sig_by_suffix(ctx.tcx, "const_array_caller").inputs()[0];
        let rustc_public::ty::TyKind::RigidTy(RigidTy::Array(_, raw_len)) = raw_input_ty.kind()
        else {
            panic!("expected raw input type to be an array, got {:?}", raw_input_ty.kind());
        };
        assert!(
            matches!(raw_len.kind(), TyConstKind::Param(_)),
            "generic signature should expose unresolved const parameter, got {:?}",
            raw_len.kind()
        );

        let chc_ctx = ChcCtx::new_with_instance(
            ctx.tcx,
            &body,
            instance,
            "const_array_caller",
            ChcConfig::default(),
        );
        let resolved_input_ty = chc_ctx.resolve_body_ty(raw_input_ty);
        let rustc_public::ty::TyKind::RigidTy(RigidTy::Array(elem_ty, resolved_len)) =
            resolved_input_ty.kind()
        else {
            panic!(
                "expected resolved input type to be an array, got {:?}",
                resolved_input_ty.kind()
            );
        };

        assert!(
            matches!(elem_ty.kind(), rustc_public::ty::TyKind::RigidTy(RigidTy::Uint(UintTy::U8))),
            "resolved array element type should stay u8, got {:?}",
            elem_ty.kind()
        );
        match resolved_len.kind() {
            TyConstKind::Value(_, alloc) => {
                assert_eq!(
                    alloc.read_uint().ok(),
                    Some(4),
                    "const generic array length should resolve to the concrete instance arg"
                );
            }
            other => panic!("expected concrete array length after resolution, got {other:?}"),
        }
    });
}

#[test]
fn test_resolve_body_ty_substitutes_fn_def_generic_args() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_u16_anchor(v: u16) -> u16 { v }

        pub fn generic_identity<T>(x: T) -> T { x }

        pub fn generic_caller<T: Copy>(x: T) -> T {
            let f = generic_identity::<T>;
            f(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let concrete_ty = fn_sig_by_suffix(ctx.tcx, "probe_u16_anchor").inputs()[0];
        let instance =
            resolve_single_type_generic_instance_by_suffix(ctx.tcx, "generic_caller", concrete_ty);
        let body = instance.body().expect("resolved generic function body");
        let item = find_crate_item_by_suffix(ctx.tcx, "generic_identity");
        let def_id = rustc_internal::internal(ctx.tcx, item.def_id());
        let raw_fn_item_ty = rustc_internal::stable(ctx.tcx.type_of(def_id)).value;
        let rustc_public::ty::TyKind::RigidTy(RigidTy::FnDef(_, raw_args)) = raw_fn_item_ty.kind()
        else {
            panic!(
                "expected generic identity item to have FnDef type, got {:?}",
                raw_fn_item_ty.kind()
            );
        };
        assert!(
            matches!(raw_args.0.first(), Some(GenericArgKind::Type(arg_ty)) if matches!(arg_ty.kind(), rustc_public::ty::TyKind::Param(_))),
            "raw FnDef args should retain the generic parameter before body resolution, got {:?}",
            raw_args
        );

        let chc_ctx = ChcCtx::new_with_instance(
            ctx.tcx,
            &body,
            instance,
            "generic_caller",
            ChcConfig::default(),
        );
        let resolved_fn_item_ty = chc_ctx.resolve_body_ty(raw_fn_item_ty);
        let rustc_public::ty::TyKind::RigidTy(RigidTy::FnDef(_, resolved_args)) =
            resolved_fn_item_ty.kind()
        else {
            panic!("expected resolved FnDef type, got {:?}", resolved_fn_item_ty.kind());
        };
        assert!(
            matches!(resolved_args.0.first(), Some(GenericArgKind::Type(arg_ty)) if *arg_ty == concrete_ty),
            "resolved FnDef args should substitute the concrete instance type, got {:?}",
            resolved_args
        );
    });
}
