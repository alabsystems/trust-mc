// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual bundled-MIR String producers, declared header views and refusals.

use super::*;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::context::{AYCtx, with_test_ay_ctx_for_external_source};
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
use crate::kani_middle::tuple_usage::TupleUsageAnalysis;
use ay_bindings::ExprValue;
use rustc_public::mir::Body;

const DEPENDENCY: &str = r#"
pub use std::string::String as LibraryString;
pub struct String { pub vec:Vec<u8> }
impl String { pub unsafe fn as_mut_vec(&mut self)->&mut Vec<u8> { &mut self.vec } }
"#;
const SOURCE: &str = r#"
#![allow(dead_code, unused_assignments)]
extern crate external_vec_lookalike;
use external_vec_lookalike::LibraryString as Text;
pub fn empty_safe() { let value=Text::new(); assert!(value.len() == 0); }
pub fn empty_bug() { let value=Text::new(); assert!(value.len() == 1); }
pub fn deref_len_safe() { let value=Text::new(); assert!(value.as_str().len() == 0); }
pub fn deref_len_bug() { let value=Text::new(); assert!(value.as_str().len() == 1); }
pub fn from_safe() { let value=Text::from("x"); assert!(value.len() == 1); }
pub fn from_bug() { let value=Text::from("x"); assert!(value.len() == 2); }
pub fn raw_derived() { let mut a=Text::new(); let p=&raw mut a; let r=unsafe{&mut *p}; unsafe{std::ptr::drop_in_place(r)}; std::mem::forget(a); }
pub fn retargeted() { let mut a=Text::new(); let mut b=Text::new(); let mut r=&mut a; r=&mut b; unsafe{std::ptr::drop_in_place(r)}; std::mem::forget(a); std::mem::forget(b); }
pub fn exposed() { let mut a=Text::new(); let mut b=Text::new(); let mut r=&mut a; let slot=&raw mut r; unsafe{*slot=&mut b; std::ptr::drop_in_place(r)}; std::mem::forget(a); std::mem::forget(b); }
pub fn mutable_direct_bug() { let mut value=Text::new(); unsafe{value.as_mut_vec().push(b'x')}; assert!(value.len() == 0); }
pub fn mutable_fnptr_bug() { let mut value=Text::new(); let f:unsafe fn(&mut Text)->&mut Vec<u8>=Text::as_mut_vec; unsafe{f(&mut value).push(b'x')}; assert!(value.len() == 0); }
pub fn reserve_refusal() { let mut value=Text::new(); value.reserve(1); assert!(value.len() == 0); }
pub fn pop_refusal() { let mut value=Text::new(); let _=value.pop(); assert!(value.len() == 0); }
pub fn pointer_null_bug() { let value=Text::new(); assert!(value.as_ptr().is_null()); }
pub fn pointer_nonnull_safe() { let value=Text::new(); assert!(!value.as_ptr().is_null()); }
pub fn pointer_converted_null_bug() { let value=Text::new(); assert!(value.as_str().as_bytes().as_ptr().is_null()); }
pub fn pointer_default_nonnull_safe() { let value=Text::default(); assert!(!value.as_ptr().is_null()); }
pub fn pointer_before_forget_bug() { let value=Text::new(); let is_null=value.as_ptr().is_null(); std::mem::forget(value); assert!(is_null,"NATIVE_EMPTY_STRING_POINTER_NULL_BUG_EXPECT_FALSE"); }
pub fn pointer_before_forget_safe() { let value=Text::new(); let is_null=value.as_ptr().is_null(); std::mem::forget(value); assert!(!is_null,"NATIVE_EMPTY_STRING_POINTER_NONNULL_SAFE_EXPECT_TRUE"); }
pub fn pointer_escape() -> *const u8 { let value=Text::new(); value.as_ptr() }
pub fn pointer_load_bug() { let value=Text::new(); let byte=unsafe{*value.as_ptr()}; assert!(byte == 0); }
pub fn pointer_after_move_bug() { let value=Text::new(); let pointer=value.as_ptr(); std::mem::drop(value); assert!(pointer.is_null()); }
pub fn pointer_after_mutation_bug() { let mut value=Text::new(); value.push('x'); assert!(value.as_ptr().is_null()); }
pub fn pointer_address_arithmetic_bug() { let value=Text::new(); let address=value.as_ptr().addr().wrapping_add(1); assert!(address == 0); }
pub fn pointer_from_bug() { let value=Text::from("x"); assert!(value.as_ptr().is_null()); }
pub fn pointer_parameter_bug(value:Text) { assert!(value.as_ptr().is_null()); }
pub fn pointer_index_bug(bytes:[u8;4]) { let value=Text::new(); let address=value.as_ptr().addr(); let is_null=address==0; let byte=bytes[0]; assert!(is_null,"EMPTY_STRING_POINTER_ADDRESS_INDEX_REFUSAL"); assert!(byte==0); }
pub fn raw_header_address_bug() { let value=Text::new(); let address=&raw const value; assert!(address.is_null()); std::mem::forget(value); }
pub fn header_cast_bug() { let value=Text::new(); let address=&value as *const Text as *const u8; assert!(address.is_null()); std::mem::forget(value); }
pub fn clone_raw_header_bug() { let value=Text::from("x"); let cloned=value.clone(); let address=&raw const cloned; assert!(address.is_null()); std::mem::forget(value); std::mem::forget(cloned); }
struct Envelope { inner:Text }
pub fn wrapped_header_bug() { let value=Envelope{inner:Text::new()}; let address=&raw const value; assert!(address.is_null()); std::mem::forget(value); }
pub fn transmute_header_bug() { let value=Text::new(); let address:*const u8=unsafe{std::mem::transmute(&value)}; assert!(address.is_null()); std::mem::forget(value); }
pub fn foreign_cast(value:&external_vec_lookalike::String)->*const u8 { value as *const external_vec_lookalike::String as *const u8 }
pub fn foreign_escape(value:&mut external_vec_lookalike::String)->&mut Vec<u8> { unsafe{value.as_mut_vec()} }
"#;

fn context(callback: impl for<'tcx> FnOnce(AYCtx<'tcx, 'static>) + Send) {
    let _ = tracing_subscriber::fmt()
        .with_env_filter("trust_mc_engine::codegen_ay::context::properties=debug")
        .with_ansi(false)
        .with_test_writer()
        .try_init();
    let flags = native_header_test_flags();
    let flags: Vec<_> = flags.iter().map(String::as_str).collect();
    with_test_ay_ctx_for_external_source(DEPENDENCY, SOURCE, &flags, callback);
}

fn transformed(ctx: &AYCtx<'_, '_>, suffix: &str) -> (rustc_public::mir::mono::Instance, Body) {
    let instance = find_instance_by_suffix(ctx.tcx, suffix);
    let abstraction = StdAbstraction::resolve(ctx.tcx);
    let (_, body) = FunctionInlinePass::new(InlineConfig {
        max_depth: ctx.config.inline_depth,
        enabled: ctx.config.function_inlining,
        preserve_block_on: false,
        preserve_array_comparisons: false,
        bmc_native_box_validity: true,
        chc_native_box_drop: false,
    })
    .with_unit_stubs(ctx.unit_has_stubs())
    .transform_with_body_provider(
        ctx.tcx,
        instance.callee_body().unwrap(),
        instance,
        |callee| {
            if abstraction.abstracts_public_instance(ctx.tcx, callee) {
                None
            } else {
                callee.callee_body()
            }
        },
    );
    if let Some(directory) = std::env::var_os("MC_VEC_APPEND_ARTIFACT_DIR") {
        std::fs::write(
            std::path::Path::new(&directory).join(format!("native-string-header-{suffix}.mir")),
            format!("{body:#?}"),
        )
        .unwrap();
    }
    (instance, body)
}

#[test]
#[ignore = "requires an attested bundled TRUST_MC_NATIVE_VEC_SDK; run explicitly with --ignored"]
fn actual_string_header_views_use_normal_producers_current_owner_and_keep_debt() {
    context(|mut ctx| {
        ctx.init_memory();
        for (suffix, expected) in [
            ("empty_safe", "assertion failed: value.len() == 0"),
            ("empty_bug", "assertion failed: value.len() == 1"),
            ("deref_len_safe", "assertion failed: value.as_str().len() == 0"),
            ("deref_len_bug", "assertion failed: value.as_str().len() == 1"),
            ("from_safe", "assertion failed: value.len() == 1"),
            ("from_bug", "assertion failed: value.len() == 2"),
        ] {
            let (instance, body) = transformed(&ctx, suffix);
            ctx.set_current_fn(instance);
            let name = ctx.current_fn_name().to_owned();
            let unsupported = ctx.unsupported_construct_total();
            let vec_fallback =
                crate::codegen_ay::statement::collections::get_vec_field_fallback_count();
            let (order, reachable) =
                crate::codegen_ay::codegen_function::native_test_compute_topo(&body);
            assert_eq!(order.len(), reachable);
            let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let (mut string_calls, mut vec_views, mut raw_views, mut expired) = (0, 0, 0, 0);
            let mut owners = Vec::new();
            for bb in order {
                cg.initialize_block_entry_env(bb);
                for statement in &body.blocks[bb].statements {
                    cg.codegen_statement(statement);
                    if let StatementKind::Assign(
                        _,
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place),
                    ) = &statement.kind
                        && let Some(Some(value)) = cg.native_vec_field_place(place)
                    {
                        let mut work = 4096;
                        let target =
                            if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
                                cg.native_vec_reference_target(
                                    place.local,
                                    &mut work,
                                    &mut Vec::new(),
                                )
                                .unwrap()
                            } else {
                                HeaderTarget { owner: place.local, fields: Vec::new() }
                            };
                        if !matches!(body.locals()[target.owner].ty.kind(), TyKind::RigidTy(RigidTy::Adt(def,_)) if StatementCodegen::is_native_string_adt(def))
                        {
                            continue;
                        }
                        let root = cg
                            .current_native_header_value(&HeaderTarget {
                                owner: target.owner,
                                fields: Vec::new(),
                            })
                            .unwrap();
                        let model = root.sort().datatype_name().unwrap().to_owned();
                        let ExprValue::DatatypeConstructor { args, .. } = value.value() else {
                            panic!("actual typed header constructor")
                        };
                        let fields =
                            if StatementCodegen::native_vec_ty(place.ty(body.locals()).unwrap())
                                .is_some()
                            {
                                vec_views += 1;
                                vec!["fld_ptr", "fld_len", "fld_cap", "fld_data"]
                            } else {
                                raw_views += 1;
                                vec!["fld_ptr", "fld_cap"]
                            };
                        assert_eq!(args.len(), fields.len());
                        for (actual, field) in args.iter().zip(fields) {
                            let sort = actual.sort().clone();
                            let expected = root.clone().field_select(&model, field, sort);
                            assert_eq!(
                                cg.deep_resolve_value(actual),
                                cg.deep_resolve_value(&expected)
                            );
                        }
                        assert_eq!(
                            value.sort(),
                            &StatementCodegen::infer_sort_from_ty(place.ty(body.locals()).unwrap())
                                .unwrap()
                        );
                        // A cached scalar is not the field's declared typed value.
                        let key = cg.ssa_base_name(place);
                        let saved = cg.current_env.clone();
                        cg.current_env.insert(key.into(), Expr::bitvec_const(99u64, 64));
                        assert_eq!(cg.native_vec_field_place(place), Some(Some(value)));
                        cg.current_env = saved;
                        owners.push(target.owner);
                    }
                    if let StatementKind::StorageDead(owner) = statement.kind {
                        if owners.contains(&owner) {
                            assert!(
                                cg.current_native_header_value(&HeaderTarget {
                                    owner,
                                    fields: Vec::new()
                                })
                                .is_none()
                            );
                            expired += 1;
                        }
                    }
                }
                let term = &body.blocks[bb].terminator;
                if let TerminatorKind::Call { func, .. } = &term.kind {
                    if crate::codegen_ay::native_string_call_boundary(
                        cg.ctx.tcx,
                        func,
                        body.locals(),
                    ) {
                        string_calls += 1;
                    }
                }
                let successors = cg.codegen_terminator_with_successors(term);
                if let TerminatorKind::Call { destination, .. } = &term.kind {
                    cg.forget_joined_ref_pointees(destination);
                }
                for (next, condition) in successors {
                    cg.record_outgoing_edge(next, condition);
                }
            }
            assert!(
                string_calls >= 2 && vec_views > 0 && raw_views > 0 && expired > 0,
                "actual normal producer/query/drop/expiry sites {suffix}"
            );
            assert!(
                cg.ctx.bmc_vc.violations.iter().any(|v| v.message.as_deref() == Some(expected)),
                "exact source assertion {suffix}"
            );
            assert_eq!(
                cg.ctx.unsupported_construct_total(),
                unsupported,
                "{suffix}: {:?}",
                cg.ctx.unsupported_constructs
            );
            assert_eq!(
                crate::codegen_ay::statement::collections::get_vec_field_fallback_count(),
                vec_fallback
            );
            drop(cg);
            let debt = crate::codegen_ay::chc::take_sound_havoc_drop_by_fn();
            let count = debt.get(&name).copied().unwrap_or(0);
            if suffix.starts_with("from_") {
                assert!(count > 0, "normal String::from allocation/data debt remains");
            } else {
                assert_eq!(
                    count, 0,
                    "empty normal producers acquire no header-read debt: {suffix}"
                );
            }
        }
    });
}

#[test]
#[ignore = "requires an attested bundled TRUST_MC_NATIVE_VEC_SDK; run explicitly with --ignored"]
fn actual_string_header_custody_refuses_raw_retarget_exposure_and_mutable_child_updates() {
    context(|mut ctx| {
        ctx.init_memory();
        for suffix in [
            "raw_derived",
            "retargeted",
            "exposed",
            "mutable_direct_bug",
            "mutable_fnptr_bug",
            "reserve_refusal",
            "pop_refusal",
            "pointer_escape",
            "pointer_load_bug",
            "pointer_after_move_bug",
            "pointer_after_mutation_bug",
            "pointer_address_arithmetic_bug",
            "pointer_from_bug",
            "pointer_parameter_bug",
            "pointer_index_bug",
            "raw_header_address_bug",
            "header_cast_bug",
            "clone_raw_header_bug",
            "wrapped_header_bug",
            "transmute_header_bug",
        ] {
            let (instance, mut body) = transformed(&ctx, suffix);
            if suffix == "pointer_index_bug" {
                // The unmodified compiled source has only null comparisons and
                // an unrelated constant array read. Replace that one actual
                // typed projection with its real address local. Keeping the
                // original constant-index bounds code prevents an unrelated
                // bounds comparison from masking the projection-use defect.
                assert!(crate::codegen_ay::statement::string_nullness::test_body_eligible(
                    ctx.tcx, &body
                ));
                let address = body
                    .blocks
                    .iter()
                    .flat_map(|b| &b.statements)
                    .find_map(|s| {
                        let StatementKind::Assign(
                            _,
                            Rvalue::BinaryOp(rustc_public::mir::BinOp::Eq, a, _),
                        ) = &s.kind
                        else {
                            return None;
                        };
                        let (Operand::Copy(p) | Operand::Move(p)) = a else { return None };
                        (p.projection.is_empty()
                            && matches!(
                                p.ty(body.locals()).ok()?.kind(),
                                TyKind::RigidTy(RigidTy::Uint(rustc_public::ty::UintTy::Usize))
                            ))
                        .then_some(p.local)
                    })
                    .expect("actual null-comparison address local");
                let locals: Vec<_> = body.locals().iter().map(|l| l.ty).collect();
                let mut changed = 0;
                for block in &mut body.blocks {
                    for s in &mut block.statements {
                        if let StatementKind::Assign(
                            _,
                            Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..),
                        ) = &mut s.kind
                            && matches!(locals[p.local].kind(), TyKind::RigidTy(RigidTy::Array(..)))
                        {
                            for projection in &mut p.projection {
                                if matches!(
                                    projection,
                                    ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                                ) {
                                    *projection = ProjectionElem::Index(address);
                                    changed += 1;
                                }
                            }
                        }
                    }
                }
                assert_eq!(changed, 1, "one actual declared array read");
                assert!(
                    !crate::codegen_ay::statement::string_nullness::test_body_eligible(
                        ctx.tcx, &body
                    ),
                    "address use in a memory projection is a hard refusal"
                );
                if let Some(directory) = std::env::var_os("MC_VEC_APPEND_ARTIFACT_DIR") {
                    std::fs::write(
                        std::path::Path::new(&directory)
                            .join("native-string-header-pointer_index_bug-projection-index.mir"),
                        format!("{body:#?}"),
                    )
                    .unwrap();
                }
            }
            ctx.set_current_fn(instance);
            let unsupported = ctx.unsupported_construct_total();
            let reason = if matches!(suffix, "raw_derived" | "retargeted" | "exposed") {
                "native_vec_field_custody"
            } else if matches!(
                suffix,
                "raw_header_address_bug"
                    | "header_cast_bug"
                    | "clone_raw_header_bug"
                    | "wrapped_header_bug"
                    | "transmute_header_bug"
            ) {
                "native_string_header_physical_custody_unqualified"
            } else if suffix.starts_with("pointer_") {
                "native_string_view_physical_custody_unqualified"
            } else {
                "native_string_unmodeled_operation"
            };
            let exact_before = ctx.unsupported_constructs.get(reason).map_or(0, Vec::len);
            let (order, reachable) =
                crate::codegen_ay::codegen_function::native_test_compute_topo(&body);
            assert_eq!(order.len(), reachable);
            let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let mut calls = 0;
            for bb in order {
                cg.initialize_block_entry_env(bb);
                if bb == 0 && suffix == "pointer_parameter_bug" {
                    // Empty-looking fields in a correctly typed live parameter are
                    // not an authenticated constructor. This is a refusal input,
                    // not source/proof authority or a fabricated successful run.
                    let ty = body.locals()[1].ty;
                    let sort = StatementCodegen::infer_sort_from_ty(ty).unwrap();
                    let zero = Expr::bitvec_const(0u64, crate::codegen_ay::types::POINTER_WIDTH);
                    let data = Expr::const_array(
                        crate::codegen_ay::types::ptr_sort(),
                        Expr::bitvec_const(0u8, 8),
                    );
                    let value = Expr::datatype_constructor(
                        crate::codegen_ay::names::RUST_STRING_SORT,
                        crate::codegen_ay::names::RUST_STRING_CONS,
                        vec![
                            Expr::bitvec_const(1u64, crate::codegen_ay::types::POINTER_WIDTH),
                            zero.clone(),
                            zero,
                            data,
                        ],
                        sort,
                    );
                    let base = cg.ssa_base_name(&Place { local: 1, projection: Vec::new() });
                    cg.env_update(base, value);
                    assert!(
                        cg.native_live_string_owner(1),
                        "live typed empty-looking parameter fixture"
                    );
                }
                for statement in &body.blocks[bb].statements {
                    cg.codegen_statement(statement);
                }
                let term = &body.blocks[bb].terminator;
                if matches!(term.kind, TerminatorKind::Call { .. }) {
                    calls += 1;
                }
                let successors = cg.codegen_terminator_with_successors(term);
                if let TerminatorKind::Call { destination, .. } = &term.kind {
                    cg.forget_joined_ref_pointees(destination);
                }
                for (next, condition) in successors {
                    cg.record_outgoing_edge(next, condition);
                }
            }
            assert!(
                calls > 0 && cg.ctx.unsupported_construct_total() > unsupported,
                "hard refusal must survive actual MIR {suffix}"
            );
            assert!(
                cg.ctx
                    .unsupported_constructs
                    .get(reason)
                    .is_some_and(|sites| sites.len() > exact_before),
                "exact refusal {suffix}"
            );
            if matches!(
                suffix,
                "pointer_load_bug"
                    | "pointer_after_move_bug"
                    | "pointer_after_mutation_bug"
                    | "pointer_address_arithmetic_bug"
                    | "pointer_from_bug"
                    | "pointer_parameter_bug"
                    | "pointer_index_bug"
            ) {
                let expected = match suffix {
                    "pointer_load_bug" => "assertion failed: byte == 0",
                    "pointer_after_move_bug" => "assertion failed: pointer.is_null()",
                    "pointer_after_mutation_bug" => "assertion failed: value.as_ptr().is_null()",
                    "pointer_from_bug" | "pointer_parameter_bug" => {
                        "assertion failed: value.as_ptr().is_null()"
                    }
                    "pointer_index_bug" => "\"EMPTY_STRING_POINTER_ADDRESS_INDEX_REFUSAL\"",
                    "pointer_address_arithmetic_bug" => "assertion failed: address == 0",
                    _ => unreachable!(),
                };
                assert!(
                    cg.ctx.bmc_vc.violations.iter().any(|v| v.message.as_deref() == Some(expected)),
                    "exact pointer source assertion retained"
                );
            }
            if matches!(
                suffix,
                "raw_header_address_bug"
                    | "header_cast_bug"
                    | "clone_raw_header_bug"
                    | "wrapped_header_bug"
                    | "transmute_header_bug"
            ) {
                assert!(
                    cg.ctx.bmc_vc.violations.iter().any(
                        |v| v.message.as_deref() == Some("assertion failed: address.is_null()")
                    ),
                    "raw header source assertion retained"
                );
            }
            if suffix.starts_with("mutable_") {
                assert!(cg.ctx.bmc_vc.violations.iter().any(|v|v.message.as_deref()==Some("assertion failed: value.len() == 0")),"source Bug assertion retained despite refusal");
            }
        }
        let foreign_cast = find_instance_by_suffix(ctx.tcx, "foreign_cast");
        let foreign_body = foreign_cast.callee_body().unwrap();
        let mut foreign_casts = 0;
        for block in &foreign_body.blocks {
            for statement in &block.statements {
                if let StatementKind::Assign(_, Rvalue::Cast(_, operand, target)) = &statement.kind
                {
                    assert!(
                        !crate::codegen_ay::shared::string_identity::type_contains_native_string(
                            ctx.tcx,
                            operand.ty(foreign_body.locals()).unwrap()
                        )
                    );
                    assert!(
                        !crate::codegen_ay::shared::string_identity::type_contains_native_string(
                            ctx.tcx, *target
                        )
                    );
                    foreign_casts += 1;
                }
            }
        }
        assert!(foreign_casts > 0, "actual foreign cast is not a native String transport");
        let instance = find_instance_by_suffix(ctx.tcx, "foreign_escape");
        let body = instance.callee_body().unwrap();
        let mut calls = 0;
        for block in &body.blocks {
            if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
                assert!(!crate::codegen_ay::native_string_unmodeled_operation(
                    ctx.tcx,
                    func,
                    body.locals(),
                    false
                ));
                calls += 1;
            }
        }
        assert_eq!(calls, 1, "actual foreign same-spelled method is not a native refusal boundary");
    });
}

#[test]
#[ignore = "requires an attested bundled TRUST_MC_NATIVE_VEC_SDK; run explicitly with --ignored"]
fn actual_empty_string_nullness_has_constructor_custody_without_physical_or_havoc_debt() {
    context(|mut ctx| {
        ctx.init_memory();
        for (suffix, expected) in [
            ("pointer_null_bug", "assertion failed: value.as_ptr().is_null()"),
            ("pointer_nonnull_safe", "assertion failed: !value.as_ptr().is_null()"),
            (
                "pointer_converted_null_bug",
                "assertion failed: value.as_str().as_bytes().as_ptr().is_null()",
            ),
            ("pointer_default_nonnull_safe", "assertion failed: !value.as_ptr().is_null()"),
            ("pointer_before_forget_bug", "\"NATIVE_EMPTY_STRING_POINTER_NULL_BUG_EXPECT_FALSE\""),
            (
                "pointer_before_forget_safe",
                "\"NATIVE_EMPTY_STRING_POINTER_NONNULL_SAFE_EXPECT_TRUE\"",
            ),
        ] {
            let (instance, body) = transformed(&ctx, suffix);
            ctx.set_current_fn(instance);
            let name = ctx.current_fn_name().to_owned();
            let unsupported = ctx.unsupported_construct_total();
            let (order, reachable) =
                crate::codegen_ay::codegen_function::native_test_compute_topo(&body);
            assert_eq!(order.len(), reachable);
            let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let mut source_views = 0;
            for bb in order {
                cg.initialize_block_entry_env(bb);
                for statement in &body.blocks[bb].statements {
                    cg.codegen_statement(statement);
                }
                let term = &body.blocks[bb].terminator;
                if let TerminatorKind::Call { func, args, destination, .. } = &term.kind
                    && crate::codegen_ay::shared::string_identity::string_stub_is_authorized(
                        cg.ctx.tcx,
                        func,
                        body.locals(),
                        crate::codegen_ay::stubs::StubKind::StringAsStr,
                    )
                {
                    assert!(
                        cg.native_empty_string_nullness_view(args, destination),
                        "actual live empty constructor path {suffix}"
                    );
                    source_views += 1;
                }
                let successors = cg.codegen_terminator_with_successors(term);
                if let TerminatorKind::Call { destination, .. } = &term.kind {
                    cg.forget_joined_ref_pointees(destination);
                }
                for (next, condition) in successors {
                    cg.record_outgoing_edge(next, condition);
                }
            }
            assert!(source_views > 0, "actual String view must execute {suffix}");
            assert_eq!(
                cg.ctx.unsupported_construct_total(),
                unsupported,
                "{suffix}: {:?}",
                cg.ctx.unsupported_constructs
            );
            assert!(
                cg.ctx.bmc_vc.violations.iter().any(|v| v.message.as_deref() == Some(expected)),
                "exact source assertion retained {suffix}"
            );
            drop(cg);
            let debt = crate::codegen_ay::chc::take_sound_havoc_drop_by_fn();
            assert_eq!(
                debt.get(&name).copied().unwrap_or(0),
                0,
                "nullness does not walk a fresh-data fat-pointer approximation {suffix}"
            );
        }
    });
}
