// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};

#[test]
fn boxed_callable_constants_keep_exact_typed_views() {
    if std::env::var_os("TRUST_MC_CALLABLE_CONST_TRACE").is_some() {
        let _ = tracing_subscriber::fmt().with_env_filter(
            "warn,trust_mc_engine::codegen_ay::chc::decl::global_objects=debug,trust_mc_engine::codegen_ay::chc::stmt::codegen_stmt_rvalue_ref::unsize_dyn=debug"
        ).with_test_writer().try_init();
    }
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let source =
        include_str!("../../../../../tools/soundness-duals/callable_reference_tuple_dual.rs")
            .split("#[kani::proof]\nfn captured_reference_predicate_safe")
            .next()
            .unwrap()
            .replace("#[kani::proof]", "");
    with_native_box_ctx(&source, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        let mut failures = Vec::new();
        for depth in [0, 1] {
            for (name, expected) in [
                ("boxed_callable_reference_writeback_safe", "unsat"),
                ("boxed_callable_wrong_writeback_bug", "sat"),
            ] {
                let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
                let instance = find_instance_by_suffix(ctx.tcx, name);
                let mut pass = FunctionInlinePass::new(InlineConfig {
                    max_depth: depth,
                    chc_native_box_drop: true,
                    ..InlineConfig::default()
                });
                let (_, body) = pass.transform_with_body_provider(
                    ctx.tcx,
                    instance.callee_body().unwrap(),
                    instance,
                    |callee| {
                        (!abstraction.abstracts_public_instance(ctx.tcx, callee))
                            .then(|| callee.callee_body())
                            .flatten()
                    },
                );
                let (vc, _, diagnostics) =
                    ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
                let result =
                    run_z3_on_smt2_with_timeout(&crate::codegen_ay::emit_chc(&vc).to_string(), 30);
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                eprintln!(
                    "CALLABLE_CONSTANT depth={depth} {name}: {result:?}; drop={}; reasons={reasons:?}",
                    diagnostics.place_translation_drop.get()
                );
                if result.as_deref() != Ok(expected)
                    || diagnostics.place_translation_drop.get() != 0
                    || !reasons.is_empty()
                {
                    failures.push((
                        depth,
                        name,
                        result,
                        diagnostics.place_translation_drop.get(),
                        reasons,
                    ));
                }
            }
        }
        assert!(failures.is_empty(), "constant reference qualification: {failures:?}");
    });
}

#[test]
fn boxed_callable_constants_physical_bytes_keep_view_debt() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let source =
        include_str!("../../../../../tools/soundness-duals/boxed_callable_const_view_dual.rs")
            .lines()
            .filter(|line| !line.starts_with("//!"))
            .collect::<Vec<_>>()
            .join("\n")
            .replace("#[kani::proof]", "");
    let source = format!(
        r#"
        #![feature(register_tool)]
        #![register_tool(kanitool)]
        mod kani {{
            #[kanitool::fn_marker = "AnyModel"]
            pub fn any<T>() -> T {{ any_raw() }}
            #[kanitool::fn_marker = "AnyRawHook"]
            fn any_raw<T>() -> T {{ panic!("model-only raw hook") }}
        }}
        {source}
    "#
    );
    with_native_box_ctx(&source, |ctx| {
        for name in [
            "physical_byte_safe",
            "physical_byte_bug",
            "escaped_byte_safe",
            "escaped_byte_bug",
            "symbolic_byte_safe",
            "symbolic_byte_bug",
        ] {
            let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.callee_body().unwrap();
            let (vc, _, diagnostics) =
                ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
            let verdict =
                run_z3_on_smt2_with_timeout(&crate::codegen_ay::emit_chc(&vc).to_string(), 30);
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove(name)
                .unwrap_or_default();
            eprintln!(
                "CALLABLE_BYTES {name}: {verdict:?}; drop={}; reasons={reasons:?}",
                diagnostics.place_translation_drop.get()
            );
            if !name.starts_with("escaped_") {
                assert!(
                    reasons.contains_key("heap_view_read_unwritten")
                        || reasons.contains_key("heap_view_read_stale"),
                    "a reached physical byte view requires ledger debt: {name} {verdict:?} {reasons:?}"
                );
            } else {
                // The current nested raw-pointer binder refuses this escape
                // before a typed heap byte load is reached. This is a distinct
                // boundary, not permission to use an unreported byte value.
                assert!(
                    reasons.contains_key("pointer_bytes_rewritten_untyped"),
                    "an unsupported escaped reference image must stay refused: {name} {verdict:?} {reasons:?}"
                );
                assert_eq!(
                    super::super::codegen_ctx::fallback_soundness(
                        "pointer_bytes_rewritten_untyped"
                    ),
                    super::super::codegen_ctx::FallbackSoundness::FailClose
                );
                assert!(diagnostics.place_translation_drop.get() > 0);
            }
        }
    });
}

#[test]
fn boxed_callable_constants_deep_discovery_and_late_view_refusal() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        const IMAGE: &[u64; 4] = &[0x0201020102010201u64; 4];
        #[inline(never)] fn read3(p: *const u8) -> u16 { unsafe { p.cast::<u16>().read() } }
        #[inline(never)] fn read2(p: *const u8) -> u16 { read3(p) }
        #[inline(never)] fn read1(p: *const u8) -> u16 { read2(p) }
        pub fn discovery() -> u16 { read1(IMAGE.as_ptr().cast::<u8>()) }
        struct Late(u64, u64);
        fn late_type(_: Late) {}
    "#;
    with_native_box_ctx(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "discovery");
        let body = instance.callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "discovery", mem_config());
        chc.declare_block_relations();
        let u16_ty = rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U16);
        assert!(
            chc.ref_resolution.extra_read_types.contains(&u16_ty),
            "the third ordinary callee's actual dereference type must precede entry seeding"
        );
        assert!(
            chc.ref_resolution.const_ref_memory_inits.iter().any(|(_, sort, value, _, _)| {
                sort == &ay_bindings::Sort::bitvec(16)
                    && value == &Expr::bitvec_const(0x0201u16, 16)
            }),
            "the canonical native window must be seeded in its own u16 view"
        );
        chc.close_object_seeding();
        let late_body = find_instance_by_suffix(ctx.tcx, "late_type").callee_body().unwrap();
        let late_ty = late_body.locals()[1].ty;
        assert!(!chc.ref_resolution.extra_read_types.contains(&late_ty));
        let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        chc.note_extra_read_type(late_ty);
        let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
            .remove("discovery")
            .unwrap_or_default();
        assert!(
            reasons.contains_key("const_object_unseeded"),
            "a genuinely late view stays refused: {reasons:?}"
        );
    });
}

#[test]
fn boxed_callable_constants_scan_budget_keeps_late_read_refusal() {
    let mut source = String::from("#![allow(dead_code)]\nconst IMAGE: &[u64; 4] = &[7; 4];\n");
    for i in 0..140 {
        source.push_str(&format!(
            "#[inline(never)] fn f{i}(p: *const u8) -> u32 {{ f{}(p) }}\n",
            i + 1
        ));
    }
    source.push_str("fn f140(p: *const u8) -> u32 { unsafe { *(p as *const u32) } }\n");
    source.push_str("pub fn bounded() -> u32 { let image = IMAGE; f0(image as *const [u64; 4] as *const u8) ^ image[0] as u32 }\n");
    with_native_box_ctx(&source, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "bounded").callee_body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "bounded", mem_config());
        chc.declare_block_relations();
        let u32_ty = rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U32);
        assert!(
            !chc.ref_resolution.extra_read_types.contains(&u32_ty),
            "the bounded scan must stop before this deep producer"
        );
        assert!(
            !chc.ref_resolution.object_read_types.is_empty(),
            "the fixed source image is actually read"
        );
        chc.close_object_seeding();
        let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let late = find_instance_by_suffix(ctx.tcx, "f140").callee_body().unwrap();
        chc.register_callee_body_consts(&late);
        let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
            .remove("bounded")
            .unwrap_or_default();
        assert!(
            reasons.contains_key("const_object_unseeded"),
            "scan exhaustion cannot grant a seed after entry: {reasons:?}"
        );
    });
}

#[test]
fn boxed_callable_constants_omitted_byte_view_tracks_symbolic_and_escaped_reads() {
    use crate::codegen_ay::chc::codegen_ctx::ExactVar;
    use trust_mc_core::chc::{RelationApp, Rule, RuleBody};
    with_native_box_ctx("fn view_marker(_: &i32) {} pub fn view_probe() {}", |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "view_probe").callee_body().unwrap();
        let ref_ty =
            find_instance_by_suffix(ctx.tcx, "view_marker").callee_body().unwrap().locals()[1].ty;
        let ref_key = ChcCtx::type_key_for_ty(ref_ty);
        for (case, should_refuse) in [
            (0, true),
            (1, true),
            (2, true),
            (3, false),
            (4, false),
            (5, false),
            (6, true),
            (7, true),
            (8, true),
            (9, true),
        ] {
            let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            let mut chc = ChcCtx::new(ctx.tcx, &body, "view_probe", mem_config());
            chc.declare_block_relations();
            let obj = chc.heap_state.next_heap_alloc_id().unwrap();
            chc.heap_state.record_heap_alloc_size(obj, 8);
            let base = super::super::decl::global_objects::object_base_for(obj);
            assert!(
                !chc.defer_reference_byte_view(obj, &ref_key),
                "an allocation ID/layout alone cannot admit the deferred lane"
            );
            chc.note_view_write(
                &base,
                &Expr::bitvec_const(1u64 << 32, 64),
                &ref_key,
                &ay_bindings::Sort::bitvec(64),
            );
            assert!(chc.defer_reference_byte_view(obj, &ref_key));
            // A byte cell already written elsewhere does not constrain an
            // unknown offset to that cell and cannot clear the missing image.
            if case != 5 && case != 9 {
                chc.heap_state.view_ledger.next_statement();
                chc.note_view_write(
                    &(base.clone().bvadd(Expr::bitvec_const(4, 64))),
                    &Expr::bitvec_const(7, 8),
                    "u8",
                    &ay_bindings::Sort::bitvec(8),
                );
            }
            let addr = match case {
                0 => base,
                1 | 6 | 7 | 9 => Expr::bitvec_const(obj, 32)
                    .concat(ExactVar::nondet("byte_index".into(), ay_bindings::Sort::bitvec(32))),
                2 => ExactVar::nondet("escaped_byte_addr".into(), ay_bindings::Sort::bitvec(64)),
                3 => super::super::decl::global_objects::object_base_for(
                    chc.heap_state.next_heap_alloc_id().unwrap(),
                ),
                _ => base,
            };
            let (key, width) = match case {
                5 => (&*ref_key, 64),
                6 => ("u16", 16),
                7 => ("u64", 64),
                8 => (super::super::heap::heap_view_ledger::REGION_VIEW_KEY, 64),
                _ => ("u8", 8),
            };
            let byte = chc
                .load_from_type_array(addr, key, ay_bindings::Sort::bitvec(width), None)
                .unwrap();
            if case != 4 {
                chc.vc.add_rule(Rule::new(
                    RuleBody::new(None, vec![byte.eq(Expr::bitvec_const(7, width))]),
                    RelationApp::new("byte_observer", vec![]),
                ));
            }
            chc.record_heap_view_ledger_reasons();
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove("view_probe")
                .unwrap_or_default();
            assert_eq!(
                reasons.contains_key("heap_view_read_stale"),
                should_refuse,
                "only used reads that may alias the omitted reference image are refused: case{case}: {reasons:?}"
            );
        }
    });
}

#[test]
fn boxed_callable_constants_exact_fn_item_view_is_declared_at_every_track_level() {
    let source =
        include_str!("../../../../../tools/soundness-duals/callable_reference_tuple_dual.rs")
            .split("#[kani::proof]\nfn captured_reference_predicate_safe")
            .next()
            .unwrap()
            .replace("#[kani::proof]", "");
    with_native_box_ctx(&source, |ctx| {
        for track in [crate::args::ChcTrackLevel::Reg, crate::args::ChcTrackLevel::Mem] {
            let body = find_instance_by_suffix(ctx.tcx, "boxed_callable_reference_writeback_safe")
                .callee_body()
                .unwrap();
            let fn_ty = body
                .locals()
                .iter()
                .find_map(|local| match local.ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                        if matches!(pointee.kind(), TyKind::RigidTy(RigidTy::FnDef(..))) =>
                    {
                        Some(pointee)
                    }
                    _ => None,
                })
                .expect("the native reference-to-function-item producer");
            let mut chc = ChcCtx::new(
                ctx.tcx,
                &body,
                "boxed_callable_reference_writeback_safe",
                ChcConfig { track_level: track, ..ChcConfig::default() },
            );
            chc.declare_block_relations();
            assert!(
                chc.ref_resolution.extra_read_types.contains(&fn_ty),
                "the actual FnDef view must not depend on Mem array predeclaration: {track:?}"
            );
            chc.close_object_seeding();
            let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            chc.note_extra_read_type(fn_ty);
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove("boxed_callable_reference_writeback_safe")
                .unwrap_or_default();
            assert!(
                !reasons.contains_key("const_object_unseeded"),
                "the same native view was discovered before entry: {track:?} {reasons:?}"
            );
        }
    });
}
