// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::common::*;

fn source() -> String {
    include_str!("../../../../../tools/soundness-duals/chc_native_box_drop_dual.rs")
        .replace("#[kani::proof]", "")
        .replace("let branch: bool = kani::any();", "let branch: bool = false;")
}

#[test]
fn native_fat_box_host_drop_preserves_exact_destructor_and_successor() {
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
        &source(),
        &["-Cpanic=abort"],
        |ctx| {
            let mut failures = Vec::new();
            for (name, expected) in [
                ("quiet_with_loud_decoy_safe", "unsat"),
                ("quiet_with_loud_decoy_bug", "sat"),
                ("empty_drop_successor_bug", "sat"),
                ("loud_effect_safe", "unsat"),
                ("loud_effect_bug", "sat"),
                ("user_destructor_panic_bug", "sat"),
                ("walked_loud_effect_safe", "unsat"),
                ("walked_loud_effect_bug", "sat"),
                ("walked_quiet_successor_safe", "unsat"),
                ("walked_quiet_successor_bug", "sat"),
                ("walked_panic_bug", "sat"),
                ("inner_outer_drop_successor_bug", "sat"),
                ("explicit_mem_drop_effect_safe", "unsat"),
                ("explicit_mem_drop_effect_bug", "sat"),
                ("user_named_drop_keeps_its_body_safe", "unsat"),
                ("user_named_drop_keeps_its_body_bug", "sat"),
            ] {
                let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
                let config = ChcConfig {
                    track_level: crate::args::ChcTrackLevel::Mem,
                    ..ChcConfig::default()
                };
                let (vc, _, diagnostics) =
                    ChcCtx::new(ctx.tcx, &body, name, config).translate_with_diagnostics();
                let smt = crate::codegen_ay::emit_chc(&vc).to_string();
                let verdict = run_z3_on_smt2_with_timeout(&smt, 30).unwrap();
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                eprintln!(
                    "BOX_DROP_ROW {name} expected={expected} actual={verdict} debt={} reasons={reasons:?}",
                    diagnostics.place_translation_drop.get()
                );
                if let Some(directory) = std::env::var_os("MC_BOX_DROP_ARTIFACT_DIR") {
                    let _ = std::fs::write(
                        std::path::Path::new(&directory).join(format!("{name}.smt2")),
                        &smt,
                    );
                }
                if verdict != expected || diagnostics.place_translation_drop.get() != 0 {
                    failures.push((
                        name,
                        verdict,
                        diagnostics.place_translation_drop.get(),
                        reasons,
                    ));
                }
            }
            assert!(failures.is_empty(), "strict Box drop controls: {failures:?}");
        },
    );
}

#[cfg(test)]
mod metadata_effect_tests {
    use super::*;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::chc::codegen_expr_heap::{
        obj_size_in, obj_size_out, obj_valid_in, obj_valid_out,
    };
    use crate::codegen_ay::chc::rules::codegen_rules::transition_drop::append_outer_free;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

    fn pointer(id: u32) -> Expr {
        Expr::bitvec_const(id, 32).concat(Expr::bitvec_const(0u32, 32))
    }
    #[test]
    fn inner_then_outer_frees_compose_and_preserve_both_dead_objects() {
        with_test_ay_ctx_for_source("pub fn probe() {}", |context| {
            let body = find_instance_by_suffix(context.tcx, "probe").body().unwrap();
            let mut ctx = ChcCtx::new(context.tcx, &body, "probe", ChcConfig::default());
            append_outer_free(&mut ctx, pointer(101), Some(101)).unwrap();
            append_outer_free(&mut ctx, pointer(102), Some(102)).unwrap();
            for output in [obj_valid_out(), obj_size_out()] {
                assert_eq!(
                    ctx.heap_state
                        .pending_updates
                        .iter()
                        .filter(|c| matches!(c.value(),ExprValue::Eq(left,_) if *left==output))
                        .count(),
                    1
                );
            }
            let clauses = ctx
                .heap_state
                .pending_updates
                .iter()
                .map(|e| format!("(assert {e})\n"))
                .collect::<String>();
            let common = format!(
                "(set-logic QF_AUFBV)\n(declare-const obj_valid (Array (_ BitVec 32) Bool))\n(declare-const obj_valid__out (Array (_ BitVec 32) Bool))\n(declare-const obj_size (Array (_ BitVec 32) (_ BitVec 32)))\n(declare-const obj_size__out (Array (_ BitVec 32) (_ BitVec 32)))\n(assert (= obj_valid ((as const (Array (_ BitVec 32) Bool)) true)))\n(assert (= obj_size ((as const (Array (_ BitVec 32) (_ BitVec 32))) (_ bv4 32))))\n{clauses}"
            );
            let both_dead = Expr::or(
                obj_valid_out().select(Expr::bitvec_const(101u32, 32)),
                obj_valid_out().select(Expr::bitvec_const(102u32, 32)),
            );
            let solver = |query: &str| run_z3_on_smt2_with_timeout(query, 30).unwrap();
            assert_eq!(
                solver(&format!("{common}(check-sat)\n")),
                "sat",
                "free composition must retain a successor"
            );
            assert_eq!(
                solver(&format!("{common}(assert {both_dead})(check-sat)\n")),
                "unsat",
                "neither freed allocation may remain live"
            );
        });
    }
    #[test]
    fn ambiguous_or_output_dependent_metadata_refuses_without_erasing_it() {
        with_test_ay_ctx_for_source("pub fn probe() {}", |context| {
            let body = find_instance_by_suffix(context.tcx, "probe").body().unwrap();
            for ambiguous in [false, true] {
                let mut ctx = ChcCtx::new(context.tcx, &body, "probe", ChcConfig::default());
                let initial = if ambiguous { obj_valid_in() } else { obj_valid_out() };
                ctx.heap_state.pending_updates.push(obj_valid_out().eq(initial));
                if ambiguous {
                    ctx.heap_state.pending_updates.push(obj_valid_out().eq(obj_valid_in()));
                }
                ctx.mark_obj_valid_modified();
                let saved = ctx.heap_state.pending_updates.clone();
                assert!(append_outer_free(&mut ctx, pointer(101), Some(101)).is_none());
                assert_eq!(ctx.heap_state.pending_updates, saved);
                assert!(ctx.diagnostics.place_translation_drop.get() > 0);
            }
        });
    }

    #[test]
    fn destructor_metadata_observations_are_not_rebound_to_the_outer_free() {
        with_test_ay_ctx_for_source("pub fn probe(){}", |context| {
            let body = find_instance_by_suffix(context.tcx, "probe").body().unwrap();
            for in_check in [false, true] {
                let mut ctx = ChcCtx::new(context.tcx, &body, "probe", ChcConfig::default());
                append_outer_free(&mut ctx, pointer(101), Some(101)).unwrap();
                let observation = obj_valid_out().select(Expr::bitvec_const(102u32, 32));
                if in_check {
                    ctx.heap_state.pending_checks.push(observation);
                } else {
                    ctx.heap_state
                        .pending_updates
                        .push(Expr::var("observed", ay_bindings::Sort::bool()).eq(observation));
                }
                let saved = ctx.heap_state.pending_updates.clone();
                assert!(append_outer_free(&mut ctx, pointer(102), Some(102)).is_none());
                assert_eq!(ctx.heap_state.pending_updates, saved);
                assert!(ctx.diagnostics.place_translation_drop.get() > 0);
            }
        });
    }

    #[test]
    fn deallocation_extent_uses_current_layout_instead_of_readable_prefix() {
        with_test_ay_ctx_for_source("pub fn probe(){}", |context| {
            use crate::codegen_ay::chc::rules::codegen_rules::transition_drop::require_native_deallocation_extent;
            let body = find_instance_by_suffix(context.tcx, "probe").body().unwrap();
            for current in [0u32, 4, 8] {
                let mut ctx = ChcCtx::new(context.tcx, &body, "probe", ChcConfig::default());
                ctx.heap_state.pending_updates.push(
                    obj_size_out().eq(obj_size_in()
                        .store(Expr::bitvec_const(101u32, 32), Expr::bitvec_const(current, 32))),
                );
                ctx.mark_obj_size_modified();
                require_native_deallocation_extent(&mut ctx, Expr::bitvec_const(101u32, 32), 4)
                    .unwrap();
                let check = ctx.heap_state.pending_checks.pop().unwrap();
                assert!(
                    !check.to_string().contains("__out"),
                    "event-time snapshot is independent of final output"
                );
                let query = format!(
                    "(set-logic QF_AUFBV)\n(declare-const obj_size (Array (_ BitVec 32) (_ BitVec 32)))\n(assert {check})\n(check-sat)\n"
                );
                assert_eq!(
                    run_z3_on_smt2_with_timeout(&query, 30).unwrap(),
                    if current == 4 { "sat" } else { "unsat" }
                );
            }
        });
    }
}

#[test]
fn native_inner_box_without_address_origin_retains_hard_refusal() {
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
        &source(),
        &["-Cpanic=abort"],
        |ctx| {
            let body = find_instance_by_suffix(ctx.tcx, "inner_outer_drop_safe").body().unwrap();
            let (_, _, diagnostics) = ChcCtx::new(
                ctx.tcx,
                &body,
                "inner_outer_drop_safe",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            )
            .translate_with_diagnostics();
            assert!(
                diagnostics.place_translation_drop.get() > 0,
                "pointer-valued field loads must not invent allocation/alignment authority"
            );
        },
    );
}

#[test]
fn malformed_unknown_and_cyclic_native_fat_drops_keep_hard_refusal() {
    let source = source()
        + r#"
        pub fn unknown_argument(_value:Box<dyn Tag>) {}
        pub fn malformed_box() {
            let pointer:*mut dyn Tag=unsafe{core::mem::transmute((1usize,0usize))};
            let _value=unsafe{Box::from_raw(pointer)};
        }
        pub fn same_concrete_join(branch:bool) {
            let value:Box<dyn Tag>=if branch{Box::new(Quiet(1))}else{Box::new(Quiet(2))};
            drop(value);
        }
        pub fn reassigned_argument(mut value:Box<dyn Tag>,branch:bool) {
            if branch {value=Box::new(Quiet(2));}
            drop(value);
        }
        struct Empty;
        impl Tag for Empty {}
        pub fn native_zero_sized_box(){let _value:Box<dyn Tag>=Box::new(Empty);}
    "#;
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
        &source,
        &["-Cpanic=abort"],
        |ctx| {
            for name in [
                "unknown_argument",
                "malformed_box",
                "repeated_drop_safe",
                "inner_outer_drop_uaf_bug",
                "same_concrete_join",
                "reassigned_argument",
                "native_zero_sized_box",
            ] {
                let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
                let (_, _, diagnostics) = ChcCtx::new(
                    ctx.tcx,
                    &body,
                    name,
                    ChcConfig {
                        track_level: crate::args::ChcTrackLevel::Mem,
                        ..ChcConfig::default()
                    },
                )
                .translate_with_diagnostics();
                assert!(
                    diagnostics.place_translation_drop.get() > 0,
                    "{name}: unavailable native origin must not become clean authority"
                );
            }
        },
    );
}

#[path = "test_native_box_drop/joins.rs"]
mod joins;

#[test]
fn payload_destructor_reads_use_event_time_memory_ssa() {
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
        &source(),
        &["-Cpanic=abort"],
        |ctx| {
            for (name, expected) in [
                ("payload_destructor_value_safe", "unsat"),
                ("payload_destructor_value_bug", "sat"),
            ] {
                let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
                let (vc, _, diagnostics) = ChcCtx::new(
                    ctx.tcx,
                    &body,
                    name,
                    ChcConfig {
                        track_level: crate::args::ChcTrackLevel::Mem,
                        ..ChcConfig::default()
                    },
                )
                .translate_with_diagnostics();
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                assert_eq!(diagnostics.place_translation_drop.get(), 0, "{name}: {reasons:?}");
                let query = crate::codegen_ay::emit_chc(&vc).to_string();
                if let Some(dir) = std::env::var_os("MC_BOX_DROP_ARTIFACT_DIR") {
                    std::fs::write(std::path::Path::new(&dir).join(format!("{name}.smt2")), &query)
                        .unwrap();
                }
                super::test_native_drop_memory::assert_native_memory_properties(
                    &vc, name, expected,
                );
            }
        },
    );
}

#[test]
fn native_fat_global_carrier_authentication_refuses_allocator_lookalikes_and_stubs() {
    let source = r#"
        #![feature(allocator_api)]
        use std::alloc::{Allocator,AllocError,Layout};
        use core::ptr::NonNull;
        trait Tag{}
        struct Custom;
        unsafe impl Allocator for Custom {
            fn allocate(&self,_layout:Layout)->Result<NonNull<[u8]>,AllocError>{Err(AllocError)}
            unsafe fn deallocate(&self,_pointer:NonNull<u8>,_layout:Layout){}
        }
        struct BoxRaw<T:?Sized>(*mut T);
        pub fn carriers(native:Box<dyn Tag>, custom:Box<dyn Tag,Custom>, fake:BoxRaw<dyn Tag>){}
        pub fn marker(){}
        pub fn call_marker(){marker();}
    "#;
    with_test_ay_ctx_for_source(source, |ctx| {
        use crate::codegen_ay::shared::native_box_drop::native_global_box_pointee;
        let signature = fn_sig_by_suffix(ctx.tcx, "carriers");
        let instance = find_instance_by_suffix(ctx.tcx, "carriers");
        let types = signature
            .inputs()
            .iter()
            .map(|ty| crate::codegen_ay::shared::mono_ty::body_ty(instance, *ty).unwrap())
            .collect::<Vec<_>>();
        assert!(native_global_box_pointee(ctx.tcx, types[0]).is_some());
        assert!(native_global_box_pointee(ctx.tcx, types[1]).is_none());
        assert!(native_global_box_pointee(ctx.tcx, types[2]).is_none());
        let caller = find_instance_by_suffix(ctx.tcx, "call_marker").body().unwrap();
        let func = caller
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Call { func, .. } => Some(func),
                _ => None,
            })
            .unwrap();
        let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(marker, _)) =
            func.ty(caller.locals()).unwrap().kind()
        else {
            panic!("actual marker function")
        };
        let _scope = crate::kani_middle::transform::UnitStubsTestScope::install(
            std::collections::HashMap::from([(marker, marker)]),
        );
        assert!(native_global_box_pointee(ctx.tcx, types[0]).is_none());
    });
}

#[test]
fn host_drop_statement_memory_composes_only_without_temporal_aliases() {
    with_test_ay_ctx_for_source("pub fn probe(){}", |context| {
        use crate::codegen_ay::chc::rules::codegen_rules::transition_drop::compose_host_drop_constraints;
        let body = find_instance_by_suffix(context.tcx, "probe").body().unwrap();
        let ctx = ChcCtx::new(context.tcx, &body, "probe", ChcConfig::default());
        let sort =
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(64), ay_bindings::Sort::bitvec(32));
        let input = Expr::var("memory", sort.clone());
        let output = Expr::var("memory__out", sort);
        let pointer = Expr::bitvec_const(4u64, 64);
        let earlier = input.store(pointer.clone(), Expr::bitvec_const(1u32, 32));
        let later = earlier.clone().store(pointer.clone(), Expr::bitvec_const(7u32, 32));
        let shared = vec![output.clone().eq(earlier)];
        let effects = vec![output.clone().eq(later)];
        assert!(compose_host_drop_constraints(&ctx, &shared, &effects, &[]).unwrap().is_empty());
        let observation = output.select(pointer).eq(Expr::bitvec_const(1u32, 32));
        assert!(
            compose_host_drop_constraints(&ctx, &shared, &effects, &[observation.clone()])
                .is_none(),
            "old-lane observations cannot be reinterpreted as post-destructor reads"
        );
        let mut observed_effects = effects;
        observed_effects.push(Expr::var("observed", ay_bindings::Sort::bool()).eq(observation));
        assert!(
            compose_host_drop_constraints(&ctx, &shared, &observed_effects, &[]).is_none(),
            "other effect equations may observe the pre-destructor memory lane"
        );
    });
}
