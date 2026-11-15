// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Actual native deferred allocation, initialization and Vec ownership transfer.

use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};

#[test]
fn native_vec_literal_preserves_allocation_initialization_and_element_updates() {
    let source = format!(
        "{}\n{}",
        include_str!("../../../../../tools/soundness-duals/native_vec_literal_dual.rs"),
        include_str!("../../../../../tools/soundness-duals/native_uninit_handoff_dual.rs")
    )
    .replace("#[kani::proof]", "")
    .replace("#![feature(liballoc_internals)]", "");
    let source = format!("#![feature(liballoc_internals)]\n{source}");
    with_native_box_ctx(&source, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        let mut failures = Vec::new();
        for uninit_checks in [false, true] {
            for depth in [0, 32] {
                for name in [
                    "native_vec_literal_len_safe",
                    "native_vec_literal_len_bug",
                    "native_vec_literal_element_safe",
                    "native_vec_literal_element_bug",
                    "native_vec_literal_updated_element_safe",
                    "native_vec_literal_updated_element_bug",
                    "uninit_scalar_drop_successor_safe",
                    "uninit_scalar_drop_successor_bug",
                    "uninit_array_drop_successor_safe",
                    "uninit_array_drop_successor_bug",
                    "uninit_overaligned_drop_successor_safe",
                    "uninit_overaligned_drop_successor_bug",
                    "vec_initialization_observes_store_time_source_safe",
                    "vec_initialization_observes_store_time_source_bug",
                    "uninit_drop_before_typed_box_safe",
                    "uninit_drop_before_typed_box_bug",
                    "native_scalar_write_then_assume_init_safe",
                    "native_scalar_write_then_assume_init_bug",
                    "native_array_write_then_assume_init_safe",
                    "native_array_write_then_assume_init_bug",
                    "native_array_rewrite_into_vec_safe",
                    "native_array_rewrite_into_vec_bug",
                    "native_bool_write_then_assume_init_safe",
                    "native_bool_write_then_assume_init_bug",
                    "native_bool_array_into_vec_safe",
                    "native_bool_array_into_vec_bug",
                ] {
                    let instance = find_instance_by_suffix(ctx.tcx, name);
                    let body = instance.callee_body().unwrap();
                    let mut pass = FunctionInlinePass::new(InlineConfig {
                        max_depth: depth,
                        chc_native_box_drop: true,
                        ..InlineConfig::default()
                    });
                    let (_, body) =
                        pass.transform_with_body_provider(ctx.tcx, body, instance, |callee| {
                            if abstraction.abstracts_public_instance(ctx.tcx, callee) {
                                None
                            } else {
                                callee.callee_body()
                            }
                        });
                    let (vc, _, diagnostics) = ChcCtx::new(
                        ctx.tcx,
                        &body,
                        name,
                        ChcConfig { uninit_checks, ..mem_config() },
                    )
                    .translate_with_diagnostics();
                    if let Some(dir) = std::env::var_os("MC_NATIVE_INIT_ARTIFACT_DIR") {
                        let path = std::path::Path::new(&dir);
                        std::fs::write(
                            path.join(format!("{uninit_checks}-{depth}-{name}.mir")),
                            format!("{body:#?}"),
                        )
                        .unwrap();
                        std::fs::write(
                            path.join(format!("{uninit_checks}-{depth}-{name}.smt2")),
                            crate::codegen_ay::emit_chc(&vc).to_string(),
                        )
                        .unwrap();
                        let problem =
                            ay_chc::ChcParser::parse(&crate::codegen_ay::emit_chc(&vc).to_string())
                                .unwrap();
                        let mut metadata = Vec::new();
                        for (index, obligation) in
                            problem.query_obligations().unwrap().into_iter().enumerate()
                        {
                            let (id, mut problem) = obligation.into_parts();
                            problem.expand_nullary_fail_queries(false);
                            let file = format!(
                                "{uninit_checks}-{depth}-{name}-property-{index}.normalized"
                            );
                            std::fs::write(path.join(&file), problem.normalized_input()).unwrap();
                            let property = vc
                                .properties
                                .iter()
                                .find(|property| property.relation == id.label());
                            metadata.push(serde_json::json!({"file":file,"id":id.label(),"kind":property.map(|p|format!("{:?}",p.kind)),"message":property.and_then(|p|p.message.clone()),"approximation_dependent":property.and_then(|p|p.approximation_dependent),"approximation_identity_complete":vc.approximation_identity_complete}));
                        }
                        std::fs::write(
                            path.join(format!("{uninit_checks}-{depth}-{name}-properties.json")),
                            serde_json::to_vec_pretty(&metadata).unwrap(),
                        )
                        .unwrap();
                    }
                    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                        .remove(name)
                        .unwrap_or_default();
                    let verdict = run_z3_on_smt2_with_timeout(
                        &crate::codegen_ay::emit_chc(&vc).to_string(),
                        30,
                    );
                    let expected = if name.ends_with("safe") { "unsat" } else { "sat" };
                    eprintln!(
                        "NATIVE_VEC depth={depth} shadow={uninit_checks} {name}: {verdict:?}, place={}, reasons={reasons:?}",
                        diagnostics.place_translation_drop.get()
                    );
                    if verdict.as_deref() != Ok(expected)
                        || !reasons.is_empty()
                        || diagnostics.place_translation_drop.get() != 0
                    {
                        failures.push((depth, name, verdict, reasons));
                    }
                }
            }
        }
        assert!(failures.is_empty(), "native Vec initialization rows: {failures:?}");
    });
}

#[test]
fn native_uninit_box_does_not_silently_assume_complete_initialization() {
    // Compiler-only refusal controls, including UB adversaries and unsupported
    // defined cases. None is executed by the defined native oracle.
    let source = include_str!("fixtures/native_uninit_adversaries.rs");
    with_native_box_ctx(source, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        for depth in [0, 32] {
            for uninit_checks in [false, true] {
                for name in [
                    "missing_initialization",
                    "partial_initialization",
                    "direct_missing_initialization",
                    "poison_rhs_initialization",
                    "poisoned_native_write",
                    "byte_clobber_after_native_write",
                    "rebound_native_owner",
                    "initialized_other_object",
                    "conditional_initialization",
                    "zst_without_native_address_authority",
                    "missing_slice_initialization",
                    "repeated_allocation_generations",
                    "borrowed_box_storage_is_not_payload",
                    "boxed_uninit_assume_init_read",
                    "boxed_uninit_assume_init_ref",
                    "boxed_uninit_assume_init_mut",
                    "boxed_uninit_assume_init_drop",
                    "stack_uninit_assume_init",
                    "array_uninit_assume_init",
                    "slice_uninit_assume_init_ref",
                    "slice_uninit_assume_init_mut",
                    "slice_uninit_assume_init_drop",
                    "nested_uninit_accessor",
                    "payload_alias_after_transfer",
                    "raw_uninitialized_payload_read",
                    "raw_partially_initialized_payload_read",
                    "raw_uninitialized_payload_reference",
                    "raw_stack_poison_rhs_initialization",
                    "discarded_raw_stack_read_before_initialization",
                    "discarded_address_of_stack_maybe_read",
                    "discarded_constant_maybe_read",
                    "discarded_maybe_byte_view_read",
                    "discarded_nested_stack_read",
                    "discarded_twice_nested_stack_read",
                    "discarded_array_maybe_read",
                    "discarded_wrapped_maybe_read",
                    "initialized_stack_maybe_without_frame_certificate",
                    "native_address_word_is_not_a_logical_object_number",
                ] {
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
                            if abstraction.abstracts_public_instance(ctx.tcx, callee) {
                                None
                            } else {
                                callee.callee_body()
                            }
                        },
                    );
                    let config = ChcConfig { uninit_checks, ..mem_config() };
                    let (vc, _, diagnostics) =
                        ChcCtx::new(ctx.tcx, &body, name, config).translate_with_diagnostics();
                    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                        .remove(name)
                        .unwrap_or_default();
                    let verdict = run_z3_on_smt2_with_timeout(
                        &crate::codegen_ay::emit_chc(&vc).to_string(),
                        30,
                    );
                    eprintln!(
                        "UNINIT_ADVERSARY depth={depth} shadow={uninit_checks} {name}: {verdict:?}, reasons={reasons:?}"
                    );
                    if let Some(dir) = std::env::var_os("MC_NATIVE_INIT_ARTIFACT_DIR") {
                        let prefix = std::path::Path::new(&dir)
                            .join(format!("adversary-{uninit_checks}-{depth}-{name}"));
                        std::fs::write(
                            prefix.with_extension("smt2"),
                            crate::codegen_ay::emit_chc(&vc).to_string(),
                        )
                        .unwrap();
                        std::fs::write(prefix.with_extension("mir"), format!("{body:#?}")).unwrap();
                        std::fs::write(prefix.with_extension("json"),serde_json::to_vec_pretty(&serde_json::json!({"verdict":verdict,"place_translation_drop":diagnostics.place_translation_drop.get(),"reasons":reasons,"approximation_identity_complete":vc.approximation_identity_complete})).unwrap()).unwrap();
                    }
                    assert!(
                        diagnostics.place_translation_drop.get() != 0,
                        "{name}: missing/partial/poison initialization must retain actual refusal"
                    );
                    assert!(
                        !vc.approximation_identity_complete,
                        "{name}: unsupported initialization must not export complete proof authority"
                    );
                    if name.starts_with("boxed_uninit_assume_init_")
                        || [
                            "stack_uninit_assume_init",
                            "array_uninit_assume_init",
                            "slice_uninit_assume_init_ref",
                            "slice_uninit_assume_init_mut",
                            "slice_uninit_assume_init_drop",
                            "nested_uninit_accessor",
                        ]
                        .contains(&name)
                    {
                        assert!(
                            reasons.contains_key(
                                "native_maybe_unsafe_accessor_without_initialization_certificate"
                            ) || reasons.contains_key(
                                "native_initialized_handoff_nested_custody_unmodeled"
                            ) || (name == "nested_uninit_accessor"
                                && reasons.contains_key(
                                    "native_maybe_frame_without_initializedness_provenance"
                                )),
                            "{name}: unchecked native accessor boundary was lost: {reasons:?}"
                        );
                    }
                }
            }
        }
    });
}

#[test]
fn native_uninit_site_reservations_cannot_shift_a_later_typed_box_or_columns() {
    use rustc_public::mir::TerminatorKind;
    let source = r#"
        pub fn reservations() {
            let _uninit=Box::<[u8;2]>::new_uninit();
            let initialized=Box::new(9u32);
            assert!(*initialized==9);
        }
    "#;
    with_native_box_ctx(source, |ctx| {
        let original = find_instance_by_suffix(ctx.tcx, "reservations").callee_body().unwrap();
        let native_site = original
            .blocks
            .iter()
            .enumerate()
            .find_map(|(site, _)| {
                crate::codegen_ay::shared::native_box_uninit::native_box_new_uninit_site(
                    ctx.tcx, &original, site,
                )
                .map(|_| site)
            })
            .unwrap();
        for cyclic in [false, true] {
            let mut body = original.clone();
            if cyclic {
                let TerminatorKind::Call { target, .. } =
                    &mut body.blocks[native_site].terminator.kind
                else {
                    panic!("native call");
                };
                *target = Some(native_site);
            }
            let mut chc = ChcCtx::new(ctx.tcx, &body, "reservations", mem_config());
            chc.declare_block_relations();
            assert_eq!(chc.heap_state.native_uninit_reservations.len(), usize::from(!cyclic));
            assert_eq!(
                chc.heap_state.preallocated_heap_ids.len(),
                1,
                "native IDs must not enter the unrelated allocator FIFO"
            );
            let expected = *chc.heap_state.preallocated_heap_ids.front().unwrap();
            let columns = chc.state_var_mgr.state_vars.len();
            let (site, args) = body
                .blocks
                .iter()
                .enumerate()
                .find_map(|(site, block)| {
                    let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                        return None;
                    };
                    (chc.detect_alloc_stub(func) == Some(StubKind::BoxNew)).then_some((site, args))
                })
                .unwrap();
            chc.current_encode_bb = site;
            chc.heap_state.encode_bb = site;
            let allocated =
                chc.translate_alloc_call(StubKind::BoxNew, args, &HashSet::new()).unwrap();
            assert_eq!(allocated.alloc_obj_id, Some(expected));
            assert!(chc.heap_state.preallocated_heap_ids.is_empty());
            assert_eq!(
                chc.heap_state.get_region_array(expected).unwrap().2.bitvec_width(),
                Some(32)
            );
            assert_eq!(
                chc.state_var_mgr.state_vars.len(),
                columns,
                "an unhandled native site must not cause a late region column"
            );
        }
    });
}
