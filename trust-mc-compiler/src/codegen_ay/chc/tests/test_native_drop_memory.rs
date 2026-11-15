// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::common::*;
const SOURCE: &str =
    include_str!("../../../../../tools/soundness-duals/chc_native_box_drop_temporal_dual.rs");

/// The production CHC route asks each named property. Their conjunction is
/// exactly aggregate safety, while a validated refutation of one assertion is
/// a real failure. Keep every safety property in this compiler control too.
pub(super) fn assert_native_memory_properties(
    vc: &trust_mc_core::chc::ChcVc,
    name: &str,
    expected: &str,
) {
    let query = crate::codegen_ay::emit_chc(vc).to_string();
    let problem = ay_chc::ChcParser::parse(&query).unwrap();
    let obligations = problem.query_obligations().unwrap();
    assert!(!vc.properties.is_empty());
    assert!(!obligations.is_empty() || !problem.pruned_false_query_ids().is_empty());
    let mut unsolved = Vec::new();
    let mut assertion_failed = false;
    let count = obligations.len();
    for obligation in obligations {
        let (id, mut row) = obligation.into_parts();
        row.expand_nullary_fail_queries(false);
        if let Some(dir) = std::env::var_os("MC_BOX_DROP_ARTIFACT_DIR") {
            std::fs::write(
                std::path::Path::new(&dir).join(format!("{name}-{}.normalized", id.label())),
                row.normalized_input(),
            )
            .unwrap();
        }
        let property = vc
            .properties
            .iter()
            .find(|property| property.relation == id.label())
            .expect("the actual source property identity");
        let actual = match ay_chc::AdaptivePortfolio::new(row, ay_adaptive_config_with_timeout(30))
            .solve()
        {
            ay_chc::VerifiedChcResult::Safe(_) => "unsat",
            ay_chc::VerifiedChcResult::Unsafe(_) => "sat",
            _ => "unknown",
        };
        if actual != "unsat" {
            unsolved.push((id.label().to_owned(), actual, property.message.clone()));
        }
        if actual == "sat"
            && matches!(
                property.kind,
                trust_mc_core::violation::PropertyKind::Assertion
                    | trust_mc_core::violation::PropertyKind::Panic
            )
        {
            assertion_failed = true;
        }
    }
    eprintln!(
        "NATIVE_DROP_SSA_PROPERTIES {name} expected={expected} rows={count} unresolved={unsolved:?}"
    );
    if expected == "unsat" {
        assert!(unsolved.is_empty(), "{name}: {unsolved:?}");
    } else {
        assert!(
            assertion_failed,
            "{name}: intended assertion must have a validated refutation, got {unsolved:?}"
        );
    }
}

#[test]
fn native_destructors_read_current_memory_and_keep_earlier_observations() {
    let source = SOURCE.replace("#[kani::proof]", "");
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
        &source,
        &["-Cpanic=abort"],
        |ctx| {
            let mut failed = Vec::new();
            for (name, expected) in [
                ("native_payload_alias_and_later_store_safe", "unsat"),
                ("native_payload_alias_and_later_store_bug", "sat"),
                ("native_earlier_payload_observation_safe", "unsat"),
                ("native_later_payload_store_cannot_repair_earlier_check_bug", "sat"),
                ("native_two_static_stores_preserve_successor_safe", "unsat"),
                ("native_two_static_stores_do_not_prune_successor_bug", "sat"),
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
                let query = crate::codegen_ay::emit_chc(&vc).to_string();
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                eprintln!(
                    "NATIVE_DROP_SSA_ROW {name} expected={expected} debt={} reasons={reasons:?}",
                    diagnostics.place_translation_drop.get()
                );
                if let Some(dir) = std::env::var_os("MC_BOX_DROP_ARTIFACT_DIR") {
                    std::fs::write(std::path::Path::new(&dir).join(format!("{name}.smt2")), &query)
                        .unwrap();
                }
                if diagnostics.place_translation_drop.get() != 0 {
                    failed.push((name, reasons));
                } else {
                    assert_native_memory_properties(&vc, name, expected);
                }
            }
            assert!(failed.is_empty(), "{failed:?}");
        },
    );
}

#[test]
fn unknown_numeric_reinterpreted_and_joined_addresses_keep_hard_refusal() {
    let source = format!(
        "#![allow(invalid_reference_casting)]\n{}",
        SOURCE.replace("#[kani::proof]", "")
    ) + r#"
        #[repr(packed)]struct WeakAlign(u32);
        impl Tag for WeakAlign{}
        impl Drop for WeakAlign {fn drop(&mut self){let pointer=&raw mut self.0;unsafe{*pointer=9;OBSERVED=*pointer;}}}
        pub fn weak_alignment_probe(){let _value:Box<dyn Tag>=Box::new(WeakAlign(19));}
        struct SharedCast(u32);
        impl Tag for SharedCast{}
        impl Drop for SharedCast {fn drop(&mut self){let shared=&self.0;let pointer=shared as *const u32 as *mut u32;unsafe{*pointer=9;OBSERVED=self.0;}}}
        pub fn shared_address_probe(){let _value:Box<dyn Tag>=Box::new(SharedCast(19));}
        struct Numeric(u64);
        impl Tag for Numeric{}
        impl Drop for Numeric {fn drop(&mut self){let pointer=self.0 as *mut u32;unsafe{OBSERVED=*pointer;}}}
        pub fn numeric_pointer_probe(){let _value:Box<dyn Tag>=Box::new(Numeric(0x0000000300000000));}
        struct ChangedView(u32);
        impl Tag for ChangedView{}
        impl Drop for ChangedView {fn drop(&mut self){let pointer=&raw mut self.0;let byte=pointer as *mut u8;unsafe{*byte=0;OBSERVED=self.0;}}}
        pub fn changed_view_probe(){let _value:Box<dyn Tag>=Box::new(ChangedView(19));}
        #[inline(never)]fn returned_address(value:&mut u32)->&mut u32{value}
        struct Joined {branch:bool, first:u32, second:u32}
        impl Tag for Joined{}
        impl Drop for Joined {fn drop(&mut self){let pointer=if self.branch{returned_address(&mut self.second)}else{&mut self.first};unsafe{OBSERVED=*pointer;}}}
        pub fn joined_address_probe(branch:bool){let _value:Box<dyn Tag>=Box::new(Joined{branch,first:1,second:2});}
    "#;
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
        &source,
        &["-Cpanic=abort"],
        |ctx| {
            for name in [
                "numeric_pointer_probe",
                "changed_view_probe",
                "joined_address_probe",
                "shared_address_probe",
                "weak_alignment_probe",
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
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                assert!(
                    diagnostics.place_translation_drop.get() > 0
                        && reasons.keys().any(|reason| reason.starts_with("native_drop_")),
                    "{name}: {reasons:?}"
                );
                for reason in reasons.keys().filter(|reason| reason.starts_with("native_drop_")) {
                    assert_eq!(
                        super::super::codegen_ctx::fallback_soundness(reason),
                        super::super::codegen_ctx::FallbackSoundness::FailClose,
                        "{reason}"
                    );
                }
            }
        },
    );
}
