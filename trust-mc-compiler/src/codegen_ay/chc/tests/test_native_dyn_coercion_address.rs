// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A native Box coercion retains its allocation address, not its payload bits.

use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};

const SOURCE: &str =
    include_str!("../../../../../tools/soundness-duals/native_trait_dispatch_owner_dual.rs");

#[test]
fn actual_native_dyn_coercion_preserves_strict_source_and_bound_polarity() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    // Keep all input bytes symbolic using the same marked AnyModel/AnyRawHook
    // boundary as the native Box compiler controls. No raw hook runs natively.
    let source = SOURCE.replace("#[kani::proof]", "").replace(
        "#![allow(dead_code)]",
        r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]
        mod kani {
            #[kanitool::fn_marker = "AnyModel"]
            pub fn any<T>() -> T { any_raw() }
            #[kanitool::fn_marker = "AnyRawHook"]
            fn any_raw<T>() -> T { panic!("model-only raw hook") }
        }
        "#,
    );
    with_native_box_ctx(&source, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        for name in [
            "native_trait_dispatch_safe",
            "native_trait_dispatch_bug",
            "native_trait_copied_owner_safe",
            "native_trait_copied_owner_bug",
            "native_trait_pointer_oob_bug",
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let mut pass = FunctionInlinePass::new(InlineConfig {
                max_depth: 32,
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
            let (vc, _, diagnostics) =
                ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
            assert_eq!(diagnostics.place_translation_drop.get(), 0, "{name}");
            assert!(vc.approximation_identity_complete, "{name}: complete identity accounting");
            let query = crate::codegen_ay::emit_chc(&vc).to_string();
            if let Some(directory) = std::env::var_os("MC_NATIVE_DYN_ADDRESS_ARTIFACT_DIR") {
                std::fs::write(
                    std::path::Path::new(&directory).join(format!("{name}.smt2")),
                    &query,
                )
                .unwrap();
            }
            let aggregate = ay_chc::ChcParser::parse(&query).unwrap();
            let obligations = aggregate.query_obligations().unwrap();
            assert!(!obligations.is_empty(), "{name}: preserve every actual obligation");
            let mut unsafe_rows = Vec::new();
            let mut unresolved = Vec::new();
            for obligation in obligations {
                let (id, mut problem) = obligation.into_parts();
                problem.expand_nullary_fail_queries(false);
                let verdict =
                    ay_chc::AdaptivePortfolio::new(problem, ay_adaptive_config_with_timeout(30))
                        .solve();
                match verdict {
                    ay_chc::VerifiedChcResult::Safe(_) => {}
                    ay_chc::VerifiedChcResult::Unsafe(_) => {
                        let property = vc.properties.iter().find(|p| p.relation == id.label());
                        if let Some(property) = property {
                            assert_eq!(
                                property.approximation_dependent,
                                Some(false),
                                "{name}: a labelled refutation must be independent"
                            );
                        } else {
                            // Direct source-error definitions are actual AY
                            // queries without a labelled VC property. Their
                            // source provenance and absence of any approximation
                            // must both be established before accepting Unsafe.
                            assert_eq!(vc.accounted_approximations, 0, "{name}");
                            assert!(vc.approximated_vars.is_empty(), "{name}");
                            assert_eq!(diagnostics.sound_havoc_drop.get(), 0, "{name}");
                            let source_query = &aggregate.clauses()[id.query_clause_index()];
                            assert!(source_query.is_query(), "{name}: actual source query");
                            if let Some(index) = id.defining_clause_index() {
                                let definition = &aggregate.clauses()[index];
                                let marker = definition.head.predicate_id().unwrap();
                                assert_eq!(
                                    source_query.body.predicates,
                                    vec![(marker, Vec::new())],
                                    "{name}: exact original nullary marker definition"
                                );
                                assert!(source_query.body.constraint.is_none(), "{name}");
                            }
                            eprintln!("NATIVE_DYN_ADDRESS_SOURCE {name}: {}", id.label());
                        }
                        unsafe_rows.push(id.label().to_owned());
                    }
                    _ => unresolved.push(id.label().to_owned()),
                }
            }
            eprintln!(
                "NATIVE_DYN_ADDRESS {name}: unsafe={unsafe_rows:?} unresolved={unresolved:?}"
            );
            assert!(unresolved.is_empty(), "{name}: every original obligation stays strict");
            assert_eq!(unsafe_rows.is_empty(), name.ends_with("_safe"), "{name}");
        }
    });
}
