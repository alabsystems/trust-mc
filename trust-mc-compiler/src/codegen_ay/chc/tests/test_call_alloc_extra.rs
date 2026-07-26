// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for codegen_call_alloc_extra — non-layout allocation path extras.
//!
//! Covers: alloc smoke, diverging HandleAllocError, display_cow string-length
//! propagation, Alignment::new, Alignment::as_usize, LayoutMaxSizeForAlign.
//!
//! Extracted from test_call_misc.rs (Part of #3746).

#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use super::common::*;
use super::test_call_alloc_layout_helpers::with_misc_usize_call_scaffold;
use crate::codegen_ay::chc::chc_call_context::ChcCallContext;

// =============================================================================
// Alloc-extra smoke tests
// =============================================================================

/// HandleAllocError is diverging (no successor emitted). Box::new with a large
/// type may generate the alloc error path.
#[test]
fn test_alloc_extra_via_box() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_alloc_extra() -> Box<[u32; 100]> {
            Box::new([0u32; 100])
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_alloc_extra");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_alloc_extra",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut has_alloc_extra = false;
        let mut alloc_extra_candidate_calls = 0usize;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                if let Some(callee_path) = chc_ctx.resolve_callee_path(func)
                    && let Some(stub) = chc_ctx.stub_registry.lookup(&callee_path)
                    && stub.is_alloc_extra()
                {
                    alloc_extra_candidate_calls += 1;
                }
                if chc_ctx.detect_stub_matching(func, StubKind::is_alloc_extra).is_some() {
                    has_alloc_extra = true;
                }
            }
        }
        assert!(
            alloc_extra_candidate_calls == 0 || has_alloc_extra,
            "Found {alloc_extra_candidate_calls} alloc-extra candidate call(s) but none detected"
        );

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_alloc_extra",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_alloc_extra", body.blocks.len());
        // Semantic: Box::new for large array should produce constrained rules
        let constrained_rules = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some() && !r.body.constraints.is_empty())
            .count();
        assert!(
            constrained_rules >= 1,
            "Box::new alloc extra should produce constrained rules, got {constrained_rules}"
        );
    });
}

/// RustNoAllocShimIsUnstable is a no-op signal. Vec operations may trigger it.
#[test]
fn test_alloc_extra_noop_shim() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_noop_alloc() -> Vec<u8> {
            let mut v = Vec::with_capacity(16);
            v.push(1);
            v.push(2);
            v
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_noop_alloc");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_noop_alloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_noop_alloc", body.blocks.len());

        // Should complete without panic; alloc shim is no-op
        assert!(
            !vc.rules.is_empty(),
            "alloc noop shim pipeline should produce at least some rules"
        );
    });
}

// =============================================================================
// Unit-level alloc-extra call tests (via scaffold)
// =============================================================================

/// HandleAllocError is diverging and must not emit a successor transition rule.
#[test]
fn test_alloc_extra_handle_alloc_error_emits_no_successor_rule() {
    with_misc_usize_call_scaffold(
        |chc_ctx, _func, _args, destination, target, from_app, sc, ml| {
            let before_rules = chc_ctx.vc.rules.len();

            let cx = ChcCallContext {
                stub: StubKind::HandleAllocError,
                args: &[],
                destination,
                target,
                from_app,
                stmt_constraints: sc,
                modified_locals: ml,
            };
            chc_ctx.codegen_call_alloc_extra_impl(0, &cx);

            assert_eq!(
                chc_ctx.vc.rules.len(),
                before_rules,
                "HandleAllocError should be diverging and emit no successor rule"
            );
        },
    );
}

/// Cow<str>::to_string should seed the destination String's tracked length so
/// downstream String::len reads a concrete value instead of a fresh symbolic BV.
#[test]
fn test_display_cow_propagates_destination_string_length() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::borrow::Cow;

        pub fn probe_display_cow_len() -> usize {
            let cow: Cow<str> = Cow::Borrowed("hello");
            let s = cow.to_string();
            s.len()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_display_cow_len");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_display_cow_len", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_display_cow)
            {
                call_site = Some((bb_idx, stub, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, stub, args, destination, target) =
            call_site.expect("expected Cow::to_string call in MIR");

        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let before_rules = chc_ctx.vc.rules.len();
        let before_state_vars = chc_ctx.state_var_mgr.state_vars.len();
        let modified_locals = HashSet::new();
        let len_var_before = chc_ctx.collections.len_state.get_len_var(destination.local).cloned();

        let cx = ChcCallContext {
            stub,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_display_cow(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one transition rule");
        assert_eq!(
            chc_ctx.state_var_mgr.state_vars.len(),
            before_state_vars,
            "Cow::to_string should reuse the predeclared String len state, not late-declare one"
        );
        let len_var_name =
            len_var_before.expect("destination String should already have a tracked len state");
        let len_out_name = crate::codegen_ay::names::out_name(&len_var_name);
        let rule = chc_ctx.vc.rules.last().expect("expected emitted Cow::to_string rule");
        assert!(
            rule.body.constraints.iter().any(|constraint| {
                let rendered = constraint.to_string();
                rendered.contains(&len_out_name) && rendered.contains("#x0000000000000005")
            }),
            "Cow::to_string should constrain the destination len to the borrowed string length"
        );
        assert!(
            chc_ctx.ref_resolution.const_ref_values.contains_key(&destination.local),
            "Cow::to_string should seed String backing metadata for downstream string stubs"
        );
    });
}

/// Alignment::new encoding should produce an Option-shape ITE constraint when
/// destination sort is Option<usize>.
#[test]
fn test_alloc_extra_alignment_new_emits_option_ite_constraint() {
    with_misc_usize_call_scaffold(|chc_ctx, _func, args, destination, target, from_app, sc, ml| {
        assert!(!args.is_empty(), "scaffold call must provide one argument");
        let dest_idx = chc_ctx.state_idx_for_local(destination.local);
        chc_ctx.state_var_mgr.output_state_vars[dest_idx].1 = option_datatype_sort(
            ay_bindings::Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH),
        );

        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::AlignmentNew,
            args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_alloc_extra_impl(0, &cx);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "AlignmentNew should emit one transition rule"
        );

        let rule = chc_ctx.vc.rules.last().expect("expected emitted AlignmentNew rule");
        assert!(
            rule.body.constraints.len() > sc.len(),
            "AlignmentNew option path should add semantic constraints beyond stmt constraints"
        );

        let has_option_ite = rule.body.constraints.iter().any(|constraint| {
            constraint_tree_contains(constraint, &|expr| {
                matches!(
                    expr.value(),
                    ExprValue::Ite { then_expr, else_expr, .. }
                        if matches!(
                            then_expr.value(),
                            ExprValue::DatatypeConstructor { constructor_name, .. }
                                if names::is_some_constructor(constructor_name)
                        ) && matches!(
                            else_expr.value(),
                            ExprValue::DatatypeConstructor { constructor_name, .. }
                                if names::is_none_constructor(constructor_name)
                        )
                )
            })
        });
        assert!(
            has_option_ite,
            "AlignmentNew should encode Option result via ite(valid, Some(x), None)"
        );
    });
}

/// Alignment::as_usize should preserve value flow by emitting an equality
/// constraint on the destination local.
#[test]
fn test_alloc_extra_alignment_as_usize_emits_equality_constraint() {
    with_misc_usize_call_scaffold(|chc_ctx, _func, args, destination, target, from_app, sc, ml| {
        assert!(!args.is_empty(), "scaffold call must provide one argument");
        let before_rules = chc_ctx.vc.rules.len();

        let cx = ChcCallContext {
            stub: StubKind::AlignmentAsUsize,
            args,
            destination,
            target,
            from_app,
            stmt_constraints: sc,
            modified_locals: ml,
        };
        chc_ctx.codegen_call_alloc_extra_impl(0, &cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one transition rule");
        let rule = chc_ctx.vc.rules.last().expect("expected emitted AlignmentAsUsize rule");
        assert!(
            rule.body.constraints.len() > sc.len(),
            "AlignmentAsUsize should add an equality constraint"
        );
        let has_eq = rule.body.constraints.iter().any(|constraint| {
            constraint_tree_contains(constraint, &|expr| {
                matches!(expr.value(), ExprValue::Eq(_, _))
            })
        });
        assert!(has_eq, "AlignmentAsUsize path should include an Eq constraint");
    });
}

/// Layout::max_size_for_align helper should constrain destination to `u64::MAX`.
#[test]
fn test_alloc_extra_layout_max_size_for_align_emits_u64_max_constraint() {
    with_misc_usize_call_scaffold(
        |chc_ctx, _func, _args, destination, target, from_app, sc, ml| {
            let before_rules = chc_ctx.vc.rules.len();

            let cx = ChcCallContext {
                stub: StubKind::LayoutMaxSizeForAlign,
                args: &[],
                destination,
                target,
                from_app,
                stmt_constraints: sc,
                modified_locals: ml,
            };
            chc_ctx.codegen_call_alloc_extra_impl(0, &cx);

            assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one transition rule");
            let rule =
                chc_ctx.vc.rules.last().expect("expected emitted LayoutMaxSizeForAlign rule");
            assert!(
                rule.body.constraints.len() > sc.len(),
                "LayoutMaxSizeForAlign should add a max-size equality constraint"
            );

            let max_u64_text = u64::MAX.to_string();
            let has_max_const = rule.body.constraints.iter().any(|constraint| {
                constraint_tree_contains(constraint, &|expr| {
                    matches!(
                        expr.value(),
                        ExprValue::BitVecConst { value, width }
                            if *width == crate::codegen_ay::types::POINTER_WIDTH
                                && value.to_string() == max_u64_text
                    )
                })
            });
            assert!(
                has_max_const,
                "LayoutMaxSizeForAlign should constrain destination using bv64::MAX"
            );
        },
    );
}
