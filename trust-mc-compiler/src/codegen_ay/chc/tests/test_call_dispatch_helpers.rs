// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Helper-local regression guards for `dispatch_helpers.rs` identity-call branches.
//!
//! Part of #4189: direct tests for the flattened-destination leaf-decomposition path
//! and the receiver-vtable preservation path.

#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use super::common::*;
use crate::codegen_ay::chc::call::dispatch_helpers::DispatchHelpers;
use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
use rustc_public::mir::TerminatorKind;

/// Build a `DispatchCallContext` for a Call terminator and invoke `callback`.
/// Returns how many matching calls were found.
fn with_detected_call(
    chc_ctx: &mut ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    detector: impl Fn(&ChcCtx<'_, '_>, &rustc_public::mir::Operand) -> bool,
    mut callback: impl FnMut(&mut ChcCtx<'_, '_>, &DispatchCallContext<'_>, usize),
) -> usize {
    let mut found = 0usize;
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        let TerminatorKind::Call { func, args, destination, target, .. } = &block.terminator.kind
        else {
            continue;
        };
        if !detector(chc_ctx, func) {
            continue;
        }
        let Some(target_bb) = *target else {
            continue;
        };
        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| ay_bindings::Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [ay_bindings::Expr::bool_const(true)];
        let modified_locals = HashSet::new();
        let target_opt = Some(target_bb);
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target: &target_opt,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
            callee_path: None,
        };
        callback(chc_ctx, &dcx, destination.local);
        found += 1;
    }
    found
}

fn rules_text_from(chc_ctx: &ChcCtx<'_, '_>, start: usize) -> String {
    chc_ctx.vc.rules[start..].iter().map(|r| format!("{r:?}")).collect::<Vec<_>>().join("\n")
}

// =============================================================================
// D1: Flattened-destination leaf-decomposition regression guard
// =============================================================================

const MANUALLY_DROP_DEREF_STRUCT_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::mem::ManuallyDrop;
    use std::ops::DerefMut;

    pub fn probe_manually_drop_deref_struct(
        md: &mut ManuallyDrop<(u32, u64)>,
    ) -> &mut (u32, u64) {
        <ManuallyDrop<(u32, u64)> as DerefMut>::deref_mut(md)
    }
"#;

/// D1: `emit_identity_call` on a flattened destination must constrain ALL leaves.
#[test]
fn test_identity_call_flattened_destination_constrains_all_leaves() {
    with_test_ay_ctx_for_source(MANUALLY_DROP_DEREF_STRUCT_SOURCE, |ctx| {
        let fn_name = "probe_manually_drop_deref_struct";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let found = with_detected_call(
            &mut chc_ctx,
            &body,
            |c, f| c.detect_manually_drop_deref_call(f),
            |chc_ctx, dcx, dest_local| {
                let before_fb = chc_ctx.sound_fallback_count();
                let before_rules = chc_ctx.vc.rules.len();

                let handled = chc_ctx.emit_identity_call(dcx, "test_identity", |ctx, d| {
                    d.args
                        .first()
                        .and_then(|a| ctx.translate_operand_with_modified(a, d.modified_locals))
                });
                assert!(handled);
                assert_eq!(chc_ctx.sound_fallback_count(), before_fb, "no fallback expected");
                assert!(chc_ctx.vc.rules.len() > before_rules, "should emit rules");

                assert_flattened_leaves_constrained(chc_ctx, dest_local, before_rules);
            },
        );
        assert!(found > 0, "expected ManuallyDrop::deref_mut call in MIR");
    });
}

fn assert_flattened_leaves_constrained(
    chc_ctx: &ChcCtx<'_, '_>,
    dest_local: usize,
    before_rules: usize,
) {
    if !chc_ctx.flatten.flattened_tuple_locals.contains(&dest_local) {
        return;
    }
    let field_count = chc_ctx.flattened_field_count(dest_local);
    assert!(field_count >= 2, "expected >=2 fields, got {field_count}");

    let dest_out_names: Vec<String> = chc_ctx
        .state_var_mgr
        .output_state_vars
        .iter()
        .filter(|(n, _)| n.starts_with(&format!("__local_{dest_local}_")) && n.ends_with("__out"))
        .map(|(n, _)| n.to_string())
        .collect();

    let text = rules_text_from(chc_ctx, before_rules);
    for name in &dest_out_names {
        assert!(text.contains(name), "output var '{name}' missing from rules:\n{text}");
    }
    if dest_out_names.len() >= 2 {
        let non_first = dest_out_names[1..].iter().any(|n| text.contains(n));
        assert!(non_first, "at least one non-first leaf must be constrained");
    }
}

// =============================================================================
// D2: Receiver-vtable preservation regression guard
// =============================================================================

const PIN_AS_MUT_DYN_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::pin::Pin;

    pub trait Identity {
        fn id(&self) -> u32;
    }

    struct Concrete { val: u32 }
    impl Identity for Concrete {
        fn id(&self) -> u32 { self.val }
    }

    pub fn probe_pin_as_mut_dyn<'a>(
        pin: &'a mut Pin<&'a mut dyn Identity>,
    ) -> Pin<&'a mut dyn Identity> {
        pin.as_mut()
    }
"#;

/// D2: `emit_identity_call_preserving_receiver_vtable` must attach `__vtable_sv_`.
#[test]
fn test_identity_call_vtable_preservation_attaches_constraint() {
    with_test_ay_ctx_for_source(PIN_AS_MUT_DYN_SOURCE, |ctx| {
        let fn_name = "probe_pin_as_mut_dyn";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let found = with_detected_call(
            &mut chc_ctx,
            &body,
            |c, f| c.detect_pin_as_mut_call(f),
            |chc_ctx, dcx, _dest_local| {
                let before_fb = chc_ctx.sound_fallback_count();
                let before_rules = chc_ctx.vc.rules.len();

                let handled = chc_ctx.emit_identity_call_preserving_receiver_vtable(
                    dcx,
                    "test_vtable_preserve",
                    |ctx: &mut ChcCtx<'_, '_>, d: &DispatchCallContext<'_>| {
                        d.args.first().and_then(|arg| {
                            ctx.resolve_ref_operand(arg, d.modified_locals).or_else(|| {
                                ctx.translate_operand_with_modified(arg, d.modified_locals)
                            })
                        })
                    },
                );
                assert!(handled);
                assert_eq!(chc_ctx.sound_fallback_count(), before_fb, "no fallback expected");
                assert!(chc_ctx.vc.rules.len() > before_rules, "should emit rules");

                let text = rules_text_from(chc_ctx, before_rules);
                assert!(
                    text.contains("__vtable_sv_"),
                    "vtable constraint missing from rules:\n{text}"
                );
            },
        );
        assert!(found > 0, "expected Pin::as_mut call in MIR");
    });
}
