// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_option_result::CallOptionResult;
use super::common::*;
use ay_bindings::{Expr, Sort};

const STRING_GET_MUT_UNWRAP_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::string::String;

    pub fn probe_string_get_mut_unwrap(buf: &mut String) -> usize {
        let s = buf.get_mut(..).unwrap();
        s.len()
    }
"#;

const DYN_OPTION_UNWRAP_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub trait Subscriber {
        fn process(&self) -> u32;
    }

    pub fn probe_dyn_option_unwrap(x: Option<&dyn Subscriber>) -> u32 {
        x.unwrap().process()
    }
"#;

fn with_option_unwrap_dispatch(
    mut body: impl FnMut(&mut ChcCtx<'_, '_>, usize, usize, &ChcCallContext<'_>) + Send,
) {
    with_test_ay_ctx_for_source(STRING_GET_MUT_UNWRAP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_get_mut_unwrap");
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &mir_body, "probe_string_get_mut_unwrap", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, args, destination, target) = mir_body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                let rustc_public::mir::TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target: Some(target),
                    ..
                } = &block.terminator.kind
                else {
                    return None;
                };
                (chc_ctx.detect_stub_matching(func, |stub| stub == StubKind::OptionUnwrap)
                    == Some(StubKind::OptionUnwrap))
                .then(|| (bb_idx, args.clone(), destination.clone(), *target))
            })
            .expect("expected Option::unwrap call terminator");

        let option_local = match args.first() {
            Some(Operand::Copy(place) | Operand::Move(place)) if place.projection.is_empty() => {
                place.local
            }
            other => panic!("expected unwrap self operand to be a plain local, got {other:?}"),
        };

        let (stmt_constraints, _output_args, modified_locals, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(bb_idx));
        let cx = ChcCallContext {
            stub: StubKind::OptionUnwrap,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };

        body(&mut chc_ctx, option_local, destination.local, &cx);
    });
}

fn with_dyn_option_unwrap_dispatch(
    mut body: impl FnMut(&mut ChcCtx<'_, '_>, usize, usize, &ChcCallContext<'_>) + Send,
) {
    with_test_ay_ctx_for_source(DYN_OPTION_UNWRAP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dyn_option_unwrap");
        let mir_body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &mir_body, "probe_dyn_option_unwrap", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, args, destination, target) = mir_body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                let rustc_public::mir::TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target: Some(target),
                    ..
                } = &block.terminator.kind
                else {
                    return None;
                };
                (chc_ctx.detect_stub_matching(func, |stub| stub == StubKind::OptionUnwrap)
                    == Some(StubKind::OptionUnwrap))
                .then(|| (bb_idx, args.clone(), destination.clone(), *target))
            })
            .expect("expected Option::unwrap call terminator");

        let option_local = match args.first() {
            Some(Operand::Copy(place) | Operand::Move(place)) if place.projection.is_empty() => {
                place.local
            }
            other => panic!("expected unwrap self operand to be a plain local, got {other:?}"),
        };

        let (stmt_constraints, _output_args, modified_locals, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(bb_idx));
        let cx = ChcCallContext {
            stub: StubKind::OptionUnwrap,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };

        body(&mut chc_ctx, option_local, destination.local, &cx);
    });
}

fn seed_option_local_metadata(
    chc_ctx: &mut ChcCtx<'_, '_>,
    option_local: usize,
) -> (Expr, Expr, Expr, Expr) {
    let backing = Expr::const_array(Sort::bitvec(POINTER_WIDTH), Expr::bitvec_const(0u64, 8))
        .store(Expr::bitvec_const(3u64, POINTER_WIDTH), Expr::bitvec_const(65u64, 8))
        .store(Expr::bitvec_const(4u64, POINTER_WIDTH), Expr::bitvec_const(66u64, 8));
    let slice_view = Expr::bool_const(true);
    let len = Expr::bitvec_const(2u64, POINTER_WIDTH);
    let offset = Expr::bitvec_const(3u64, POINTER_WIDTH);

    chc_ctx
        .ref_resolution
        .ref_targets
        .insert(option_local, RefTarget::with_projections(777, vec![]));
    chc_ctx.ref_resolution.const_ref_values.insert(option_local, backing.clone());
    chc_ctx.ref_resolution.const_ref_slice_views.insert(option_local, slice_view.clone());
    chc_ctx.ref_resolution.subslice_len.insert(option_local, len.clone());
    chc_ctx.ref_resolution.subslice_offset.insert(option_local, offset.clone());

    (backing, slice_view, len, offset)
}

fn assert_unwrap_dest_metadata(
    chc_ctx: &ChcCtx<'_, '_>,
    dest_local: usize,
    backing: &Expr,
    slice_view: &Expr,
    len: &Expr,
    offset: &Expr,
) {
    let actual_ref_target = chc_ctx
        .ref_resolution
        .ref_targets
        .get(&dest_local)
        .expect("unwrap destination should keep ref_targets");
    assert_eq!(
        actual_ref_target.local, 777,
        "Option::unwrap should preserve the option local's referent"
    );
    assert!(
        chc_ctx.ref_resolution.call_forwarded_raw_ptrs.contains(&dest_local),
        "Option::unwrap should keep the unwrapped ref in the forwarded-ptr set"
    );

    let actual_backing = chc_ctx
        .ref_resolution
        .const_ref_values
        .get(&dest_local)
        .expect("unwrap destination should preserve backing metadata");
    assert_eq!(
        actual_backing.to_string(),
        backing.to_string(),
        "Option::unwrap should preserve backing array metadata"
    );

    let actual_slice_view = chc_ctx
        .ref_resolution
        .const_ref_slice_views
        .get(&dest_local)
        .expect("unwrap destination should preserve slice view metadata");
    assert_eq!(
        actual_slice_view.to_string(),
        slice_view.to_string(),
        "Option::unwrap should preserve const_ref_slice_views"
    );

    let actual_len = chc_ctx
        .ref_resolution
        .subslice_len
        .get(&dest_local)
        .expect("unwrap destination should preserve subslice_len");
    assert_eq!(
        actual_len.to_string(),
        len.to_string(),
        "Option::unwrap should preserve subslice_len"
    );

    let actual_offset = chc_ctx
        .ref_resolution
        .subslice_offset
        .get(&dest_local)
        .expect("unwrap destination should preserve subslice_offset");
    assert_eq!(
        actual_offset.to_string(),
        offset.to_string(),
        "Option::unwrap should preserve subslice_offset"
    );
}

#[test]
fn test_option_unwrap_propagates_string_get_mut_metadata_bundle() {
    with_option_unwrap_dispatch(|chc_ctx, option_local, dest_local, cx| {
        let (backing, slice_view, len, offset) = seed_option_local_metadata(chc_ctx, option_local);
        assert!(
            !chc_ctx.ref_resolution.const_ref_values.contains_key(&dest_local),
            "precondition: unwrap destination should start without backing metadata"
        );

        let before_rules = chc_ctx.vc.rules.len();
        chc_ctx.codegen_call_unwrap_expect(cx);
        assert!(
            chc_ctx.vc.rules.len() > before_rules,
            "Option::unwrap should emit at least one transition rule"
        );

        assert_unwrap_dest_metadata(chc_ctx, dest_local, &backing, &slice_view, &len, &offset);
    });
}

#[test]
fn test_option_unwrap_propagates_dyn_vtable_metadata() {
    with_dyn_option_unwrap_dispatch(|chc_ctx, option_local, dest_local, cx| {
        let expected_vtable = Expr::bitvec_const(17u128, POINTER_WIDTH);
        let stale_vtable = Expr::bitvec_const(99u128, POINTER_WIDTH);
        chc_ctx.dyn_vtable_ids.insert(option_local, expected_vtable.clone());
        chc_ctx.dyn_vtable_ids.insert(dest_local, stale_vtable);

        let before_rules = chc_ctx.vc.rules.len();
        let before_fallback = chc_ctx.sound_fallback_count();
        chc_ctx.codegen_call_unwrap_expect(cx);
        assert!(
            chc_ctx.vc.rules.len() > before_rules,
            "Option::unwrap should emit at least one transition rule"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_fallback,
            "vtable propagation through Option::unwrap should not introduce fallback"
        );

        let actual = chc_ctx
            .dyn_vtable_ids
            .get(&dest_local)
            .expect("unwrap destination should inherit dyn vtable metadata");
        assert_eq!(
            actual.to_string(),
            expected_vtable.to_string(),
            "Option::unwrap should propagate wrapper-side dyn vtable metadata to the unwrapped local"
        );
    });
}
