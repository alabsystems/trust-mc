// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rc NonNull ordering + from_inner_in regression tests.
//! Extracted from test_call_dispatch_misc_pointer_wrappers.rs for file-size limit.

#![allow(clippy::unwrap_used)]
use std::collections::HashSet;

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::codegen_call_dispatch_misc::CallDispatchMisc;
use crate::codegen_ay::emit_chc;
use ay_bindings::Expr;
use rustc_public::mir::TerminatorKind;
use trust_mc_core::chc::RelationApp;

pub(super) const RC_DYN_COERCE_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::ops::Deref;
    use std::rc::Rc;

    pub trait Identity {
        fn id(&self) -> u16;
    }

    pub struct Outer<T: ?Sized> {
        pub outer_id: u8,
        pub inner: T,
    }

    pub struct Inner {
        pub id: u8,
    }

    impl<T> Identity for Outer<T>
    where
        T: ?Sized + Identity,
    {
        fn id(&self) -> u16 {
            ((self.outer_id as u16) << 8) + (self.inner.id() as u16)
        }
    }

    impl Identity for Inner {
        fn id(&self) -> u16 {
            self.id.into()
        }
    }

    pub fn id_from_coerce<T>(identity: T) -> u16
    where
        T: Deref<Target = dyn Identity>,
    {
        identity.id()
    }

    pub fn probe_rc_dyn_dispatch(outer_id: u8, inner_id: u8) -> u16 {
        let outer: Rc<dyn Identity> = Rc::new(Outer { inner: Inner { id: inner_id }, outer_id });
        id_from_coerce(outer)
    }
"#;

const RC_NONNULL_ORDERING_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::rc::Rc;

    pub fn probe_rc_nonnull_ordering() -> Rc<u32> {
        Rc::new(42u32)
    }
"#;

fn dispatch_nonnull_and_check_alloc_id(
    chc_ctx: &mut ChcCtx<'_, '_>,
    bb_idx: usize,
    block: &rustc_public::mir::BasicBlock,
) -> bool {
    let TerminatorKind::Call { func, args, destination, target, .. } = &block.terminator.kind
    else {
        return false;
    };
    let Some(callee_path) = chc_ctx.resolve_callee_path(func) else {
        return false;
    };
    if !(callee_path.contains("NonNull") && callee_path.contains("new")) {
        return false;
    }
    let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
    let output_args: Vec<_> = chc_ctx
        .state_var_mgr
        .state_vars
        .iter()
        .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
        .collect();
    let from_app = RelationApp::new(&from_rel, output_args);
    let stmt_constraints = [Expr::bool_const(true)];
    let modified_locals = HashSet::new();
    let Some(target_bb) = *target else {
        return true;
    };
    let target_opt = Some(target_bb);

    let seeded_obj_id =
        super::test_call_dispatch_misc_box_wrappers::seed_box_alloc_id(chc_ctx, args, bb_idx);
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

    assert!(
        chc_ctx.try_dispatch_call_misc(&dcx),
        "NonNull::new should be handled by misc dispatch"
    );

    if let Some(expected_id) = seeded_obj_id {
        assert_eq!(
            chc_ctx.known_alloc_ids.get(&destination.local).copied(),
            Some(expected_id),
            "NonNull::new must propagate alloc_id (route table ordering invariant)"
        );
    }
    true
}

#[test]
fn test_nonnull_new_route_propagates_alloc_id() {
    with_test_ay_ctx_for_source(RC_NONNULL_ORDERING_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_nonnull_ordering");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_rc_nonnull_ordering", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = 0usize;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if dispatch_nonnull_and_check_alloc_id(&mut chc_ctx, bb_idx, block) {
                found += 1;
            }
        }
        let _ = found;
    });
}

fn with_each_from_inner_in_call_for_source(
    source: &str,
    fn_suffix: &str,
    mut body_fn: impl FnMut(
        &mut ChcCtx<'_, '_>,
        usize,
        rustc_public::mir::Operand,
        Vec<rustc_public::mir::Operand>,
        rustc_public::mir::Place,
        usize,
        RelationApp,
    ) + Send,
) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_suffix, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found = 0usize;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(callee_path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            let Some(target_bb) = *target else {
                continue;
            };
            // Part of #3959: Match both `::from_inner_in` and `::from_inner`.
            if !ChcCtx::is_shared_pointer_wrapper_constructor_path(&callee_path) {
                continue;
            }
            found += 1;
            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            body_fn(
                &mut chc_ctx,
                bb_idx,
                func.clone(),
                args.clone(),
                destination.clone(),
                target_bb,
                from_app,
            );
        }
        let _ = found;
    });
}

fn with_each_from_inner_in_call(
    body_fn: impl FnMut(
        &mut ChcCtx<'_, '_>,
        usize,
        rustc_public::mir::Operand,
        Vec<rustc_public::mir::Operand>,
        rustc_public::mir::Place,
        usize,
        RelationApp,
    ) + Send,
) {
    with_each_from_inner_in_call_for_source(
        RC_NONNULL_ORDERING_SOURCE,
        "probe_rc_nonnull_ordering",
        body_fn,
    );
}

#[test]
fn test_from_inner_in_clears_stale_alloc_id_when_source_is_untracked() {
    with_each_from_inner_in_call(
        |chc_ctx, bb_idx, func, args, destination, target_bb, from_app| {
            let stmt_constraints = [Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = Some(target_bb);

            chc_ctx.known_alloc_ids.clear();
            chc_ctx.known_alloc_ids.insert(destination.local, 0xD00D_u32);

            let dcx = DispatchCallContext {
                bb_idx,
                func: &func,
                args: &args,
                destination: &destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: None,
            };

            assert!(
                chc_ctx.try_dispatch_call_misc(&dcx),
                "Rc::from_inner_in should be handled by misc dispatch"
            );
            assert!(
                !chc_ctx.known_alloc_ids.contains_key(&destination.local),
                "from_inner_in must clear stale alloc_id when source is untracked"
            );
        },
    );
}

#[test]
fn test_from_inner_in_coercion_fallback_clears_alloc_id() {
    with_each_from_inner_in_call(
        |chc_ctx, bb_idx, func, args, destination, target_bb, from_app| {
            let stmt_constraints = [Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = Some(target_bb);
            let src_local =
                match args.first() {
                    Some(
                        rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p),
                    ) if p.projection.is_empty() => p.local,
                    other => panic!("expected direct from_inner_in source local, got {other:?}"),
                };
            let dest_local = destination.local;
            let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
            chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 =
                ay_bindings::Sort::array(ay_bindings::Sort::int(), ay_bindings::Sort::int());

            chc_ctx.known_alloc_ids.clear();
            chc_ctx.known_alloc_ids.insert(src_local, 0xABCD_u32);
            chc_ctx.known_alloc_ids.insert(dest_local, 0xD00D_u32);
            let before_fallback = chc_ctx.sound_fallback_count();

            let dcx = DispatchCallContext {
                bb_idx,
                func: &func,
                args: &args,
                destination: &destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: None,
            };

            assert!(
                chc_ctx.try_dispatch_call_misc(&dcx),
                "Rc::from_inner_in should be handled by misc dispatch"
            );
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                before_fallback + 1,
                "from_inner_in coercion failure must record a sound fallback"
            );
            assert!(
                !chc_ctx.known_alloc_ids.contains_key(&dest_local),
                "from_inner_in fallback must clear destination alloc_id state"
            );
        },
    );
}

fn assert_from_inner_in_fallback_clears_stale_vtable_tracking(
    chc_ctx: &mut ChcCtx<'_, '_>,
    bb_idx: usize,
    func: rustc_public::mir::Operand,
    args: Vec<rustc_public::mir::Operand>,
    destination: rustc_public::mir::Place,
    target_bb: usize,
    from_app: RelationApp,
) {
    let dest_local = destination.local;
    let (vtable_in, vtable_out) = chc_ctx.get_or_create_vtable_state_var(dest_local);
    let stmt_constraints = [Expr::bool_const(true)];
    let modified_locals = HashSet::new();
    let target_opt = Some(target_bb);
    let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
    chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 =
        ay_bindings::Sort::array(ay_bindings::Sort::int(), ay_bindings::Sort::int());

    let vtable_state_idx = chc_ctx
        .state_var_index_by_name(&vtable_in)
        .expect("vtable input state var should be declared");
    chc_ctx.dyn_vtable_ids.insert(
        dest_local,
        Expr::bitvec_const(0xC0DE_u32, crate::codegen_ay::types::POINTER_WIDTH),
    );
    assert!(
        !chc_ctx.encode.modified_state_indices.contains(&vtable_state_idx),
        "precondition: vtable state should start unmodified"
    );
    let before_fallback = chc_ctx.sound_fallback_count();

    let dcx = DispatchCallContext {
        bb_idx,
        func: &func,
        args: &args,
        destination: &destination,
        target: &target_opt,
        from_app: &from_app,
        stmt_constraints: &stmt_constraints,
        modified_locals: &modified_locals,
        callee_path: None,
    };

    assert!(
        chc_ctx.try_dispatch_call_misc(&dcx),
        "Rc::from_inner_in should be handled by misc dispatch"
    );
    assert_eq!(
        chc_ctx.sound_fallback_count(),
        before_fallback + 1,
        "from_inner_in coercion failure must record a sound fallback"
    );
    assert!(!chc_ctx.dyn_vtable_ids.contains_key(&dest_local));
    assert!(chc_ctx.encode.modified_state_indices.contains(&vtable_state_idx));

    let rule = chc_ctx.vc.rules.last().expect("from_inner_in should emit one rule");
    let head_arg =
        rule.head.args.get(vtable_state_idx).expect("vtable state slot should exist in rule head");
    if let ay_bindings::ExprValue::Var { name } = head_arg.value() {
        assert_eq!(name.as_str(), &*vtable_out);
    } else {
        panic!("expected vtable head arg variable, got {:?}", head_arg.value());
    }
}

#[test]
fn test_from_inner_in_coercion_fallback_clears_stale_vtable_tracking() {
    with_each_from_inner_in_call_for_source(
        RC_DYN_COERCE_SOURCE,
        "probe_rc_dyn_dispatch",
        assert_from_inner_in_fallback_clears_stale_vtable_tracking,
    );
}

#[test]
fn test_is_shared_pointer_wrapper_constructor_path_recognizes_from_inner() {
    // `::from_inner` (no allocator) must be recognized
    assert!(ChcCtx::is_shared_pointer_wrapper_constructor_path("std::rc::Rc::<Table>::from_inner"));
    assert!(ChcCtx::is_shared_pointer_wrapper_constructor_path(
        "std::sync::Arc::<dyn Furniture>::from_inner"
    ));
    // `::from_inner_in` (with allocator) must still be recognized
    assert!(ChcCtx::is_shared_pointer_wrapper_constructor_path(
        "std::rc::Rc::<Table, std::alloc::Global>::from_inner_in"
    ));
    // Unrelated paths must not match
    assert!(!ChcCtx::is_shared_pointer_wrapper_constructor_path("std::vec::Vec::<u8>::from_inner"));
    assert!(!ChcCtx::is_shared_pointer_wrapper_constructor_path("std::rc::Rc::<Table>::deref"));
}

/// MIR-backed regression: exercises Rc shared-pointer constructor dispatch
/// through `try_dispatch_call_misc()`. Uses the dyn coercion source where
/// `from_inner_in` is known to appear in MIR. Verifies that the widened
/// `is_shared_pointer_wrapper_constructor_path()` correctly routes both
/// `::from_inner` and `::from_inner_in` variants when present.
#[test]
fn test_from_inner_constructor_dispatched_by_misc_handler() {
    with_each_from_inner_in_call_for_source(
        RC_DYN_COERCE_SOURCE,
        "probe_rc_dyn_dispatch",
        |chc_ctx, bb_idx, func, args, destination, target_bb, from_app| {
            let stmt_constraints = [Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = Some(target_bb);

            super::test_call_dispatch_misc_box_wrappers::seed_box_alloc_id(chc_ctx, &args, bb_idx);

            let dcx = DispatchCallContext {
                bb_idx,
                func: &func,
                args: &args,
                destination: &destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: None,
            };

            assert!(
                chc_ctx.try_dispatch_call_misc(&dcx),
                "Rc constructor (from_inner/from_inner_in) must be handled by misc dispatch"
            );
        },
    );
}

#[test]
fn test_codegen_pointer_wrapper_from_inner_in_preserves_alloc_id_and_vtable_on_success() {
    with_each_from_inner_in_call_for_source(
        RC_DYN_COERCE_SOURCE,
        "probe_rc_dyn_dispatch",
        |chc_ctx, bb_idx, func, args, destination, target_bb, from_app| {
            let stmt_constraints = [Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let target_opt = Some(target_bb);
            let seeded_obj_id = super::test_call_dispatch_misc_box_wrappers::seed_box_alloc_id(
                chc_ctx, &args, bb_idx,
            )
            .expect("expected direct from_inner_in source local");

            let dcx = DispatchCallContext {
                bb_idx,
                func: &func,
                args: &args,
                destination: &destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: None,
            };

            chc_ctx.codegen_pointer_wrapper_from_inner_in(&dcx);

            assert_eq!(
                chc_ctx.known_alloc_ids.get(&destination.local).copied(),
                Some(seeded_obj_id),
                "from_inner_in success should preserve the source allocation identity on the destination"
            );
            assert!(
                chc_ctx.dyn_vtable_ids.contains_key(&destination.local),
                "from_inner_in on Rc<dyn Trait> should register destination vtable tracking"
            );

            let rule = chc_ctx.vc.rules.last().expect("from_inner_in should emit one rule");
            assert_ne!(rule.head.name, "error", "from_inner_in success must stay on the goto path");

            let smt = emit_chc(&chc_ctx.vc).to_string();
            assert!(
                smt.contains("__vtable_sv_"),
                "from_inner_in success should capture dyn vtable state. SMT prefix: {}",
                &smt[..smt.len().min(1200)]
            );
            assert!(
                smt.contains("bvadd") || smt.contains("BvAdd"),
                "from_inner_in success should offset the Rc pointer past the header. SMT prefix: {}",
                &smt[..smt.len().min(1200)]
            );
        },
    );
}
