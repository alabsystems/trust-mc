// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rc pointer-wrapper misc-dispatch regression tests.
//!
//! Split from `test_call_dispatch_misc_pointer_wrappers.rs` (D4 of #4010).
//! Covers: Rc::deref concrete value-field pointer materialization and
//! Rc wrapper inferable-summary avoidance.

#![allow(clippy::unwrap_used)]

use num_bigint::BigInt;

use super::common::*;
use super::test_call_dispatch_misc_pointer_wrapper_common::assert_source_has_no_inferable_summaries;
use super::test_call_dispatch_rc_from_inner::RC_DYN_COERCE_SOURCE;
use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::codegen_call_dispatch_misc::CallDispatchMisc;
use crate::codegen_ay::emit_chc;
use ay_bindings::{Expr, ExprValue};

const RC_DEREF_DISPATCH_SOURCE: &str = r#"
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

    #[inline(never)]
    pub fn probe_rc_deref_dispatch(outer_id: u8, inner_id: u8) -> u16 {
        let ptr: Rc<dyn Identity> =
            Rc::new(Outer { inner: Inner { id: inner_id }, outer_id });
        let identity: &dyn Identity = <Rc<dyn Identity> as Deref>::deref(&ptr);
        identity.id()
    }
"#;

fn with_rc_deref_dispatch_call(
    body_fn: impl FnOnce(
        &mut ChcCtx<'_, '_>,
        rustc_public::mir::Operand,
        Vec<rustc_public::mir::Operand>,
        rustc_public::mir::Place,
        usize,
        RelationApp,
        &[ay_bindings::Expr],
        &HashSet<usize>,
        usize,
    ) + Send,
) {
    with_test_ay_ctx_for_source(RC_DEREF_DISPATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_deref_dispatch");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_rc_deref_dispatch", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(callee_path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if !(callee_path.contains("rc::Rc")
                && callee_path.ends_with("as std::ops::Deref>::deref"))
            {
                continue;
            }
            let Some(target_bb) = *target else {
                continue;
            };
            call_site = Some((bb_idx, func.clone(), args.clone(), destination.clone(), target_bb));
            break;
        }

        let (bb_idx, func, args, destination, target_bb) =
            call_site.expect("expected explicit Rc::deref call in probe_rc_deref_dispatch");
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

        body_fn(
            &mut chc_ctx,
            func,
            args,
            destination,
            target_bb,
            from_app,
            &stmt_constraints,
            &modified_locals,
            bb_idx,
        );
    });
}

fn expr_is_bv_const(expr: &Expr, width: u32, value: u128) -> bool {
    matches!(
        expr.value(),
        ExprValue::BitVecConst { value: actual, width: actual_width }
            if *actual_width == width && *actual == BigInt::from(value)
    )
}

fn expr_is_rc_base_ptr(expr: &Expr, obj_id: u32) -> bool {
    let expected_base_addr = (obj_id as u128) << 32;
    matches!(
        expr.value(),
        ExprValue::BvConcat(hi, lo)
            if expr_is_bv_const(hi, 32, obj_id as u128) && expr_is_bv_const(lo, 32, 0)
    ) || expr_is_bv_const(expr, 64, expected_base_addr)
}

fn expr_is_rc_value_ptr(expr: &Expr, obj_id: u32) -> bool {
    let expected_value_addr = ((obj_id as u128) << 32) + 0x10;
    match expr.value() {
        ExprValue::BitVecConst { value, width } => {
            *width == 64 && *value == BigInt::from(expected_value_addr)
        }
        ExprValue::BvAdd(lhs, rhs) => {
            (expr_is_rc_base_ptr(lhs, obj_id) && expr_is_bv_const(rhs, 64, 0x10))
                || (expr_is_rc_base_ptr(rhs, obj_id) && expr_is_bv_const(lhs, 64, 0x10))
        }
        _ => false,
    }
}

fn rule_has_rc_value_ptr(rule: &trust_mc_core::chc::Rule, obj_id: u32) -> bool {
    rule.body.constraints.iter().any(|constraint| {
        constraint_tree_contains(constraint, &|expr| expr_is_rc_value_ptr(expr, obj_id))
    })
}

fn assert_rc_deref_dispatch_uses_concrete_value_field_pointer() {
    with_rc_deref_dispatch_call(
        |chc_ctx,
         func,
         args,
         destination,
         target_bb,
         from_app,
         stmt_constraints,
         modified_locals,
         bb_idx| {
            let target_opt = Some(target_bb);
            let src_local = args
                .first()
                .and_then(|arg| match arg {
                    rustc_public::mir::Operand::Copy(place)
                    | rustc_public::mir::Operand::Move(place)
                        if place.projection.is_empty() =>
                    {
                        chc_ctx
                            .ref_resolution
                            .ref_targets
                            .get(&place.local)
                            .map(|rt| rt.local)
                            .or(Some(place.local))
                    }
                    _ => None,
                })
                .expect("expected direct Rc::deref source local");
            let seeded_obj_id = 0x1234_u32 + bb_idx as u32;
            chc_ctx.known_alloc_ids.insert(src_local, seeded_obj_id);

            let callee_path = chc_ctx.resolve_callee_path(&func);
            let dcx = DispatchCallContext {
                bb_idx,
                func: &func,
                args: &args,
                destination: &destination,
                target: &target_opt,
                from_app: &from_app,
                stmt_constraints,
                modified_locals,
                callee_path,
            };

            assert!(
                chc_ctx.try_dispatch_call_misc(&dcx),
                "Rc::deref should be handled by misc dispatch"
            );
            assert!(
                !chc_ctx.known_alloc_ids.contains_key(&destination.local),
                "Rc::deref should not preserve the raw allocation-base map on the destination"
            );

            let expected_value_addr = ((seeded_obj_id as u128) << 32) + 0x10;
            let has_expected_value_ptr = rule_has_rc_value_ptr(
                chc_ctx.vc.rules.last().expect("Rc::deref should emit one rule"),
                seeded_obj_id,
            );
            let smt = emit_chc(&chc_ctx.vc).to_string();
            assert!(
                has_expected_value_ptr,
                "expected Rc::deref rule to constrain the deref result to the \
                 concrete RcInner.value pointer for obj_id {seeded_obj_id} (addr \
                 {expected_value_addr:016x}), got: {}",
                &smt[..smt.len().min(1200)]
            );
        },
    );
}

/// Regression guard (#3589): when `Rc::deref` knows the backing allocation,
/// the misc-dispatch fast path must materialize the concrete `RcInner.value`
/// pointer (`alloc_addr + 0x10`) in the emitted CHC rule instead of leaving the
/// deref result symbolic.
#[test]
fn test_rc_deref_dispatch_uses_concrete_value_field_pointer_when_alloc_known() {
    assert_rc_deref_dispatch_uses_concrete_value_field_pointer();
}

/// Rc unsized coercion should not fall back to inferable `P_inf_*` summaries for
/// `Rc::from_inner_in` or wrapper `Deref::deref`; those summaries break pointer
/// identity across the coercion chain.
#[test]
fn test_rc_wrapper_calls_avoid_inferable_summaries() {
    assert_source_has_no_inferable_summaries(
        RC_DYN_COERCE_SOURCE,
        "probe_rc_dyn_dispatch",
        |name| {
            name.contains("from_inner_in") || (name.contains("Deref>") && name.ends_with("::deref"))
        },
        "Rc wrapper calls should bypass inferable summaries",
    );
}

// --- Part of #4139: Rc::into_raw / Rc::from_raw identity handling tests ---

const SHARED_PTR_RAW_ROUNDTRIP_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::rc::Rc;
    use std::sync::Arc;

    pub trait DummyTrait {}

    pub struct Wrapper<T: ?Sized> {
        pub w_id: u8,
        pub inner: T,
    }

    pub struct DummyImpl {
        pub id: u8,
    }

    impl DummyTrait for DummyImpl {}

    #[inline(never)]
    pub fn probe_rc_into_raw() -> *const Wrapper<DummyImpl> {
        let rc = Rc::new(Wrapper { w_id: 0, inner: DummyImpl { id: 1 } });
        Rc::into_raw(rc)
    }

    #[inline(never)]
    pub fn probe_rc_from_raw(ptr: *const Wrapper<DummyImpl>) -> Rc<Wrapper<DummyImpl>> {
        unsafe { Rc::from_raw(ptr) }
    }

    #[inline(never)]
    pub fn probe_rc_raw_roundtrip_dyn() -> u8 {
        let original = Rc::new(Wrapper { w_id: 42, inner: DummyImpl { id: 7 } });
        let raw = Rc::into_raw(original) as *const Wrapper<dyn DummyTrait>;
        let _reconstructed = unsafe { Rc::from_raw(raw) };
        42
    }

    #[inline(never)]
    pub fn probe_arc_into_raw() -> *const Wrapper<DummyImpl> {
        let arc = Arc::new(Wrapper { w_id: 0, inner: DummyImpl { id: 1 } });
        Arc::into_raw(arc)
    }

    #[inline(never)]
    pub fn probe_arc_from_raw(ptr: *const Wrapper<DummyImpl>) -> Arc<Wrapper<DummyImpl>> {
        unsafe { Arc::from_raw(ptr) }
    }

    #[inline(never)]
    pub fn probe_arc_raw_roundtrip_dyn() -> u8 {
        let original = Arc::new(Wrapper { w_id: 42, inner: DummyImpl { id: 7 } });
        let raw = Arc::into_raw(original) as *const Wrapper<dyn DummyTrait>;
        let _reconstructed = unsafe { Arc::from_raw(raw) };
        42
    }
"#;

/// Part of #4139: `Rc::into_raw` should be handled by misc dispatch without
/// falling back to inferable summaries.
#[test]
fn test_rc_into_raw_avoids_inferable_summaries() {
    assert_source_has_no_inferable_summaries(
        SHARED_PTR_RAW_ROUNDTRIP_SOURCE,
        "probe_rc_into_raw",
        |name| name.contains("into_raw"),
        "Rc::into_raw should bypass inferable summaries",
    );
}

/// Part of #4139: `Rc::from_raw` should be handled by misc dispatch without
/// falling back to inferable summaries.
#[test]
fn test_rc_from_raw_avoids_inferable_summaries() {
    assert_source_has_no_inferable_summaries(
        SHARED_PTR_RAW_ROUNDTRIP_SOURCE,
        "probe_rc_from_raw",
        |name| name.contains("from_raw"),
        "Rc::from_raw should bypass inferable summaries",
    );
}

/// Part of #4139: The full `Rc::into_raw` → cast → `Rc::from_raw` dyn roundtrip
/// should not produce inferable summaries for either the into_raw or from_raw call.
#[test]
fn test_rc_raw_dyn_roundtrip_avoids_inferable_summaries() {
    assert_source_has_no_inferable_summaries(
        SHARED_PTR_RAW_ROUNDTRIP_SOURCE,
        "probe_rc_raw_roundtrip_dyn",
        |name| name.contains("into_raw") || name.contains("from_raw"),
        "Rc raw roundtrip with dyn cast should bypass inferable summaries",
    );
}

/// Part of #4139: `Arc::into_raw` should be handled by misc dispatch without
/// falling back to inferable summaries.
#[test]
fn test_arc_into_raw_avoids_inferable_summaries() {
    assert_source_has_no_inferable_summaries(
        SHARED_PTR_RAW_ROUNDTRIP_SOURCE,
        "probe_arc_into_raw",
        |name| name.contains("into_raw"),
        "Arc::into_raw should bypass inferable summaries",
    );
}

/// Part of #4139: `Arc::from_raw` should be handled by misc dispatch without
/// falling back to inferable summaries.
#[test]
fn test_arc_from_raw_avoids_inferable_summaries() {
    assert_source_has_no_inferable_summaries(
        SHARED_PTR_RAW_ROUNDTRIP_SOURCE,
        "probe_arc_from_raw",
        |name| name.contains("from_raw"),
        "Arc::from_raw should bypass inferable summaries",
    );
}

/// Part of #4139: The full `Arc::into_raw` → cast → `Arc::from_raw` dyn roundtrip
/// should not produce inferable summaries for either the into_raw or from_raw call.
#[test]
fn test_arc_raw_dyn_roundtrip_avoids_inferable_summaries() {
    assert_source_has_no_inferable_summaries(
        SHARED_PTR_RAW_ROUNDTRIP_SOURCE,
        "probe_arc_raw_roundtrip_dyn",
        |name| name.contains("into_raw") || name.contains("from_raw"),
        "Arc raw roundtrip with dyn cast should bypass inferable summaries",
    );
}
