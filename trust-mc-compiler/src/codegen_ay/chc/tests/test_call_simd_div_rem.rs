// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The CHC zero-divisor lane check of `simd_div` / `simd_rem` is UB for the raw
//! intrinsic and a panic for the portable-SIMD operator, which checks the
//! divisor in its own body (core_simd `int_divrem_guard`) before it divides.
//! The same body defines signed `MIN / -1` (it divides that lane by 1), so
//! only the raw intrinsic checks it, and only core's own operator impl is
//! intercepted as the portable operator.

use super::common::*;
use crate::codegen_ay::chc::call::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::call::{
    SimdBinopOrigin, SimdIntrinsicKind, codegen_simd_elementwise_binop, codegen_simd_shift,
    divisor_lanes_nonzero, extract_simd_layout, resolve_simd_array, try_dispatch_simd_lib_call,
};
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use rustc_public::mir::TerminatorKind;
use trust_mc_core::violation::PropertyKind;

const SIMD_DIV_SOURCE: &str = r#"
    #![allow(dead_code, unused_variables)]

    #[derive(Clone, Copy)]
    pub struct U32x4([u32; 4]);

    pub fn probe_div(a: U32x4, b: U32x4) -> U32x4 {
        a
    }
"#;

/// Signed lanes, the only ones with a `MIN / -1` lane.
const SIMD_SIGNED_DIV_SOURCE: &str = r#"
    #![allow(dead_code, unused_variables)]

    #[derive(Clone, Copy)]
    pub struct I32x4([i32; 4]);

    pub fn probe_div(a: I32x4, b: I32x4) -> I32x4 {
        a
    }
"#;

/// The (kind, message) of every property the element-wise binop registers.
fn div_properties(
    kind: SimdIntrinsicKind,
    origin: SimdBinopOrigin,
) -> Vec<(PropertyKind, Option<String>)> {
    div_properties_for(SIMD_DIV_SOURCE, kind, origin)
}

/// [`div_properties`] over `source`, whose `probe_div` takes the two vectors.
fn div_properties_for(
    source: &str,
    kind: SimdIntrinsicKind,
    origin: SimdBinopOrigin,
) -> Vec<(PropertyKind, Option<String>)> {
    let mut out = Vec::new();
    with_test_ay_ctx_for_source(source, |ctx| {
        let fn_name = "probe_div";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let from_rel = chc_ctx.block_relations.get(&0).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();
        let func = Operand::Copy(Place { local: 0usize, projection: vec![] });
        let args = [
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
            Operand::Copy(Place { local: 2usize, projection: vec![] }),
        ];
        let destination = Place { local: 0usize, projection: vec![] };
        let target = 0usize;
        let target_opt = Some(target);
        let dcx = DispatchCallContext {
            bb_idx: 0,
            func: &func,
            args: &args,
            destination: &destination,
            target: &target_opt,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
            callee_path: None,
        };

        let before = chc_ctx.vc.properties.len();
        codegen_simd_elementwise_binop(&mut chc_ctx, &dcx, target, kind, origin);
        out = chc_ctx.vc.properties[before..].iter().map(|p| (p.kind, p.message.clone())).collect();
    });
    out
}

#[test]
fn test_raw_simd_div_rem_zero_lane_is_ub_not_a_panic() {
    for kind in [SimdIntrinsicKind::Div, SimdIntrinsicKind::Rem] {
        let props = div_properties(kind, SimdBinopOrigin::RawIntrinsic);
        assert_eq!(props.len(), 4, "{kind:?}: one zero-divisor check per U32x4 lane: {props:?}");
        for (k, message) in &props {
            assert_eq!(*k, PropertyKind::UndefinedBehavior, "{kind:?}: {props:?}");
            assert_eq!(message.as_deref(), Some("division by zero"), "{kind:?}: {props:?}");
        }
    }
}

#[test]
fn test_portable_simd_operator_zero_lane_keeps_the_panic_kind() {
    for kind in [SimdIntrinsicKind::Div, SimdIntrinsicKind::Rem] {
        let props = div_properties(kind, SimdBinopOrigin::PortableOperator);
        assert_eq!(props.len(), 4, "{kind:?}: one zero-divisor check per U32x4 lane: {props:?}");
        for (k, message) in &props {
            assert_eq!(*k, PropertyKind::DivisionByZero, "{kind:?}: {props:?}");
            assert_eq!(*message, None, "{kind:?}: {props:?}");
        }
    }
}

#[test]
fn test_raw_simd_div_rem_signed_lane_checks_min_by_neg_one() {
    for (kind, intrinsic) in
        [(SimdIntrinsicKind::Div, "simd_div"), (SimdIntrinsicKind::Rem, "simd_rem")]
    {
        let props = div_properties_for(SIMD_SIGNED_DIV_SOURCE, kind, SimdBinopOrigin::RawIntrinsic);
        let overflow = format!("attempt to compute {intrinsic} which would overflow");
        let ub = props.iter().filter(|(k, _)| *k == PropertyKind::UndefinedBehavior).count();
        let min_by_neg_one = props
            .iter()
            .filter(|(k, m)| {
                *k == PropertyKind::ArithmeticOverflow && m.as_deref() == Some(overflow.as_str())
            })
            .count();
        assert_eq!(
            (props.len(), ub, min_by_neg_one),
            (8, 4, 4),
            "{kind:?}: a zero-divisor and a MIN / -1 check per I32x4 lane: {props:?}"
        );
    }
}

#[test]
fn test_portable_simd_operator_signed_lane_defines_min_by_neg_one() {
    // core_simd `int_divrem_guard` divides a `MIN / -1` lane by 1: Rust
    // returns MIN (div) and 0 (rem) there, with no panic and no UB.
    for kind in [SimdIntrinsicKind::Div, SimdIntrinsicKind::Rem] {
        let props =
            div_properties_for(SIMD_SIGNED_DIV_SOURCE, kind, SimdBinopOrigin::PortableOperator);
        assert_eq!(
            props.len(),
            4,
            "{kind:?}: only the zero-divisor panic per I32x4 lane: {props:?}"
        );
        for (k, message) in &props {
            assert_eq!(*k, PropertyKind::DivisionByZero, "{kind:?}: {props:?}");
            assert_eq!(*message, None, "{kind:?}: {props:?}");
        }
    }
}

/// Signed `/` through the real call-dispatch hook: core's operator, and a
/// user impl whose path spells "simd" and "ops" (its body is no division).
const PORTABLE_DIV_DISPATCH_SOURCE: &str = r#"
    #![feature(portable_simd)]
    #![allow(dead_code, unused_variables)]

    use std::simd::i32x4;

    pub mod simd_ops {
        #[derive(Clone, Copy)]
        pub struct I32x4(pub [i32; 4]);

        impl core::ops::Div for I32x4 {
            type Output = I32x4;
            fn div(self, rhs: I32x4) -> I32x4 {
                self
            }
        }
    }

    pub fn probe_core_div(a: i32x4, b: i32x4) -> i32x4 {
        a / b
    }

    pub fn probe_user_div(a: simd_ops::I32x4, b: simd_ops::I32x4) -> simd_ops::I32x4 {
        a / b
    }
"#;

/// Hand the one `Call` terminator of `fn_name` to `try_dispatch_simd_lib_call`:
/// whether it took the call, and the (kind, message) of what it registered.
fn simd_lib_dispatch(fn_name: &str) -> (bool, Vec<(PropertyKind, Option<String>)>) {
    let mut out = (false, Vec::new());
    with_test_ay_ctx_for_source(PORTABLE_DIV_DISPATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let calls: Vec<_> = body
            .blocks
            .iter()
            .enumerate()
            .filter_map(|(bb_idx, block)| {
                if let TerminatorKind::Call { func, args, destination, target, .. } =
                    &block.terminator.kind
                {
                    Some((bb_idx, func.clone(), args.clone(), destination.clone(), *target))
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(calls.len(), 1, "{fn_name}: one operator call");
        let (bb_idx, func, args, destination, target) =
            calls.into_iter().next().expect("one operator call");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();
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
        let dcx = DispatchCallContext {
            bb_idx,
            func: &func,
            args: &args,
            destination: &destination,
            target: &target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
            callee_path: None,
        };

        let before = chc_ctx.vc.properties.len();
        let handled = try_dispatch_simd_lib_call(&mut chc_ctx, &dcx);
        out = (
            handled,
            chc_ctx.vc.properties[before..].iter().map(|p| (p.kind, p.message.clone())).collect(),
        );
    });
    out
}

#[test]
fn test_core_portable_div_dispatch_checks_zero_lanes_only() {
    let (handled, props) = simd_lib_dispatch("probe_core_div");
    assert!(handled, "core's `<Simd<i32, 4> as Div>::div` is intercepted");
    assert_eq!(props.len(), 4, "one zero-divisor panic per lane, no MIN / -1 rule: {props:?}");
    assert!(
        props.iter().all(|(k, m)| *k == PropertyKind::DivisionByZero && m.is_none()),
        "{props:?}"
    );
}

#[test]
fn test_user_impl_under_a_simd_ops_path_is_not_intercepted() {
    let (handled, props) = simd_lib_dispatch("probe_user_div");
    assert!(!handled, "a local `simd_ops` Div impl is user code, dispatched like any call");
    assert!(props.is_empty(), "{props:?}");
}

/// What one SIMD handler emitted on `probe_div(a, b)` of `source`: the
/// (kind, message) of each property, the constraints of every rule into the
/// target block, and the resolved divisor (distance) vector `b` with its
/// layout.
struct SimdOutcome {
    props: Vec<(PropertyKind, Option<String>)>,
    gotos: Vec<Vec<Expr>>,
    rhs: Expr,
    layout: crate::codegen_ay::chc::call::SimdLayoutInfo,
}

fn simd_outcome(
    source: &str,
    config: ChcConfig,
    handler: impl FnOnce(&mut ChcCtx<'_, '_>, &DispatchCallContext<'_>, usize) + Send,
) -> SimdOutcome {
    let mut out = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let fn_name = "probe_div";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, config);
        chc_ctx.declare_block_relations();

        let from_rel = chc_ctx.block_relations.get(&0).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();
        let func = Operand::Copy(Place { local: 0usize, projection: vec![] });
        let args = [
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
            Operand::Copy(Place { local: 2usize, projection: vec![] }),
        ];
        let destination = Place { local: 0usize, projection: vec![] };
        let target = 0usize;
        let target_opt = Some(target);
        let dcx = DispatchCallContext {
            bb_idx: 0,
            func: &func,
            args: &args,
            destination: &destination,
            target: &target_opt,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
            callee_path: None,
        };

        let rhs = resolve_simd_array(&mut chc_ctx, &args[1], &modified_locals).expect("rhs");
        let layout = extract_simd_layout(body.locals()[1].ty).expect("simd layout");
        let before_props = chc_ctx.vc.properties.len();
        let before_rules = chc_ctx.vc.rules.len();
        handler(&mut chc_ctx, &dcx, target);
        let props = chc_ctx.vc.properties[before_props..]
            .iter()
            .map(|p| (p.kind, p.message.clone()))
            .collect();
        let gotos = chc_ctx.vc.rules[before_rules..]
            .iter()
            .filter(|rule| rule.head.name == from_rel)
            .map(|rule| rule.body.constraints.iter().cloned().collect())
            .collect();
        out = Some(SimdOutcome { props, gotos, rhs, layout });
    });
    out.expect("handler ran")
}

/// The portable operator panics on a zero divisor lane before it divides, so
/// its successor is reached only where every divisor lane is nonzero. Without
/// that conjunct the code after a panicking division stayed reachable and its
/// checks reported failures Rust never reaches. The raw intrinsic's zero lane is
/// UB, reported as such, and its successor keeps no such guard.
#[test]
fn test_portable_div_successor_needs_every_divisor_lane_nonzero() {
    for kind in [SimdIntrinsicKind::Div, SimdIntrinsicKind::Rem] {
        let portable =
            simd_outcome(SIMD_SIGNED_DIV_SOURCE, ChcConfig::default(), |ctx, dcx, target| {
                codegen_simd_elementwise_binop(
                    ctx,
                    dcx,
                    target,
                    kind,
                    SimdBinopOrigin::PortableOperator,
                );
            });
        let guard = divisor_lanes_nonzero(&portable.rhs, &portable.layout).expect("integer lanes");
        assert_eq!(portable.gotos.len(), 1, "{kind:?}: one successor rule");
        assert!(
            portable.gotos[0].contains(&guard),
            "{kind:?}: the successor needs every divisor lane nonzero: {:?}",
            portable.gotos[0]
        );

        let raw = simd_outcome(SIMD_SIGNED_DIV_SOURCE, ChcConfig::default(), |ctx, dcx, target| {
            codegen_simd_elementwise_binop(ctx, dcx, target, kind, SimdBinopOrigin::RawIntrinsic);
        });
        assert_eq!(raw.gotos.len(), 1, "{kind:?}: one successor rule");
        assert!(!raw.gotos[0].contains(&guard), "{kind:?}: {:?}", raw.gotos[0]);
    }
}

/// core_simd's `<<`/`>>` (`wrap_bitshift`) masks every distance lane with
/// `BITS - 1` before the intrinsic, so it can neither panic nor reach the
/// intrinsic's UB: no check, and the lane is shifted by the masked distance.
/// The raw intrinsic checks each lane and shifts by the distance as given.
#[test]
fn test_portable_shift_masks_the_distance_and_checks_nothing() {
    for kind in [SimdIntrinsicKind::Shl, SimdIntrinsicKind::Shr] {
        let portable =
            simd_outcome(SIMD_SIGNED_DIV_SOURCE, ChcConfig::default(), |ctx, dcx, target| {
                codegen_simd_shift(ctx, dcx, target, kind, SimdBinopOrigin::PortableOperator);
            });
        assert!(portable.props.is_empty(), "{kind:?}: {:?}", portable.props);
        let lane0 = portable.rhs.clone().select(Expr::bitvec_const(0u64, POINTER_WIDTH));
        let masked = lane0.clone().bvand(Expr::bitvec_const(31u128, 32)).to_string();
        assert_eq!(portable.gotos.len(), 1, "{kind:?}: one successor rule");
        let rendered: String = portable.gotos[0].iter().map(ToString::to_string).collect();
        assert!(rendered.contains(&masked), "{kind:?}: lane 0 shifts by `{masked}`: {rendered}");

        let raw = simd_outcome(SIMD_SIGNED_DIV_SOURCE, ChcConfig::default(), |ctx, dcx, target| {
            codegen_simd_shift(ctx, dcx, target, kind, SimdBinopOrigin::RawIntrinsic);
        });
        assert_eq!(raw.props.len(), 4, "{kind:?}: one distance check per lane: {:?}", raw.props);
        let rendered: String = raw.gotos[0].iter().map(ToString::to_string).collect();
        assert!(!rendered.contains(&masked), "{kind:?}: {rendered}");
    }
}

/// The raw intrinsics' lane checks are kept under `--no-overflow-checks`: a
/// shift past the lane width is UB, and Kani's compiler asserts both it and a
/// lane add/sub/mul overflow whatever that flag says (it takes only CBMC's
/// instrumentation off), as the BMC lane does. Gated, the flag dropped them
/// while the lane value goes on.
#[test]
fn test_simd_lane_checks_survive_no_overflow_checks() {
    let off = || ChcConfig { overflow_checks: false, ..ChcConfig::default() };
    let shift = simd_outcome(SIMD_SIGNED_DIV_SOURCE, off(), |ctx, dcx, target| {
        codegen_simd_shift(ctx, dcx, target, SimdIntrinsicKind::Shl, SimdBinopOrigin::RawIntrinsic);
    });
    assert_eq!(shift.props.len(), 4, "one distance check per lane: {:?}", shift.props);
    for kind in [SimdIntrinsicKind::Add, SimdIntrinsicKind::Sub, SimdIntrinsicKind::Mul] {
        let arith = simd_outcome(SIMD_SIGNED_DIV_SOURCE, off(), |ctx, dcx, target| {
            codegen_simd_elementwise_binop(ctx, dcx, target, kind, SimdBinopOrigin::RawIntrinsic);
        });
        assert_eq!(
            arith.props.len(),
            4,
            "{kind:?}: one overflow check per lane: {:?}",
            arith.props
        );
    }
}
