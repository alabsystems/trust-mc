// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Heap metadata lanes. A rule head that carries `obj_valid__out` or
//! `obj_size__out` without anything in the rule binding it HAVOCS that lane (a
//! clause variable is universally quantified). A site that writes one lane
//! must mark only that lane, and a call terminator's metadata update must
//! reach the call's own rule. Before either held, `Box::new` followed by
//! `ptr::null()` havocked every allocation's validity and size with no
//! approximation recorded, and the Box's drop-time checks were refuted with a
//! counterexample certified Genuine (tools/soundness-duals/
//! heap_metadata_lane_dual.rs).

#![allow(clippy::unwrap_used)]

use super::super::translate::unbound_heap_metadata_outputs;
use super::common::*;
use trust_mc_core::chc::{ChcVc, RelationApp, Rule, RuleBody};

fn is_var(expr: &Expr, want: &str) -> bool {
    matches!(expr.value(), ExprValue::Var { name } if name.as_str() == want)
}

/// The rules that write `obj_valid__out = store(obj_valid, _, false)`: the
/// invalidation a null, dangling or integer-derived pointer makes.
fn invalidating_rules(vc: &ChcVc) -> Vec<&Rule> {
    vc.rules
        .iter()
        .filter(|rule| {
            rule.body.constraints.iter().any(|c| match c.value() {
                ExprValue::Eq(lhs, rhs) => {
                    is_var(lhs, "obj_valid__out")
                        && matches!(rhs.value(), ExprValue::Store { array, value, .. }
                            if is_var(array, "obj_valid")
                                && matches!(value.value(), ExprValue::BoolConst(false)))
                }
                _ => false,
            })
        })
        .collect()
}

fn head_carries(rule: &Rule, name: &str) -> bool {
    rule.head.args.iter().any(|arg| is_var(arg, name))
}

/// `ptr::null()` is a call terminator (StubKind::PtrNull). Its `obj_valid`
/// invalidation went to `heap_state.pending_updates`, which the block's
/// statement encoding had already drained, so the call's rule carried an
/// unbound `obj_valid__out`; and it marked `obj_size` modified without writing
/// it. Each half alone leaves an unbound lane in some head.
#[test]
fn test_ptr_null_call_binds_obj_valid_and_leaves_obj_size_input() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_then_null() -> u32 {
            let b = Box::new(5u32);
            let p: *const u8 = core::ptr::null();
            if p.is_null() { *b } else { 0 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_then_null");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_box_then_null", ChcConfig::default());
        let found_null = body.blocks.iter().any(|block| {
            matches!(&block.terminator.kind,
                rustc_public::mir::TerminatorKind::Call { func, .. }
                    if chc_ctx.detect_stub_matching(func, StubKind::is_pointer_utility)
                        == Some(StubKind::PtrNull))
        });
        assert_mir_pattern_found(found_null, "ptr::null() call terminator (StubKind::PtrNull)");

        let vc = pre_pass_vc(chc_ctx);
        let offenders = unbound_heap_metadata_outputs(&vc);
        assert!(
            offenders.is_empty(),
            "no rule may carry a heap metadata output its body does not bind: {offenders:?}"
        );
        // The Box's drop also invalidates (and frames obj_size__out = obj_size);
        // the ptr::null() rule is the invalidating rule that writes no obj_size.
        let invalidating = invalidating_rules(&vc);
        assert!(
            invalidating.iter().all(|rule| head_carries(rule, "obj_valid__out")),
            "an invalidation is delivered to the rule whose head carries obj_valid__out"
        );
        assert!(
            invalidating
                .iter()
                .any(|rule| head_carries(rule, "obj_size") && !head_carries(rule, "obj_size__out")),
            "ptr::null() writes no obj_size; its rule must carry obj_valid__out = \
             store(obj_valid, _, false) and the INPUT obj_size in its head"
        );
    });
}

/// An integer-to-pointer cast is a statement: its invalidation is drained at
/// block end, but it marked `obj_size` modified too, so the head carried an
/// `obj_size__out` nothing bound.
#[test]
fn test_int_to_ptr_cast_leaves_obj_size_input() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_then_int2ptr(a: usize) -> u32 {
            let b = Box::new(5u32);
            let p = a as *const u8;
            if p.is_null() { *b } else { 1 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_then_int2ptr");
        let body = instance.body().expect("function body");
        let vc = pre_pass_vc(ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_box_then_int2ptr",
            ChcConfig::default(),
        ));
        let invalidating = invalidating_rules(&vc);
        assert_mir_pattern_found(
            !invalidating.is_empty(),
            "PointerWithExposedProvenance cast invalidating obj_valid",
        );
        let offenders = unbound_heap_metadata_outputs(&vc);
        assert!(offenders.is_empty(), "unbound heap metadata outputs: {offenders:?}");
        assert!(
            invalidating
                .iter()
                .any(|rule| head_carries(rule, "obj_size") && !head_carries(rule, "obj_size__out")),
            "an int-to-pointer cast writes no obj_size; its rule must carry the INPUT obj_size"
        );
    });
}

/// The invalidation an integer-to-pointer cast makes is fail-closed, never
/// evidence: the lane keeps no exposed set, so a legitimate round trip
/// (`E as *const u32 as usize`, then `(a + 4) as *const u32`) names its own
/// object and reads as a use after free. Before, nothing was recorded and that
/// counterexample was certified Genuine
/// (tools/soundness-duals/const_pointer_raw_from_ref_dual.rs::
/// safe_int_roundtrip). The cast records `int_to_ptr_obj_invalidated`
/// through `invalidate_int_to_ptr_object` (SoundHavoc: a proof over it
/// stands, a counterexample is not certified), as the BMC lane records
/// `pointer_with_exposed_provenance`; the same body without the cast records
/// nothing.
#[test]
fn test_int_to_ptr_invalidation_is_never_evidence() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_int_to_ptr(a: usize) -> *const u8 {
            a as *const u8
        }
        pub fn probe_ptr_identity(p: *const u8) -> *const u8 {
            p
        }
        pub fn probe_f64_bits_to_ptr(f: f64) -> *const u8 {
            unsafe { std::mem::transmute::<f64, *const u8>(f) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sound_havocs = |name: &str| {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().expect("function body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();
            chc_ctx.emit_entry_rule();
            chc_ctx.generate_transition_rules();
            let invalidates = !invalidating_rules(&chc_ctx.vc).is_empty();
            (invalidates, chc_ctx.diagnostics.sound_havoc_drop.get())
        };
        let (invalidates, recorded) = sound_havocs("probe_int_to_ptr");
        assert_mir_pattern_found(
            invalidates,
            "PointerWithExposedProvenance cast invalidating obj_valid",
        );
        assert_eq!(recorded, 1, "the cast's invalidation is recorded as an approximation");
        assert_eq!(sound_havocs("probe_ptr_identity"), (false, 0), "no cast, nothing recorded");
        // A float's bits carry no provenance either: the pointer a transmute
        // makes of them is the integer-to-pointer lane, invalidation and
        // record alike (stack_address::ty_is_provenance_free_bits). Before,
        // the f64 sort (the IEEE pattern, 64 bits) passed a pointer's bits
        // through with its object (bit_launder_dual.rs::
        // bug_static_f64_transmute_nostore was PROVED).
        assert_eq!(
            sound_havocs("probe_f64_bits_to_ptr"),
            (true, 1),
            "a pointer made of a float's bits is invalidated and recorded like an integer's"
        );
    });
}

/// A float roundtrip must not inherit the integer exposed-address exception.
/// Exercise the real cast lowering and metadata updates, including the static
/// read which previously kept its seeded object and verified successfully.
#[test]
fn test_float_roundtrip_does_not_regain_exposed_provenance() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        static SC: [u16; 2] = [1, 0x0102];

        pub fn probe_float_roundtrip(p: *const u8) -> *const u8 {
            let bits: f64 = unsafe { std::mem::transmute(p) };
            unsafe { std::mem::transmute(bits) }
        }
        pub fn probe_float_integer_alias(p: *const u8) -> *const u8 {
            let bits: f64 = unsafe { std::mem::transmute(p) };
            let integer: usize = unsafe { std::mem::transmute(bits) };
            unsafe { std::mem::transmute(integer) }
        }
        pub fn probe_static_float_roundtrip() -> u8 {
            let bits: f64 = unsafe {
                std::mem::transmute(std::ptr::addr_of!(SC) as *const u8)
            };
            let p: *const u8 = unsafe { std::mem::transmute(bits) };
            unsafe { *p.add(2) }
        }
        pub fn probe_integer_roundtrip(p: *const u8) -> *const u8 {
            let address = p as usize;
            unsafe { std::mem::transmute(address) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let metadata = |name: &str| {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().expect("function body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            chc_ctx.declare_block_relations();
            chc_ctx.declare_error_relation();
            chc_ctx.emit_entry_rule();
            chc_ctx.generate_transition_rules();
            (
                !invalidating_rules(&chc_ctx.vc).is_empty(),
                chc_ctx.diagnostics.sound_havoc_drop.get(),
            )
        };
        assert!(
            !metadata("probe_integer_roundtrip").0,
            "an ordinary exposed integer address keeps its supported roundtrip"
        );
        for name in
            ["probe_float_roundtrip", "probe_float_integer_alias", "probe_static_float_roundtrip"]
        {
            let (invalidates, recorded) = metadata(name);
            assert!(invalidates, "{name}: float bits must not retain allocation provenance");
            assert!(recorded > 0, "{name}: invalidation must remain an accounted approximation");
        }
    });
}

/// The detector itself, on hand-built rules: a lane is defined by an equality
/// with an expression free of it, or by the body relation carrying it.
#[test]
fn test_unbound_heap_metadata_outputs_detects_undefined_lanes() {
    let ov_sort = super::super::codegen_expr_heap::obj_valid_sort();
    let os_sort = super::super::codegen_expr_heap::obj_size_sort();
    let ov = Expr::var("obj_valid", ov_sort.clone());
    let ov_out = Expr::var("obj_valid__out", ov_sort.clone());
    let os = Expr::var("obj_size", os_sort.clone());
    let os_out = Expr::var("obj_size__out", os_sort.clone());
    let os_mid = Expr::var("obj_size__mid_bb3", os_sort);
    let lane = Expr::var("obj_valid_at_0x2_bv32__out", ay_bindings::Sort::bool());

    let rule = |constraints: Vec<Expr>, head: Vec<Expr>| {
        Rule::new(
            RuleBody::new(
                Some(RelationApp::new("f__bb0", vec![ov.clone(), os.clone()])),
                constraints,
            ),
            RelationApp::new("f__bb1", head),
        )
    };
    let mut vc = ChcVc::new();
    // 0: both lanes carried unchanged (input variables): nothing unbound.
    vc.add_rule(rule(vec![], vec![ov.clone(), os.clone()]));
    // 1: obj_valid written, obj_size carried: nothing unbound.
    let invalidate =
        ov_out.clone().eq(ov.clone().store(Expr::bitvec_const(0u64, 32), Expr::bool_const(false)));
    vc.add_rule(rule(vec![invalidate.clone()], vec![ov_out.clone(), os.clone()]));
    // 2: obj_valid written, obj_size__out in the head with nothing binding it.
    vc.add_rule(rule(vec![invalidate], vec![ov_out.clone(), os_out.clone()]));
    // 3: a large-step middle value no conjunct mentions.
    vc.add_rule(rule(vec![], vec![ov.clone(), os_mid]));
    // 4: an explicit identity frame binds it.
    vc.add_rule(rule(vec![os_out.clone().eq(os.clone())], vec![ov.clone(), os_out]));
    // 5: a scalarized lane name is not a pre-scalarization metadata output.
    vc.add_rule(rule(vec![], vec![lane, os.clone()]));
    // 6: no body relation (an entry rule) is not a transition.
    vc.add_rule(Rule::new(
        RuleBody::new(None, vec![]),
        RelationApp::new("f__bb0", vec![ov_out.clone(), os.clone()]),
    ));
    // 7: a self-referential store pins one element and leaves the rest free.
    let self_store = ov_out
        .clone()
        .eq(ov_out.clone().store(Expr::bitvec_const(1u64, 32), Expr::bool_const(false)));
    vc.add_rule(rule(vec![self_store], vec![ov_out.clone(), os.clone()]));
    // 8: a read of the output (`select`) is not a definition either.
    let read_only = ov_out.clone().select(Expr::bitvec_const(1u64, 32));
    vc.add_rule(rule(vec![read_only], vec![ov_out, os.clone()]));

    let offenders = unbound_heap_metadata_outputs(&vc);
    assert_eq!(
        offenders,
        vec![
            ("f__bb1".to_string(), vec!["obj_size__out".to_string()]),
            ("f__bb1".to_string(), vec!["obj_size__mid_bb3".to_string()]),
            ("f__bb1".to_string(), vec!["obj_valid__out".to_string()]),
            ("f__bb1".to_string(), vec!["obj_valid__out".to_string()]),
        ]
    );
}
