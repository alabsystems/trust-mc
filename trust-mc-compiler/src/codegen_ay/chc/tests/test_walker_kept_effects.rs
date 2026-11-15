// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The inline walker walks what Rule D used to book as lost (decision
//! TRUSTMC-OPEN-REDS, docs/DECISION_QUEUE.md): an array literal and a
//! symbolic index into it, an arm that reaches `unreachable_unchecked`, a
//! slice's length through `get_unchecked`, and a loop whose exit condition is
//! constant past the replay fuel. A path that needs more iterations of a loop
//! than the walk replays is never left on a guessed exit: the visit that finds
//! the fuel spent is the loop's last pass (its exit test decides), and a path
//! back at the header takes the bailed-arm fallback, which accounts for what
//! the walk abandoned (`loop_replay.rs` `visit_loop_header`; the merge of
//! fix/chc-walker-fail-closed kept that design for main's
//! `WALKER_LOOP_FUEL_TRUNCATED_CHECK`). Each probe is a dyn call, so the
//! walker translates the method body.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::call::codegen_call_virtual_inline::uncertified_check::WALKER_BAILED_ARM_OBLIGATION;
use crate::codegen_ay::chc::call::inline_walk_guard::LostEffect;

const SOURCE: &str = r#"
    #![allow(dead_code)]
    #[inline(never)]
    fn sink<T>(_value: T) {}
    pub trait Op {
        fn op(&self, a: u8, i: u8) -> u8;
    }
    pub struct ArrayIndex;
    impl Op for ArrayIndex {
        fn op(&self, a: u8, i: u8) -> u8 {
            let arr = [a, 1, 2, 3];
            let v = arr[(i % 4) as usize];
            sink(v + 200);
            a
        }
    }
    pub struct Unreachable;
    impl Op for Unreachable {
        fn op(&self, a: u8, _i: u8) -> u8 {
            if a == 3 {
                unsafe { core::hint::unreachable_unchecked() }
            }
            a
        }
    }
    pub struct GetUnchecked;
    impl Op for GetUnchecked {
        fn op(&self, a: u8, i: u8) -> u8 {
            let arr = [a, 20, 30, 40];
            unsafe { *arr.get_unchecked((i % 4) as usize) }
        }
    }
    pub struct ConstantLoop;
    impl Op for ConstantLoop {
        fn op(&self, a: u8, _i: u8) -> u8 {
            let mut acc = a;
            let mut k: u8 = 0;
            while k < 10 {
                acc = acc.wrapping_add(20);
                k += 1;
            }
            acc
        }
    }
    pub struct SymbolicLoop;
    impl Op for SymbolicLoop {
        fn op(&self, a: u8, _i: u8) -> u8 {
            let mut k: u8 = 0;
            loop {
                if k >= a {
                    break;
                }
                k += 1;
            }
            k
        }
    }
    pub fn probe_array_index(a: u8, i: u8) -> u8 {
        let obj: Box<dyn Op> = Box::new(ArrayIndex);
        obj.op(a, i)
    }
    pub fn probe_unreachable(a: u8, i: u8) -> u8 {
        let obj: Box<dyn Op> = Box::new(Unreachable);
        obj.op(a, i)
    }
    pub fn probe_get_unchecked(a: u8, i: u8) -> u8 {
        let obj: Box<dyn Op> = Box::new(GetUnchecked);
        obj.op(a, i)
    }
    pub fn probe_constant_loop(a: u8, i: u8) -> u8 {
        let obj: Box<dyn Op> = Box::new(ConstantLoop);
        obj.op(a, i)
    }
    pub fn probe_symbolic_loop(a: u8, i: u8) -> u8 {
        let obj: Box<dyn Op> = Box::new(SymbolicLoop);
        obj.op(a, i)
    }
"#;

/// The fallback reasons translating `fn_name` records.
fn recorded_reasons(fn_name: &str) -> Vec<String> {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut reasons = Vec::new();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, _) = chc_ctx.translate_with_diagnostics();
        assert!(!vc.rules.is_empty(), "{fn_name} produces rules");
        let sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        reasons = sites
            .get(fn_name)
            .map(|v| v.iter().map(|(reason, _)| reason.to_string()).collect())
            .unwrap_or_default();
    });
    reasons
}

fn assert_not_booked(fn_name: &str, effects: &[LostEffect]) {
    let reasons = recorded_reasons(fn_name);
    for effect in effects {
        assert!(
            !reasons.iter().any(|r| r == effect.reason()),
            "{fn_name}: {effect:?} booked, reasons {reasons:?}"
        );
    }
}

/// `[a, 1, 2, 3]` and `arr[(i % 4) as usize]` translate, so the overflow
/// check over the element stays a check.
#[test]
fn test_array_literal_and_index_keep_the_check() {
    assert_not_booked(
        "probe_array_index",
        &[LostEffect::UntranslatableAssert, LostEffect::BailedArm],
    );
}

/// An arm reaching `unreachable_unchecked` is a check arm, not a bailed one.
#[test]
fn test_unreachable_arm_is_a_check() {
    assert_not_booked("probe_unreachable", &[LostEffect::BailedArm]);
}

/// `get_unchecked`'s `slice.len()` reads the array's length, so the callee
/// walks instead of being havocked.
#[test]
fn test_get_unchecked_reads_the_slice_length() {
    assert_not_booked("probe_get_unchecked", &[LostEffect::NestedCallFallback]);
    let reasons = recorded_reasons("probe_get_unchecked");
    assert!(
        !reasons.iter().any(|r| r == "inline_ptr_metadata_lost_for_wide_type"),
        "the slice length is known: {reasons:?}"
    );
}

/// A constant trip count replays past the fuel without dropping an iteration.
#[test]
fn test_constant_loop_replays_every_iteration() {
    assert_not_booked("probe_constant_loop", &[LostEffect::BailedArm]);
    let reasons = recorded_reasons("probe_constant_loop");
    assert!(
        !reasons.iter().any(|r| r == WALKER_BAILED_ARM_OBLIGATION || r == "switchint_branch_overapprox"),
        "a constant exit condition truncates nothing: {reasons:?}"
    );
}

/// A symbolic loop that outruns the replay is never left on a guessed exit:
/// the path back at the spent header abandons its arm, and the bailed-arm
/// fallback accounts for the abandoned region (its reach check, its value
/// havoc, or Rule D's booking), so no iteration is dropped silently.
#[test]
fn test_symbolic_loop_past_the_replay_is_accounted() {
    let reasons = recorded_reasons("probe_symbolic_loop");
    assert!(
        reasons.iter().any(|r| r == WALKER_BAILED_ARM_OBLIGATION
            || r == "switchint_branch_overapprox"
            || r == LostEffect::BailedArm.reason()),
        "a loop past the replay is accounted: {reasons:?}"
    );
}
