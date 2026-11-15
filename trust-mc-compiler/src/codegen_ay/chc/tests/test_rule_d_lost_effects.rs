// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rule D (design trust-mc-reds-final §4.1): a translation that removes a
//! check, a write or a deallocation the program can reach books FailClose.
//! One predicate (`inline_walk_guard::region_may_check_or_write`) and one
//! recorder (`record_lost_obligation`) serve every site; these tests hold the
//! predicate on small regions and every lost effect off the audited SoundHavoc
//! list.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::call::inline_walk_guard::{LostEffect, region_may_check_or_write};
use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
use rustc_public::mir::TerminatorKind;

/// Every lost effect is fail-closed, so a later edit to the SoundHavoc list
/// cannot bless one, and the reasons are distinct. The unresolved drop glue
/// Rule A skips is fail-closed too.
#[test]
fn test_every_lost_effect_is_fail_closed() {
    let mut reasons = std::collections::HashSet::new();
    for effect in LostEffect::ALL {
        assert_eq!(
            fallback_soundness(effect.reason()),
            FallbackSoundness::FailClose,
            "{effect:?} must not be a SoundHavoc reason"
        );
        assert!(reasons.insert(effect.reason()), "{effect:?} reuses a reason");
    }
    assert_eq!(
        fallback_soundness(crate::codegen_ay::shared::mono_ty::DROP_GLUE_UNRESOLVED),
        FallbackSoundness::FailClose
    );
}

const SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_pure(a: u32, flag: bool) -> u32 { if flag { a } else { a ^ 1 } }
    pub fn probe_div(a: u32, b: u32, flag: bool) -> u32 { if flag { a / b } else { 0 } }
    pub fn probe_unchecked(a: u32, flag: bool) -> u32 {
        if flag { unsafe { a.unchecked_add(1) } } else { a }
    }
    pub fn probe_rotate(a: u32, flag: bool) -> u32 { if flag { a.rotate_left(3) } else { a } }
    pub fn probe_asm(flag: bool) -> u32 {
        if flag { unsafe { core::arch::asm!("nop") }; 1 } else { 0 }
    }
    pub fn probe_write(r: &mut u32, flag: bool) { if flag { *r = 7; } }
"#;

/// For each arm of `fn_name`'s first `SwitchInt`: whether its region may check
/// or write.
fn arm_regions(fn_name: &str) -> Vec<bool> {
    let mut out = Vec::new();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let switch = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                TerminatorKind::SwitchInt { targets, .. } => Some(targets.clone()),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{fn_name} has no SwitchInt"));
        let mut arms: Vec<usize> = switch.branches().map(|(_, bb)| bb).collect();
        arms.push(switch.otherwise());
        out = arms.into_iter().map(|bb| region_may_check_or_write(&chc_ctx, &body, bb)).collect();
    });
    out
}

#[test]
fn test_region_without_effects_is_inert() {
    assert!(
        arm_regions("probe_pure").iter().all(|may| !may),
        "a Goto/Return-only region neither checks nor writes"
    );
}

#[test]
fn test_region_with_an_assert_checks() {
    assert!(arm_regions("probe_div").iter().any(|may| *may), "the divisor Assert is a check");
}

#[test]
fn test_region_with_a_ub_carrying_call_checks() {
    assert!(
        arm_regions("probe_unchecked").iter().any(|may| *may),
        "unchecked_add carries a UB precondition"
    );
}

#[test]
fn test_region_with_inline_asm_checks() {
    assert!(arm_regions("probe_asm").iter().any(|may| *may), "inline asm is opaque");
}

#[test]
fn test_region_with_a_write_through_a_deref_writes() {
    assert!(arm_regions("probe_write").iter().any(|may| *may), "*r = 7 writes");
}

/// An obligation-free intrinsic behind a call keeps the region inert, so the
/// `Rotate` proofs `rotate_left`'s body reaches keep their class.
#[test]
fn test_region_calling_rotate_left_is_inert() {
    assert!(
        arm_regions("probe_rotate").iter().all(|may| !may),
        "rotate_left is total and checks nothing"
    );
}
