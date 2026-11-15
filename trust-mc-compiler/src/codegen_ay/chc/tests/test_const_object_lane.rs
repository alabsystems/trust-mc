// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The global-object bound (`object_span_checks`) checks the address's
//! obj_id lane as well as its offset. A wrapping step of exactly 2^32 bytes
//! through a constant pointer to a static moves the lane and leaves the low
//! 32 offset bits inside the object, so a bound that read only the offset
//! proved `*(&V as *const u32).wrapping_byte_add(k)` with `k == 2^32`, where
//! Kani reports "pointer outside object bounds" (main dd0d949a9 alike).
//!
//! Each bug probe must reach its error, and each safe twin must prove.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

const CONST_LANE_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, _msg: &str) {
            let _ = cond;
        }
    }

    use std::ptr::addr_of;
    use std::sync::atomic::AtomicU32;

    static V: u32 = 7;
    static A: AtomicU32 = AtomicU32::new(5);

    pub fn probe_ref_static_wrap_2p32_bug(k: usize) -> u32 {
        if k != 1usize << 32 {
            return 0;
        }
        let p: *const u32 = &V;
        unsafe { *p.wrapping_byte_add(k) }
    }

    pub fn probe_ref_static_wrap_zero_safe(k: usize) {
        if k != 0 {
            return;
        }
        let p: *const u32 = &V;
        kani::assert(unsafe { *p.wrapping_byte_add(k) } == 7, "inside V");
    }

    pub fn probe_addr_of_static_wrap_sub_2p32_bug(k: usize) -> u32 {
        if k != 1usize << 32 {
            return 0;
        }
        let p: *const u32 = addr_of!(V);
        unsafe { *p.wrapping_byte_sub(k) }
    }

    pub fn probe_atomic_cast_wrap_2p32_bug(k: usize) -> u32 {
        if k != 1usize << 32 {
            return 0;
        }
        let p = &A as *const AtomicU32 as *const u32;
        unsafe { *p.wrapping_byte_add(k) }
    }
"#;

/// Encode `fn_name`, solve it, and return the verdict.
fn solve_probe(fn_name: &str) -> String {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut verdict = None;
    with_test_ay_ctx_for_source(CONST_LANE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        vc.propagate_constants();
        vc.prune_orphan_block_rules();
        vc.prune_dead_identity_scalars();
        vc.normalize_free_array_bases();
        crate::codegen_ay::chc::scalarize_vc(&mut vc);
        vc.prune_dead_vars_and_constraints();
        let smt = emit_chc(&vc).to_string();
        verdict = Some(
            run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30))
                .unwrap_or_else(|e| panic!("AY failed on {fn_name}: {e}")),
        );
    });
    verdict.expect("the probe was encoded")
}

#[test]
fn test_wrap_by_2p32_past_a_static_through_a_reference_fails() {
    assert_eq!(solve_probe("probe_ref_static_wrap_2p32_bug"), "sat");
}

#[test]
fn test_wrap_by_zero_inside_a_static_through_a_reference_proves() {
    assert_eq!(solve_probe("probe_ref_static_wrap_zero_safe"), "unsat");
}

#[test]
fn test_wrap_back_by_2p32_through_addr_of_fails() {
    assert_eq!(solve_probe("probe_addr_of_static_wrap_sub_2p32_bug"), "sat");
}

#[test]
fn test_wrap_by_2p32_past_an_atomic_static_through_a_cast_fails() {
    assert_eq!(solve_probe("probe_atomic_cast_wrap_2p32_bug"), "sat");
}
