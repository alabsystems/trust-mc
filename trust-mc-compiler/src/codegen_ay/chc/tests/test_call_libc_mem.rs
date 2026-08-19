// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for `codegen_call_libc_mem.rs` — the direct
//! `libc::{malloc, free, memset}` models.
//!
//! The property under test is the pair the model has to hold at once:
//! - a modelled call does NOT reach the undefined-foreign `error()` emission
//!   (that head is what made every C-allocation harness fail on a
//!   counterexample naming no user assertion), and
//! - a shape the model cannot encode exactly DOES still reach it, because the
//!   alternative — encoding it approximately — would leave a pre-`memset` value
//!   readable and hide a bug.
//!
//! Part of #3175.

#![allow(clippy::unwrap_used)]

use super::common::*;

const MALLOC_MEMSET_FREE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(rustc_private)]

    extern crate libc;

    pub unsafe fn probe_libc_malloc_memset_free() {
        unsafe {
            let p = libc::malloc(4);
            let _ = libc::memset(p, 1, 4);
            libc::free(p);
        }
    }
"#;

const MEMSET_STACK_LOCAL_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(rustc_private)]

    extern crate libc;

    pub unsafe fn probe_libc_memset_stack_local() -> u32 {
        let mut x: u32 = 7;
        unsafe {
            libc::memset(&mut x as *mut u32 as *mut libc::c_void, 0, 4);
        }
        x
    }
"#;

const DOUBLE_FREE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(rustc_private)]

    extern crate libc;

    pub unsafe fn probe_libc_double_free() {
        unsafe {
            let p = libc::malloc(4);
            libc::free(p);
            libc::free(p);
        }
    }
"#;

/// The undefined-foreign emission is the ONLY producer of an `error` head whose
/// body is a block relation: every checked obligation heads a per-property
/// `error_p{id}` relation and reaches `error` through a relation-only bridge
/// rule. So this predicate separates "the call was not modelled" from "the call
/// was modelled and carries obligations".
fn has_undefined_foreign_error_rule(vc: &trust_mc_core::chc::ChcVc) -> bool {
    vc.rules.iter().any(|rule| {
        rule.head.name == "error"
            && rule
                .body
                .relation
                .as_ref()
                .is_some_and(|body_rel| !body_rel.name.starts_with("error_p"))
    })
}

#[test]
fn test_libc_malloc_memset_free_are_modeled_not_undefined_foreign() {
    with_test_ay_ctx_for_source(MALLOC_MEMSET_FREE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_libc_malloc_memset_free");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_libc_malloc_memset_free", ChcConfig::default());

        assert!(
            !has_undefined_foreign_error_rule(&vc),
            "malloc/memset/free must be modeled, not emitted as undefined-foreign error()"
        );
        // The models are not silent: malloc's allocation preconditions, memset's
        // base-identity and validity obligations and free's double-free /
        // base-address obligations are all registered as properties.
        assert!(
            !vc.properties.is_empty(),
            "the malloc / memset / free models must carry their obligations"
        );
    });
}

#[test]
fn test_libc_memset_on_stack_local_stays_fail_closed() {
    with_test_ay_ctx_for_source(MEMSET_STACK_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_libc_memset_stack_local");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_libc_memset_stack_local", ChcConfig::default());

        // A stack local is read through its state VARIABLE, which no memory-array
        // fill reaches — encoding the fill anyway would prove the local kept its
        // pre-`memset` value. The model must refuse the shape and leave the
        // fail-closed emission in place.
        assert!(
            has_undefined_foreign_error_rule(&vc),
            "memset of a stack local must stay fail-closed, not be modeled as a fill"
        );
    });
}

#[test]
fn test_libc_free_keeps_double_free_obligation() {
    with_test_ay_ctx_for_source(DOUBLE_FREE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_libc_double_free");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_libc_double_free", ChcConfig::default());

        assert!(
            !has_undefined_foreign_error_rule(&vc),
            "free must be modeled, not emitted as undefined-foreign error()"
        );
        assert!(
            !vc.properties.is_empty(),
            "the free model must keep its memory-safety obligations (double free)"
        );
    });
}
