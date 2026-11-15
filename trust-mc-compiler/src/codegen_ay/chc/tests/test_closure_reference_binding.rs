// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::common::*;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};

pub(super) const SOURCE: &str = r#"
#![feature(fn_traits)]
#![allow(dead_code, unused_assignments)]
fn copied(value: &u64) -> bool { let copy = value; *copy == 19 }
fn forwarded<F: FnOnce(&u64) -> bool>(value: &u64, f: F) -> bool { let copy = value; f(copy) }
pub fn direct_safe() { let x=19u64; assert!(forwarded(&x, copied)); }
pub fn direct_bug() { let x=19u64; assert!(!forwarded(&x, copied)); }
pub fn host_rustcall_safe() { let x=19u64; let a=&x; let b=a; assert!(FnOnce::call_once(copied,(b,))); }
pub fn host_rustcall_bug() { let x=19u64; let a=&x; let b=a; assert!(!FnOnce::call_once(copied,(b,))); }
pub fn host_pointer_safe() { let x=19u64; let y=19u64; let captures=(&x,&y); let env=&captures; let a=env.0; let b=env.1; assert!((a as *const u64)!=(b as *const u64)); }
pub fn host_pointer_bug() { let x=19u64; let y=19u64; let captures=(&x,&y); let env=&captures; let a=env.0; let b=env.1; assert!((a as *const u64)==(b as *const u64)); }
pub fn raw_reborrow_safe() { let p=core::ptr::null::<u64>(); let q=core::ptr::addr_of!(*p); assert!(q==p); }
pub fn raw_reborrow_bug() { let p=core::ptr::null::<u64>(); let q=core::ptr::addr_of!(*p); assert!(q!=p); }
pub fn joined_safe(flag: bool) { let a=11u64; let b=19u64; let r=if flag {&a} else {&b}; let f=|v:&u64| *v; assert!(f(r)==if flag {11} else {19}); }
pub fn joined_bug(flag: bool) { let a=11u64; let b=19u64; let r=if flag {&a} else {&b}; let f=|v:&u64| *v; assert!(f(r)!=if flag {11} else {19}); }
pub fn reassigned_tuple_safe(flag: bool) { let a=11u64; let b=19u64; let mut args=(&a,); if flag {args=(&b,);} let f=|v:&u64| *v; assert!(FnOnce::call_once(f,args)==if flag {19} else {11}); }
pub fn reassigned_tuple_bug(flag: bool) { let a=11u64; let b=19u64; let mut args=(&a,); if flag {args=(&b,);} let f=|v:&u64| *v; assert!(FnOnce::call_once(f,args)!=if flag {19} else {11}); }
pub fn escaped_tuple_safe() { let a=11u64; let b=19u64; let mut args=(&a,); let alias=&mut args; alias.0=&b; let f=|v:&u64| *v; assert!(FnOnce::call_once(f,args)==19); }
pub fn escaped_tuple_bug() { let a=11u64; let b=19u64; let mut args=(&a,); let alias=&mut args; alias.0=&b; let f=|v:&u64| *v; assert!(FnOnce::call_once(f,args)!=19); }
pub fn copied_tuple_safe() { let a=11u64; let b=19u64; let mut args=(&a,); let copy=args; args=(&b,); let f=|v:&u64| *v; assert!(FnOnce::call_once(f,copy)==11); }
pub fn copied_tuple_bug() { let a=11u64; let b=19u64; let mut args=(&a,); let copy=args; args=(&b,); let f=|v:&u64| *v; assert!(FnOnce::call_once(f,copy)!=11); }
pub fn reassigned_reference_safe() { let a=11u64; let b=19u64; let mut r=&a; r=&b; let f=|v:&u64| *v; assert!(f(r)==19); }
pub fn reassigned_reference_bug() { let a=11u64; let b=19u64; let mut r=&a; r=&b; let f=|v:&u64| *v; assert!(f(r)!=19); }

fn direct_compare(value: &u64) -> bool { *value == 11 }
fn copy_compare(value: &u64) -> bool { let copied = value; *copied == 11 }
pub fn joined_direct_safe(flag: bool) { let x=11u64; let y=11u64; let reference=if flag {&x} else {&y}; assert!(direct_compare(reference)); }
pub fn joined_direct_bug(flag: bool) { let x=11u64; let y=11u64; let reference=if flag {&x} else {&y}; assert!(!direct_compare(reference)); }
pub fn joined_copy_safe(flag: bool) { let x=11u64; let y=11u64; let reference=if flag {&x} else {&y}; assert!(copy_compare(reference)); }
pub fn joined_copy_bug(flag: bool) { let x=11u64; let y=11u64; let reference=if flag {&x} else {&y}; assert!(!copy_compare(reference)); }
pub fn capture_scalar_safe() { let bound=19u64; let f=|v:&u64| *v<bound; assert!(f(&11u64)); }
pub fn capture_scalar_bug() { let bound=19u64; let f=|v:&u64| *v<bound; assert!(!f(&11u64)); }
pub fn capture_pointer_safe() { let x=19u64; let y=19u64; let a=&x; let b=&y; let f=move|| (a as *const u64)==(b as *const u64); assert!(!f()); }
pub fn capture_pointer_bug() { let x=19u64; let y=19u64; let a=&x; let b=&y; let f=move|| (a as *const u64)==(b as *const u64); assert!(f()); }
pub fn capture_carrier_safe() { let x=19u64; let a=&x; let f=move|| { let address=&a as *const &u64; address==(&a as *const &u64) }; assert!(f()); }
pub fn capture_carrier_bug() { let x=19u64; let a=&x; let f=move|| { let address=&a as *const &u64; address==(&a as *const &u64) }; assert!(!f()); }

struct NarrowCapture<'a> { value: &'a u32 }
pub fn capture_selected_narrow_safe() { let x=19u32; let h=NarrowCapture{value:&x}; let r=h.value; let f=move|| *r==19; assert!(f()); }
pub fn capture_selected_narrow_bug() { let x=19u32; let h=NarrowCapture{value:&x}; let r=h.value; let f=move|| *r==19; assert!(!f()); }
"#;

#[test]
fn host_raw_reborrow_is_an_identity_without_a_pointee_load() {
    with_test_ay_ctx_for_source(
        "pub fn raw(p: *const u64) -> *const u64 { core::ptr::addr_of!(*p) }",
        |ctx| {
            let body = find_instance_by_suffix(ctx.tcx, "raw").callee_body().unwrap();
            for track in [crate::args::ChcTrackLevel::Reg, crate::args::ChcTrackLevel::Mem] {
                let mut chc = ChcCtx::new(
                    ctx.tcx,
                    &body,
                    "raw",
                    ChcConfig { track_level: track, ..ChcConfig::default() },
                );
                chc.declare_block_relations();
                let pointer = Expr::bitvec_const(0u64, 64);
                chc.encode.local_expr_env.insert(1, pointer.clone());
                let rvalue = rustc_public::mir::Rvalue::AddressOf(
                    rustc_public::mir::RawPtrKind::Const,
                    rustc_public::mir::Place {
                        local: 1,
                        projection: vec![rustc_public::mir::ProjectionElem::Deref],
                    },
                );
                assert_eq!(
                    chc.translate_rvalue_with_modified(&rvalue, &HashSet::from([1]), None),
                    Some(pointer)
                );
                assert!(
                    !chc.needs_mem_promote,
                    "a raw identity needs no reference validity checks"
                );
                assert!(chc.heap_state.pending_checks.is_empty());
            }
        },
    );
}

#[test]
fn closure_reference_binding_preserves_values_or_records_incomplete() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for track in [crate::args::ChcTrackLevel::Reg, crate::args::ChcTrackLevel::Mem] {
            for name in [
                "direct_safe",
                "direct_bug",
                "host_rustcall_safe",
                "host_rustcall_bug",
                "host_pointer_safe",
                "host_pointer_bug",
                "raw_reborrow_safe",
                "raw_reborrow_bug",
                "joined_safe",
                "joined_bug",
                "reassigned_tuple_safe",
                "reassigned_tuple_bug",
                "escaped_tuple_safe",
                "escaped_tuple_bug",
                "copied_tuple_safe",
                "copied_tuple_bug",
                "reassigned_reference_safe",
                "reassigned_reference_bug",
                "joined_direct_safe",
                "joined_direct_bug",
                "joined_copy_safe",
                "joined_copy_bug",
                "capture_scalar_safe",
                "capture_scalar_bug",
                "capture_pointer_safe",
                "capture_pointer_bug",
                "capture_carrier_safe",
                "capture_carrier_bug",
                "capture_selected_narrow_safe",
                "capture_selected_narrow_bug",
            ] {
                let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
                let chc = ChcCtx::new(
                    ctx.tcx,
                    &body,
                    name,
                    ChcConfig { track_level: track, ..ChcConfig::default() },
                );
                let (mut vc, promotion, mut diagnostics) = chc.translate_with_diagnostics();
                if promotion == crate::codegen_ay::chc::MemPromoteAction::Promote {
                    // Match the production entry point: a speculative Reg
                    // translation that requests memory is never a verdict.
                    let chc = ChcCtx::new(
                        ctx.tcx,
                        &body,
                        name,
                        ChcConfig {
                            track_level: crate::args::ChcTrackLevel::Mem,
                            ..ChcConfig::default()
                        },
                    );
                    let (promoted, action, checked) = chc.translate_with_diagnostics();
                    assert_eq!(action, crate::codegen_ay::chc::MemPromoteAction::Keep);
                    vc = promoted;
                    diagnostics = checked;
                }
                let result =
                    run_z3_on_smt2_with_timeout(&crate::codegen_ay::emit_chc(&vc).to_string(), 30);
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                eprintln!(
                    "CLOSURE_BIND {track:?} {name}: {result:?}; drop={}; reasons={reasons:?}",
                    diagnostics.place_translation_drop.get()
                );
                let expected = if name.ends_with("safe") { "unsat" } else { "sat" };
                assert!(result.is_ok(), "{name}: {result:?}");
                if name.starts_with("direct_")
                    || name.starts_with("host_rustcall_")
                    || name.starts_with("capture_scalar_")
                {
                    assert_eq!(result.as_deref(), Ok(expected), "{name}: {reasons:?}");
                    assert_eq!(diagnostics.place_translation_drop.get(), 0, "{name}: {reasons:?}");
                } else if result.as_deref() != Ok(expected) {
                    assert!(
                        diagnostics.place_translation_drop.get() > 0
                            && reasons
                                .keys()
                                .any(|reason| fallback_soundness(reason)
                                    == FallbackSoundness::FailClose),
                        "{name}: wrong clean model {result:?}, {reasons:?}"
                    );
                }
            }
        }
    });
}
