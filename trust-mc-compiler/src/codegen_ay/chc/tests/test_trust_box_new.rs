// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Trust toolchain: `Box::new` without `Rvalue::ShallowInitBox`.
//!
//! The frozen nightly lowers `Box::new` through `ShallowInitBox`, and every test of that shape is
//! `cfg(not(trust_toolchain))`. Trust's library has neither `ShallowInitBox` nor
//! `exchange_malloc`: `Box::new` is `box_new_uninit(LAYOUT) as *mut T; write_via_move(ptr, x);
//! transmute(ptr)`. A direct `Box::new` call must still be claimed by the name-keyed `BoxNew`
//! allocation stub, so the Trust library body is never encoded, and the encoding must prove a
//! correct read through the box and refute a wrong one.

#![allow(clippy::unwrap_used, clippy::panic)]

use rustc_public::mir::TerminatorKind;
use rustc_public::mir::mono::Instance;

use super::common::*;

const BOX_READ_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_box_new_read_ok() {
        let b = Box::new(42u32);
        assert!(*b == 42);
    }

    pub fn probe_box_new_read_bug() {
        let b = Box::new(42u32);
        assert!(*b == 43);
    }
"#;

/// Match the driver's default abort strategy without disabling the compiler's
/// null, alignment, overflow or other debug checks.
pub(super) fn with_native_box_ctx<F>(source: &str, callback: F)
where
    F: for<'tcx> FnOnce(crate::codegen_ay::context::AYCtx<'tcx, 'static>) + Send,
{
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
        source,
        &["-Cpanic=abort"],
        callback,
    );
}

pub(super) fn mem_config() -> ChcConfig {
    ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() }
}

fn chc_verdict(tcx: TyCtxt<'_>, name: &str) -> (String, usize) {
    let instance = find_instance_by_suffix(tcx, name);
    let body = instance.body().expect("function body");
    let (vc, _, diagnostics) =
        ChcCtx::new(tcx, &body, name, mem_config()).translate_with_diagnostics();
    let smt = crate::codegen_ay::emit_chc(&vc).to_string();
    let verdict = run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30))
        .unwrap_or_else(|err| format!("error:{err}"));
    let drops = diagnostics.place_translation_drop.get();
    if drops != 0 || (name.ends_with("ok") && verdict != "unsat") {
        let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
            .remove(name)
            .unwrap_or_default();
        eprintln!("{name}: {verdict}; drops={drops}; reasons={reasons:?}\n{smt}");
    }
    (verdict, drops)
}

#[test]
fn test_trust_box_new_call_is_claimed_by_the_box_new_stub() {
    with_native_box_ctx(BOX_READ_SOURCE, |ctx| {
        for name in ["probe_box_new_read_ok", "probe_box_new_read_bug"] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, name, mem_config());
            let mut claimed = 0;
            for block in &body.blocks {
                let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                    continue;
                };
                let Some(path) = chc_ctx.resolve_callee_path(func) else {
                    continue;
                };
                if !(path.contains("boxed::Box::") && path.ends_with(">::new")) {
                    continue;
                }
                assert_eq!(
                    chc_ctx.detect_alloc_stub(func),
                    Some(StubKind::BoxNew),
                    "{name}: `{path}` must be claimed by the BoxNew allocation stub"
                );
                claimed += 1;

                // Pin the Trust library shape the stub stands in for.
                let ty = func.ty(body.locals()).expect("callee type");
                let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else {
                    panic!("{name}: Box::new callee is not a FnDef: {ty:?}");
                };
                let callee = Instance::resolve(def, &args).expect("resolve Box::new");
                let callee_body = callee.body().expect("Box::new body");
                let calls: Vec<String> = callee_body
                    .blocks
                    .iter()
                    .filter_map(|block| match &block.terminator.kind {
                        TerminatorKind::Call { func, .. } => {
                            match func.ty(callee_body.locals()).ok()?.kind() {
                                TyKind::RigidTy(RigidTy::FnDef(def, _)) => Some(def.name()),
                                _ => None,
                            }
                        }
                        _ => None,
                    })
                    .collect();
                eprintln!("[trust box_new] {name}: `{path}` body calls {calls:?}");
                assert!(
                    !calls.iter().any(|call| call.contains("exchange_malloc")),
                    "Trust's Box::new must not reach exchange_malloc: {calls:?}"
                );
            }
            assert_eq!(claimed, 1, "{name}: expected exactly one Box::new call");
        }
    });
}

#[test]
fn test_trust_box_new_read_proves() {
    with_native_box_ctx(BOX_READ_SOURCE, |ctx| {
        assert_eq!(
            chc_verdict(ctx.tcx, "probe_box_new_read_ok"),
            ("unsat".to_owned(), 0),
            "reading back the boxed value must prove"
        );
    });
}

#[test]
fn test_trust_box_new_wrong_read_fails() {
    with_native_box_ctx(BOX_READ_SOURCE, |ctx| {
        assert_eq!(
            chc_verdict(ctx.tcx, "probe_box_new_read_bug"),
            ("sat".to_owned(), 0),
            "a wrong read through the box must be refuted"
        );
    });
}

#[test]
fn native_box_unwind_cleanup_retains_its_failclosed_debt() {
    // The separate unwind lane must not have its Resume refusal subtracted
    // just to satisfy the default abort lane's strict zero-debt controls.
    with_test_ay_ctx_for_source(BOX_READ_SOURCE, |ctx| {
        let (verdict, drops) = chc_verdict(ctx.tcx, "probe_box_new_read_ok");
        assert_eq!(verdict, "unsat");
        assert!(drops > 0, "unsupported unwind cleanup must retain actual debt");
    });
}

#[test]
fn zero_sized_box_birth_does_not_authorize_a_heap_allocation_address() {
    use rustc_public::mir::{CastKind, Rvalue, StatementKind};
    let source = r#"
        pub fn zst_pointer() -> *const () {
            let value = Box::new(());
            let pointer = &raw const *value;
            core::mem::forget(value);
            pointer
        }
    "#;
    with_native_box_ctx(source, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "zst_pointer").body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "zst_pointer", mem_config());
        let (site, args, destination) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(site, block)| {
                let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                else {
                    return None;
                };
                (chc.detect_alloc_stub(func) == Some(StubKind::BoxNew)).then_some((
                    site,
                    args,
                    destination,
                ))
            })
            .unwrap();
        chc.current_encode_bb = site;
        let allocation = chc.translate_alloc_call(StubKind::BoxNew, args, &HashSet::new()).unwrap();
        // Reproduce the legacy stub's synthetic allocation ID. It is not a
        // native Box allocation, and must not license address recovery.
        assert!(allocation.alloc_obj_id.is_some());
        chc.record_alloc_dest(destination.local, allocation.alloc_obj_id);
        let (operand, target) = body
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .find_map(|statement| match &statement.kind {
                StatementKind::Assign(
                    _,
                    Rvalue::Cast(CastKind::BoxDerefTransmute, operand, target),
                ) => Some((operand, target)),
                _ => None,
            })
            .expect("actual native ZST BoxDerefTransmute");
        assert!(chc.host_native_thin_box_address(operand, *target).is_none());
    });
}

pub(super) fn native_box_runtime_source() -> String {
    let mut source = include_str!("../../../../../tools/soundness-duals/native_boxraw_dual.rs")
        .lines()
        .filter(|line| !line.starts_with("//!"))
        .collect::<Vec<_>>()
        .join("\n")
        .replace("#[kani::proof]", "");
    source.insert_str(
        0,
        r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]
        mod kani {
            #[kanitool::fn_marker = "AnyModel"]
            pub fn any<T>() -> T { any_raw() }
            #[kanitool::fn_marker = "AnyRawHook"]
            fn any_raw<T>() -> T { panic!("model-only raw hook") }
            #[kanitool::fn_marker = "AssumeHook"]
            pub fn assume(_value: bool) {}
        }
    "#,
    );
    source
}

#[test]
fn native_box_runtime_source_keeps_strict_read_and_write_polarity() {
    let source = native_box_runtime_source();
    with_native_box_ctx(&source, |ctx| {
        let mut failures = Vec::new();
        for name in [
            "boxed_scalar_read_safe",
            "boxed_scalar_wrong_value_bug",
            "boxed_array_element_read_safe",
            "boxed_array_wrong_element_bug",
            "boxed_symbolic_element_write_safe",
            "boxed_symbolic_element_wrong_value_bug",
            "user_boxraw_keeps_its_actual_fields_safe",
            "user_boxraw_wrong_field_bug",
        ] {
            let expected = if name.ends_with("safe") { "unsat" } else { "sat" };
            let actual = chc_verdict(ctx.tcx, name);
            eprintln!("NATIVE_BOX_ROW {name}: {actual:?}");
            if actual != (expected.to_owned(), 0) {
                failures.push((name, actual));
            }
        }
        assert!(failures.is_empty(), "strict native Box rows: {failures:?}");
    });
}

#[test]
fn native_box_address_recovery_preserves_moves_and_distinct_allocations() {
    let source = r#"
        #![allow(dead_code)]
        pub fn moved_ok() {
            let first = Box::new(3u32);
            let value = Box::new(11u32);
            let moved = value;
            assert!(*moved == 11 && *first == 3);
        }
        pub fn moved_bug() {
            let first = Box::new(3u32);
            let value = Box::new(11u32);
            let moved = value;
            assert!(*moved == 3 && *first == 3);
        }
    "#;
    with_native_box_ctx(source, |ctx| {
        assert_eq!(chc_verdict(ctx.tcx, "moved_ok"), ("unsat".to_owned(), 0));
        assert_eq!(chc_verdict(ctx.tcx, "moved_bug"), ("sat".to_owned(), 0));
    });
}

#[test]
fn native_box_joined_or_replaced_carriers_keep_polarity_or_fail_closed() {
    let source = r#"
        #![allow(dead_code)]
        pub fn joined_ok(branch: bool) {
            let value = if branch { Box::new(11u32) } else { Box::new(13u32) };
            assert!(*value == 11 || *value == 13);
        }
        pub fn joined_bug(branch: bool) {
            let value = if branch { Box::new(11u32) } else { Box::new(13u32) };
            assert!(*value == 7);
        }
        #[inline(never)]
        fn replace(value: &mut Box<u32>) { *value = Box::new(19); }
        pub fn replaced_ok() {
            let mut value = Box::new(11u32);
            replace(&mut value);
            assert!(*value == 19);
        }
        pub fn replaced_bug() {
            let mut value = Box::new(11u32);
            replace(&mut value);
            assert!(*value == 11);
        }
    "#;
    with_native_box_ctx(source, |ctx| {
        for name in ["joined_ok", "joined_bug", "replaced_ok", "replaced_bug"] {
            let (verdict, drops) = chc_verdict(ctx.tcx, name);
            let expected = if name.ends_with("ok") { "unsat" } else { "sat" };
            assert!(verdict == expected || drops > 0, "{name}: wrong clean {verdict}");
        }
    });
}

#[test]
fn user_global_allocator_effects_prevent_clean_box_certification() {
    let source = r#"
        #![allow(dead_code)]
        use std::alloc::{GlobalAlloc, Layout, System};
        use std::sync::atomic::{AtomicUsize, Ordering};
        struct Allocator;
        static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
        unsafe impl GlobalAlloc for Allocator {
            unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
                ALLOCATIONS.fetch_add(1, Ordering::SeqCst);
                unsafe { System.alloc(layout) }
            }
            unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
                unsafe { System.dealloc(pointer, layout) }
            }
        }
        #[global_allocator]
        static ALLOCATOR: Allocator = Allocator;
        pub fn allocator_probe() {
            let value = Box::new(11u32);
            assert!(*value == 11);
        }
    "#;
    with_native_box_ctx(source, |ctx| {
        let (_, drops) = chc_verdict(ctx.tcx, "allocator_probe");
        assert!(drops > 0, "custom allocator effects require actual FailClose debt");
    });
}
