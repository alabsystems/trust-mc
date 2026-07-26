// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_bindings::{Expr, Sort};

use crate::codegen_ay::chc::{ChcConfig, ChcCtx};
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::CrateItem;
use rustc_public::rustc_internal;
use rustc_public::ty::FnSig;

use super::baseline::restore_dyn_drop_d2_candidate_baseline;
use super::box_drop::find_concrete_source_for_box_dyn_local;
use super::codegen_drop::{coroutine_drop_fields_trivially_no_drop, pin_box_coroutine_inner_ty};
use super::no_drop::is_box_with_dyn_inner;
use super::shared_ptr::shared_pointer_value_ptr_from_alloc_id;
use super::ty_trivially_no_drop;
use crate::codegen_ay::chc::dyn_coercion::{
    extract_dyn_trait_def_id, peel_pointer_like_wrapper_ty, resolve_dyn_target_vtable_id,
};

fn fn_sig_by_suffix(tcx: TyCtxt<'_>, suffix: &str) -> FnSig {
    let item = find_crate_item_by_suffix(tcx, suffix);
    let def_id = rustc_internal::internal(tcx, item.def_id());
    let fn_ty = rustc_internal::stable(tcx.type_of(def_id)).value;
    fn_ty.kind().fn_sig().expect("expected function signature").skip_binder()
}

fn find_crate_item_by_suffix(tcx: TyCtxt<'_>, suffix: &str) -> CrateItem {
    let matches: Vec<_> = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| {
            let def_id = rustc_internal::internal(tcx, item.def_id());
            let path = tcx.def_path_str(def_id);
            path == suffix || path.ends_with(&format!("::{suffix}"))
        })
        .collect();
    match matches.as_slice() {
        [] => panic!("missing item with suffix '{suffix}'"),
        [single] => *single,
        many => panic!("ambiguous suffix '{suffix}': {} matches", many.len()),
    }
}

fn fn_input_ty_by_suffix(tcx: TyCtxt<'_>, suffix: &str, index: usize) -> rustc_public::ty::Ty {
    fn_sig_by_suffix(tcx, suffix)
        .inputs()
        .get(index)
        .copied()
        .unwrap_or_else(|| panic!("missing input {index} for '{suffix}'"))
}

fn collect_auto_trait_box_unsize_sites(
    chc_ctx: &ChcCtx<'_, '_>,
) -> Vec<(usize, rustc_public::ty::Ty, rustc_public::ty::Ty)> {
    use rustc_public::mir::{CastKind, PointerCoercion, Rvalue, StatementKind};
    use rustc_public::ty::{RigidTy, TyKind};

    let mut sites = Vec::new();
    for bb in &chc_ctx.body.blocks {
        for stmt in &bb.statements {
            let StatementKind::Assign(
                place,
                Rvalue::Cast(
                    CastKind::PointerCoercion(PointerCoercion::Unsize),
                    operand,
                    target_ty,
                ),
            ) = &stmt.kind
            else {
                continue;
            };

            let target_inner = peel_pointer_like_wrapper_ty(*target_ty);
            if !matches!(target_inner.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
                continue;
            }
            // After #4097 D2, extract_dyn_trait_def_id returns Some for
            // auto-traits (Send/Sync/Unpin). Filter to auto-trait-only dyn
            // types by checking if the resolved trait is an auto-trait.
            let Some(trait_def_id) = extract_dyn_trait_def_id(chc_ctx, target_inner) else {
                continue;
            };
            let trait_name = chc_ctx.tcx.item_name(trait_def_id);
            if !matches!(trait_name.as_str(), "Send" | "Sync" | "Unpin") {
                continue;
            }

            let src_ty = operand.ty(chc_ctx.body.locals()).expect("unsize src ty");
            sites.push((place.local, src_ty, target_inner));
        }
    }
    sites
}

#[test]
fn test_restore_dyn_drop_d2_candidate_baseline_clears_candidate_heap_residue() {
    with_test_ay_ctx_for_source(
        "pub fn probe_dyn_drop_d2_restore(seed: u32) -> u32 { seed }",
        |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "probe_dyn_drop_d2_restore");
            let body = instance.body().expect("body");
            let mut chc_ctx =
                ChcCtx::new(ctx.tcx, &body, "probe_dyn_drop_d2_restore", ChcConfig::default());
            let baseline_modified = chc_ctx.encode.modified_state_indices.clone();
            let baseline_heap = chc_ctx.heap_state.snapshot_transient_rule_state();

            // Candidate A leaves transient heap residue while inlining.
            chc_ctx.encode.modified_state_indices.insert(usize::MAX);
            chc_ctx.heap_state.pending_updates.push(Expr::bool_const(true));
            chc_ctx.heap_state.pending_checks.push(Expr::bool_const(false));
            chc_ctx.heap_state.modified_arrays.insert("candidate_a".into());
            let addr = Expr::bitvec_const(0, 64);
            let base = Expr::var(
                "_dyn_drop_candidate_mem",
                Sort::array(Sort::bitvec(64), Sort::bitvec(32)),
            );
            let store = base.store(addr.clone(), Expr::bitvec_const(7, 32));
            chc_ctx.heap_state.store_chains.insert(
                "candidate_a".into(),
                ("_dyn_drop_candidate_mem__out".into(), store.clone()),
            );
            chc_ctx.heap_state.drained_store_chain_seeds.insert("candidate_a".into(), store);
            chc_ctx.heap_state.metadata_arrays_modified = true;
            chc_ctx.heap_state.mirror_base_addrs.insert("candidate_a".into(), addr);
            chc_ctx.heap_state.store_forward_map.insert(0, (0, Expr::bitvec_const(9, 32)));

            restore_dyn_drop_d2_candidate_baseline(
                &mut chc_ctx,
                &baseline_modified,
                &baseline_heap,
            );

            assert_eq!(chc_ctx.encode.modified_state_indices, baseline_modified);
            assert!(chc_ctx.heap_state.pending_updates.is_empty());
            assert!(chc_ctx.heap_state.pending_checks.is_empty());
            assert!(chc_ctx.heap_state.modified_arrays.is_empty());
            assert!(chc_ctx.heap_state.store_chains.is_empty());
            assert!(chc_ctx.heap_state.drained_store_chain_seeds.is_empty());
            assert!(!chc_ctx.heap_state.metadata_arrays_modified);
            assert!(chc_ctx.heap_state.mirror_base_addrs.is_empty());
            assert!(chc_ctx.heap_state.store_forward_map.is_empty());

            // Candidate B starts from the same baseline, not candidate A residue.
            chc_ctx.encode.modified_state_indices.insert(1234);
            chc_ctx.heap_state.pending_updates.push(Expr::bool_const(false));
            chc_ctx.heap_state.modified_arrays.insert("candidate_b".into());

            restore_dyn_drop_d2_candidate_baseline(
                &mut chc_ctx,
                &baseline_modified,
                &baseline_heap,
            );

            assert_eq!(chc_ctx.encode.modified_state_indices, baseline_modified);
            assert!(chc_ctx.heap_state.pending_updates.is_empty());
            assert!(chc_ctx.heap_state.modified_arrays.is_empty());
        },
    );
}

#[test]
fn test_ty_trivially_no_drop_recognizes_plain_struct_and_tuple_inputs() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Plain {
            a: u8,
            b: [u16; 2],
        }

        pub fn probe_plain(x: Plain) {
            let _ = x;
        }

        pub fn probe_tuple(x: (u8, [u16; 2])) {
            let _ = x;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let plain_ty = fn_input_ty_by_suffix(ctx.tcx, "probe_plain", 0);
        let tuple_ty = fn_input_ty_by_suffix(ctx.tcx, "probe_tuple", 0);

        assert!(ty_trivially_no_drop(plain_ty));
        assert!(ty_trivially_no_drop(tuple_ty));
    });
}

#[test]
fn test_no_drop_helpers_reject_box_backed_inputs_and_detect_dyn_box() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub trait Marker {}

        pub struct NeedsDrop {
            inner: Box<u8>,
        }

        pub fn probe_needs_drop(x: NeedsDrop) {
            let _ = x;
        }

        pub fn probe_box_dyn(x: Box<dyn Marker>) {
            let _ = x;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let needs_drop_ty = fn_input_ty_by_suffix(ctx.tcx, "probe_needs_drop", 0);
        let box_dyn_ty = fn_input_ty_by_suffix(ctx.tcx, "probe_box_dyn", 0);

        assert!(!ty_trivially_no_drop(needs_drop_ty));
        assert!(is_box_with_dyn_inner(box_dyn_ty));
        assert!(!ty_trivially_no_drop(box_dyn_ty));
    });
}

#[test]
fn test_find_concrete_source_for_box_dyn_local_handles_auto_trait_unsize_sites() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        struct Concrete;

        pub fn probe_box_dyn_send() {
            let _plain: Box<dyn Send> = Box::new(Concrete);
            let inner: Box<dyn Send> = Box::new(Concrete);
            let _nested: Box<dyn Send> = Box::new(inner);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_dyn_send");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_box_dyn_send", ChcConfig::default());
        let sites = collect_auto_trait_box_unsize_sites(&chc_ctx);
        assert!(
            sites.len() >= 2,
            "expected plain and nested Box<dyn Send> unsize sites, got {}",
            sites.len()
        );

        for (local_idx, src_ty, _) in sites {
            let concrete_ty = find_concrete_source_for_box_dyn_local(&chc_ctx, local_idx)
                .unwrap_or_else(|| panic!("missing concrete source for local {local_idx}"));
            let expected = peel_pointer_like_wrapper_ty(src_ty);
            assert_eq!(
                concrete_ty, expected,
                "local {local_idx} should resolve to the peeled concrete unsize source"
            );
        }
    });
}

#[test]
fn test_resolve_dyn_target_vtable_id_handles_auto_trait_candidates() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        struct Concrete;

        pub fn probe_box_dyn_send() {
            let _plain: Box<dyn Send> = Box::new(Concrete);
            let inner: Box<dyn Send> = Box::new(Concrete);
            let _nested: Box<dyn Send> = Box::new(inner);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_dyn_send");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_box_dyn_send", ChcConfig::default());
        let sites = collect_auto_trait_box_unsize_sites(&chc_ctx);
        let mut ids = Vec::new();

        for (_local_idx, src_ty, target_inner) in sites {
            let concrete_ty = peel_pointer_like_wrapper_ty(src_ty);
            let vtable_id = resolve_dyn_target_vtable_id(&chc_ctx, target_inner, concrete_ty)
                .unwrap_or_else(|| panic!("missing auto-trait vtable id for {concrete_ty:?}"));
            ids.push(vtable_id);
        }

        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids, vec![0, 1], "auto-trait unsize candidates should get stable ids");
    });
}

#[test]
fn test_shared_pointer_value_ptr_from_alloc_id_applies_rc_header_offset() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::cell::RefCell;
        use std::rc::Rc;

        pub fn probe_rc_refcell() {
            let _wrapped: Rc<RefCell<u32>> = Rc::new(RefCell::new(1));
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_refcell");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_rc_refcell", ChcConfig::default());
        let local_idx = body
            .locals()
            .iter()
            .enumerate()
            .find_map(|(idx, local)| match local.ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "Rc" => Some(idx),
                _ => None,
            })
            .expect("missing Rc local");
        let inner_ty = match body.locals()[local_idx].ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(_, args)) => match args.0.first() {
                Some(GenericArgKind::Type(ty)) => *ty,
                other => panic!("missing Rc inner type: {other:?}"),
            },
            other => panic!("unexpected Rc local ty: {other:?}"),
        };

        chc_ctx.known_alloc_ids.insert(local_idx, 7);
        let ptr_expr = shared_pointer_value_ptr_from_alloc_id(&chc_ctx, local_idx, inner_ty)
            .expect("expected shared-pointer value ptr");
        let ptr_str = format!("{ptr_expr}");
        assert!(
            ptr_str.contains("#x00000007") && ptr_str.contains("#x0000000000000010"),
            "expected alloc_id 7 with 16-byte Rc header offset, got {ptr_str}"
        );
    });
}

/// Part of #4268: Verify that Mutex/RwLock types are classified as trivially-no-drop.
/// Mutex<T>::drop only destroys the platform mutex (no program-visible side effects).
/// This prevents the recursive no-drop check from failing on types like
/// Arc<Mutex<[u8]>> where the Mutex wrapper has a non-empty drop shim.
#[test]
fn test_ty_trivially_no_drop_classifies_mutex_rwlock_as_dealloc_only() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::sync::Mutex;
        use std::sync::RwLock;
        use std::cell::RefCell;

        pub fn probe_mutex(x: Mutex<u32>) {
            let _ = x;
        }

        pub fn probe_rwlock(x: RwLock<u32>) {
            let _ = x;
        }

        pub fn probe_refcell_u32(x: RefCell<u32>) {
            let _ = x;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let mutex_ty = fn_input_ty_by_suffix(ctx.tcx, "probe_mutex", 0);
        let rwlock_ty = fn_input_ty_by_suffix(ctx.tcx, "probe_rwlock", 0);
        let refcell_ty = fn_input_ty_by_suffix(ctx.tcx, "probe_refcell_u32", 0);

        // Mutex/RwLock should be trivially-no-drop (dealloc-only Drop).
        assert!(ty_trivially_no_drop(mutex_ty), "Mutex<u32> should be trivially-no-drop (#4268)");
        assert!(ty_trivially_no_drop(rwlock_ty), "RwLock<u32> should be trivially-no-drop (#4268)");
        // RefCell<u32> has a non-empty drop shim because RefCell internally
        // uses Cell<isize> for borrow tracking and UnsafeCell for the value.
        // The compiler generates drop glue even when T has no Drop impl.
        // RefCell is NOT in the dealloc-only allowlist because its drop glue
        // must recurse into T's Drop when T implements Drop.
        assert!(
            !ty_trivially_no_drop(refcell_ty),
            "RefCell<u32> has a non-empty drop shim (borrow tracking internals)"
        );
    });
}

#[test]
fn test_pin_box_coroutine_drop_guard_rejects_custom_drop_capture() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(unused_variables)]

        use std::future;
        use std::sync::{
            Arc,
            atomic::AtomicI64,
        };

        struct NeedsDrop(u8);

        impl Drop for NeedsDrop {
            fn drop(&mut self) {
                assert!(std::mem::size_of::<usize>() > 0);
            }
        }

        pub fn probe_arc_pinbox() {
            let x = Arc::new(AtomicI64::new(0));
            let fut = async move {
                future::pending::<()>().await;
                std::mem::drop(x);
            };
            let pinbox = Box::pin(fut);
        }

        pub fn probe_custom_pinbox() {
            let needs_drop = NeedsDrop(1);
            let fut = async move {
                future::pending::<()>().await;
                std::mem::drop(needs_drop);
            };
            let pinbox = Box::pin(fut);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let arc_instance = find_instance_by_suffix(ctx.tcx, "probe_arc_pinbox");
        let arc_body = arc_instance.body().expect("probe_arc_pinbox body");
        let arc_chc_ctx = ChcCtx::new(ctx.tcx, &arc_body, "probe_arc_pinbox", ChcConfig::default());
        let arc_coroutine_ty = arc_body
            .locals()
            .iter()
            .find_map(|local| pin_box_coroutine_inner_ty(local.ty))
            .expect("missing Pin<Box<Coroutine>> local for Arc capture");
        assert!(
            coroutine_drop_fields_trivially_no_drop(&arc_chc_ctx, arc_coroutine_ty),
            "Arc capture should be safe for Pin<Box<Coroutine>> dealloc-only drop"
        );

        let custom_instance = find_instance_by_suffix(ctx.tcx, "probe_custom_pinbox");
        let custom_body = custom_instance.body().expect("probe_custom_pinbox body");
        let custom_chc_ctx =
            ChcCtx::new(ctx.tcx, &custom_body, "probe_custom_pinbox", ChcConfig::default());
        let custom_coroutine_ty = custom_body
            .locals()
            .iter()
            .find_map(|local| pin_box_coroutine_inner_ty(local.ty))
            .expect("missing Pin<Box<Coroutine>> local for custom Drop capture");
        assert!(
            !coroutine_drop_fields_trivially_no_drop(&custom_chc_ctx, custom_coroutine_ty),
            "custom Drop capture must stay on the generic drop path"
        );
    });
}
