// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Cell/RefCell semantic-handler regression guards.
//!
//! Covers the three soundness-critical behaviors of `codegen_call_cell.rs`:
//! - `detect_cell_method` classifies each accessor by callee def-path;
//! - the handler FAILS CLOSED (declines the call) when no real referent
//!   address can be recovered — never a store to a fabricated address;
//! - a `Cell::replace` with a recoverable address is modeled as a direct
//!   load/store sequence (dispatch handled, no sound-fallback demotion).

#![allow(clippy::unwrap_used, clippy::panic)]

use std::collections::HashSet;

use super::common::*;
use crate::args::ChcTrackLevel;
use crate::codegen_ay::chc::call::codegen_call_cell::{CallCell, CellMethod};
use crate::codegen_ay::chc::chc_call_context::CallEmitContext;
use crate::codegen_ay::chc::codegen_ctx::RefTarget;

const CELL_OPS_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::{Cell, RefCell};

    pub fn probe_cell_ops(c: &Cell<u32>, r: &RefCell<u32>, v: u32) -> u32 {
        c.set(v);
        let a = c.get();
        let b = c.replace(v);
        let t = c.take();
        r.replace(v);
        a.wrapping_add(b).wrapping_add(t)
    }
"#;

/// `detect_cell_method` must classify each `Cell`/`RefCell` accessor call by
/// its callee def-path, and only those calls.
#[test]
fn test_detect_cell_method_classifies_accessors() {
    with_test_ay_ctx_for_source(CELL_OPS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_ops");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_cell_ops", ChcConfig::default());

        let mut seen: Vec<CellMethod> = Vec::new();
        for block in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
            else {
                continue;
            };
            let Some(path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            let detected = chc_ctx.detect_cell_method(func);
            // Every Cell accessor must be classified; Cell::new and the
            // wrapping_add helper calls must not.
            if path.contains("cell::Cell") && path.ends_with("::get") {
                assert_eq!(detected, Some(CellMethod::Get), "{path}");
            } else if path.contains("cell::Cell") && path.ends_with("::set") {
                assert_eq!(detected, Some(CellMethod::Set), "{path}");
            } else if path.contains("cell::Cell") && path.ends_with("::take") {
                assert_eq!(detected, Some(CellMethod::Take), "{path}");
            } else if path.ends_with("::replace_with") {
                assert_eq!(detected, Some(CellMethod::ReplaceWith), "{path}");
            } else if path.ends_with("::replace")
                && (path.contains("cell::Cell") || path.contains("cell::RefCell"))
            {
                assert_eq!(detected, Some(CellMethod::Replace), "{path}");
            } else if path.ends_with("::new") && path.contains("cell::") {
                assert_eq!(detected, None, "Cell::new must not be a cell accessor: {path}");
            }
            if let Some(m) = detected {
                seen.push(m);
            }
        }
        // The probe exercises set, get, replace (Cell), take, and RefCell::replace.
        assert!(seen.contains(&CellMethod::Get), "expected a Cell::get call, saw {seen:?}");
        assert!(seen.contains(&CellMethod::Set), "expected a Cell::set call, saw {seen:?}");
        assert!(seen.contains(&CellMethod::Replace), "expected a replace call, saw {seen:?}");
        assert!(seen.contains(&CellMethod::Take), "expected a Cell::take call, saw {seen:?}");
    });
}

const CELL_AS_PTR_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::{Cell, RefCell};

    pub fn probe_cell_as_ptr(c: &Cell<u32>, r: &RefCell<u32>) -> *mut u32 {
        let _p = c.as_ptr();
        r.as_ptr()
    }
"#;

/// `detect_cell_method` must classify both `Cell::as_ptr` and `RefCell::as_ptr`
/// as `CellMethod::AsPtr`. This is the read-side companion to the mutating
/// accessors: `*self.as_ptr()` contract reads must resolve the referent address
/// (the same object the store writes) rather than the provenance-losing inlined
/// `self.value.get()` pointer cast.
#[test]
fn test_detect_cell_method_classifies_as_ptr() {
    with_test_ay_ctx_for_source(CELL_AS_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_as_ptr");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_cell_as_ptr", ChcConfig::default());

        let mut as_ptr_hits = 0;
        for block in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
            else {
                continue;
            };
            let Some(path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if path.ends_with("::as_ptr")
                && (path.contains("cell::Cell") || path.contains("cell::RefCell"))
            {
                assert_eq!(
                    chc_ctx.detect_cell_method(func),
                    Some(CellMethod::AsPtr),
                    "Cell/RefCell as_ptr must classify as AsPtr: {path}"
                );
                as_ptr_hits += 1;
            }
        }
        assert_eq!(as_ptr_hits, 2, "expected both Cell::as_ptr and RefCell::as_ptr calls");
    });
}

const CELL_U64_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;

    pub fn probe_cell_u64(c: &Cell<u64>, v: u64) {
        c.set(v);
    }
"#;

/// SOUNDNESS: with no recoverable referent address (empty `ref_targets`) and a
/// pointer-width value type that disables the thin-pointer route-2 fallback,
/// the handler must FAIL CLOSED (return `false`) instead of storing to a
/// fabricated address — leaving the call for the sound deep-inline path.
#[test]
fn test_cell_method_fails_closed_without_recoverable_address() {
    with_test_ay_ctx_for_source(CELL_U64_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_u64");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_u64",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        // No ref_targets are seeded, so route-1 recovery fails; the value type
        // is u64 (== pointer width) so route-2 is gated off.
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(CellMethod::Set) = chc_ctx.detect_cell_method(func) else {
                continue;
            };
            let Some(target_bb) = *target else { continue };
            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("src rel").clone();
            let from_app = RelationApp::new(&from_rel, Vec::new());
            let stmt_constraints = [ay_bindings::Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let ecx = CallEmitContext {
                args,
                destination,
                target: target_bb,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
            };
            let handled = chc_ctx.codegen_call_cell_method(bb_idx, &ecx, CellMethod::Set);
            assert!(
                !handled,
                "Cell::set with no recoverable address must fail closed (deep-inline), not store"
            );
            return;
        }
        panic!("no Cell::set call found in probe_cell_u64 MIR");
    });
}

const CELL_REPLACE_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;

    pub fn probe_cell_replace() -> u32 {
        let c: Cell<u32> = Cell::new(5);
        c.replace(7)
    }
"#;

/// A `Cell::replace` whose `&self` receiver has a tracked `ref_targets` entry
/// must be modeled directly (dispatch returns handled) as an `old = load;
/// store(new); dest = old` sequence — NOT demoted to a sound fallback.
#[test]
fn test_cell_replace_emits_load_store_sequence() {
    with_test_ay_ctx_for_source(CELL_REPLACE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_replace");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_replace",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        // The Cell<u32> stack local (referent of the replace receiver).
        let cell_local = body
            .locals()
            .iter()
            .position(|d| {
                matches!(d.ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _))
                    if def.0.name().contains("cell::Cell"))
            })
            .expect("Cell<u32> local");

        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let Some(CellMethod::Replace) = chc_ctx.detect_cell_method(func) else {
                continue;
            };
            let Some(target_bb) = *target else { continue };
            // Seed the receiver's ref_target so the sound (obj,offset) recovery
            // resolves to the Cell stack local.
            if let rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p) =
                &args[0]
                && p.projection.is_empty()
            {
                chc_ctx
                    .ref_resolution
                    .ref_targets
                    .insert(p.local, RefTarget::with_projections(cell_local, Vec::new()));
            }

            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("src rel").clone();
            let output_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| ay_bindings::Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, output_args);
            let stmt_constraints = [ay_bindings::Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let ecx = CallEmitContext {
                args,
                destination,
                target: target_bb,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
            };

            let before = chc_ctx.sound_fallback_count();
            let handled = chc_ctx.codegen_call_cell_method(bb_idx, &ecx, CellMethod::Replace);
            assert!(handled, "Cell::replace with a recoverable address must be handled directly");
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                before,
                "direct Cell::replace load/store must not record a sound fallback"
            );
            return;
        }
        panic!("no Cell::replace call found in probe_cell_replace MIR");
    });
}

const REFCELL_BORROW_GUARD_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::RefCell;

    pub fn probe_refcell_replace_while_borrowed(r: &RefCell<u32>, v: u32) -> u32 {
        let g = r.borrow_mut();
        drop(g);
        r.replace(v)
    }
"#;

/// SOUNDNESS: the intercepted `RefCell::replace` skips the borrow-flag panic
/// check, so it must be DECLINED (fail-closed at the quarantine) whenever any
/// borrow guard (`Ref`/`RefMut`/`BorrowRef`/`BorrowRefMut`) exists in the
/// translated body — a live borrow would make `replace` panic, and silently
/// skipping that panic is a false Safe.
#[test]
fn test_refcell_replace_declined_when_borrow_guards_present() {
    with_test_ay_ctx_for_source(REFCELL_BORROW_GUARD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_refcell_replace_while_borrowed");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_refcell_replace_while_borrowed",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(
            chc_ctx.body_has_refcell_borrow_guards(),
            "borrow_mut guard local must be detected in the body"
        );

        let mut checked = 0;
        for block in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
            else {
                continue;
            };
            let Some(method) = chc_ctx.detect_cell_method(func) else { continue };
            if method == CellMethod::Replace {
                assert!(
                    chc_ctx.refcell_mutator_must_fail_close(func, method),
                    "RefCell::replace must fail closed while borrow guards exist in the body"
                );
                checked += 1;
            }
        }
        assert!(checked > 0, "expected a RefCell::replace call in probe MIR");
    });
}

const REFCELL_NO_GUARD_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::RefCell;

    pub fn probe_refcell_replace_no_borrow(r: &RefCell<u32>, v: u32) -> u32 {
        r.replace(v)
    }
"#;

/// Companion: with NO borrow guards anywhere in the body, no borrow can be
/// live at the intercepted `replace`, so the gate must not decline it.
#[test]
fn test_refcell_replace_not_declined_without_borrow_guards() {
    with_test_ay_ctx_for_source(REFCELL_NO_GUARD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_refcell_replace_no_borrow");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_refcell_replace_no_borrow",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(
            !chc_ctx.body_has_refcell_borrow_guards(),
            "no borrow guard locals expected in the guard-free probe"
        );

        let mut checked = 0;
        for block in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
            else {
                continue;
            };
            let Some(method) = chc_ctx.detect_cell_method(func) else { continue };
            if method == CellMethod::Replace {
                assert!(
                    !chc_ctx.refcell_mutator_must_fail_close(func, method),
                    "guard-free RefCell::replace must not be declined by the borrow gate"
                );
                checked += 1;
            }
        }
        assert!(checked > 0, "expected a RefCell::replace call in probe MIR");
    });
}

const CELL_MOVE_HAZARD_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;

    pub fn probe_cell_move_after_set(v: u32) -> u32 {
        let c = Cell::new(1u32);
        c.set(v);
        let c2 = c; // by-value move of an address-exposed cell
        c2.get()
    }
"#;

/// SOUNDNESS (move_after_set dual): a body that address-exposes a cell AND
/// moves it by value must trip the register-move hazard, declining the whole
/// cell lane (the moved-to local would otherwise read the stale register
/// mirror — a false Safe).
#[test]
fn test_cell_lane_declines_on_register_move_hazard() {
    with_test_ay_ctx_for_source(CELL_MOVE_HAZARD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_move_after_set");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_move_after_set",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        assert!(
            chc_ctx.cell_lane_register_move_hazard(),
            "address-exposed + by-value-moved Cell must trip the register-move hazard"
        );
    });
}

const CELL_CONSTRUCTION_ONLY_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;

    pub struct Wrapper { x: Cell<u32> }

    pub fn probe_cell_construction(v: u32) -> u32 {
        let w = Wrapper { x: Cell::new(v) }; // construction move of a never-exposed temp
        w.x.set(v.wrapping_add(1));
        w.x.get()
    }
"#;

/// Companion: the ubiquitous construction shape (Cell::new temp moved into an
/// aggregate before any address exposure) must NOT trip the hazard — the
/// moved temp never had an intercepted op targeting its memory mirror.
#[test]
fn test_cell_lane_construction_move_is_not_a_hazard() {
    with_test_ay_ctx_for_source(CELL_CONSTRUCTION_ONLY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_construction");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_construction",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        assert!(
            !chc_ctx.cell_lane_register_move_hazard(),
            "construction-only move of a never-exposed Cell temp must not trip the hazard"
        );
    });
}

const CELL_NAME_COLLISION_SOURCE: &str = r#"
    #![allow(dead_code)]
    mod cell {
        pub struct Cell(pub u32);
        impl Cell {
            #[inline(never)]
            pub fn get(&self) -> u32 { self.0 }
            #[inline(never)]
            pub fn set(&mut self, v: u32) { self.0 = v; }
        }
    }

    pub fn probe_user_cell(c: &mut cell::Cell, v: u32) -> u32 {
        c.set(v);
        c.get()
    }
"#;

/// Exact-matching hygiene (the quarantine session's lesson): a user type whose
/// path merely ends in `cell::Cell` must never receive the canonical
/// standard-library Cell accessor semantics.
#[test]
fn test_detect_cell_method_rejects_user_cell_collision() {
    with_test_ay_ctx_for_source(CELL_NAME_COLLISION_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_user_cell");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_user_cell", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
            else {
                continue;
            };
            let Some(path) = chc_ctx.resolve_callee_path(func) else {
                continue;
            };
            if path.ends_with("Cell::get") || path.ends_with("Cell::set") {
                found = true;
                assert_eq!(
                    chc_ctx.detect_cell_method(func),
                    None,
                    "user-defined {path} must not be intercepted as a std Cell accessor"
                );
            }
        }
        assert!(found, "expected user cell::Cell accessor calls in probe MIR");
    });
}
