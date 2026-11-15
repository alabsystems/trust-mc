// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Register-mirror coherence of the Cell/RefCell store lane (R5).
//!
//! `Cell::set` wrote only the referent's memory mirror; the next `&c` copied
//! the local's stale state variable back over it, so `c.set(7); c.get()` read
//! the pre-store value (tools/soundness-duals/cell_set_lost_write_dual.rs).
//! These tests pin the repair in `codegen_call_cell_register.rs`:
//! - a store binds the referent local's output state to the stored value;
//! - a store after a same-block assignment of the referent supersedes that
//!   assignment's binding instead of contradicting it, and rewrites the
//!   block's earlier readers of the slot to the pre-call value; a binding
//!   that is not one plain `slot == rhs` is renamed onto a fresh pre-call
//!   variable instead of blocking the sync;
//! - an array element store is a functional array store on the register;
//! - a store whose register update cannot be built exactly havocs the
//!   referent's register completely (also when the block assigned it), as a
//!   certified fresh havoc whose freed slots are recorded;
//! - a RefCell store (whose register the lane does not model) havocs that
//!   register fail-closed, even when the block assigned the RefCell, and its
//!   old value is a fresh value;
//! - the block's pending heap terms are rewritten onto the pre-call value
//!   before the call adds a term of its own;
//! - a store whose receiver no stack local's address reaches (an `Rc`
//!   payload beside a local Cell) havocs nothing;
//! - a flattened `Cell::get` destination is bound on every slot;
//! - an interior-mutable constant-initialised local is never cached as a
//!   single-assignment constant.

#![allow(clippy::unwrap_used, clippy::panic)]

use std::collections::HashSet;

use super::common::*;
use crate::args::ChcTrackLevel;
use crate::codegen_ay::chc::call::codegen_call_cell::{CallCell, CellMethod};
use crate::codegen_ay::chc::chc_call_context::CallEmitContext;
use crate::codegen_ay::chc::codegen_call_cmp_string::math_const_prescan::compute_single_assign_locals;
use crate::codegen_ay::chc::codegen_ctx::RefTarget;

/// The first local whose type is the canonical `Cell` (or `RefCell`) ADT.
fn first_local_of_adt(body: &rustc_public::mir::Body, adt: &str) -> usize {
    body.locals()
        .iter()
        .position(|d| {
            matches!(d.ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _))
                if def.0.name() == format!("std::cell::{adt}")
                    || def.0.name() == format!("core::cell::{adt}"))
        })
        .unwrap_or_else(|| panic!("no {adt} local"))
}

/// The output state variable name of `local`'s first slot.
fn out_name_of(chc_ctx: &ChcCtx<'_, '_>, local: usize) -> String {
    let idx = chc_ctx.try_state_idx_for_local(local).expect("state slot");
    chc_ctx.state_var_mgr.output_state_vars[idx].0.to_string()
}

/// Whether `constraint` is `Var(name) == bv const value`.
fn is_var_eq_const(constraint: &Expr, name: &str, value: u32) -> bool {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else { return false };
    let ExprValue::Var { name: var } = lhs.value() else { return false };
    var == name
        && matches!(rhs.value(), ExprValue::BitVecConst { value: v, .. }
            if *v == num_bigint::BigInt::from(value))
}

/// Run one intercepted Cell call of `method` in `fn_name`, with the
/// receiver's ref target seeded to `referent` (a place in the body), the
/// block's statement constraints `stmt` and modified set `modified`.
/// Returns whether the call was handled.
#[allow(clippy::too_many_arguments)]
fn run_cell_call(
    chc_ctx: &mut ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    method: CellMethod,
    referent: Option<RefTarget>,
    stmt: &[Expr],
    modified: &HashSet<usize>,
) -> bool {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
            &block.terminator.kind
        else {
            continue;
        };
        if chc_ctx.detect_cell_method(func) != Some(method) {
            continue;
        }
        let Some(target_bb) = *target else { continue };
        if let Some(referent) = referent.clone()
            && let Operand::Copy(p) | Operand::Move(p) = &args[0]
            && p.projection.is_empty()
        {
            chc_ctx.ref_resolution.ref_targets.insert(p.local, referent);
        }
        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("src rel").clone();
        let input_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, input_args);
        let ecx = CallEmitContext {
            args,
            destination,
            target: target_bb,
            from_app: &from_app,
            stmt_constraints: stmt,
            modified_locals: modified,
        };
        return chc_ctx.codegen_call_cell_method(bb_idx, &ecx, method);
    }
    panic!("no {method:?} call found");
}

const CELL_SET_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;

    pub fn probe_cell_set_get() -> u32 {
        let c: Cell<u32> = Cell::new(5);
        c.set(7);
        c.get()
    }
"#;

/// R5: `Cell::set` must bind the referent local's output state to the stored
/// value, so the next `&c` re-mirrors the stored value, not the stale one.
#[test]
fn test_cell_set_binds_referent_register_to_stored_value() {
    with_test_ay_ctx_for_source(CELL_SET_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_set_get");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_set_get",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let cell = first_local_of_adt(&body, "Cell");
        let c_out = out_name_of(&chc_ctx, cell);

        let before = chc_ctx.sound_fallback_count();
        let stmt = [Expr::bool_const(true)];
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Set,
            Some(RefTarget::with_projections(cell, Vec::new())),
            &stmt,
            &HashSet::new(),
        );
        assert!(handled, "Cell::set with a recoverable address must be handled");
        assert_eq!(chc_ctx.sound_fallback_count(), before, "an exact sync records no fallback");
        let rule = chc_ctx.vc.rules.last().expect("set rule");
        assert!(
            rule.body.constraints.iter().any(|c| is_var_eq_const(c, &c_out, 7)),
            "the set rule must bind {c_out} to the stored 7; constraints: {:?}",
            rule.body.constraints.iter().map(ToString::to_string).collect::<Vec<_>>()
        );
        assert!(
            rule.head
                .args
                .iter()
                .any(|a| matches!(a.value(), ExprValue::Var { name } if *name == c_out)),
            "the cell's output slot must reach the rule head"
        );
    });
}

/// R5, same-block assignment: when the block already bound the referent's
/// output (`c_out == 5`), the store's binding must REPLACE that constraint.
/// Two bindings of `c_out` would contradict each other and make every path
/// through the call vacuous (a false proof).
#[test]
fn test_cell_set_supersedes_same_block_assignment() {
    with_test_ay_ctx_for_source(CELL_SET_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_set_get");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_set_get",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let cell = first_local_of_adt(&body, "Cell");
        let c_out = out_name_of(&chc_ctx, cell);
        let idx = chc_ctx.try_state_idx_for_local(cell).unwrap();
        let sort = chc_ctx.state_var_mgr.output_state_vars[idx].1.clone();
        let assigned = Expr::var(c_out.clone(), sort).eq(Expr::bitvec_const(5u32, 32));

        let before = chc_ctx.sound_fallback_count();
        let stmt = [assigned, Expr::bool_const(true)];
        let modified: HashSet<usize> = [cell].into_iter().collect();
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Set,
            Some(RefTarget::with_projections(cell, Vec::new())),
            &stmt,
            &modified,
        );
        assert!(handled);
        assert_eq!(chc_ctx.sound_fallback_count(), before);
        let rule = chc_ctx.vc.rules.last().expect("set rule");
        let rendered: Vec<String> = rule.body.constraints.iter().map(ToString::to_string).collect();
        assert!(
            rule.body.constraints.iter().any(|c| is_var_eq_const(c, &c_out, 7)),
            "the store must bind {c_out} to 7: {rendered:?}"
        );
        assert!(
            !rule.body.constraints.iter().any(|c| is_var_eq_const(c, &c_out, 5)),
            "the superseded same-block binding {c_out} == 5 must be dropped: {rendered:?}"
        );
    });
}

/// A same-block term that read the pre-call value through the output slot
/// (a `&c` mirror store, a forwarded load) must keep meaning the pre-call
/// value once the slot is rebound: it is rewritten through the superseded
/// binding, never left naming the rebound slot.
#[test]
fn test_cell_set_rewrites_same_block_readers_of_the_rebound_slot() {
    with_test_ay_ctx_for_source(CELL_SET_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_set_get");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_set_get",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let cell = first_local_of_adt(&body, "Cell");
        let c_out = out_name_of(&chc_ctx, cell);
        let idx = chc_ctx.try_state_idx_for_local(cell).unwrap();
        let sort = chc_ctx.state_var_mgr.output_state_vars[idx].1.clone();
        let c_out_var = Expr::var(c_out.clone(), sort);
        let assigned = c_out_var.clone().eq(Expr::bitvec_const(5u32, 32));
        let reader = c_out_var.bvult(Expr::bitvec_const(9u32, 32));
        let rewritten_reader = Expr::bitvec_const(5u32, 32).bvult(Expr::bitvec_const(9u32, 32));

        let before = chc_ctx.sound_fallback_count();
        let stmt = [assigned, reader];
        let modified: HashSet<usize> = [cell].into_iter().collect();
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Set,
            Some(RefTarget::with_projections(cell, Vec::new())),
            &stmt,
            &modified,
        );
        assert!(handled);
        assert_eq!(chc_ctx.sound_fallback_count(), before);
        let rule = chc_ctx.vc.rules.last().expect("set rule");
        let rendered: Vec<String> = rule.body.constraints.iter().map(ToString::to_string).collect();
        assert!(
            rule.body.constraints.iter().any(|c| is_var_eq_const(c, &c_out, 7)),
            "{rendered:?}"
        );
        assert!(
            !rule.body.constraints.iter().any(|c| is_var_eq_const(c, &c_out, 5)),
            "{rendered:?}"
        );
        assert!(
            rule.body.constraints.iter().any(|c| *c == rewritten_reader),
            "the reader must read the pre-call 5, not the rebound slot: {rendered:?}"
        );
        assert!(
            !rule
                .body
                .constraints
                .iter()
                .any(|c| { c.to_string().contains(&c_out) && !is_var_eq_const(c, &c_out, 7) }),
            "no term but the new binding may name the rebound slot: {rendered:?}"
        );
    });
}

/// A same-block binding that is not one plain `slot == rhs` (here it names
/// the slot itself) is renamed onto a fresh pre-call variable: the block's
/// meaning is unchanged, the store's binding `c_out == 7` is the only term
/// naming the slot, and the sync stays exact (no fallback). Before, this
/// shape could not be superseded and left the stale binding in place.
#[test]
fn test_cell_set_renames_a_non_plain_same_block_binding() {
    with_test_ay_ctx_for_source(CELL_SET_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_set_get");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_set_get",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let cell = first_local_of_adt(&body, "Cell");
        let c_out = out_name_of(&chc_ctx, cell);
        let idx = chc_ctx.try_state_idx_for_local(cell).unwrap();
        let sort = chc_ctx.state_var_mgr.output_state_vars[idx].1.clone();
        let c_out_var = Expr::var(c_out.clone(), sort);
        let self_referential = c_out_var.clone().eq(c_out_var.bvand(Expr::bitvec_const(5u32, 32)));

        let before = chc_ctx.sound_fallback_count();
        let stmt = [self_referential];
        let modified: HashSet<usize> = [cell].into_iter().collect();
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Set,
            Some(RefTarget::with_projections(cell, Vec::new())),
            &stmt,
            &modified,
        );
        assert!(handled);
        assert_eq!(chc_ctx.sound_fallback_count(), before, "the renamed sync is exact");
        let rule = chc_ctx.vc.rules.last().expect("set rule");
        let rendered: Vec<String> = rule.body.constraints.iter().map(ToString::to_string).collect();
        assert!(
            rule.body.constraints.iter().any(|c| is_var_eq_const(c, &c_out, 7)),
            "the store must bind {c_out} to 7: {rendered:?}"
        );
        assert!(
            !rule
                .body
                .constraints
                .iter()
                .any(|c| { c.to_string().contains(&c_out) && !is_var_eq_const(c, &c_out, 7) }),
            "the block's own binding must no longer name {c_out}: {rendered:?}"
        );
        assert!(
            rendered.iter().any(|c| c.contains("__cell_pre") && c.contains("bvand")),
            "the block's binding must survive over the fresh pre-call variable: {rendered:?}"
        );
    });
}

const CELL_FIELD_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;

    pub struct Wrapper { a: u32, x: Cell<u32> }

    pub fn probe_cell_field(v: u32) -> u32 {
        let w = Wrapper { a: 1, x: Cell::new(v) };
        w.x.set(7);
        w.x.get()
    }
"#;

/// A store into a field of a struct local that the block assigned is synced
/// exactly through the field (no fallback), even when a same-block reader
/// names every output slot of the local.
#[test]
fn test_cell_set_field_of_same_block_struct_is_synced_exactly() {
    with_test_ay_ctx_for_source(CELL_FIELD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_field",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let wrapper = body
            .locals()
            .iter()
            .position(|d| {
                matches!(d.ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _))
                    if def.0.name().ends_with("Wrapper"))
            })
            .expect("Wrapper local");
        let idx = chc_ctx.try_state_idx_for_local(wrapper).unwrap();
        let (name, sort) = chc_ctx.state_var_mgr.output_state_vars[idx].clone();
        let reader =
            Expr::var(name.to_string(), sort.clone()).eq(Expr::var(name.to_string(), sort));
        let stmt = [reader];
        let modified: HashSet<usize> = [wrapper].into_iter().collect();
        let x_field = rustc_public::mir::ProjectionElem::Field(
            1,
            body.locals()
                .iter()
                .find(|d| matches!(d.ty.kind(), TyKind::RigidTy(RigidTy::Ref(..))))
                .and_then(|d| match d.ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, t, _)) => Some(t),
                    _ => None,
                })
                .expect("&Cell<u32> receiver type"),
        );
        let before = chc_ctx.sound_fallback_count();
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Set,
            Some(RefTarget::with_projections(wrapper, vec![x_field])),
            &stmt,
            &modified,
        );
        assert!(handled);
        assert_eq!(chc_ctx.sound_fallback_count(), before, "the field sync is exact");
        let rule = chc_ctx.vc.rules.last().expect("set rule");
        let rendered: Vec<String> = rule.body.constraints.iter().map(ToString::to_string).collect();
        let slots = if chc_ctx.flatten.flattened_tuple_locals.contains(&wrapper) {
            chc_ctx.flattened_field_count(wrapper)
        } else {
            1
        };
        let slot_names: Vec<String> = (0..slots)
            .map(|i| chc_ctx.state_var_mgr.output_state_vars[idx + i].0.to_string())
            .collect();
        assert!(
            rendered
                .iter()
                .any(|c| slot_names.iter().any(|n| c.contains(n.as_str()))
                    && c.contains("#x00000007")),
            "an output slot of the wrapper must carry the stored 7 in its field: {rendered:?}"
        );
        assert!(
            !rendered
                .iter()
                .any(|c| c.contains(&*name) && c.contains(&format!("(= {name} {name})"))),
            "the same-block reader must be rewritten off the rebound slot: {rendered:?}"
        );
    });
}

const REFCELL_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::RefCell;

    pub fn probe_refcell_replace_twice(v: u32) -> u32 {
        let r = RefCell::new(0u32);
        r.replace(v);
        r.replace(1)
    }
"#;

/// A RefCell's register is its (borrow flag, value) pair, which the store
/// lane does not model: a RefCell store whose register the next `&r`
/// re-mirrors must fail closed (on main, `r.replace(200); r.replace(1)`
/// returned the initial value and `old < 100` proved clean).
#[test]
fn test_refcell_store_fails_closed_when_remirrored() {
    with_test_ay_ctx_for_source(REFCELL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_refcell_replace_twice");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_refcell_replace_twice",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let refcell = first_local_of_adt(&body, "RefCell");
        assert!(chc_ctx.cell_register_remirror_exposed(refcell), "`&r` receivers re-mirror r");
        let before = chc_ctx.sound_fallback_count();
        let stmt = [Expr::bool_const(true)];
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Replace,
            Some(RefTarget::with_projections(refcell, Vec::new())),
            &stmt,
            &HashSet::new(),
        );
        assert!(handled, "the store itself is still emitted");
        assert!(
            chc_ctx.sound_fallback_count() > before,
            "an unmodelled RefCell register that is re-mirrored must fail closed"
        );
        // ... and be havoced: every output slot of `r` reaches the head with
        // no binding, so the next `&r` re-mirrors an arbitrary value, never
        // the stale one (a demoted proof from the stale value is still a
        // proof of the wrong assertion at the check level).
        let rule = chc_ctx.vc.rules.last().expect("replace rule");
        let base = chc_ctx.try_state_idx_for_local(refcell).unwrap();
        let slots = if chc_ctx.flatten.flattened_tuple_locals.contains(&refcell) {
            chc_ctx.flattened_field_count(refcell)
        } else {
            1
        };
        for i in 0..slots {
            let name = chc_ctx.state_var_mgr.output_state_vars[base + i].0.to_string();
            assert!(
                rule.head
                    .args
                    .iter()
                    .any(|a| matches!(a.value(), ExprValue::Var { name: v } if *v == name)),
                "havoced slot {name} must reach the rule head"
            );
            assert!(
                !rule.body.constraints.iter().any(|c| c.to_string().contains(&name)),
                "havoced slot {name} must stay unbound"
            );
        }
    });
}

const CELL_PAIR_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;

    pub fn probe_cell_pair() -> u8 {
        let c = Cell::new((1u8, 2u8));
        c.set((3, 4));
        let p = c.get();
        p.1
    }
"#;

/// A flattened `Cell::get` destination owns one state variable per leaf.
/// Binding only the first slot left `.1` free, and `c.set((1, 2));
/// assert!(c.get().1 == 2)` FAILED with a Genuine counterexample.
#[test]
fn test_cell_get_binds_every_flattened_destination_slot() {
    with_test_ay_ctx_for_source(CELL_PAIR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_pair");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_pair",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let cell = first_local_of_adt(&body, "Cell");
        let dest = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Call { func, destination, .. }
                    if chc_ctx.detect_cell_method(func) == Some(CellMethod::Get) =>
                {
                    Some(destination.local)
                }
                _ => None,
            })
            .expect("Cell::get call");
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&dest),
            "the (u8, u8) get destination is flattened"
        );
        let slots = chc_ctx.flattened_field_count(dest);
        let base = chc_ctx.try_state_idx_for_local(dest).unwrap();
        let slot_names: Vec<String> = (0..slots)
            .map(|i| chc_ctx.state_var_mgr.output_state_vars[base + i].0.to_string())
            .collect();

        let stmt = [Expr::bool_const(true)];
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Get,
            Some(RefTarget::with_projections(cell, Vec::new())),
            &stmt,
            &HashSet::new(),
        );
        assert!(handled);
        let rule = chc_ctx.vc.rules.last().expect("get rule");
        for name in &slot_names {
            assert!(
                rule.body.constraints.iter().any(|c| matches!(c.value(),
                    ExprValue::Eq(lhs, _) if matches!(lhs.value(),
                        ExprValue::Var { name: v } if v == name))),
                "flattened destination slot {name} must be bound: {:?}",
                rule.body.constraints.iter().map(ToString::to_string).collect::<Vec<_>>()
            );
        }
    });
}

const CONST_CELL_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;

    const CC: Cell<u8> = Cell::new(3);
    const K: u8 = 3;

    pub fn probe_const_cell() -> u8 {
        let c = CC;
        c.set(4);
        let x = K;
        let r = &x;
        c.get().wrapping_add(*r)
    }
"#;

/// A shared borrow does not freeze an interior-mutable local: a Cell
/// initialised once from a constant must not be admitted as a
/// single-assignment constant (its first value would be cached over every
/// later `set`), while a plain constant-initialised, shared-borrowed `u8`
/// still is.
#[test]
fn test_interior_mut_const_referent_is_not_single_assign() {
    with_test_ay_ctx_for_source(CONST_CELL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_const_cell");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_const_cell",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let cell = first_local_of_adt(&body, "Cell");
        let plain = body
            .blocks
            .iter()
            .flat_map(|b| &b.statements)
            .find_map(|stmt| match &stmt.kind {
                rustc_public::mir::StatementKind::Assign(
                    _,
                    rustc_public::mir::Rvalue::Ref(_, _, place),
                ) if place.projection.is_empty()
                    && matches!(
                        body.locals()[place.local].ty.kind(),
                        TyKind::RigidTy(RigidTy::Uint(UintTy::U8))
                    ) =>
                {
                    Some(place.local)
                }
                _ => None,
            })
            .expect("&x of the u8 constant");
        for local in [cell, plain] {
            chc_ctx
                .ref_resolution
                .ref_targets
                .insert(usize::MAX - local, RefTarget::with_projections(local, Vec::new()));
        }
        compute_single_assign_locals(&mut chc_ctx);
        assert!(
            !chc_ctx.encode.single_assign_locals.contains(&cell),
            "a constant-initialised Cell is interior-mutable, never a cached constant"
        );
        assert!(
            chc_ctx.encode.single_assign_locals.contains(&plain),
            "a constant-initialised, shared-borrowed u8 stays a single-assignment constant"
        );
    });
}

const REFCELL_SAME_BLOCK_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::RefCell;

    pub fn probe_refcell_same_block(v: u32) -> u32 {
        let r = RefCell::new(v);
        r.replace(7);
        r.replace(1)
    }
"#;

/// Design 3 review follow-up (S1): a RefCell store whose referent the block
/// ALSO assigned must still havoc the register. Before, the candidate was
/// dropped from the havoc because the block had bound its output slots, so
/// the next `&r` re-mirrored the block's own (pre-call) binding and a check
/// over it read SUCCESS on the stale value. The block's binding is rewritten
/// onto the pre-call value and every output slot of `r` reaches the head
/// unbound.
#[test]
fn test_refcell_store_havocs_a_same_block_referent() {
    with_test_ay_ctx_for_source(REFCELL_SAME_BLOCK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_refcell_same_block");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_refcell_same_block",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let refcell = first_local_of_adt(&body, "RefCell");
        let base = chc_ctx.try_state_idx_for_local(refcell).unwrap();
        let slots = if chc_ctx.flatten.flattened_tuple_locals.contains(&refcell) {
            chc_ctx.flattened_field_count(refcell)
        } else {
            1
        };
        let names: Vec<String> = (0..slots)
            .map(|i| chc_ctx.state_var_mgr.output_state_vars[base + i].0.to_string())
            .collect();
        // The block's own binding of the RefCell's first output slot.
        let (n0, s0) = chc_ctx.state_var_mgr.output_state_vars[base].clone();
        let zero = match s0.bitvec_width() {
            Some(w) => Expr::bitvec_const(0u32, w),
            None => Expr::var("__probe_unrelated", s0.clone()),
        };
        let assigned = Expr::var(n0.to_string(), s0).eq(zero);
        let stmt = [assigned];
        let modified: HashSet<usize> = [refcell].into_iter().collect();
        let fail_close_before = chc_ctx.diagnostics.place_translation_drop.get();
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Replace,
            Some(RefTarget::with_projections(refcell, Vec::new())),
            &stmt,
            &modified,
        );
        assert!(handled);
        assert!(
            chc_ctx.diagnostics.place_translation_drop.get() > fail_close_before,
            "a RefCell store stays fail-closed"
        );
        let rule = chc_ctx.vc.rules.last().expect("replace rule");
        let rendered: Vec<String> = rule.body.constraints.iter().map(ToString::to_string).collect();
        for name in &names {
            assert!(
                rule.head
                    .args
                    .iter()
                    .any(|a| matches!(a.value(), ExprValue::Var { name: v } if v == name)),
                "havoced slot {name} must reach the rule head"
            );
            assert!(
                !rendered.iter().any(|c| c.contains(name.as_str())),
                "havoced slot {name} must stay unbound, also by the block's own binding: \
                 {rendered:?}"
            );
        }
    });
}

/// A RefCell replace does not read its old value at the object base (where
/// the lane would find the borrow flag): the result is a fresh value.
/// `let r = RefCell::new(5); assert!(r.replace(6) == 0)` verified SUCCESSFUL
/// clean on main 1f7de891d (Kani fails it).
#[test]
fn test_refcell_replace_old_value_is_fresh() {
    with_test_ay_ctx_for_source(REFCELL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_refcell_replace_twice");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_refcell_replace_twice",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let refcell = first_local_of_adt(&body, "RefCell");
        let fail_close_before = chc_ctx.diagnostics.place_translation_drop.get();
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Replace,
            Some(RefTarget::with_projections(refcell, Vec::new())),
            &[Expr::bool_const(true)],
            &HashSet::new(),
        );
        assert!(handled);
        let rule = chc_ctx.vc.rules.last().expect("replace rule");
        let rendered: Vec<String> = rule.body.constraints.iter().map(ToString::to_string).collect();
        assert!(
            rendered.iter().any(|c| c.contains("__refcell_old")),
            "the replaced value must be the fresh `__refcell_old`: {rendered:?}"
        );
        assert!(
            chc_ctx.diagnostics.place_translation_drop.get() >= fail_close_before + 2,
            "the fresh read and the register havoc are both recorded fail-closed"
        );
    });
}

/// A Cell store whose register cannot be rebound exactly (here the referent
/// is the whole struct, whose type is not the stored payload) havocs the
/// referent's register completely: the certified fresh havoc lane
/// (`cell_store_register_havoc`, SoundHavoc), with every havoced output slot
/// recorded as a freed variable, every slot in the head and none bound.
#[test]
fn test_cell_store_unsyncable_register_is_a_certified_havoc() {
    with_test_ay_ctx_for_source(CELL_FIELD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_field");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_field",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let wrapper = body
            .locals()
            .iter()
            .position(|d| {
                matches!(d.ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _))
                    if def.0.name().ends_with("Wrapper"))
            })
            .expect("Wrapper local");
        let base = chc_ctx.try_state_idx_for_local(wrapper).unwrap();
        let slots = if chc_ctx.flatten.flattened_tuple_locals.contains(&wrapper) {
            chc_ctx.flattened_field_count(wrapper)
        } else {
            1
        };
        let names: Vec<String> = (0..slots)
            .map(|i| chc_ctx.state_var_mgr.output_state_vars[base + i].0.to_string())
            .collect();
        let sound_before = chc_ctx.diagnostics.sound_havoc_drop.get();
        let fail_close_before = chc_ctx.diagnostics.place_translation_drop.get();
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Set,
            Some(RefTarget::with_projections(wrapper, Vec::new())),
            &[Expr::bool_const(true)],
            &HashSet::new(),
        );
        assert!(handled);
        assert_eq!(chc_ctx.diagnostics.sound_havoc_drop.get(), sound_before + 1);
        assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), fail_close_before);
        let rule = chc_ctx.vc.rules.last().expect("set rule");
        let rendered: Vec<String> = rule.body.constraints.iter().map(ToString::to_string).collect();
        for name in &names {
            assert!(
                rule.head
                    .args
                    .iter()
                    .any(|a| matches!(a.value(), ExprValue::Var { name: v } if v == name)),
                "havoced slot {name} must reach the rule head"
            );
            assert!(!rendered.iter().any(|c| c.contains(name.as_str())), "{rendered:?}");
            let normalized = name.strip_suffix("__out").unwrap_or(name);
            assert!(
                chc_ctx.vc.approximated_vars.iter().any(|v| v == normalized),
                "havoced slot {normalized} must be a freed variable: {:?}",
                chc_ctx.vc.approximated_vars
            );
        }
    });
}

const CELL_ARRAY_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;

    pub fn probe_cell_array() -> u32 {
        let arr = [Cell::new(0u32), Cell::new(0u32)];
        arr[1].set(5);
        let r = &arr;
        r[1].get()
    }
"#;

/// An array element store is a functional array store on the array local's
/// register (review of fix/chc-cell-set-write: `arr[1].set(5)` then `&arr`
/// re-mirrored a havoced register and a correct sum overflowed).
#[test]
fn test_cell_set_array_element_is_a_functional_store() {
    with_test_ay_ctx_for_source(CELL_ARRAY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_array");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_array",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let arr = body
            .locals()
            .iter()
            .position(|d| matches!(d.ty.kind(), TyKind::RigidTy(RigidTy::Array(..))))
            .expect("array local");
        let arr_out = out_name_of(&chc_ctx, arr);
        let before = chc_ctx.sound_fallback_count();
        let elem = rustc_public::mir::ProjectionElem::ConstantIndex {
            offset: 1,
            min_length: 2,
            from_end: false,
        };
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Set,
            Some(RefTarget::with_projections(arr, vec![elem])),
            &[Expr::bool_const(true)],
            &HashSet::new(),
        );
        assert!(handled);
        assert_eq!(chc_ctx.sound_fallback_count(), before, "the element sync is exact");
        let rule = chc_ctx.vc.rules.last().expect("set rule");
        let rendered: Vec<String> = rule.body.constraints.iter().map(ToString::to_string).collect();
        assert!(
            rendered.iter().any(|c| {
                c.contains(&arr_out) && c.contains("store") && c.contains("#x00000005")
            }),
            "{arr_out} must be the input array with element 1 stored to 5: {rendered:?}"
        );
    });
}

/// Every pending heap term of the block (a store chain the `&c` mirror
/// built from the register before the call) is rewritten onto the pre-call
/// value BEFORE the call adds a term that means the post-call value: after
/// the call, no pending chain may name the rebound slot.
#[test]
fn test_cell_set_rewrites_pending_heap_terms_before_its_own() {
    with_test_ay_ctx_for_source(CELL_SET_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_set_get");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_cell_set_get",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let cell = first_local_of_adt(&body, "Cell");
        let c_out = out_name_of(&chc_ctx, cell);
        let idx = chc_ctx.try_state_idx_for_local(cell).unwrap();
        let sort = chc_ctx.state_var_mgr.output_state_vars[idx].1.clone();
        let c_out_var = Expr::var(c_out.clone(), sort.clone());
        let assigned = c_out_var.clone().eq(Expr::bitvec_const(5u32, 32));
        // A chain the block built before the call, over the output slot.
        let arr_sort = ay_bindings::Sort::array(ay_bindings::Sort::bitvec(64), sort);
        let probe_arr = Expr::var("probe_mirror_arr", arr_sort);
        let chain = probe_arr.store(Expr::bitvec_const(0u64, 64), c_out_var);
        chc_ctx.heap_state.accumulate_store("probe_mirror_key", "probe_mirror_arr__out", chain);
        let stmt = [assigned];
        let modified: HashSet<usize> = [cell].into_iter().collect();
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Set,
            Some(RefTarget::with_projections(cell, Vec::new())),
            &stmt,
            &modified,
        );
        assert!(handled);
        let rule = chc_ctx.vc.rules.last().expect("set rule");
        let rendered: Vec<String> = rule.body.constraints.iter().map(ToString::to_string).collect();
        let mirror = rendered
            .iter()
            .find(|c| c.contains("probe_mirror_arr__out"))
            .unwrap_or_else(|| panic!("the pending chain must be drained: {rendered:?}"));
        assert!(
            !mirror.contains(&c_out) && mirror.contains("#x00000005"),
            "the pre-call chain must read the pre-call 5, not {c_out}: {mirror}"
        );
        assert!(rule.body.constraints.iter().any(|c| is_var_eq_const(c, &c_out, 7)));
    });
}

const RC_BESIDE_LOCAL_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;
    use std::rc::Rc;

    pub fn probe_rc_beside_local() -> u32 {
        let a = Cell::new(1u32);
        let b = Rc::new(Cell::new(0u32));
        b.set(7);
        a.get()
    }
"#;

/// A store through a receiver no stack local's address reaches (an `Rc`
/// payload) havocs no register: the local Cell `a` next to it, whose address
/// only ever reaches its own `get` receiver, keeps its register (review of
/// fix/chc-cell-set-write: every whole-borrowed interior-mutable local was
/// havoced and `a.get() == 1` FAILED).
#[test]
fn test_cell_store_through_rc_havocs_no_unrelated_local() {
    with_test_ay_ctx_for_source(RC_BESIDE_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_beside_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_rc_beside_local",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();
        let a = first_local_of_adt(&body, "Cell");
        let a_out = out_name_of(&chc_ctx, a);
        let before = chc_ctx.sound_fallback_count();
        let handled = run_cell_call(
            &mut chc_ctx,
            &body,
            CellMethod::Set,
            None,
            &[Expr::bool_const(true)],
            &HashSet::new(),
        );
        assert!(handled, "the Rc receiver's address is recoverable (route 2)");
        // The store through the receiver is bounded by the size of the object
        // its lane names (`symbolic_lane_bounds`, a plain check). It havocs
        // nothing.
        assert_eq!(chc_ctx.sound_fallback_count(), before, "no register is havoced");
        let rule = chc_ctx.vc.rules.last().expect("set rule");
        assert!(
            !rule
                .head
                .args
                .iter()
                .any(|arg| matches!(arg.value(), ExprValue::Var { name } if *name == a_out)),
            "the unrelated local Cell's register must pass through unchanged"
        );
    });
}
