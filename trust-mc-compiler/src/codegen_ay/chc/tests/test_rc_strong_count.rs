// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Two `Rc` handles to one allocation
//! (tools/soundness-duals/rc_shared_handle_dual.rs).
//!
//! - `rc_strong_count.rs`: a strong-count state variable per cloned `Rc::new`
//!   site, declared only when the pre-scan accounts for every handle of the
//!   body. The drop of a handle frees the allocation only when the count
//!   reaches 0, so dropping two handles of one `Rc<Cell<u8>>` is no double free.
//! - `codegen_call_ptr_identity_cast.rs`: `NonNull::as_ref` through a receiver
//!   that is no whole local reads the `NonNull` it points at, not the address
//!   of the receiver's slot.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::ChcCallContext;
use crate::codegen_ay::chc::codegen_call_ptr_identity::CallPtrIdentity;
use crate::codegen_ay::chc::codegen_ctx::RefTarget;
use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind, TerminatorKind};

const RC_SHARED_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::cell::Cell;
    use std::ptr::NonNull;
    use std::rc::Rc;

    pub fn probe_rc_clone_safe() {
        let r = Rc::new(Cell::new(0u8));
        let r2 = r.clone();
        r2.set(200);
        assert!(r.get() == 200);
    }

    pub fn probe_rc_clone_bug() {
        let r = Rc::new(Cell::new(0u8));
        let r2 = r.clone();
        r2.set(200);
        assert!(r.get() == 0);
    }

    pub fn probe_rc_counter() {
        let shared = Rc::new(Cell::new(0u32));
        let other = Rc::clone(&shared);
        other.set(other.get() + 1);
        assert!(shared.get() == 1);
    }

    pub fn probe_rc_no_clone() {
        let r = Rc::new(Cell::new(0u8));
        r.set(1);
        assert!(r.get() == 1);
    }

    fn consume(r: Rc<Cell<u8>>) -> u8 {
        r.get()
    }

    pub fn probe_rc_handle_escapes() {
        let r = Rc::new(Cell::new(0u8));
        let r2 = r.clone();
        assert!(consume(r2) == 0);
    }

    pub fn probe_rc_in_option() {
        let r = Rc::new(Cell::new(0u8));
        let o = Some(r.clone());
        assert!(o.is_some());
    }

    pub struct D(pub u64);
    impl Drop for D {
        fn drop(&mut self) {}
    }
    pub struct SD {
        pub r: Rc<D>,
    }
    pub enum ED {
        A(Rc<D>),
        B,
    }
    pub struct RR<'a> {
        pub r: &'a Rc<Cell<u8>>,
    }

    pub fn probe_rc_clone_in_struct_pushed() {
        let a = Rc::new(D(7));
        let mut v: Vec<SD> = Vec::new();
        v.push(SD { r: a.clone() });
    }

    pub fn probe_rc_clone_in_enum_pushed() {
        let a = Rc::new(D(7));
        let mut v: Vec<ED> = Vec::new();
        v.push(ED::A(a.clone()));
    }

    #[inline(never)]
    fn stash(w: RR<'_>) {
        std::mem::forget(w.r.clone());
    }

    pub fn probe_rc_ref_in_struct() {
        let a = Rc::new(Cell::new(0u8));
        let b = a.clone();
        stash(RR { r: &a });
        b.set(1);
    }

    pub fn probe_rc_clone_transmuted() {
        let a = Rc::new(Cell::new(0u8));
        let b = a.clone();
        let raw: usize = unsafe { std::mem::transmute(b) };
        assert!(raw != 0);
    }

    pub fn probe_rc_increment_count() {
        let a = Rc::new(Cell::new(0u8));
        let b = a.clone();
        unsafe { Rc::increment_strong_count(Rc::as_ptr(&a)) };
        b.set(1);
    }

    pub trait MakeRc {
        fn new(v: u8) -> Self;
    }
    impl MakeRc for Rc<Cell<u8>> {
        fn new(v: u8) -> Self {
            let r = Rc::new(Cell::new(v));
            std::mem::forget(r.clone());
            r
        }
    }

    pub fn probe_rc_user_new() {
        let a = <Rc<Cell<u8>> as MakeRc>::new(1);
        let b = a.clone();
        b.set(2);
    }

    pub fn probe_rc_new_in_loop(n: u8) {
        let mut i = 0u8;
        while i < n {
            let a = Rc::new(Cell::new(i));
            let b = a.clone();
            b.set(1);
            i += 1;
        }
    }

    struct H {
        k: u8,
        p: NonNull<u8>,
    }

    pub fn probe_nonnull_field_as_ref_safe() {
        let x = 7u8;
        let h = H { k: 1, p: NonNull::from(&x) };
        let v = unsafe { *h.p.as_ref() };
        assert!(v == 7);
    }

    pub fn probe_nonnull_field_as_ref_bug() {
        let x = 7u8;
        let h = H { k: 1, p: NonNull::from(&x) };
        let v = unsafe { *h.p.as_ref() };
        assert!(v == 8);
    }
"#;

/// The strong-count state variables the encoder of `fn_name` declares.
fn rc_strong_state_vars(fn_name: &str) -> Vec<String> {
    let mut names = Vec::new();
    with_test_ay_ctx_for_source(RC_SHARED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new_with_instance(ctx.tcx, &body, instance, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();
        names = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, _)| name.to_string())
            .filter(|name| name.starts_with("__rc_strong_bb"))
            .collect();
    });
    names
}

/// A body that clones the handle of one `Rc::new` site, and does nothing else
/// with its handles, gets exactly one count; a body without a clone gets none.
#[test]
fn test_rc_strong_count_declared_for_a_cloned_site_only() {
    let cloned = rc_strong_state_vars("probe_rc_clone_safe");
    assert_eq!(cloned.len(), 1, "one cloned Rc::new site, one count: {cloned:?}");
    // `Rc::inner` leaves `NonNull::<RcInner<T>>::as_ref` as a call: its path
    // names `RcInner`, no handle type, and touches no count.
    let counter = rc_strong_state_vars("probe_rc_counter");
    assert_eq!(counter.len(), 1, "the counter's cloned site keeps its count: {counter:?}");
    let uncloned = rc_strong_state_vars("probe_rc_no_clone");
    assert!(uncloned.is_empty(), "no clone, no count (relation arity unchanged): {uncloned:?}");
}

/// A handle a callee receives by value, or one moved into an aggregate, can be
/// cloned or dropped where the host does not see it: the pre-scan refuses the
/// body and the old encoding stands.
#[test]
fn test_rc_strong_count_refused_when_a_handle_escapes() {
    let escapes = rc_strong_state_vars("probe_rc_handle_escapes");
    assert!(escapes.is_empty(), "a handle passed to a callee: no count: {escapes:?}");
    let in_option = rc_strong_state_vars("probe_rc_in_option");
    assert!(in_option.is_empty(), "a handle inside an Option: no count: {in_option:?}");
}

/// A clone moved into a NON-generic struct or enum and pushed into a `Vec`
/// is dropped by the `Vec`'s element drop, which never reaches the count: the
/// allocation would never be freed (review of item 1; the `bug_vec_*` rows of
/// rc_shared_handle_dual.rs). "Mentions" looks through ADT fields, so a local
/// of type `SD`/`ED`/`Vec<SD>` refuses the body.
#[test]
fn test_rc_strong_count_refused_when_a_handle_escapes_in_a_struct_field() {
    let counted = counted_probes(&[
        // A clone moved into SD { r } and pushed.
        "probe_rc_clone_in_struct_pushed",
        // A clone moved into ED::A and pushed.
        "probe_rc_clone_in_enum_pushed",
        // &Rc stored in RR { r } and handed to a callee that clones it.
        "probe_rc_ref_in_struct",
    ]);
    assert!(counted.is_empty(), "each body must keep the old encoding: {counted:?}");
}

/// A handle read whole by any statement other than a move, an unsizing cast
/// or a borrow leaves the tracked locals (`transmute::<Rc<_>, usize>` has a
/// destination type that mentions no handle); a call to another function of
/// the `Rc` family (`increment_strong_count` takes a raw pointer) changes the
/// real count; a user trait method named `new` on `Rc<_>` is no `Rc::new`; a
/// `new` inside a loop makes allocations that one count cannot tell apart.
/// Each refuses the body.
#[test]
fn test_rc_strong_count_refused_for_escapes_the_types_do_not_show() {
    let counted = counted_probes(&[
        "probe_rc_clone_transmuted",
        "probe_rc_increment_count",
        "probe_rc_user_new",
        "probe_rc_new_in_loop",
    ]);
    assert!(counted.is_empty(), "each body must keep the old encoding: {counted:?}");
}

/// The probes among `fn_names` whose encoder declares a strong count.
fn counted_probes(fn_names: &[&str]) -> Vec<(String, Vec<String>)> {
    fn_names
        .iter()
        .map(|fn_name| (fn_name.to_string(), rc_strong_state_vars(fn_name)))
        .filter(|(_, counts)| !counts.is_empty())
        .collect()
}

fn tree_has(expr: &Expr, pred: &impl Fn(&Expr) -> bool) -> bool {
    constraint_tree_contains(expr, pred)
}

fn names_counter(expr: &Expr) -> bool {
    matches!(expr.value(), ExprValue::Var { name } if name.starts_with("__rc_strong_bb"))
}

/// `count - 1 == 0` (the last handle) or its negation, over a strong count.
fn is_last_handle_guard(expr: &Expr) -> bool {
    let ExprValue::Eq(lhs, rhs) = expr.value() else { return false };
    matches!(lhs.value(), ExprValue::BvSub(count, _) if tree_has(count, &names_counter))
        && matches!(rhs.value(), ExprValue::BitVecConst { value, .. } if *value == num_bigint::BigInt::from(0))
}

fn is_other_handle_guard(expr: &Expr) -> bool {
    matches!(expr.value(), ExprValue::Not(inner) if is_last_handle_guard(inner))
}

/// The drops of the two handles of a counted allocation free it only on the
/// path where the count reaches 0: every rule that frees the allocation
/// carries the last-handle guard, and each drop also has a rule that frees
/// nothing and carries the other-handle guard. `Rc::new` sets the count to 1
/// and the clone adds 1.
#[test]
fn test_rc_counted_drop_frees_only_at_zero() {
    with_test_ay_ctx_for_source(RC_SHARED_SOURCE, |ctx| {
        let fn_name = "probe_rc_clone_safe";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new_with_instance(ctx.tcx, &body, instance, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.generate_transition_rules();
        let rules = &chc_ctx.vc.rules;
        let mut frees = 0usize;
        let mut other_handle = 0usize;
        let mut set_one = false;
        let mut incremented = false;
        for rule in rules {
            let constraints = &rule.body.constraints;
            let has = |pred: &dyn Fn(&Expr) -> bool| constraints.iter().any(|c| tree_has(c, &pred));
            let counted = has(&names_counter);
            if !counted {
                continue;
            }
            if has(&expr_is_obj_valid_false_update) {
                frees += 1;
                assert!(
                    constraints.iter().any(is_last_handle_guard),
                    "a counted drop frees the allocation only when the count reaches 0"
                );
            }
            if constraints.iter().any(is_other_handle_guard) {
                other_handle += 1;
                assert!(
                    !has(&expr_is_obj_valid_false_update),
                    "the drop of a handle that is not the last frees nothing"
                );
            }
            set_one |= constraints.iter().any(|c| {
                matches!(c.value(), ExprValue::Eq(lhs, rhs)
                    if matches!(lhs.value(), ExprValue::Var { name } if name.starts_with("__rc_strong_bb") && name.ends_with("__out"))
                        && matches!(rhs.value(), ExprValue::BitVecConst { value, .. } if *value == num_bigint::BigInt::from(1)))
            });
            incremented |= has(
                &|e: &Expr| matches!(e.value(), ExprValue::BvAdd(count, _) if tree_has(count, &names_counter)),
            );
        }
        assert!(set_one, "Rc::new sets the count to 1");
        assert!(incremented, "the clone adds 1 to the count");
        // Two drops on the normal path (and their twins in the unwind cleanup).
        assert!(
            other_handle >= 2,
            "each of the two drops has a path where another handle remains: {other_handle}"
        );
        assert!(
            frees >= 2,
            "each of the two drops frees the allocation on its last-handle path: {frees}"
        );
    });
}

/// `NonNull::as_ref(&h.p)`: the receiver `&(h.1)` is no whole local. The result
/// is the `NonNull` read through it (`h`'s field), never the receiver's own
/// value, which is the ADDRESS of that field.
#[test]
fn test_nonnull_as_ref_projected_receiver_reads_the_nonnull() {
    with_test_ay_ctx_for_source(RC_SHARED_SOURCE, |ctx| {
        let fn_name = "probe_nonnull_field_as_ref_safe";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new_with_instance(ctx.tcx, &body, instance, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();
        let mut checked = false;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let path = chc_ctx.resolve_callee_path(func).unwrap_or_default();
            if !(path.contains("NonNull") && path.ends_with("::as_ref")) {
                continue;
            }
            let [Operand::Copy(recv) | Operand::Move(recv)] = args.as_slice() else {
                panic!("as_ref takes one receiver: {args:?}");
            };
            // The statement lane records `recv = &(h.1)` as a ref target.
            let referent = body
                .blocks
                .iter()
                .flat_map(|b| b.statements.iter())
                .find_map(|stmt| match &stmt.kind {
                    StatementKind::Assign(lhs, Rvalue::Ref(_, _, place))
                        if lhs.local == recv.local && lhs.projection.is_empty() =>
                    {
                        Some(place.clone())
                    }
                    _ => None,
                })
                .expect("the receiver is a borrow of a place");
            assert!(
                matches!(referent.projection.as_slice(), [ProjectionElem::Field(..)]),
                "the receiver borrows a field of a local: {referent:?}"
            );
            chc_ctx.ref_resolution.ref_targets.insert(
                recv.local,
                RefTarget::with_projections(referent.local, referent.projection.clone()),
            );
            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("src rel").clone();
            let input_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, input_args);
            let modified = HashSet::new();
            let rules_before = chc_ctx.vc.rules.len();
            let cx = ChcCallContext {
                stub: StubKind::PtrCast,
                args,
                destination,
                target: *target,
                from_app: &from_app,
                stmt_constraints: &[],
                modified_locals: &modified,
            };
            chc_ctx.codegen_call_ptr_cast(&cx);

            let dest_idx = chc_ctx.try_state_idx_for_local(destination.local).expect("dest slot");
            let dest_out = chc_ctx.state_var_mgr.output_state_vars[dest_idx].0.to_string();
            let recv_idx = chc_ctx.try_state_idx_for_local(recv.local).expect("recv slot");
            let recv_in = chc_ctx.state_var_mgr.state_vars[recv_idx].0.to_string();
            let owner_idx = chc_ctx.try_state_idx_for_local(referent.local).expect("owner slot");
            let owner_vars: Vec<String> = chc_ctx.state_var_mgr.state_vars
                [owner_idx..owner_idx + chc_ctx.flattened_field_count(referent.local).max(1)]
                .iter()
                .map(|(name, _)| name.to_string())
                .collect();
            let rhs = chc_ctx.vc.rules[rules_before..]
                .iter()
                .flat_map(|rule| rule.body.constraints.iter())
                .find_map(|c| match c.value() {
                    ExprValue::Eq(lhs, rhs)
                        if matches!(lhs.value(), ExprValue::Var { name } if *name == dest_out) =>
                    {
                        Some(rhs.clone())
                    }
                    _ => None,
                })
                .expect("the as_ref result is bound");
            assert!(
                !tree_has(
                    &rhs,
                    &|e: &Expr| matches!(e.value(), ExprValue::Var { name } if *name == recv_in)
                ),
                "the result must not be the receiver (the field's address): {rhs}"
            );
            assert!(
                tree_has(
                    &rhs,
                    &|e: &Expr| matches!(e.value(), ExprValue::Var { name } if owner_vars.contains(&name.to_string()))
                ),
                "the result is read from the owner's field {owner_vars:?}: {rhs}"
            );
            checked = true;
        }
        assert!(checked, "the probe calls NonNull::as_ref");
    });
}
