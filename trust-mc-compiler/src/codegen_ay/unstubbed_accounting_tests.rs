// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use rustc_public::CrateDef;

#[test]
fn accounting_inventory_preserves_noncall_and_indirect_uses() {
    const SOURCE: &str = r#"
        use std::sync::atomic::AtomicI32;
        static CELLS: [AtomicI32; 2] = [AtomicI32::new(1), AtomicI32::new(2)];
        pub fn exact() -> *mut i32 { CELLS[1].as_ptr() }
        pub fn escaped() -> fn(&AtomicI32) -> *mut i32 { AtomicI32::as_ptr }
        pub fn indirect(f: fn(&AtomicI32) -> *mut i32) -> *mut i32 { f(&CELLS[1]) }
    "#;
    let mut exercised = false;
    with_test_ay_ctx_for_source(SOURCE, |tcx| {
        let root = find_instance_by_suffix(tcx.tcx, "exact");
        let body = root.body().unwrap();
        let (block, callee) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb, b)| {
                let TerminatorKind::Call { func, .. } = &b.terminator.kind else {
                    return None;
                };
                let TyKind::RigidTy(RigidTy::FnDef(def, args)) =
                    func.ty(body.locals()).ok()?.kind()
                else {
                    return None;
                };
                def.name()
                    .ends_with("::as_ptr")
                    .then(|| (bb, Instance::resolve(def, &args).unwrap()))
            })
            .expect("real Atomic::as_ptr");
        for (helper, expect_indirect) in [("escaped", false), ("indirect", true)] {
            let scope = AccountingScope::begin(Some(root));
            begin_inventory();
            record_reachable_body(root, &body);
            record_pending(
                "as_ptr",
                callee,
                Some(AbstractionCallsite { caller: root, body: &body, block }),
                true,
            );
            let helper = find_instance_by_suffix(tcx.tcx, helper);
            record_reachable_body(helper, &helper.body().unwrap());
            finish_inventory();
            with_current(|state| {
                if expect_indirect {
                    assert!(state.invalid);
                } else {
                    assert!(state.opaque_uses.contains(&callee));
                }
                assert_eq!(state.unresolved(true), 1);
            });
            scope.finish();
        }
        // Mutating even a non-call statement after the inliner handoff
        // invalidates whole-body custody at the encoder boundary.
        let scope = AccountingScope::begin(Some(root));
        begin_inventory();
        record_reachable_body(root, &body);
        record_pending(
            "as_ptr",
            callee,
            Some(AbstractionCallsite { caller: root, body: &body, block }),
            true,
        );
        finish_inventory();
        let token = before_root_inline(root, &body);
        assert!(token.is_some());
        after_root_inline(token, &body);
        let mut changed = body.clone();
        changed.blocks[0].statements.clear();
        assert_ne!(BodyIdentity::of(&body).blocks, BodyIdentity::of(&changed).blocks);
        let attempt = EncodingAttempt::begin(Some(root), &changed);
        attempt.finish();
        with_current(|state| assert!(state.invalid));
        assert_eq!(unresolved_for_test(), 1);
        scope.finish();
        exercised = true;
    });
    assert!(exercised, "compiler-backed inventory checks must execute");
}
#[test]
fn accounting_lifecycle_keeps_actual_counter_deltas_and_coverage() {
    use super::super::diagnostics::{coverage_count_for_test, get_unstubbed_abstraction_count};
    use std::panic::{AssertUnwindSafe, catch_unwind};
    let mut exercised = false;
    with_test_ay_ctx_for_source("pub fn root() {}", |tcx| {
        let root = find_instance_by_suffix(tcx.tcx, "root");
        let path = "accounting-lifecycle-test-unique";
        let record = || record_pending(path, root, None, false);
        let before = get_unstubbed_abstraction_count();
        let coverage_before = coverage_count_for_test(path);
        // Completion without a model, ordinary early return, and unwind all count.
        let first = AccountingScope::begin(Some(root));
        record();
        first.finish();
        {
            let _early_return = AccountingScope::begin(Some(root));
            record();
        }
        assert!(
            catch_unwind(AssertUnwindSafe(|| {
                let _panic = AccountingScope::begin(Some(root));
                record();
                panic!("test unwind");
            }))
            .is_err()
        );
        assert!(get_unstubbed_abstraction_count() >= before + 3);
        assert_eq!(coverage_count_for_test(path), coverage_before + 3);
        // Removing an outer guard must not steal its inner ledger or restore a stale one.
        let outer = AccountingScope::begin(Some(root));
        record();
        let inner = AccountingScope::begin(Some(root));
        record();
        record();
        drop(outer);
        record();
        inner.finish();
        assert!(get_unstubbed_abstraction_count() >= before + 7);
        assert_eq!(coverage_count_for_test(path), coverage_before + 7);
        // The next harness sees only its own pending event.
        let next = AccountingScope::begin(Some(root));
        record();
        assert_eq!(unresolved_for_test(), 1);
        next.finish();
        assert!(get_unstubbed_abstraction_count() >= before + 8);
        assert_eq!(coverage_count_for_test(path), coverage_before + 8);
        SCOPES.with(|scopes| assert!(scopes.borrow().is_empty()));
        println!(
            "ACCOUNTING_GLOBAL_DELTA before={} after={} coverage_delta=8",
            before,
            get_unstubbed_abstraction_count()
        );
        exercised = true;
    });
    assert!(exercised, "compiler callback must execute lifecycle assertions");
}

#[test]
fn accounting_requires_complete_inventory_and_every_encoding() {
    let mut exercised = false;
    with_test_ay_ctx_for_source("pub fn root() {}", |tcx| {
        let root = find_instance_by_suffix(tcx.tcx, "root");
        let body = root.body().unwrap();
        // Deliberately seed downstream bookkeeping to ensure it cannot substitute
        // for reachability completion. This is a ledger test, not model evidence.
        let seed_receipt = || {
            with_current(|ledger| {
                ledger.encounters.push(Encounter {
                    callee: root,
                    identity_established: true,
                    site: Some(Site {
                        caller: root,
                        block: 0,
                        body: Rc::new(BodyIdentity::of(&body)),
                    }),
                });
                ledger.preserved.insert(0, root);
                ledger.confirmed = Some(HashSet::from([0]));
                ledger.encoded_body = Some(BodyIdentity::of(&body));
            });
        };
        for (observe, finish) in [(false, false), (false, true), (true, false)] {
            let scope = AccountingScope::begin(Some(root));
            begin_inventory();
            if observe {
                record_reachable_body(root, &body);
            }
            if finish {
                finish_inventory();
            }
            seed_receipt();
            assert_eq!(unresolved_for_test(), 1, "partial/absent root inventory");
            scope.finish();
        }
        let scope = AccountingScope::begin(Some(root));
        begin_inventory();
        record_reachable_body(root, &body);
        finish_inventory();
        seed_receipt();
        assert_eq!(unresolved_for_test(), 0);
        let missing_model = EncodingAttempt::begin(Some(root), &body);
        missing_model.finish();
        assert_eq!(unresolved_for_test(), 1, "second attempt omitted the modeled call");
        scope.finish();
        // An attempt owns its ledger even if another scope is now on top.
        let outer = AccountingScope::begin(Some(root));
        begin_inventory();
        record_reachable_body(root, &body);
        finish_inventory();
        seed_receipt();
        let abandoned = EncodingAttempt::begin(Some(root), &body);
        let inner = AccountingScope::begin(Some(root));
        drop(abandoned);
        with_owned(outer.id, |ledger| assert!(ledger.invalid));
        with_owned(inner.id, |ledger| assert!(!ledger.invalid));
        inner.finish();
        outer.finish();
        exercised = true;
    });
    assert!(exercised, "compiler callback must execute custody assertions");
}

#[test]
fn accounting_scope_guards_cannot_cross_threads() {
    // If a guard gains the bound, both implementations apply and Rust rejects
    // this inference as ambiguous. The invariant is checked by compilation.
    macro_rules! assert_not_impl {
        ($ty:ty, $bound:path) => {{
            struct ImplementsBound;
            trait Ambiguous<A> {
                fn check() {}
            }
            impl<T: ?Sized> Ambiguous<()> for T {}
            impl<T: ?Sized + $bound> Ambiguous<ImplementsBound> for T {}
            let _ = <$ty as Ambiguous<_>>::check;
        }};
    }
    assert_not_impl!(AccountingScope, Send);
    assert_not_impl!(AccountingScope, Sync);
    assert_not_impl!(EncodingAttempt<'static>, Send);
    assert_not_impl!(EncodingAttempt<'static>, Sync);
    assert_not_impl!(InlineCustody, Send);
    assert_not_impl!(InlineCustody, Sync);
}
