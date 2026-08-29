// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The transitive obligation-free certificate, asserted directly.
//!
//! `ArtifactMetadata.obligation_free_body` is what lets the driver's V4
//! vacuity gate report a harness with zero checks as SUCCESSFUL instead of
//! VACUOUS. A certificate handed to a harness that DOES have an obligation is
//! therefore a false-Safe channel, and the only thing standing in its way
//! would be the encoder happening to emit the check anyway — luck, given the
//! certificate exists precisely for when it does not.
//!
//! The soundness dual wall cannot score this. A certified harness emits ZERO
//! checks by definition, and the wall (correctly) refuses to count a
//! zero-check run as a pass, so both directions land in its unscoreable
//! bucket. Here the certificate is read straight off the artifact, so
//! "certified" and "refused" are each directly observable.
//!
//! `tools/soundness-duals/obligation_free_walk_dual.rs` keeps the
//! verdict-level half: the same bug shapes must FAIL end to end.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::obligation_free_walk::{
    body_has_visible_obligation, body_is_transitively_obligation_free,
};
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

/// Does the walk certify `fn_suffix` in `source`?
fn certifies(source: &str, fn_suffix: &str) -> bool {
    let mut answer = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        answer = Some(body_is_transitively_obligation_free(
            ctx.tcx,
            instance,
            &body,
            &Default::default(),
        ));
    });
    answer.expect("walk should have run")
}

// ---------------------------------------------------------------------------
// REFUSED: the obligation is real, and hidden behind a call.
// ---------------------------------------------------------------------------

/// `assert!` is REDEFINED by trust-mc's own `library/std` to call
/// `kani::assert`, whose body is an empty `Return`. The first version of this
/// walk followed it, saw a no-op, and CERTIFIED this exact shape.
#[test]
fn test_assert_one_call_deep_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn inner() { assert!(false); }
        pub fn probe_assert_deep() { inner(); }
    "#;
    assert!(
        !certifies(SOURCE, "probe_assert_deep"),
        "an assert one call deep must never be certified obligation-free"
    );
}

#[test]
fn test_overflow_three_calls_deep_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn lvl3(x: u32) -> u32 { x + 1 }
        fn lvl2(x: u32) -> u32 { lvl3(x) }
        fn lvl1(x: u32) -> u32 { lvl2(x) }
        pub fn probe_overflow_deep() { let _ = lvl1(u32::MAX); }
    "#;
    assert!(
        !certifies(SOURCE, "probe_overflow_deep"),
        "an overflow site three frames down must not be certified — two \
         obligation-free frames in front of it change nothing"
    );
}

#[test]
fn test_unwrap_on_none_one_call_deep_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn inner(o: Option<u32>) -> u32 { o.unwrap() }
        pub fn probe_unwrap_deep() { let _ = inner(None); }
    "#;
    assert!(!certifies(SOURCE, "probe_unwrap_deep"), "a panicking unwrap is an obligation");
}

/// The memory-safety class: no `assert!`, no Kani hook. It is refused because
/// rustc still emits an `Assert` terminator for the null/alignment check.
#[test]
fn test_raw_deref_one_call_deep_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn inner(p: *const u32) -> u32 { unsafe { *p } }
        pub fn probe_deref_deep() { let _ = inner(std::ptr::null()); }
    "#;
    assert!(!certifies(SOURCE, "probe_deref_deep"), "a raw dereference is an obligation");
}

/// `get_unchecked` is UNSAFE, so rustc emits no `Assert` for the bound. The
/// walk must still refuse — it reaches `core` code it cannot clear.
#[test]
fn test_get_unchecked_one_call_deep_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn inner(v: &[u32]) -> u32 { unsafe { *v.get_unchecked(5) } }
        pub fn probe_unchecked_deep() { let a = [1u32, 2, 3]; let _ = inner(&a); }
    "#;
    assert!(!certifies(SOURCE, "probe_unchecked_deep"), "an unchecked index is an obligation");
}

/// An indirect call is the case the walk cannot see through at all.
#[test]
fn test_call_through_a_function_pointer_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn a(x: u32) -> u32 { x }
        pub fn probe_fn_ptr(pick: bool) -> u32 {
            let f: fn(u32) -> u32 = if pick { a } else { a };
            f(7)
        }
    "#;
    assert!(
        !certifies(SOURCE, "probe_fn_ptr"),
        "an indirect callee is not visible to the walk, so it must fail closed"
    );
}

/// A `dyn` receiver on a trait with exactly ONE non-blanket concrete impl is
/// decided statically, so the walk devirtualizes and walks the real body.
///
/// This used to fail closed unconditionally, which made `kani/DynTrait/upcast.rs`
/// — a harness whose only call is `(x as &dyn Super).method()` into an empty
/// default body — uncertifiable and therefore VACUOUS despite genuinely having
/// nothing to prove.
#[test]
fn test_single_impl_virtual_call_is_certified() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        trait T { fn go(&self) -> u32; }
        struct S;
        impl T for S { fn go(&self) -> u32 { 1 } }
        pub fn probe_virtual() -> u32 { let d: &dyn T = &S; d.go() }
    "#;
    assert!(
        certifies(SOURCE, "probe_virtual"),
        "one non-blanket impl decides the callee statically; its body has nothing to prove"
    );
}

/// Devirtualization must WALK the concrete body, not bless it: a single-impl
/// `dyn` call whose real body carries an obligation must still be refused.
#[test]
fn test_single_impl_virtual_call_with_obligation_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        trait T { fn go(&self) -> u32; }
        struct S;
        impl T for S { fn go(&self) -> u32 { assert!(1 == 2); 1 } }
        pub fn probe_virtual_obligation() -> u32 { let d: &dyn T = &S; d.go() }
    "#;
    assert!(
        !certifies(SOURCE, "probe_virtual_obligation"),
        "the devirtualized body asserts; certifying it would be a false Safe"
    );
}

/// With MORE THAN ONE concrete impl the callee is genuinely undecided, so the
/// walk must still fail closed — `try_devirtualize` returns None and the
/// verdict stays Unknown.
#[test]
fn test_multi_impl_virtual_call_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        trait T { fn go(&self) -> u32; }
        struct S1;
        struct S2;
        impl T for S1 { fn go(&self) -> u32 { 1 } }
        impl T for S2 { fn go(&self) -> u32 { assert!(1 == 2); 2 } }
        pub fn probe_virtual_multi(pick: bool) -> u32 {
            let d: &dyn T = if pick { &S1 as &dyn T } else { &S2 as &dyn T };
            d.go()
        }
    "#;
    assert!(
        !certifies(SOURCE, "probe_virtual_multi"),
        "two impls leave the callee undecided; the walk must fail closed"
    );
}

// ---------------------------------------------------------------------------
// CERTIFIED: nothing to prove anywhere reachable.
// ---------------------------------------------------------------------------

/// The shape the old one-frame certificate refused: a harness that calls
/// something. Three frames, no obligation in any of them.
#[test]
fn test_three_obligation_free_frames_are_certified() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn lvl3(x: u32) -> u32 { x }
        fn lvl2(x: u32) -> u32 { lvl3(x) }
        fn lvl1(x: u32) -> u32 { lvl2(x) }
        pub fn probe_safe_deep() { let _ = lvl1(7); }
    "#;
    assert!(
        certifies(SOURCE, "probe_safe_deep"),
        "a call chain with no obligation is the whole point of the walk — if \
         this fails the certificate has stopped converting anything"
    );
}

/// A body that calls NOTHING still certifies, as it did before the walk.
#[test]
fn test_empty_body_is_certified() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_empty() {}
    "#;
    assert!(certifies(SOURCE, "probe_empty"), "an empty body has no obligation site");
}

/// Recursion must terminate, and must not be certified by the cycle cut when
/// the obligation sits past the recursive edge.
#[test]
fn test_recursion_with_an_obligation_past_the_cycle_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn rec(n: u32) -> u32 { if n == 0 { assert!(false); 0 } else { rec(n - 1) } }
        pub fn probe_recursive() { let _ = rec(3); }
    "#;
    assert!(
        !certifies(SOURCE, "probe_recursive"),
        "the visited-set cut must not swallow an obligation on the other side \
         of the recursive edge"
    );
}

// ---------------------------------------------------------------------------
// Body-less callees: refused, except the one the encoder declares total.
// ---------------------------------------------------------------------------

/// An atomic fence is dispatched as "no-op in sequential verification — no
/// memory effect, no return value", so a harness that only fences has nothing
/// to prove. `tests/kani/Intrinsics/Atomic/**/Fence` say so in their own
/// comments ("Nothing to assert").
#[test]
fn test_fences_only_is_certified() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::sync::atomic::{Ordering, fence};
        pub fn probe_fences() { fence(Ordering::Acquire); fence(Ordering::SeqCst); }
    "#;
    assert!(
        certifies(SOURCE, "probe_fences"),
        "a fence has no obligation; refusing it leaves the Fence harnesses vacuous"
    );
}

/// A fence must not launder an obligation standing next to it.
#[test]
fn test_a_fence_does_not_launder_a_neighbouring_obligation_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::sync::atomic::{Ordering, fence};
        fn inner(x: u32) -> u32 { fence(Ordering::SeqCst); x + 1 }
        pub fn probe_fence_plus_overflow() { let _ = inner(u32::MAX); }
    "#;
    assert!(
        !certifies(SOURCE, "probe_fence_plus_overflow"),
        "the overflow is still an obligation — the allow-list clears the FENCE, \
         not the frame it sits in"
    );
}

/// The allow-list is Fence-only. A real atomic operation touches memory, so a
/// body-less atomic load must keep failing closed.
#[test]
fn test_a_real_atomic_operation_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::sync::atomic::{AtomicU32, Ordering};
        pub fn probe_atomic_load() -> u32 {
            let a = AtomicU32::new(1);
            a.load(Ordering::SeqCst)
        }
    "#;
    assert!(
        !certifies(SOURCE, "probe_atomic_load"),
        "load/store are not fences; widening the allow-list past Fence would \
         certify code that reads memory"
    );
}

// ---------------------------------------------------------------------------
// POSITIVE obligation sighting — the nested-call fallback's discriminator.
// ---------------------------------------------------------------------------

/// Does the walk POSITIVELY see an obligation reachable from `fn_suffix`?
fn sees_obligation(source: &str, fn_suffix: &str) -> bool {
    let mut answer = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        answer = Some(body_has_visible_obligation(ctx.tcx, instance));
    });
    answer.expect("walk should have run")
}

/// The confirmed missed bug: an obligation inside a callee the walker gave up
/// on was blessed away as a sound havoc, so `assert!` inside `kani::block_on`
/// never reached the check list and the harness reported a CLEAN SUCCESSFUL.
#[test]
fn test_a_reachable_assert_is_a_visible_obligation() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn inner() { assert!(false); }
        pub fn probe_has_obligation() { inner(); }
    "#;
    assert!(
        sees_obligation(SOURCE, "probe_has_obligation"),
        "an assert behind a call must be SEEN, or the nested-call fallback \
         blesses away a dropped obligation"
    );
}

/// The other half of the lattice. A clean body must NOT be reported as
/// carrying an obligation, or the fallback demotes harnesses it should bless.
#[test]
fn test_a_clean_body_is_not_a_visible_obligation() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn lvl2(x: u32) -> u32 { x }
        fn lvl1(x: u32) -> u32 { lvl2(x) }
        pub fn probe_clean() { let _ = lvl1(7); }
    "#;
    assert!(!sees_obligation(SOURCE, "probe_clean"), "a clean chain carries no obligation");
}

/// UNKNOWN must not read as HasObligation. Treating "could not tell" as "has
/// an obligation" would demote nearly every harness touching an un-inlinable
/// stdlib call — the exact cost the `nested_call_overapprox` blessing exists
/// to avoid — so the fallback acts only on a POSITIVE sighting.
#[test]
fn test_an_unreadable_callee_is_not_reported_as_an_obligation() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn a(x: u32) -> u32 { x }
        pub fn probe_indirect(pick: bool) -> u32 {
            let f: fn(u32) -> u32 = if pick { a } else { a };
            f(7)
        }
    "#;
    assert!(
        !sees_obligation(SOURCE, "probe_indirect"),
        "an indirect callee is UNKNOWN, not an obligation sighting"
    );
    // ... and the same body must still be refused for CERTIFICATION, which is
    // the asymmetry the three-valued verdict exists to express.
    assert!(!certifies(SOURCE, "probe_indirect"), "Unknown must never certify either");
}

// ---------------------------------------------------------------------------
// Stub resolution: the walk must inspect the program the ENCODER encodes.
// ---------------------------------------------------------------------------

/// Does the walk certify `fn_suffix` when `stubs` are in effect?
///
/// The map is keyed by `FnDef`, so it is built here by resolving the two names
/// in the source rather than by re-deriving Kani's attribute parsing.
fn certifies_with_stub(source: &str, fn_suffix: &str, from: &str, to: &str) -> bool {
    let mut answer = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let harness = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let from_i = find_instance_by_suffix(ctx.tcx, from);
        let to_i = find_instance_by_suffix(ctx.tcx, to);
        let (rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(from_def, _)),
             rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(to_def, _))) =
            (from_i.ty().kind(), to_i.ty().kind())
        else {
            panic!("both stub endpoints should be FnDefs");
        };
        let mut stubs = crate::codegen_ay::obligation_free_walk::StubMap::default();
        stubs.insert(from_def, to_def);
        let body = harness.body().expect("body");
        answer = Some(body_is_transitively_obligation_free(ctx.tcx, harness, &body, &stubs));
    });
    answer.expect("walk should have run")
}

const STUB_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn stub_clean() {}
    pub fn stub_panicking() { assert!(false); }
    pub fn probe_calls_clean() { stub_clean(); }
    pub fn probe_calls_panicking() { stub_panicking(); }
"#;

/// A stub can ADD an obligation the original lacks. Walking the ORIGINAL is how
/// `#[kani::stub(clean, panicking)]` came back `certified=true` on a harness
/// whose emitted check FAILS.
#[test]
fn test_a_stub_that_adds_an_obligation_is_refused() {
    assert!(
        !certifies_with_stub(STUB_SOURCE, "probe_calls_clean", "stub_clean", "stub_panicking"),
        "the walk must follow the stub and see its assert"
    );
}

/// The other direction, and the one a blanket refusal would also pass — which
/// is why it is asserted separately. A stub that REMOVES the obligation leaves
/// an obligation-free program, and refusing it costs parity for nothing
/// (measured: `tests/kani/Stubbing/glob_{cycle,path}.rs`).
#[test]
fn test_a_stub_that_removes_the_obligation_is_certified() {
    assert!(
        certifies_with_stub(STUB_SOURCE, "probe_calls_panicking", "stub_panicking", "stub_clean"),
        "the walk must follow the stub to the CLEAN body, not refuse every stubbed unit"
    );
}
