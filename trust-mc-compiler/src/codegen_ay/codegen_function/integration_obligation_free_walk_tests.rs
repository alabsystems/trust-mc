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
//! `obligation_free_stmt_dual.rs` and `obligation_free_stmt_dual_safe.rs` do
//! the same for the STATEMENT sites asserted at the end of this file.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::*;
use crate::codegen_ay::context::{
    with_test_ay_ctx_for_source, with_test_ay_ctx_for_source_with_rustc_flags,
};
use crate::codegen_ay::obligation_free_walk::body_is_transitively_obligation_free;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

/// Does the walk certify `fn_suffix` in `source`?
fn certifies(source: &str, fn_suffix: &str) -> bool {
    certifies_with_rustc_flags(source, fn_suffix, &[])
}

/// [`certifies`] with extra `rustc` flags — `-C overflow-checks=off` and
/// `-C debug-assertions=off` strip the `Assert` terminators safe code puts in
/// front of a statement site, which is how the STATEMENT is isolated.
fn certifies_with_rustc_flags(source: &str, fn_suffix: &str, flags: &[&str]) -> bool {
    let mut answer = None;
    with_test_ay_ctx_for_source_with_rustc_flags(source, flags, |ctx| {
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

/// Exercise the full producer/consumer name boundary, not only the MIR walk.
/// The walk can prove Free while a mismatched map key loses that fact on export.
fn artifact_certifies(source: &str, fn_suffix: &str, use_chc: bool) -> bool {
    let mut answer = None;
    with_test_ay_ctx_for_source(source, |mut ctx| {
        ctx.config.use_chc = use_chc;
        ctx.queries.set_args(crate::args::Arguments::default());
        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("body");
        let internal_name = instance.name();
        let public_name = crate::rustc_compat::instance_name(ctx.tcx, instance);
        #[cfg(trust_toolchain)]
        assert_ne!(internal_name, public_name, "fixture must cross the Trust name boundary");
        ctx.set_current_fn(instance);
        codegen_function_with_body(&mut ctx, instance, body, &internal_name);
        let artifact = ctx.build_vc_artifact(&public_name, None);
        answer = Some(
            artifact.metadata.as_ref().and_then(|meta| meta.obligation_free_body).unwrap_or(false),
        );
    });
    answer.expect("artifact should have been built")
}

#[test]
fn test_obligation_free_export_uses_public_harness_identity() {
    const SOURCE: &str = r#"
        pub fn empty() {}
        pub struct Value { pub c: char }
        impl Value { pub fn new() -> Self { Self { c: ' ' } } }
    "#;
    for use_chc in [false, true] {
        for name in ["empty", "Value::new"] {
            assert!(artifact_certifies(SOURCE, name, use_chc), "{name}, CHC={use_chc}");
        }
    }
}

#[test]
fn test_obligation_free_export_keeps_same_named_sibling_refusals() {
    const SOURCE: &str = r#"
        pub mod clean { pub fn check() {} }
        pub mod dirty { pub fn check() { assert!(false); } }
        pub struct Value;
        impl Value { pub fn check() { assert!(false); } }
    "#;
    for use_chc in [false, true] {
        for reverse in [false, true] {
            with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
                ctx.config.use_chc = use_chc;
                ctx.queries.set_args(crate::args::Arguments::default());
                let mut cases =
                    vec![("clean::check", true), ("dirty::check", false), ("Value::check", false)];
                if reverse {
                    cases.reverse();
                }
                // Keep all entries in one context. A global flag, bare-name
                // key or last-generated-function answer must fail this check.
                for (name, _) in &cases {
                    let instance = find_instance_by_suffix(ctx.tcx, name);
                    let body = instance.body().expect("body");
                    let internal_name = instance.name();
                    ctx.set_current_fn(instance);
                    codegen_function_with_body(&mut ctx, instance, body, &internal_name);
                }
                for (name, expected) in cases {
                    let instance = find_instance_by_suffix(ctx.tcx, name);
                    let public_name = crate::rustc_compat::instance_name(ctx.tcx, instance);
                    let artifact = ctx.build_vc_artifact(&public_name, None);
                    let actual = artifact
                        .metadata
                        .as_ref()
                        .and_then(|meta| meta.obligation_free_body)
                        .unwrap_or(false);
                    assert_eq!(actual, expected, "{name}, CHC={use_chc}, reverse={reverse}");
                }
            });
        }
    }
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
// Rule D's discriminator at the nested-call fallback (design
// trust-mc-reds-final §4.1): only a callee the walk certifies FREE keeps the
// value-havoc blessing; "has an obligation" and "could not tell" both book the
// lost effect fail-closed.
// ---------------------------------------------------------------------------

/// The confirmed missed bug: an obligation inside a callee the walker gave up
/// on was blessed away as a sound havoc, so `assert!` inside `kani::block_on`
/// never reached the check list and the harness reported a CLEAN SUCCESSFUL.
#[test]
fn test_a_reachable_assert_is_not_inert() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn inner() { assert!(false); }
        pub fn probe_has_obligation() { inner(); }
    "#;
    assert!(
        !certifies(SOURCE, "probe_has_obligation"),
        "an assert behind a call keeps the callee from being inert"
    );
}

/// The other half: a clean chain is inert, so the fallback keeps blessing it.
#[test]
fn test_a_clean_chain_is_inert() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn lvl2(x: u32) -> u32 { x }
        fn lvl1(x: u32) -> u32 { lvl2(x) }
        pub fn probe_clean() { let _ = lvl1(7); }
    "#;
    assert!(certifies(SOURCE, "probe_clean"), "a clean chain carries no obligation");
}

/// "Could not tell" is not inert: an indirect callee is UNKNOWN, and Rule D
/// books it (before Rule D the fallback blessed it).
#[test]
fn test_an_unreadable_callee_is_not_inert() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn a(x: u32) -> u32 { x }
        pub fn probe_indirect(pick: bool) -> u32 {
            let f: fn(u32) -> u32 = if pick { a } else { a };
            f(7)
        }
    "#;
    assert!(!certifies(SOURCE, "probe_indirect"), "Unknown must never certify");
}

/// An obligation-free intrinsic (`OBLIGATION_FREE_INTRINSICS`) is inert, so
/// `rotate_left`'s body keeps its value-havoc class; its checked sibling
/// `unchecked_add` carries a UB precondition and is not.
#[test]
fn test_obligation_free_intrinsics_are_inert_and_checked_ones_are_not() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_rotate(x: u32) -> u32 { x.rotate_left(3) }
        pub fn probe_unchecked(x: u32) -> u32 { unsafe { x.unchecked_add(1) } }
    "#;
    assert!(certifies(SOURCE, "probe_rotate"), "rotate_left is total and checks nothing");
    assert!(!certifies(SOURCE, "probe_unchecked"), "unchecked_add carries a UB precondition");
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
        let (
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(from_def, _)),
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(to_def, _)),
        ) = (from_i.ty().kind(), to_i.ty().kind())
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

/// The CHC walker's obligation scans (`instance_obligation_verdict`,
/// `safe_foreign_callee_may_fail`) take the unit's stub map and resolve the
/// callee itself through it (`resolve_through_stubs`): a stub that adds an
/// obligation is seen, the original is not what they inspect. Before the
/// review round every scan used an empty map, and an abandoned region calling
/// a stubbed obligation-free function proved (`walker_stub_dual.rs`).
#[test]
fn test_walker_scans_resolve_through_the_stub_map() {
    use crate::codegen_ay::obligation_free_walk::{
        StubMap, Verdict, instance_obligation_verdict, resolve_through_stubs,
        safe_foreign_callee_may_fail,
    };
    let mut ran = false;
    with_test_ay_ctx_for_source(STUB_SOURCE, |ctx| {
        let def_of = |suffix: &str| match find_instance_by_suffix(ctx.tcx, suffix).ty().kind() {
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, args)) => {
                (def, args)
            }
            _ => panic!("{suffix} should be a FnDef"),
        };
        let (clean, clean_args) = def_of("stub_clean");
        let (panicking, _) = def_of("stub_panicking");
        let caller = find_instance_by_suffix(ctx.tcx, "probe_calls_clean");
        let none = StubMap::default();
        let mut stubs = StubMap::default();
        stubs.insert(clean, panicking);

        assert_eq!(instance_obligation_verdict(ctx.tcx, caller, &none), Verdict::Free);
        assert_eq!(
            instance_obligation_verdict(ctx.tcx, caller, &stubs),
            Verdict::HasObligation,
            "the scan follows the stub into its assert"
        );
        assert!(!safe_foreign_callee_may_fail(ctx.tcx, caller, &none));
        assert!(safe_foreign_callee_may_fail(ctx.tcx, caller, &stubs));

        let resolved = resolve_through_stubs(clean, &clean_args, &stubs).expect("resolves");
        assert_eq!(
            resolved.name(),
            find_instance_by_suffix(ctx.tcx, "stub_panicking").name(),
            "a stubbed callee resolves to the stub"
        );
        let unstubbed = resolve_through_stubs(clean, &clean_args, &none).expect("resolves");
        assert_eq!(unstubbed.name(), find_instance_by_suffix(ctx.tcx, "stub_clean").name());
        ran = true;
    });
    assert!(ran, "the test body ran");
}

/// The callee a probe function's first call terminator names, resolved.
fn first_callee(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    fn_suffix: &str,
) -> rustc_public::mir::mono::Instance {
    let body = find_instance_by_suffix(tcx, fn_suffix).body().expect("body");
    body.blocks
        .iter()
        .find_map(|block| match &block.terminator.kind {
            rustc_public::mir::TerminatorKind::Call { func, .. } => {
                match func.ty(body.locals()).ok()?.kind() {
                    rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(
                        def,
                        args,
                    )) => rustc_public::mir::mono::Instance::resolve(def, &args).ok(),
                    _ => None,
                }
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("{fn_suffix} calls something"))
}

/// A safe foreign callee the walker havocs can fail for its caller through a
/// panic at ANY depth (`slice::windows(0)` panics one call down, in
/// `Option::expect`), but not through the UB precondition checks inside the
/// std code it runs: `NonNull::new_unchecked`'s `assert_unsafe_precondition!`
/// panics through `panic_nounwind` behind `check_language_ub()`, and cannot
/// fail for a safe caller. The certificate (Full mode) still counts that
/// check; the havoc sighting does not.
#[test]
fn test_safe_foreign_callee_sights_deep_panics_but_not_ub_precondition_checks() {
    use crate::codegen_ay::obligation_free_walk::{
        StubMap, Verdict, instance_obligation_verdict, safe_foreign_callee_may_fail,
    };
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_calls_windows(s: &[u8], w: usize) -> usize {
            s.windows(w).len()
        }
        pub fn probe_calls_new_unchecked(p: *mut u8) -> core::ptr::NonNull<u8> {
            unsafe { core::ptr::NonNull::new_unchecked(p) }
        }
    "#;
    let mut ran = false;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let none = StubMap::default();
        let windows = first_callee(ctx.tcx, "probe_calls_windows");
        assert!(windows.name().contains("windows"), "resolved {}", windows.name());
        assert!(
            safe_foreign_callee_may_fail(ctx.tcx, windows, &none),
            "`windows(0)` panics below its own body"
        );
        let new_unchecked = first_callee(ctx.tcx, "probe_calls_new_unchecked");
        assert!(
            new_unchecked.name().contains("new_unchecked"),
            "resolved {}",
            new_unchecked.name()
        );
        assert_eq!(
            instance_obligation_verdict(ctx.tcx, new_unchecked, &none),
            Verdict::HasObligation,
            "the precondition check is there"
        );
        assert!(
            !safe_foreign_callee_may_fail(ctx.tcx, new_unchecked, &none),
            "a UB precondition check is not a failure a safe caller can cause"
        );
        ran = true;
    });
    assert!(ran, "the test body ran");
}

// ---------------------------------------------------------------------------
// STATEMENT sites (D16). Until 2026-09-12 the walk read terminators only, so
// every site below was invisible to it once no `Assert` stood in front —
// which is the shape rustc's `LowerIntrinsics` produces, the shape core's
// MIR takes, and the shape `--prove-safety-only` compiles. Each REFUSED case
// carries exactly one obligation and it is a statement; each CERTIFIED twin
// is the same statement kind with nothing to prove.
// ---------------------------------------------------------------------------

/// No overflow check, no debug assertion: the bare statements.
const BARE: &[&str] = &["-C", "overflow-checks=off", "-C", "debug-assertions=off"];

const INTRINSICS_PRELUDE: &str = r#"
    #![feature(core_intrinsics)]
    #![allow(internal_features, dead_code)]
"#;

fn intrinsics_source(body: &str) -> String {
    format!("{INTRINSICS_PRELUDE}\n{body}")
}

/// `unchecked_add` lowers to `BinOp::AddUnchecked` — a statement, no
/// `Assert`. The encoder's `emit_overflow_check` fires on it; the walk must
/// see the same site.
#[test]
fn test_unchecked_arithmetic_statement_is_refused() {
    for (name, expr) in [
        ("probe_unchecked_add", "core::intrinsics::unchecked_add(a, b)"),
        ("probe_unchecked_sub", "core::intrinsics::unchecked_sub(a, b)"),
        ("probe_unchecked_mul", "core::intrinsics::unchecked_mul(a, b)"),
        ("probe_unchecked_shl", "core::intrinsics::unchecked_shl(a, b)"),
        ("probe_unchecked_shr", "core::intrinsics::unchecked_shr(a, b)"),
    ] {
        let source = intrinsics_source(&format!(
            "pub fn {name}(a: u32, b: u32) -> u32 {{ unsafe {{ {expr} }} }}"
        ));
        assert!(
            !certifies(&source, name),
            "{name}: an unchecked operation is an obligation site even with no Assert in front"
        );
    }
}

/// `unchecked_div` / `unchecked_rem` lower to plain `BinOp::Div` / `Rem`
/// with NO division-by-zero `Assert`; the encoder still emits the
/// operator-level `binop_div_by_zero` / `binop_rem_by_zero` (UB, not the MIR
/// `Assert`'s panic labels).
#[test]
fn test_division_statement_is_refused() {
    for (name, expr) in [
        ("probe_div", "core::intrinsics::unchecked_div(a, b)"),
        ("probe_rem", "core::intrinsics::unchecked_rem(a, b)"),
    ] {
        let source = intrinsics_source(&format!(
            "pub fn {name}(a: u32, b: u32) -> u32 {{ unsafe {{ {expr} }} }}"
        ));
        assert!(!certifies(&source, name), "{name}: division is an obligation site");
    }
}

/// `offset` lowers to `BinOp::Offset`: non-null base, no overflow, result in
/// bounds (`emit_offset_overflow_check`, `emit_offset_object_bounds_check`).
#[test]
fn test_pointer_offset_statement_is_refused() {
    let source = intrinsics_source(
        "pub fn probe_offset(p: *const u32) -> *const u32 { unsafe { core::intrinsics::offset(p, 1isize) } }",
    );
    assert!(!certifies(&source, "probe_offset"), "an in-bounds offset is an obligation site");
}

/// The WRAPPING offset stays certified: leaving the object is not UB for
/// `arith_offset`, and the encoder emits nothing for it. The `Offset` refusal
/// above must not have widened into this.
#[test]
fn test_wrapping_pointer_offset_statement_is_certified() {
    let source = intrinsics_source(
        "pub fn probe_arith_offset(p: *const u32) -> *const u32 { unsafe { core::intrinsics::arith_offset(p, 1isize) } }",
    );
    assert!(
        certifies(&source, "probe_arith_offset"),
        "arith_offset has no obligation; refusing it costs `arith-offset-overflow/main.rs`"
    );
}

/// `copy_nonoverlapping` lowers to `StatementKind::Intrinsic`: alignment,
/// region validity, overlap and byte-count overflow are all checked.
#[test]
fn test_copy_nonoverlapping_statement_is_refused() {
    let source = intrinsics_source(
        "pub fn probe_copy(src: *const u32, dst: *mut u32) { unsafe { core::intrinsics::copy_nonoverlapping(src, dst, 1) } }",
    );
    assert!(!certifies(&source, "probe_copy"), "a byte copy is an obligation site");
}

/// `read_via_copy` lowers to `Use(Copy(*p))`, `write_via_move` to
/// `*p = move v`: a raw-pointer `Deref` projection on each side of an
/// assignment, with no null/alignment `Assert` (those are inserted BEFORE the
/// intrinsic is lowered, so they never see this deref).
#[test]
fn test_raw_pointer_deref_statement_is_refused() {
    let read = intrinsics_source(
        "pub fn probe_read(p: *const u32) -> u32 { unsafe { core::intrinsics::read_via_copy(p) } }",
    );
    assert!(!certifies(&read, "probe_read"), "a raw read is a memory-safety obligation");
    let write = intrinsics_source(
        "pub fn probe_write(p: *mut u32, v: u32) { unsafe { core::intrinsics::write_via_move(p, v) } }",
    );
    assert!(!certifies(&write, "probe_write"), "a raw write is a memory-safety obligation");
}

/// The everyday shape under `--prove-safety-only` (`-C debug-assertions=off`):
/// the user's own `*p`, with no `CheckNull` / `CheckAlignment` assert in front.
#[test]
fn test_raw_pointer_deref_without_debug_assertions_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_bare_deref(p: *const u32) -> u32 { unsafe { *p } }
        pub fn probe_bare_reborrow(p: *const u32) -> &'static u32 { unsafe { &*p } }
    "#;
    assert!(!certifies_with_rustc_flags(SOURCE, "probe_bare_deref", BARE));
    assert!(
        !certifies_with_rustc_flags(SOURCE, "probe_bare_reborrow", BARE),
        "`&*p` requires a valid pointer nothing established; the walk must not vouch for it"
    );
}

/// A dereference through a REFERENCE is safe by construction and must keep
/// certifying, or every `&T` parameter would refuse the certificate.
#[test]
fn test_reference_deref_statement_is_certified() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_ref_deref(r: &u32, m: &mut u32) -> u32 { *m = *r; *r }
    "#;
    assert!(certifies_with_rustc_flags(SOURCE, "probe_ref_deref", BARE));
}

/// `-x` on a signed integer with overflow checks OFF is a bare `UnOp::Neg`;
/// the encoder emits `emit_neg_overflow_check` (MIN overflows).
#[test]
fn test_signed_negation_statement_is_refused_without_overflow_checks() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_neg(x: i32) -> i32 { -x }
        pub fn probe_float_neg(x: f32) -> f32 { -x }
    "#;
    assert!(!certifies_with_rustc_flags(SOURCE, "probe_neg", BARE), "signed Neg overflows on MIN");
    assert!(
        certifies_with_rustc_flags(SOURCE, "probe_float_neg", BARE),
        "float negation is a sign flip and has nothing to prove"
    );
}

/// With overflow checks OFF, `a + b` is a bare wrapping `BinOp::Add` and the
/// encoder emits nothing for it — the twin of the unchecked refusal above.
#[test]
fn test_wrapping_arithmetic_statement_is_certified() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_wrapping(a: u32, b: u32) -> u32 { (a + b) * 3 - (a & b | a ^ b) }
        pub fn probe_wrapping_methods(a: u32, b: u32) -> u32 { a.wrapping_add(b).wrapping_mul(b).wrapping_sub(1) }
        pub fn probe_checked(a: u32, b: u32) -> u32 { a.overflowing_add(b).0 }
    "#;
    assert!(certifies_with_rustc_flags(SOURCE, "probe_wrapping", BARE));
    assert!(
        certifies(SOURCE, "probe_wrapping_methods"),
        "`wrapping_add` lowers to a plain `Add` inside core; nothing to prove"
    );
    assert!(
        certifies(SOURCE, "probe_checked"),
        "`CheckedBinaryOp` yields a flag; the obligation would be an Assert on it, and there is none"
    );
}

/// Float arithmetic carries the `--nan-check` obligation, so the walk does
/// not vouch for it: fail closed, never certify.
#[test]
fn test_float_arithmetic_statement_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_float(a: f32, b: f32) -> f32 { a + b }
        pub fn probe_float_div(a: f64, b: f64) -> f64 { a / b }
    "#;
    assert!(!certifies_with_rustc_flags(SOURCE, "probe_float", BARE));
    assert!(!certifies_with_rustc_flags(SOURCE, "probe_float_div", BARE));
}

/// Comparing pointers to trait objects reaches Kani's
/// `unstable_vtable_comparison` obligation; comparing thin pointers does not.
#[test]
fn test_dyn_pointer_comparison_statement_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub trait Tr {}
        pub fn probe_dyn_eq(a: *const dyn Tr, b: *const dyn Tr) -> bool { a == b }
        pub fn probe_thin_eq(a: *const u32, b: *const u32) -> bool { a == b }
    "#;
    assert!(!certifies_with_rustc_flags(SOURCE, "probe_dyn_eq", BARE));
    assert!(certifies_with_rustc_flags(SOURCE, "probe_thin_eq", BARE));
}

/// A transmute and a float cast take dedicated encoder paths this walk does
/// not re-derive; an integer cast does not.
#[test]
fn test_cast_statements() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_transmute(x: u32) -> f32 { unsafe { core::mem::transmute(x) } }
        pub fn probe_float_cast(x: f32) -> u32 { x as u32 }
        pub fn probe_int_cast(x: u32, p: *const u8) -> (u8, i64, usize) { (x as u8, x as i64, p as usize) }
    "#;
    assert!(!certifies_with_rustc_flags(SOURCE, "probe_transmute", BARE));
    assert!(!certifies_with_rustc_flags(SOURCE, "probe_float_cast", BARE));
    assert!(certifies_with_rustc_flags(SOURCE, "probe_int_cast", BARE));
}

/// Projections rustc has already checked: a slice pattern (`ConstantIndex`,
/// `Subslice`), a field, `Len` through a reference.
///
/// No enum `match` here, deliberately: rustc lowers one to a `SwitchInt`
/// whose `otherwise` arm is an `Unreachable` terminator, and the walk refuses
/// `Unreachable` (reaching it is UB; the encoder models it as an obligation).
/// That refusal is the terminator rule's, not this file's, and it is the
/// reason `kani/Enum/one_two.rs` is still not certified.
#[test]
fn test_checked_projections_are_certified() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub struct P { a: u32, b: u32 }
        pub fn probe_projections(v: [u32; 3], p: P, s: &[u32]) -> u32 {
            let [first, .., last] = v;
            let [_, middle @ ..] = v;
            first ^ last ^ middle.len() as u32 ^ p.a ^ p.b ^ (s.len() as u32)
        }
    "#;
    assert!(certifies_with_rustc_flags(SOURCE, "probe_projections", BARE));
}

/// A runtime-indexed access is a bounds obligation whether or not the
/// safe-code `Assert` is in front of it.
#[test]
fn test_runtime_index_statement_is_refused() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_index(v: &[u32], i: usize) -> u32 { v[i] }
    "#;
    assert!(!certifies(SOURCE, "probe_index"));
    assert!(!certifies_with_rustc_flags(SOURCE, "probe_index", BARE));
}

/// Package item (b) of fix/chc-walker-fail-closed: the walk's budget is not
/// evidence. A local callee whose obligation lies past the walk's body budget
/// is a SIGHTING (the walker's havoc of it fails closed), not "could not
/// tell": before, `body_has_visible_obligation` answered `false` and the
/// havoc kept the `nested_call_overapprox` blessing
/// (tools/soundness-duals/walker_obligation_budget_dual.rs). With the default
/// budget the same chains are read to the end: the obligation is sighted and
/// the clean chain is not.
#[test]
fn test_obligation_walk_budget_exhaustion_is_a_sighting() {
    use crate::codegen_ay::obligation_free_walk::{
        StubMap, WalkBudget, body_has_visible_obligation, body_has_visible_obligation_within,
    };
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #[inline(never)] fn f1(x: u8) -> u8 { f2(x) ^ 1 }
        #[inline(never)] fn f2(x: u8) -> u8 { f3(x) ^ 2 }
        #[inline(never)] fn f3(x: u8) -> u8 { f4(x) ^ 3 }
        #[inline(never)] fn f4(x: u8) -> u8 { deep_bug(x) }
        #[inline(never)] fn deep_bug(x: u8) -> u8 { assert!(x != 100); x }
        pub fn probe_deep_bug(x: u8) -> u8 { f1(x) }
        #[inline(never)] fn g1(x: u8) -> u8 { g2(x) ^ 1 }
        #[inline(never)] fn g2(x: u8) -> u8 { g3(x) ^ 2 }
        #[inline(never)] fn g3(x: u8) -> u8 { g4(x) ^ 3 }
        #[inline(never)] fn g4(x: u8) -> u8 { x }
        pub fn probe_deep_clean(x: u8) -> u8 { g1(x) }
    "#;
    let mut ran = false;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let none = StubMap::default();
        let small = WalkBudget { bodies: 3, blocks: WalkBudget::DEFAULT.blocks };
        let bug = find_instance_by_suffix(ctx.tcx, "probe_deep_bug");
        let clean = find_instance_by_suffix(ctx.tcx, "probe_deep_clean");
        assert!(body_has_visible_obligation(ctx.tcx, bug, &none), "the assert is sighted");
        assert!(!body_has_visible_obligation(ctx.tcx, clean, &none), "nothing to sight");
        assert!(
            body_has_visible_obligation_within(ctx.tcx, bug, &none, small),
            "an obligation past the budget: the unread code may hold it"
        );
        assert!(
            body_has_visible_obligation_within(ctx.tcx, clean, &none, small),
            "a clean chain past the budget is not known clean"
        );
        ran = true;
    });
    assert!(ran, "the test body ran");
}
