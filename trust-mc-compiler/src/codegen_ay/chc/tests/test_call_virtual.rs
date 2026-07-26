// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_virtual.rs` — top-level virtual dispatch semantics.
//!
//! Part of #3365 — rebaseline the virtual-dispatch coverage boundary so the
//! dispatcher has a dedicated test home separate from the inline walker.
//!
//! Coverage areas:
//! - dyn return-vtable retention across fn-inline, fn-ptr, and virtual-return paths
//! - receiver-alias recovery at the top-level virtual call site
//! - cross-block `vtable_state_vars` recovery at merge points
//! - negative/fallback coverage via the compiletest canary
//!   `tests/trust_mc/FatPointers/boxmuttrait_fail.rs`

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use rustc_public::mir::TerminatorKind;
use rustc_public::mir::mono::{Instance, InstanceKind};

/// Probe: helper returns `Box<dyn Trait>`, caller later performs virtual dispatch.
/// Exercises fn_inline return-place vtable capture plus Deref-only receiver lookup.
const INLINE_BOX_DYN_RETURN_PROBE: &str = r#"
    #![allow(dead_code)]

    trait Animal {
        fn noise(&self) -> u32;
    }

    struct Sheep;
    impl Animal for Sheep {
        fn noise(&self) -> u32 { 1 }
    }

    struct Cow;
    impl Animal for Cow {
        fn noise(&self) -> u32 { 2 }
    }

    fn random_animal(random_number: i64) -> Box<dyn Animal> {
        if random_number < 5 { Box::new(Sheep) } else { Box::new(Cow) }
    }

    pub fn probe_inline_box_dyn_dispatch(random_number: i64) {
        let animal = random_animal(random_number);
        let s = animal.noise();
        if random_number < 5 {
            assert!(s == 1);
        } else {
            assert!(s == 2);
        }
    }
"#;

/// Probe: fn-pointer call returns `Box<dyn Trait>`, caller later performs
/// virtual dispatch. Exercises top-level `fn_ptr` return vtable capture.
const FN_PTR_BOX_DYN_RETURN_PROBE: &str = r#"
    #![allow(dead_code)]

    trait Animal {
        fn noise(&self) -> u32;
    }

    struct Sheep;
    impl Animal for Sheep {
        fn noise(&self) -> u32 { 1 }
    }

    struct Cow;
    impl Animal for Cow {
        fn noise(&self) -> u32 { 2 }
    }

    fn random_animal(random_number: i64) -> Box<dyn Animal> {
        if random_number < 5 { Box::new(Sheep) } else { Box::new(Cow) }
    }

    pub fn probe_fn_ptr_box_dyn_dispatch(random_number: i64) {
        let chooser: fn(i64) -> Box<dyn Animal> = random_animal;
        let animal = chooser(random_number);
        let s = animal.noise();
        if random_number < 5 {
            assert!(s == 1);
        } else {
            assert!(s == 2);
        }
    }
"#;

/// Probe: single-impl virtual dispatch returns `Box<dyn Trait>`, caller later
/// performs another virtual dispatch on the returned object.
const SINGLE_IMPL_VIRTUAL_BOX_DYN_RETURN_PROBE: &str = r#"
    #![allow(dead_code)]

    trait Animal {
        fn noise(&self) -> u32;
    }

    struct Sheep;
    impl Animal for Sheep {
        fn noise(&self) -> u32 { 1 }
    }

    struct Cow;
    impl Animal for Cow {
        fn noise(&self) -> u32 { 2 }
    }

    fn random_animal(random_number: i64) -> Box<dyn Animal> {
        if random_number < 5 { Box::new(Sheep) } else { Box::new(Cow) }
    }

    trait Kennel {
        fn adopt(&self, random_number: i64) -> Box<dyn Animal>;
    }

    struct Farm;
    impl Kennel for Farm {
        fn adopt(&self, random_number: i64) -> Box<dyn Animal> {
            random_animal(random_number)
        }
    }

    pub fn probe_single_impl_virtual_box_dyn_dispatch(random_number: i64) {
        let farm = Farm;
        let kennel: &dyn Kennel = &farm;
        let animal = kennel.adopt(random_number);
        let s = animal.noise();
        if random_number < 5 {
            assert!(s == 1);
        } else {
            assert!(s == 2);
        }
    }
"#;

/// Probe: multi-impl virtual dispatch returns `Box<dyn Trait>`, requiring the
/// dispatch ITE chain to preserve both the value and the returned vtable.
const MULTI_IMPL_VIRTUAL_BOX_DYN_RETURN_PROBE: &str = r#"
    #![allow(dead_code)]

    trait Animal {
        fn noise(&self) -> u32;
    }

    struct Sheep;
    impl Animal for Sheep {
        fn noise(&self) -> u32 { 1 }
    }

    struct Cow;
    impl Animal for Cow {
        fn noise(&self) -> u32 { 2 }
    }

    trait Kennel {
        fn adopt(&self) -> Box<dyn Animal>;
    }

    struct SheepFarm;
    impl Kennel for SheepFarm {
        fn adopt(&self) -> Box<dyn Animal> { Box::new(Sheep) }
    }

    struct CowFarm;
    impl Kennel for CowFarm {
        fn adopt(&self) -> Box<dyn Animal> { Box::new(Cow) }
    }

    pub fn probe_multi_impl_virtual_box_dyn_dispatch(use_sheep: bool) {
        let sheep_farm = SheepFarm;
        let cow_farm = CowFarm;
        let kennel: &dyn Kennel = if use_sheep { &sheep_farm } else { &cow_farm };
        let animal = kennel.adopt();
        let s = animal.noise();
        if use_sheep {
            assert!(s == 1);
        } else {
            assert!(s == 2);
        }
    }
"#;

/// Probe: a boxed dyn value flows through a generic deref helper while an
/// unrelated blanket impl introduces a second virtual-dispatch candidate.
/// This matches the `#3872` shape where the receiver local at `value.id()`
/// is an alias temp rather than the original dyn-bearing local.
const BOX_DYN_BLANKET_IMPL_ALIAS_PROBE: &str = r#"
    #![allow(dead_code)]

    use std::ops::Deref;

    trait Identity {
        fn id(&self) -> u8;
    }

    struct Inner(u8);
    impl Identity for Inner {
        fn id(&self) -> u8 { self.0 }
    }

    struct Outer<T: ?Sized>(Box<T>);
    impl<T: ?Sized + Identity> Identity for Outer<T> {
        fn id(&self) -> u8 { self.0.id() }
    }

    fn id_from_coerce<T: Deref<Target = dyn Identity>>(value: T) -> u8 {
        value.id()
    }

    pub fn probe_box_dyn_blanket_impl_alias() {
        let boxed: Box<dyn Identity> = Box::new(Inner(7));
        let actual = id_from_coerce(boxed);
        assert!(actual == 7);
    }
"#;

/// Probe: `Pin::as_mut` on a boxed dyn receiver must preserve the receiver's
/// vtable so the immediately-following virtual dispatch does not fall back to
/// a fresh symbolic discriminant.
const PIN_AS_MUT_BOX_DYN_DISPATCH_PROBE: &str = r#"
    #![allow(dead_code)]

    use std::pin::Pin;

    trait PinnedValue {
        fn id(self: Pin<&mut Self>) -> u8;
    }

    struct Inner(u8);

    impl PinnedValue for Inner {
        fn id(self: Pin<&mut Self>) -> u8 {
            self.get_mut().0
        }
    }

    pub fn probe_pin_as_mut_box_dyn_dispatch() {
        let mut value: Pin<Box<dyn PinnedValue>> = Box::pin(Inner(7));
        let actual = value.as_mut().id();
        assert!(actual == 7);
    }
"#;

/// Probe: dyn receiver is created in predecessor blocks and used only after a
/// merge, so the dispatcher must recover the receiver identity from the
/// propagated `vtable_state_vars` path instead of a same-block side table.
const CROSS_BLOCK_VTABLE_STATE_VAR_PROBE: &str = r#"
    #![allow(dead_code)]

    trait Animal {
        fn noise(&self) -> u32;
    }

    struct Sheep;
    impl Animal for Sheep {
        fn noise(&self) -> u32 { 1 }
    }

    struct Cow;
    impl Animal for Cow {
        fn noise(&self) -> u32 { 2 }
    }

    pub fn probe_cross_block_virtual_dispatch(flag: bool) {
        let sheep = Sheep;
        let cow = Cow;
        let chosen: &dyn Animal;
        if flag {
            chosen = &sheep;
        } else {
            chosen = &cow;
        }
        let s = chosen.noise();
        if flag {
            assert!(s == 1);
        } else {
            assert!(s == 2);
        }
    }
"#;

fn assert_box_dyn_dispatch_has_precise_vtable(source: &str, entry: &str) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, entry);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, entry, ChcConfig::default());

        assert!(!vc.rules.is_empty(), "{entry} should produce rules");
        assert!(has_any_constraints(&vc), "{entry} should constrain the VC");
        assert!(
            !vc_error_rules_contain_var(&vc, "__vtable_disc"),
            "{entry} should not reach error via a fresh vtable fallback"
        );
    });
}

fn find_first_virtual_call_site(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> (usize, Vec<Operand>, String) {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| {
            let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                return None;
            };
            let func_ty = func.ty(body.locals()).ok()?;
            let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func_ty.kind() else {
                return None;
            };
            let instance = Instance::resolve(def, &substs).ok()?;
            matches!(instance.kind, InstanceKind::Virtual { .. }).then(|| {
                let callee_path = chc_ctx
                    .resolve_callee_path(func)
                    .unwrap_or_else(|| "<virtual dispatch>".to_string());
                (bb_idx, args.clone(), callee_path)
            })
        })
        .expect("expected virtual call terminator")
}

fn receiver_local_from_operand(arg: &Operand) -> Option<usize> {
    match arg {
        Operand::Copy(place) | Operand::Move(place) => Some(place.local),
        Operand::Constant(_) => None,
    }
}

#[test]
fn test_inline_box_dyn_return_avoids_fresh_vtable_fallback() {
    assert_box_dyn_dispatch_has_precise_vtable(
        INLINE_BOX_DYN_RETURN_PROBE,
        "probe_inline_box_dyn_dispatch",
    );
}

#[test]
fn test_fn_ptr_box_dyn_return_avoids_fresh_vtable_fallback() {
    assert_box_dyn_dispatch_has_precise_vtable(
        FN_PTR_BOX_DYN_RETURN_PROBE,
        "probe_fn_ptr_box_dyn_dispatch",
    );
}

#[test]
fn test_single_impl_virtual_box_dyn_return_avoids_fresh_vtable_fallback() {
    assert_box_dyn_dispatch_has_precise_vtable(
        SINGLE_IMPL_VIRTUAL_BOX_DYN_RETURN_PROBE,
        "probe_single_impl_virtual_box_dyn_dispatch",
    );
}

#[test]
fn test_multi_impl_virtual_box_dyn_return_avoids_fresh_vtable_fallback() {
    assert_box_dyn_dispatch_has_precise_vtable(
        MULTI_IMPL_VIRTUAL_BOX_DYN_RETURN_PROBE,
        "probe_multi_impl_virtual_box_dyn_dispatch",
    );
}

#[test]
fn test_box_dyn_blanket_impl_alias_avoids_fresh_vtable_fallback() {
    assert_box_dyn_dispatch_has_precise_vtable(
        BOX_DYN_BLANKET_IMPL_ALIAS_PROBE,
        "probe_box_dyn_blanket_impl_alias",
    );
}

#[test]
fn test_cross_block_virtual_dispatch_uses_vtable_state_var() {
    with_test_ay_ctx_for_source(CROSS_BLOCK_VTABLE_STATE_VAR_PROBE, |ctx| {
        let fn_name = "probe_cross_block_virtual_dispatch";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, args, callee_path) = find_first_virtual_call_site(&chc_ctx, &body);
        let (_stmt_constraints, _output_args, modified_locals, _safety_checks) =
            chc_ctx.encode_block_statements(bb_idx);
        let receiver_local = receiver_local_from_operand(
            args.first().expect("virtual dispatch should have a receiver operand"),
        )
        .expect("virtual dispatch receiver should lower through a local place");

        let mut param_exprs = Vec::with_capacity(args.len());
        for arg in &args {
            param_exprs.push(
                chc_ctx
                    .translate_operand_with_modified(arg, &modified_locals)
                    .expect("virtual call args should translate"),
            );
        }

        let vtable_expr =
            chc_ctx.try_extract_vtable_discriminant(&param_exprs, Some(receiver_local));
        let vtable_text = vtable_expr.to_string();
        assert!(
            vtable_text.contains("__vtable_sv_"),
            "{callee_path} should use a propagated vtable state var after the merge, got {vtable_text}"
        );

        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert!(
            !vc_error_rules_contain_var(&vc, "__vtable_disc"),
            "{fn_name} should not fall back to a fresh vtable discriminant"
        );
        assert!(
            !vc_error_rules_contain_var(&vc, "__assert_fail_inline"),
            "{fn_name} should preserve the merged receiver semantics"
        );
    });
}

#[test]
fn test_pin_as_mut_identity_preserves_vtable_for_virtual_dispatch() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(PIN_AS_MUT_BOX_DYN_DISPATCH_PROBE, |ctx| {
        let fn_name = "probe_pin_as_mut_box_dyn_dispatch";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, _diagnostics) = chc_ctx.translate_with_diagnostics();
        assert_vc_structure(&vc, fn_name, body.blocks.len());
    });

    let translation_drops = take_translation_drop_by_fn();
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let vtable_missing_count = translation_sites
        .get("probe_pin_as_mut_box_dyn_dispatch")
        .and_then(|reasons| reasons.get("virtual_missing_vtable"))
        .copied()
        .unwrap_or(0);

    // Worker vtable_prop expansion may introduce additional virtual_missing_vtable
    // sites for intermediate Pin projections. Accept up to 2 (over-approximation, sound).
    assert!(
        vtable_missing_count <= 2,
        "Pin::as_mut virtual_missing_vtable count should be <=2 (over-approx acceptable); \
         got {vtable_missing_count}; \
         translation_drops={translation_drops:?}, translation_sites={translation_sites:?}",
    );
}
