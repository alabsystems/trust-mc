// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Zero-sized enum payloads (row-72 regressions `expected/niche2/main.rs`,
//! `prusti/Fibonacci_sequence.rs`, `FunctionSymbols/issue1243.rs`).
//!
//! A BV-flattened multi-constructor enum omits its zero-sized fields from the
//! state vars (`unit_aware_multi_ctor_enum_layout`). Reading such a field, or
//! rebuilding the whole enum, needs the field's ONE value; a zero-sized type
//! has exactly one, so producing it is exact. Two sorts had no value to give:
//!
//! * an Array (`enum Foo { A(i32), B([i32; 0]) }`): the whole-enum read fell to
//!   the raw tag|payload concat, and the `Option<Foo>` payload coercion's
//!   unflatten built `B` with ZERO arguments — a panic since AY validates
//!   constructor signatures (ay ad07c5cc63);
//! * a Datatype (`Option<Infallible>`, the residual `?` on an `Option` moves out
//!   of `ControlFlow::Break`): the read declined, and the flattened destination
//!   fell to `flatten_self_loop_fallback`, a translation drop that demotes the
//!   harness.

use super::common::*;

const ZST_ARRAY_PAYLOAD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum Foo {
        A(i32),
        B([i32; 0]),
    }

    pub fn probe_zst_array_payload(x: i32) -> bool {
        let foo = Foo::A(x);
        let wrapped = Some(foo);
        match wrapped {
            Some(Foo::A(y)) => y == x,
            _ => false,
        }
    }
"#;

/// What `Try::branch` / `FromResidual::from_residual` on an `Option` leave in
/// the caller once inlined (`try_fold` under `Iterator::nth`): a
/// `ControlFlow<Option<Infallible>, _>` whose `Break` residual is moved out.
const OPTION_RESIDUAL_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::convert::Infallible;
    use std::ops::ControlFlow;

    pub fn probe_option_residual(x: Option<u32>) -> Option<u32> {
        let flow: ControlFlow<Option<Infallible>, u32> = match x {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        };
        match flow {
            ControlFlow::Continue(v) => Some(v / 2),
            ControlFlow::Break(residual) => from_residual(residual),
        }
    }

    #[inline(never)]
    fn from_residual(residual: Option<Infallible>) -> Option<u32> {
        match residual {
            None => None,
            Some(never) => match never {},
        }
    }
"#;

fn reset_metadata() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_aggregate_gap_reasons_by_fn();
}

/// The first local whose type is the ADT named `adt_name`.
fn local_of_adt(body: &rustc_public::mir::Body, adt_name: &str) -> usize {
    body.locals()
        .iter()
        .position(|decl| match decl.ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                let name = def.name();
                name == adt_name || name.ends_with(&format!("::{adt_name}"))
            }
            _ => false,
        })
        .unwrap_or_else(|| panic!("no local of type {adt_name}"))
}

#[test]
fn test_zst_array_payload_enum_rebuilds_as_datatype() {
    with_test_ay_ctx_for_source(ZST_ARRAY_PAYLOAD_SOURCE, |ctx| {
        let fn_name = "probe_zst_array_payload";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let foo_local = local_of_adt(&body, "Foo");
        assert!(
            chc_ctx.flatten.enum_bv_layouts.contains_key(&foo_local),
            "precondition: the Foo local must be a BV-flattened multi-ctor enum"
        );
        let foo_sort = ChcCtx::translate_ty(body.locals()[foo_local].ty).expect("Foo sort");
        assert!(foo_sort.is_datatype(), "precondition: Foo translates to a Datatype");

        let read = chc_ctx
            .translate_place_with_modified(
                &Place { local: foo_local, projection: vec![] },
                &HashSet::new(),
            )
            .expect("a whole-Foo read must translate");
        assert_eq!(
            *read.sort(),
            foo_sort,
            "the whole-Foo read must rebuild the Datatype (B's [i32; 0] is the one \
             zero-sized value), not concatenate the tag and payload into a raw BV"
        );
    });
}

#[test]
fn test_zst_array_payload_enum_wrapped_in_option_translates_without_fallback() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_metadata();

    with_test_ay_ctx_for_source(ZST_ARRAY_PAYLOAD_SOURCE, |ctx| {
        let fn_name = "probe_zst_array_payload";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        // Panicked with "datatype_constructor requires a matching datatype
        // constructor signature" before the fix.
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        assert_vc_structure(&vc, fn_name, body.blocks.len());

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(fallback_count, 0, "{fn_name} must not use a CHC fallback");
    });

    let gaps = crate::codegen_ay::take_aggregate_gap_reasons_by_fn();
    assert!(
        !gaps.contains_key("probe_zst_array_payload"),
        "the Option<Foo> payload must be the rebuilt Foo, not a fresh symbol: {gaps:?}"
    );
    let sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    assert!(
        !sites.contains_key("probe_zst_array_payload"),
        "no translation may be dropped: {sites:?}"
    );
    reset_metadata();
}

#[test]
fn test_option_residual_moved_out_of_break_is_not_a_translation_drop() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_metadata();

    with_test_ay_ctx_for_source(OPTION_RESIDUAL_SOURCE, |ctx| {
        let fn_name = "probe_option_residual";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        assert_vc_structure(&vc, fn_name, body.blocks.len());
    });

    let sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let reasons = sites.get("probe_option_residual").cloned().unwrap_or_default();
    assert!(
        !reasons.contains_key("flatten_self_loop_fallback"),
        "moving the Option<Infallible> residual out of ControlFlow::Break must assign \
         its one value (None), not self-loop the destination: {reasons:?}"
    );
    let gaps = crate::codegen_ay::take_aggregate_gap_reasons_by_fn();
    assert!(
        !gaps.contains_key("probe_option_residual"),
        "`ControlFlow::Break(None)` must build its zero-sized payload, not a fresh symbol: \
         {gaps:?}"
    );
    reset_metadata();
}
