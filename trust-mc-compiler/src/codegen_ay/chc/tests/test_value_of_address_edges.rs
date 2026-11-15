// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `ChcCtx::value_is_address`: the field types whose `ref_targets` value-of
//! edges `drop_pointer_field_value_of_edges` drops. An edge that records the
//! VALUE of an address-typed field is not a points-at edge, whatever type the
//! address is spelled in (tools/soundness-duals/dyn_deref_generic_return_dual.rs).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

const SOURCE: &str = r#"
    #![allow(dead_code, unused_variables)]
    pub trait Identity { fn id(&self) -> u16; }
    #[repr(transparent)]
    pub struct W(u32);
    pub fn probe_addresses(
        r: &u8,
        raw: *const u8,
        nonnull: std::ptr::NonNull<u8>,
        nonnull_dyn: std::ptr::NonNull<dyn Identity>,
        boxed: Box<u8>,
        boxed_dyn: Box<dyn Identity>,
    ) {
    }
    pub fn probe_values(
        word: u32,
        newtype: W,
        cell: std::cell::RefCell<*const u8>,
        pair: (*const u8, u8),
    ) {
    }
"#;

#[test]
fn test_an_address_in_any_representation_is_an_address() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_addresses");
        for (i, ty) in sig.inputs().iter().enumerate() {
            assert!(ChcCtx::value_is_address(*ty), "input {i} ({ty:?}) is an address");
        }
    });
}

#[test]
fn test_a_value_that_holds_no_address_by_representation_is_not_one() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_values");
        for (i, ty) in sig.inputs().iter().enumerate() {
            assert!(!ChcCtx::value_is_address(*ty), "input {i} ({ty:?}) is not an address");
        }
    });
}

const NONNULL_FIELD_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub struct H {
        p: std::ptr::NonNull<u8>,
    }
    pub fn probe_nonnull_field_copy(h: &H) -> u8 {
        let q = h.p;
        unsafe { *q.as_ptr() }
    }
"#;

/// `q = copy ((*h).p)` copies the NonNull's VALUE: `q` holds the address the
/// field holds, it does not point at the field. Its value-of edge onto the
/// `NonNull` field is dropped, as one onto a raw-pointer field always was;
/// kept, a read through `q` was rewritten onto the field's own bits.
#[test]
fn test_value_of_edge_onto_a_nonnull_field_is_dropped() {
    with_test_ay_ctx_for_source(NONNULL_FIELD_SOURCE, |ctx| {
        let fn_name = "probe_nonnull_field_copy";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("body");
        let copy_dest = body
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .find_map(|stmt| match &stmt.kind {
                rustc_public::mir::StatementKind::Assign(
                    lhs,
                    rustc_public::mir::Rvalue::Use(Operand::Copy(place), ..),
                ) if matches!(
                    place.projection.as_slice(),
                    [
                        rustc_public::mir::ProjectionElem::Deref,
                        rustc_public::mir::ProjectionElem::Field(0, _)
                    ]
                ) =>
                {
                    Some(lhs.local)
                }
                _ => None,
            })
            .expect("the probe copies (*h).p");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();
        assert!(
            !chc_ctx.ref_resolution.ref_targets.contains_key(&copy_dest),
            "a copy of a NonNull field holds its value, not a points-at edge: {:?}",
            chc_ctx.ref_resolution.ref_targets.get(&copy_dest)
        );
    });
}
