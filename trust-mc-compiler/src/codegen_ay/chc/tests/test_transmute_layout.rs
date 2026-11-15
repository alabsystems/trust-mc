// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A transmute between a multi-field struct (or tuple) and a bitvector follows
//! the memory layout: the field at byte offset 0 is the LOW end, and a slice
//! pointer's word at offset 8 is its length (codegen_stmt_transmute_layout.rs).
//! The declaration-order flatten this replaces put the first field in the HIGH
//! half. tools/soundness-duals/chc_transmute_memory_order_dual.rs is the
//! end-to-end twin.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::call::codegen_call_misc::Referent;
use crate::codegen_ay::provenance::Val;
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Sort;
use rustc_public::mir::{CastKind, Rvalue, StatementKind};

const TRANSMUTE_SOURCE: &str = r#"
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Words { pub lo: u64, pub hi: u64 }

#[repr(C)]
#[derive(Clone, Copy)]
pub struct FatPtr { pub data: *const u8, pub len: usize }

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Padded { pub a: u8, pub b: u32 }

pub fn probe_to_u128(w: Words) -> u128 { unsafe { core::mem::transmute(w) } }
pub fn probe_from_u128(x: u128) -> Words { unsafe { core::mem::transmute(x) } }
pub fn probe_to_slice<'a>(raw: FatPtr) -> &'a [u8] { unsafe { core::mem::transmute(raw) } }
pub fn probe_from_slice(s: &[u8]) -> FatPtr { unsafe { core::mem::transmute(s) } }
pub fn probe_padded(p: Padded) -> u64 { unsafe { core::mem::transmute(p) } }
"#;

/// The value of the first transmute in `fn_suffix`, translated.
fn translate_transmute(tcx: TyCtxt<'_>, fn_suffix: &str) -> Expr {
    let instance = find_instance_by_suffix(tcx, fn_suffix);
    let body = instance.body().expect("function body");
    let mut chc_ctx = ChcCtx::new(tcx, &body, fn_suffix, ChcConfig::default());
    chc_ctx.declare_block_relations();
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(place, rvalue @ Rvalue::Cast(CastKind::Transmute, _, _)) =
                &stmt.kind
            {
                return chc_ctx
                    .translate_rvalue_with_modified(rvalue, &HashSet::new(), Some(place.local))
                    .expect("transmute translates");
            }
        }
    }
    panic!("expected a Transmute cast in {fn_suffix}");
}

/// `true` when `expr` reads MIR field `idx` named `name` of the argument: a
/// field select, or the flattened argument's per-field state variable.
fn reads_field(expr: &Expr, idx: usize, name: &str) -> bool {
    let text = expr.to_string();
    text.contains(&format!("fld_{name}")) || text.ends_with(&format!("_fld{idx}"))
}

#[test]
fn struct_to_u128_puts_the_offset_zero_field_low() {
    with_test_ay_ctx_for_source(TRANSMUTE_SOURCE, |ctx| {
        let value = translate_transmute(ctx.tcx, "probe_to_u128");
        let ExprValue::BvConcat(high, low) = value.value() else {
            panic!("expected concat(high, low), got {value}");
        };
        assert!(reads_field(low, 0, "lo"), "offset 0 is the low word: {value}");
        assert!(reads_field(high, 1, "hi"), "offset 8 is the high word: {value}");
    });
}

#[test]
fn u128_to_struct_reads_each_field_at_its_offset() {
    with_test_ay_ctx_for_source(TRANSMUTE_SOURCE, |ctx| {
        let value = translate_transmute(ctx.tcx, "probe_from_u128");
        let ExprValue::DatatypeConstructor { args, .. } = value.value() else {
            panic!("expected the Words constructor, got {value}");
        };
        let [lo, hi] = args.as_slice() else { panic!("two fields: {value}") };
        assert!(
            matches!(lo.value(), ExprValue::BvExtract { high: 63, low: 0, .. }),
            "lo is bits 63..0: {lo}"
        );
        assert!(
            matches!(hi.value(), ExprValue::BvExtract { high: 127, low: 64, .. }),
            "hi is bits 127..64: {hi}"
        );
    });
}

#[test]
fn struct_to_slice_pointer_puts_the_length_word_high() {
    with_test_ay_ctx_for_source(TRANSMUTE_SOURCE, |ctx| {
        let value = translate_transmute(ctx.tcx, "probe_to_slice");
        let Some(PtrRepr::Fat { data, meta }) = PtrRepr::classify(&value) else {
            panic!("a structural wide pointer, got {value}");
        };
        assert!(reads_field(data.as_expr(), 0, "data"), "data word low: {value}");
        assert!(reads_field(meta.as_expr(), 1, "len"), "length word high: {value}");
    });
}

#[test]
fn slice_pointer_to_struct_reads_the_length_from_the_high_word() {
    with_test_ay_ctx_for_source(TRANSMUTE_SOURCE, |ctx| {
        let value = translate_transmute(ctx.tcx, "probe_from_slice");
        let ExprValue::DatatypeConstructor { args, .. } = value.value() else {
            panic!("expected the FatPtr constructor, got {value}");
        };
        let [_data, len] = args.as_slice() else { panic!("two fields: {value}") };
        assert!(
            matches!(len.value(), ExprValue::BvExtract { high: 127, low: 64, .. }),
            "len is the slice's high word: {len}"
        );
    });
}

#[test]
fn padded_struct_to_integer_keeps_fields_and_frees_the_padding() {
    with_test_ay_ctx_for_source(TRANSMUTE_SOURCE, |ctx| {
        // `Padded { a: u8, b: u32 }`: `a` at byte 0, three padding bytes, `b` at 4,
        // folded from the high end: concat(concat(b, padding), a).
        let value = translate_transmute(ctx.tcx, "probe_padded");
        let ExprValue::BvConcat(upper, a) = value.value() else {
            panic!("expected concat(concat(b, padding), a), got {value}");
        };
        assert!(reads_field(a, 0, "a"), "offset 0 is the low byte: {value}");
        let ExprValue::BvConcat(b, padding) = upper.value() else {
            panic!("expected concat(b, padding) above a, got {value}");
        };
        assert!(reads_field(b, 1, "b"), "offset 4 is the high word: {value}");
        assert_eq!(padding.sort().bitvec_width(), Some(24), "three padding bytes: {value}");
        assert!(
            padding.to_string().contains("__transmute_padding"),
            "padding bytes are fresh, never zero: {value}"
        );
        assert!(!value.to_string().contains("__transmute_layout_nondet"), "{value}");
    });
}

#[test]
fn slice_eq_refuses_the_operands_own_pointer() {
    with_test_ay_ctx_for_source(TRANSMUTE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_from_slice");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_from_slice", ChcConfig::default());
        let wide = Expr::var("_s", Sort::bitvec(2 * POINTER_WIDTH));
        let thin = Expr::var("_p", Sort::bitvec(POINTER_WIDTH));
        let elems = Expr::var("_e", Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8)));
        assert!(chc_ctx.slice_eq_referent_datum(Referent::Unreported(wide)).is_none());
        assert!(chc_ctx.slice_eq_referent_datum(Referent::Unreported(thin.clone())).is_none());
        assert_eq!(
            chc_ctx.slice_eq_referent_datum(Referent::Unreported(elems.clone())),
            Some(elems),
            "element storage is the datum"
        );
        assert_eq!(
            chc_ctx.slice_eq_referent_datum(Referent::Value(Val::of_value(thin.clone()))),
            Some(thin),
            "a tier that dereferenced is the datum"
        );
    });
}
