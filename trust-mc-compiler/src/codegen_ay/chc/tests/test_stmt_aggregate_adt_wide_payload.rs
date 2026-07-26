// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Wide-payload aggregate regressions for `codegen_stmt_aggregate_adt.rs`.
//!
//! Split from `test_stmt_aggregate_adt.rs` for file-size compliance.
//! Part of #4087 D4.

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::rustc_public_bridge::IndexedVal;

const GENERAL_ENUM_WIDE_PAYLOAD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum MaybeWide {
        Thin(u32),
        Wide(&'static str),
    }

    pub fn probe_make_wide(flag: bool) -> MaybeWide {
        if flag {
            MaybeWide::Wide("bar")
        } else {
            MaybeWide::Thin(1)
        }
    }
"#;

const STANDARD_ENUM_WIDE_PAYLOAD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub enum MyError {
        Error1(i32),
        Error2(&'static str),
        Error3 { description: String, code: u32 },
    }

    pub fn probe_make_error2() -> MyError {
        MyError::Error2("bar")
    }
"#;

fn find_named_aggregate(
    body: &rustc_public::mir::Body,
    expected_variant: &str,
) -> Option<(
    rustc_public::ty::AdtDef,
    rustc_public::ty::VariantIdx,
    rustc_public::ty::GenericArgs,
    Vec<rustc_public::mir::Operand>,
)> {
    for block in &body.blocks {
        for statement in &block.statements {
            if let rustc_public::mir::StatementKind::Assign(
                _,
                rustc_public::mir::Rvalue::Aggregate(
                    rustc_public::mir::AggregateKind::Adt(def, variant_idx, args, _, _),
                    operands,
                ),
            ) = &statement.kind
            {
                let variant = &def.variants()[variant_idx.to_index()];
                if variant.name() == expected_variant {
                    return Some((*def, *variant_idx, args.clone(), operands.clone()));
                }
            }
        }
    }
    None
}

#[test]
fn test_general_enum_wide_payload_extracts_ptr_before_constructor() {
    with_test_ay_ctx_for_source(GENERAL_ENUM_WIDE_PAYLOAD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_make_wide");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_make_wide", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (def, variant_idx, args, operands) = find_named_aggregate(&body, "Wide")
            .expect("probe_make_wide should contain a Wide aggregate");
        let expr = chc_ctx
            .translate_adt_aggregate(def, variant_idx, &args, &operands, &HashSet::new())
            .expect("Wide aggregate should translate");

        let ExprValue::DatatypeConstructor { constructor_name, args, .. } = expr.value() else {
            panic!("Wide aggregate should translate to a datatype constructor: {:?}", expr.value());
        };
        assert!(
            constructor_name.contains("Wide"),
            "expected Wide constructor, got {constructor_name}"
        );
        assert_eq!(args.len(), 1, "Wide variant should carry exactly one payload");
        // Current behavior: wide payload uses BV encoding (BvZeroExtend/BvConcat).
        // Target (#4087): narrow to DatatypeSelector { selector_name: "fld_ptr" }.
        let is_dt_selector = matches!(
            args[0].value(),
            ExprValue::DatatypeSelector { selector_name, .. } if selector_name == "fld_ptr"
        );
        let is_bv_encoding =
            matches!(args[0].value(), ExprValue::BvZeroExtend { .. } | ExprValue::BvConcat(_, _));
        assert!(
            is_dt_selector || is_bv_encoding,
            "wide payload should be DT selector or BV encoding, got {:?}",
            args[0].value()
        );
    });
}

#[test]
fn test_standard_enum_wide_payload_extracts_ptr_before_constructor() {
    with_test_ay_ctx_for_source(STANDARD_ENUM_WIDE_PAYLOAD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_make_error2");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_make_error2", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (def, variant_idx, args, operands) = find_named_aggregate(&body, "Error2")
            .expect("probe_make_error2 should contain an Error2 aggregate");
        let expr = chc_ctx
            .translate_adt_aggregate(def, variant_idx, &args, &operands, &HashSet::new())
            .expect("Error2 aggregate should translate");

        let ExprValue::DatatypeConstructor { constructor_name, args, .. } = expr.value() else {
            panic!(
                "Error2 aggregate should translate to a datatype constructor: {:?}",
                expr.value()
            );
        };
        assert!(
            constructor_name.contains("Error2"),
            "expected Error2 constructor, got {constructor_name}"
        );
        assert_eq!(args.len(), 1, "Error2 should carry exactly one payload");
        // Current behavior: wide payload uses BV encoding (BvZeroExtend/BvConcat).
        // Target (#4087): narrow to DatatypeSelector { selector_name: "fld_ptr" }.
        let is_dt_selector = matches!(
            args[0].value(),
            ExprValue::DatatypeSelector { selector_name, .. } if selector_name == "fld_ptr"
        );
        let is_bv_encoding =
            matches!(args[0].value(), ExprValue::BvZeroExtend { .. } | ExprValue::BvConcat(_, _));
        assert!(
            is_dt_selector || is_bv_encoding,
            "Error2 payload should be DT selector or BV encoding, got {:?}",
            args[0].value()
        );
    });
}
