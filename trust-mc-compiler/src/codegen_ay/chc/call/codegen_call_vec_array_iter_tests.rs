// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for ZST payload canonicalization in array iterator lowering.

#![allow(clippy::panic)]

use super::codegen_call_vec_array_iter::canonical_zst_option_payload_for_local;
use crate::codegen_ay::chc::{ChcConfig, ChcCtx};
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use ay_bindings::{ExprValue, Sort};

const OPTION_PAYLOAD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Marker;

    pub fn probe_option_unit() -> Option<()> {
        Some(())
    }

    pub fn probe_option_bool() -> Option<bool> {
        Some(true)
    }

    pub fn probe_option_marker() -> Option<Marker> {
        Some(Marker)
    }
"#;

fn with_payload_ctx(fn_name: &'static str, test: impl FnOnce(&ChcCtx<'_, '_>) + Send) {
    with_test_ay_ctx_for_source(OPTION_PAYLOAD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        test(&chc_ctx);
    });
}

#[test]
fn test_canonical_zst_option_payload_for_unit_option() {
    with_payload_ctx("probe_option_unit", |ctx| {
        let payload = canonical_zst_option_payload_for_local(ctx, 0, &Sort::bool())
            .expect("Option<()> payload should canonicalize");
        assert!(
            matches!(payload.value(), ExprValue::BoolConst(true)),
            "unit payload should canonicalize to true, got {payload:?}"
        );
    });
}

#[test]
fn test_canonical_zst_option_payload_does_not_collapse_option_bool() {
    with_payload_ctx("probe_option_bool", |ctx| {
        assert!(
            canonical_zst_option_payload_for_local(ctx, 0, &Sort::bool()).is_none(),
            "Option<bool> must keep iterator data, not canonicalize as a ZST"
        );
    });
}

#[test]
fn test_canonical_zst_option_payload_for_fieldless_struct_option() {
    with_payload_ctx("probe_option_marker", |ctx| {
        let payload = canonical_zst_option_payload_for_local(ctx, 0, &Sort::bool())
            .expect("Option<Marker> payload should canonicalize");
        assert!(
            matches!(payload.value(), ExprValue::BoolConst(false)),
            "fieldless struct payload should use its canonical ZST value, got {payload:?}"
        );
    });
}
