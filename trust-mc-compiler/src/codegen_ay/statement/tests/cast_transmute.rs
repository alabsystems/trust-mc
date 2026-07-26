// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for BMC transmute layout guards.
//!
//! Part of #3809: verify that layout-sensitive cross-ADT transmutes fail closed,
//! while same-struct, repr(C), and single-field wrapper transmutes still pass.

use super::*;
use rustc_public::mir::CastKind;

const TRANSMUTE_PROBE_SOURCE: &str = r#"
use std::mem;

#[repr(C)]
pub struct ReprCPair {
    pub x: u32,
    pub y: u32,
}

#[repr(C)]
pub struct ReprCOther {
    pub a: u32,
    pub b: u32,
}

pub struct DefaultPair {
    pub x: u32,
    pub y: u64,
}

pub struct DefaultOther {
    pub a: u64,
    pub b: u32,
}

#[repr(transparent)]
pub struct Wrapper(pub u64);

pub fn reprc_to_reprc(s: ReprCPair) -> ReprCOther {
    unsafe { mem::transmute(s) }
}

pub fn default_to_default(s: DefaultPair) -> DefaultOther {
    unsafe { mem::transmute(s) }
}

pub fn wrapper_to_u64(w: Wrapper) -> u64 {
    unsafe { mem::transmute(w) }
}
"#;

fn find_first_transmute_cast(
    body: &rustc_public::mir::Body,
) -> Option<(Operand, rustc_public::ty::Ty)> {
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(_, Rvalue::Cast(CastKind::Transmute, operand, target_ty)) =
                &stmt.kind
            {
                return Some((operand.clone(), *target_ty));
            }
        }
    }
    None
}

fn exercise_codegen_transmute(ctx: &mut AYCtx<'_, 'static>, fn_name: &str) -> Option<Expr> {
    let instance = find_instance_by_suffix(ctx, fn_name);
    let body = instance.body().expect("function body");
    ctx.set_current_fn(instance);
    let tuple_usage = TupleUsageAnalysis::run(&body);
    let mut codegen = StatementCodegen::new(ctx, &body, tuple_usage);

    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let local = Local::from(local_idx);
        let place = Place { local, projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("arg_{local_idx}"), sort));
        }
    }

    let (operand, target_ty) = find_first_transmute_cast(&body)
        .unwrap_or_else(|| panic!("no CastKind::Transmute found in {fn_name}"));
    codegen.codegen_cast_with_kind(&CastKind::Transmute, &operand, target_ty)
}

#[test]
fn test_transmute_default_layout_cross_adt_blocked_and_records_unsupported() {
    with_test_ay_ctx_for_source(TRANSMUTE_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_transmute(&mut ctx, "default_to_default");
        assert!(
            result.is_none(),
            "layout-sensitive cross-ADT transmute should fail closed, got {:?}",
            result
        );
        let cast_entries = ctx
            .unsupported_constructs
            .get("Cast")
            .expect("blocked transmute should record unsupported Cast details");
        assert!(
            cast_entries.iter().any(|detail| detail.contains("transmute layout-sensitive")),
            "blocked transmute should record layout-sensitive detail, got {cast_entries:?}"
        );
    });
}

#[test]
fn test_transmute_reprc_cross_adt_allowed_without_cast_unsupported() {
    with_test_ay_ctx_for_source(TRANSMUTE_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_transmute(&mut ctx, "reprc_to_reprc")
            .expect("repr(C) cross-ADT transmute should succeed");
        assert!(
            result.sort().datatype_sort().is_some(),
            "repr(C) cross-ADT transmute should produce a datatype result, got {:?}",
            result.sort()
        );
        assert!(
            !ctx.unsupported_constructs.contains_key("Cast"),
            "repr(C) cross-ADT transmute should not record Cast unsupported entries: {:?}",
            ctx.unsupported_constructs
        );
    });
}

#[test]
fn test_transmute_single_field_wrapper_allowed() {
    with_test_ay_ctx_for_source(TRANSMUTE_PROBE_SOURCE, |mut ctx| {
        let result = exercise_codegen_transmute(&mut ctx, "wrapper_to_u64")
            .expect("single-field wrapper transmute should succeed");
        assert_eq!(
            result.sort().bitvec_width(),
            Some(64),
            "wrapper transmute should lower to the wrapped bv64 payload"
        );
        assert!(
            !ctx.unsupported_constructs.contains_key("Cast"),
            "single-field wrapper transmute should not record Cast unsupported entries: {:?}",
            ctx.unsupported_constructs
        );
    });
}
