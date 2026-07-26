// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SIMD intrinsic MIR-driven tests.
//!
//! These tests exercise `statement/intrinsics/simd.rs` through real MIR bodies
//! and direct `StatementCodegen` calls.
//!
//! Decomposed from a single 1,823-line file into per-family modules.
//! Part of #3759: SIMD test decomposition.
//!
//! Submodules:
//! - `handler_bitwise_shift`: bitwise and shift handlers plus guard paths
//! - `handler_arithmetic`: arithmetic handlers and signed arithmetic variants
//! - `handler_comparison`: comparison handlers and unsigned comparison branches
//! - `handler_reductions`: reduction handlers and signed reduction branches
//! - `handler_lane_ops`: shuffle/cast/extract/insert handlers and guard paths
//! - `layout_helpers`: SIMD layout/extract/reconstruct helper coverage
//! - `dispatch_routes`: `dispatch_simd()` routing and guard behavior

use super::*;

mod dispatch_routes;
mod handler_arithmetic;
mod handler_bitwise_shift;
mod handler_comparison;
mod handler_lane_ops;
mod handler_reductions;
mod layout_helpers;

const SIMD_PROBE_SOURCE: &str = r#"
#![allow(dead_code, unused_variables)]

#[derive(Clone, Copy)]
pub struct U32x4([u32; 4]);

#[derive(Clone, Copy)]
pub struct I32x4([i32; 4]);

#[derive(Clone, Copy)]
pub struct U8x4([u8; 4]);

#[derive(Clone, Copy)]
pub struct U16x4([u16; 4]);

#[derive(Clone, Copy)]
pub struct I8x4([i8; 4]);

#[derive(Clone, Copy)]
pub struct I16x4([i16; 4]);

#[derive(Clone, Copy)]
pub struct U32x2(pub u32, pub u32);

#[derive(Clone, Copy)]
pub struct Mixedx2(pub u32, pub u16);

pub fn bitwise_probe(a: U32x4, b: U32x4) -> U32x4 { a }
pub fn shift_probe(a: I32x4, b: I32x4) -> I32x4 { a }
pub fn arith_probe(a: U32x4, b: U32x4) -> U32x4 { a }
pub fn signed_arith_probe(a: I32x4, b: I32x4) -> I32x4 { a }
pub fn cmp_probe(a: I32x4, b: I32x4) -> I32x4 { a }
pub fn unsigned_cmp_probe(a: U32x4, b: U32x4) -> U32x4 { a }
pub fn reduce_probe(a: U32x4) -> u32 { 0 }
pub fn signed_reduce_probe(a: I32x4) -> i32 { 0 }
pub fn reduce_bool_probe(a: U32x4) -> bool { false }
pub fn shuffle_probe(a: U32x4, b: U32x4, idx: U32x4) -> U32x4 { a }
pub fn cast_probe(a: U8x4) -> U16x4 { U16x4([0, 0, 0, 0]) }
pub fn cast_narrow_probe(a: U16x4) -> U8x4 { U8x4([0, 0, 0, 0]) }
pub fn cast_signed_widen_probe(a: I8x4) -> I16x4 { I16x4([0, 0, 0, 0]) }
pub fn extract_probe(a: U32x4, idx: u32) -> u32 { idx }
pub fn insert_probe(a: U32x4, idx: u32, value: u32) -> U32x4 { a }
pub fn multifield_probe(v: U32x2) -> U32x2 { v }
pub fn mixed_multifield_probe(v: Mixedx2) -> Mixedx2 { v }
"#;

fn seed_arg_locals(codegen: &mut StatementCodegen<'_, '_, '_>, body: &rustc_public::mir::Body) {
    for (idx, local_decl) in body.arg_locals().iter().enumerate() {
        let local_idx = idx + 1;
        let place = Place { local: Local::from(local_idx), projection: vec![] };
        let base = codegen.ssa_base_name(&place);
        if let Some(sort) = StatementCodegen::infer_sort_from_ty(local_decl.ty) {
            codegen.env_update(base, Expr::var(format!("simd_arg_{local_idx}"), sort));
        }
    }
}

fn return_dest_place() -> Place {
    Place { local: Local::from(0usize), projection: vec![] }
}

fn assigned_expr_for_place(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    place: &Place,
) -> Option<Expr> {
    let base = codegen.ssa_base_name(place);
    codegen.env_lookup(&base).cloned()
}

fn constraint_count(codegen: &StatementCodegen<'_, '_, '_>) -> usize {
    codegen.ctx.bmc_vc.constraints.len()
}

fn latest_constraint_text(codegen: &StatementCodegen<'_, '_, '_>) -> String {
    codegen
        .ctx
        .bmc_vc
        .constraints
        .last()
        .expect("expected an emitted assignment constraint")
        .to_string()
}
