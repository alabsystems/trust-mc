// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Collection stub operation tests.
//!
//! Decomposed from a single 6,421-line file into per-collection modules.
//! Part of #2167: test file decomposition.
//!
//! Submodules:
//! - `vec`: Vec stub + MIR-driven + real-operand tests
//! - `string`: String stub + MIR-driven + real-operand tests
//! - `hashmap`: HashMap stub + MIR helper + MIR-driven + real-operand tests
//! - `hashset`: HashSet stub + gap + real-operand tests
//! - `btreeset`: BTreeSet stub + gap + real-operand tests
//! - `btreemap`: BTreeMap internal stub + CRUD real-operand tests
//! - `bigint`: BigInt stub + MIR-driven + gap + real-operand tests
//! - `iter`: Iterator expression + adapter stub tests
//! - `vec_mir`: Vec MIR-driven codegen stub tests
//
// Originally extracted from regression.rs per #1734.

mod bigint;
mod bigint_shift;
mod btreemap;
mod btreeset;
mod hashmap;
mod hashmap_helpers;
mod hashmap_iter;
mod hashset;
mod iter;
mod iter_collection_next;
mod iter_flatten;
mod set_common;
mod string;
mod string_convert;
mod string_utf8;
mod vec;
mod vec_mir;
mod vec_view;

// Re-export shared imports for submodules
pub(super) use super::*;

// MIR-driven test shared items — used by per-collection MIR test sections.
pub(super) use crate::codegen_ay::statement::TupleUsageAnalysis;

pub(super) const COLLECTIONS_PROBE_SOURCE: &str = r#"
pub fn probe_u32(x: u32) -> u32 { x }
pub fn probe_u32_binary(x: u32, _y: u32) -> u32 { x }
pub fn probe_u32_multi(a: u32, _b: u32, _c: u32, _d: u32, _e: u32) -> u32 { a }
"#;

pub(super) fn seed_collections_local(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    local_idx: usize,
    value: ay_bindings::Expr,
) -> Operand {
    let fn_name =
        codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
    let base_name = format!("{}::local_{}", fn_name, local_idx);
    codegen.env_update(base_name, value);
    Operand::Copy(Place { local: local_idx, projection: vec![] })
}
