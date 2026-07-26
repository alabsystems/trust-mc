// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! MIR Statement and Terminator to AY Constraint Translation.
//!
//! This module translates MIR statements and terminators into AY SMT constraints
//! using SSA form with assertions/assumptions.

// Shared imports used by types defined in this module scope.
use crate::codegen_ay::types::CtorFieldExt;
use ay_bindings::SortInner;
use rustc_public::mir::BasicBlockIdx;

// Re-exports for submodules that use `use super::*;`.
// Previously these were in scope via include!() chains; now they must be
// explicitly re-exported so that `use super::*;` continues to work.
// Part of #2595: include!() to proper module migration.
pub(super) use crate::codegen_ay::context::AYCtx;
pub(super) use crate::kani_middle::abi::LayoutOf;
pub(super) use ay_bindings::{Expr, Sort};
pub(super) use rustc_public::CrateDef;
pub(super) use rustc_public::mir::alloc::GlobalAlloc;
pub(super) use rustc_public::mir::{
    AssertMessage, BinOp, CastKind, ConstOperand, Operand, Place, PointerCoercion, ProjectionElem,
    Rvalue, SwitchTargets, Terminator, TerminatorKind,
};
pub(super) use rustc_public::ty::{
    Allocation, ConstantKind, MirConst, RigidTy, TyConstKind, TyKind,
};
pub(super) use rustc_public_bridge::IndexedVal;

mod aggregate;
mod aggregate_adt;
mod aggregate_struct;
mod alloc;
mod alloc_layout;
mod alloc_posix_memalign;
mod alloc_ptr;
mod alloc_ptr_ext;
mod alloc_sysconf;
mod arithmetic;
mod arithmetic_atomic;
mod arithmetic_checks;
mod arithmetic_overflow;
mod cast;
mod cast_dt_to_bv;
mod cast_dt_to_dt;
mod cast_transmute;
mod cast_unsize;
mod memory_swap;
// Codegen modules (converted from include!() per #2595).
mod codegen_assign;
mod codegen_assign_flatten;
mod codegen_assign_helpers;
mod codegen_assign_ptr;
mod codegen_assign_ref;
mod codegen_assign_ref_deref;
mod codegen_assign_slice_cast;
mod codegen_copy;
mod codegen_kani_call;
mod codegen_kani_iter;
mod codegen_place_value;
mod codegen_prelude;
mod codegen_sort;
mod codegen_statement;
mod codegen_write_bytes;
mod comparison;
mod comparison_eq;
mod datatype;
mod datatype_deref_write;
mod dispatch;
// NOTE: INTERNAL_WORKAROUND_COUNT is available via dispatch module for telemetry
// within this crate. Not re-exported to avoid unused import warnings.
mod collections;
mod env;
mod intrinsics;
mod iter;
mod kani;
mod kani_float;
mod kani_shadow_mem;
mod operand;
mod operand_ref;
mod operand_scalar;
mod operand_scalar_enum;
mod operand_scalar_enum_multi;
mod option;
mod option_compound;
mod option_helpers;
mod panic_helpers;
mod place;
mod place_deref;
mod place_deref_first;
mod place_pointee;
mod place_post_deref;
mod place_projection;
mod result;
mod result_combinators;
mod result_helpers;
mod rvalue;
mod rvalue_address_of;
mod rvalue_binop;
mod rvalue_discriminant;
mod slice;
mod sort_inference;
mod sort_inference_adt;
mod ssa;
mod terminator;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod tests;

// Re-export StatementCodegen from codegen_prelude for crate-level access.
pub(in crate::codegen_ay) use codegen_prelude::StatementCodegen;
pub(in crate::codegen_ay) use codegen_prelude::{AdapterStage, AdapterStageKind};

// Re-export iterator unsoundness counter accessor (#1929)
pub(in crate::codegen_ay) use collections::get_bmc_iterator_unsound_skip_count;
pub(in crate::codegen_ay) use operand::take_constant_zero_fallback_count;

// Re-export Vec field fallback counter for metadata pipeline (#2733)
pub(in crate::codegen_ay) use collections::take_vec_field_fallback_counter;

// Re-export dispatch counters for metadata pipeline (#2597 Phase 3)
pub(in crate::codegen_ay) use dispatch::take_abstracted_fallback_count;
pub(in crate::codegen_ay) use dispatch::take_internal_workaround_count;

// Re-export pointee synthesis fallback counter for metadata pipeline (#3013)
pub(in crate::codegen_ay) use place_pointee::take_pointee_synthesis_fallback_count;

// Non-destructive read accessors for per-harness snapshot deltas (Part of #3080)
pub(in crate::codegen_ay) use collections::get_vec_field_fallback_count;
pub(in crate::codegen_ay) use dispatch::get_abstracted_fallback_count;
pub(in crate::codegen_ay) use dispatch::get_internal_workaround_count;
pub(in crate::codegen_ay) use env::get_sort_harmonize_fresh_var_count;
pub(in crate::codegen_ay) use env::take_sort_harmonize_fresh_var_count;
pub(in crate::codegen_ay) use operand::get_constant_zero_fallback_count;
pub(in crate::codegen_ay) use place_pointee::get_pointee_synthesis_fallback_count;

#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use collections::set_vec_field_fallback_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use dispatch::set_abstracted_fallback_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use dispatch::set_internal_workaround_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use env::set_sort_harmonize_fresh_var_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use operand::set_constant_zero_fallback_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use place_pointee::set_pointee_synthesis_fallback_count_for_test;

// Re-export TupleUsageAnalysis for tests (was in include!() scope before #2595).
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(super) use crate::kani_middle::tuple_usage::TupleUsageAnalysis;

// IntoOption trait and telemetry moved to codegen_ay::shared (#2881).
// Re-export for submodule access via `super::IntoOption`.
pub(super) use crate::codegen_ay::shared::IntoOption;
use crate::codegen_ay::shared::take_into_option_dropped_count;

/// Result of codegen for a terminator that may have multiple successors.
/// Each entry is (target_block, path_condition) where path_condition is Some
/// if we need to assume a condition to reach that block.
pub(super) type TerminatorSuccessors = Vec<(BasicBlockIdx, Option<Expr>)>;

/// Extract metadata field from a fat pointer datatype expression.
///
/// Fat pointers (slices, str refs, dyn trait refs) are encoded as datatypes
/// with named metadata fields.
/// - Data pointer: `"fld_ptr"` (or legacy `"fld_data"`/`"ptr"` in some sorts)
/// - Metadata: `"fld_len"` for slices, `"fld_vtable"` for trait objects, or `"fld_meta"` generic
///
/// Additional payload fields (for example slice `fld_data` array backing) may
/// be present; metadata extraction is name-based, not positional.
///
/// Returns the metadata field expression if the expr is a datatype with
/// a recognized metadata field name, None otherwise.
pub(super) fn extract_fat_ptr_metadata(expr: &Expr) -> Option<Expr> {
    if let SortInner::Datatype(dt) = expr.sort().inner()
        && let Some(cons) = dt.constructors.first()
        && let Some(field) = cons
            .field("fld_len")
            .or_else(|| cons.field("fld_vtable"))
            .or_else(|| cons.field("fld_meta"))
    {
        return Some(expr.clone().field_select(&*dt.name, &*field.name, field.sort.clone()));
    }
    None
}

pub(super) type Env = std::collections::BTreeMap<std::sync::Arc<str>, Expr>;

#[derive(Clone)]
pub(super) struct IncomingEdge {
    pub(super) edge_predicate: Option<Expr>,
    pub(super) env: Env,
    /// SwitchInt→variant bridge (Effort 2, #3017): variant facts that hold on this
    /// edge — snapshotted from `current_variant_facts` plus the switch's per-branch
    /// fact. Merged by INTERSECTION at the target block's entry.
    pub(super) variant_facts: Vec<VariantFact>,
}

/// SwitchInt→variant bridge (Effort 2, #3017): a path-scoped fact that the storage
/// identified by `place_key` (a version-INDEPENDENT canonical key) is provably
/// constructor `ctor_idx` (`ctor_name`) of datatype `dt_name`, established by a
/// `Discriminant`+`SwitchInt` on the current path. `guard` is the branch condition
/// under which the fact was established (defense-in-depth: the asserted
/// `is_constructor` is guarded by it, so it is vacuous on any model where the
/// establishing branch was not taken).
#[derive(Clone)]
pub(super) struct VariantFact {
    pub(super) place_key: std::sync::Arc<str>,
    pub(super) dt_name: std::sync::Arc<str>,
    pub(super) ctor_idx: usize,
    pub(super) ctor_name: std::sync::Arc<str>,
    pub(super) guard: Expr,
}

/// SwitchInt→variant bridge (Effort 2, #3017): the datatype-enum scrutinee of a
/// `Rvalue::Discriminant(P)` assigned to a bare local. Recorded ONLY when P resolves
/// to a multi-variant DATATYPE enum (never the symbolic/bitvec/unit fallbacks, which
/// carry no datatype term). Consumed at the `SwitchInt` on that local to emit a
/// per-branch `VariantFact`. `ctor_names` are the AY datatype constructor names in
/// MIR variant order (constructor index == variant index).
#[derive(Clone)]
pub(super) struct DiscrScrutinee {
    pub(super) place_key: std::sync::Arc<str>,
    pub(super) dt_name: std::sync::Arc<str>,
    pub(super) ctor_names: Vec<std::sync::Arc<str>>,
    pub(super) adt_def: rustc_public::ty::AdtDef,
}

/// Reset all statement-level diagnostic and name-generator counters to zero (Part of #2360).
pub(in crate::codegen_ay) fn reset_statement_session_counters() {
    take_into_option_dropped_count();
    dispatch::take_internal_workaround_count();
    dispatch::take_abstracted_fallback_count();
    collections::take_bmc_iterator_unsound_skip_count();
    collections::take_vec_field_fallback_counter();
    place_pointee::take_pointee_synthesis_fallback_count();
    env::take_bigint_convert_counter();
    operand::take_constant_zero_fallback_count();
}
