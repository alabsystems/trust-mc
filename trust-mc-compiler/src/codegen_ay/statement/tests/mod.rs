// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for MIR statement/terminator codegen.
//!
//! This module organizes tests by category:
//! - `basic`: Core codegen tests (binop, overflow, coercion, bitwise, comparisons)
//! - `place`: Place projection and field selection helpers
//! - `assign`: Assignment-level expression helpers
//! - `env`: Phi merge + sort conversion helpers
//! - `coercion`: Coercion edge cases and array/slice handling
//! - `bit_intrinsics`: Bit manipulation intrinsic expression tests
//! - `sort_stubs`: Collection stub sort inference
//! - `arithmetic`: Overflow/shift/wrapping/checked/saturating/overflowing patterns
//! - `atomic`: Atomic intrinsic codegen (load, store, exchange, cxchg, fetch_binop, nand, minmax)
//! - `collections`: Vec/String/BTreeSet/HashSet stub patterns
//! - `alloc_layout`: Allocation, layout, and NonNull helpers
//! - `datatype`: Sort-construction helpers (slice_sort, dyn_sort, tuple_sort_name)
//! - `btreemap`: Prefix scan performance verification
//! - `cast`: Cast expression patterns + MIR-driven codegen_cast tests
//! - `kani_call`: Kani intrinsic dispatch (any, assume, assert, iterators)
//! - `kani_intrinsics`: Kani intrinsic implementations (any_raw, enum constraints, value_view)
//! - `copy`: Copy/copy_nonoverlapping/write_bytes intrinsic patterns
//! - `rvalue`: Rvalue translation (Cmp, Offset, unchecked ops, discriminant)
//! - `operand`: Operand translation (constant extraction, scalar masking, Layout/enum ADTs)
//! - `slice`: Slice/wide pointer type utilities and codegen stubs
//! - `terminator`: Terminator translation (SwitchInt, Assert, Goto, Return)
//! - `math_intrinsics`: Math intrinsic constant extraction/folding tests
//! - `memory_intrinsics`: Memory intrinsic MIR-driven tests (size_of_val, align_of_val)
//! - `simd_intrinsics`: SIMD intrinsic codegen tests
//! - `iter_codegen`: Iterator codegen (IndexRange, PolymorphicIter, step_unchecked)
//! - `codegen_sort`: Width coercion, tuple unwrap, sort inference, checked binary ops
//! - `codegen_place_value`: Value/reference assignment, deref resolution, Box pointee
//! - `codegen_prelude`: StatementCodegen init, reference argument setup, IntoOption
//!
//! Split from a single 4218-line file per #1734.

// Test code: panic/unwrap acceptable for assertions
#![allow(clippy::panic, clippy::unwrap_used)]

mod aggregate;
mod aggregate_adt;
mod aggregate_struct;
mod alloc;
mod alloc_layout;
mod alloc_ptr;
mod arithmetic;
mod arithmetic_checks;
mod assign;
mod atomic;
mod basic;
mod bit_intrinsics;
mod bit_intrinsics_ctpop;
mod btreemap;
mod cast;
mod cast_transmute;
mod codegen_assign_advanced;
mod codegen_assign_flatten;
mod codegen_assign_helpers;
mod codegen_assign_mir;
mod codegen_assign_ptr;
mod codegen_assign_ref;
mod codegen_place_value;
mod codegen_prelude;
mod codegen_sort;
mod codegen_statement_dispatch;
mod coercion;
mod collections;
mod comparison;
mod comparison_array;
mod comparison_raw_pointers;
mod copy;
mod datatype;
mod dispatch;
mod dispatch_helpers;
mod dispatch_internal_precheck;
mod dispatch_simple;
mod env;
mod iter_codegen;
mod kani_call;
mod kani_intrinsics;
mod kani_iter;
mod math_intrinsics;
mod memory_intrinsics;
mod operand;
mod option;
mod option_helpers;
mod place;
mod place_deref;
mod place_deref_first;
mod place_pointee;
mod place_post_deref;
mod place_projection;
mod result;
mod rvalue;
mod rvalue_address_of;
mod rvalue_binop;
mod rvalue_discriminant;
mod shadow_mem;
mod simd_intrinsics;
mod slice;
mod slice_cast_materialization;
mod sort_harmonize_counter;
mod sort_inference;
mod sort_inference_adt;
mod sort_stubs;
mod ssa;
mod stub_dispatch_memory;
mod stub_dispatch_option_result;
mod stub_dispatch_simple;
mod terminator;
mod test_ssa_algorithm;

/// Serializes access to BMC_ITERATOR_UNSOUND_SKIP_COUNT across tests.
///
/// Any test that reads or drains the global `BMC_ITERATOR_UNSOUND_SKIP_COUNT`
/// atomic counter must hold this lock to prevent concurrent threads from
/// draining/incrementing between before/after reads. This includes:
/// - The 6 skip-path tests in `collections::iter` (read via `get_*`)
/// - `test_reset_statement_session_counters_*` in `operand` (drains via `take_*`)
///
/// Fix #2500: Originally in `collections::iter` only; promoted here so that
/// `operand::test_reset_statement_session_counters` also serializes.
pub(super) static SKIP_COUNTER_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

// Re-export shared imports for submodules
pub(super) use super::*;
pub(super) use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::emitter::emit_bmc;
pub(super) use crate::codegen_ay::names::{enum_sort, struct_sort};
pub(super) use crate::codegen_ay::test_fixtures::{point_expr, point_sort, vec_expr, vec_sort};
pub(super) use crate::codegen_ay::types::POINTER_WIDTH;
pub(super) use ay_bindings::Constraint;
pub(super) use ay_bindings::expr::ExprValue;
pub(super) use num_bigint::BigInt;
pub(super) use rustc_public::mir::mono::Instance;
pub(super) use rustc_public::mir::{
    AggregateKind, BinOp, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind, UnOp,
};
pub(super) use rustc_public::rustc_internal;
pub(super) use rustc_public::ty::{RigidTy, TyKind};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;
use trust_mc_core::{PropertyId, PropertyKind, Violation};

/// Shared helper: construct a `Place` for a local variable by index.
///
/// Consolidates 3 identical per-file copies (dispatch_helpers, alloc_layout, ssa).
pub(super) fn local_place(local_idx: usize) -> Place {
    Place { local: Local::from(local_idx), projection: vec![] }
}

/// Shared helper: construct a copy `Operand` for a local variable by index.
///
/// Consolidates 3 identical per-file copies (alloc_layout, ssa, simd_intrinsics).
pub(super) fn local_operand(local_idx: usize) -> Operand {
    Operand::Copy(local_place(local_idx))
}

/// Shared helper: find a function Instance by name suffix in the current crate.
///
/// Thin wrapper around `test_fixtures::find_instance_by_suffix(tcx, suffix)`
/// for callers that have a `AYCtx` instead of `TyCtxt`.
pub(super) fn find_instance_by_suffix(
    ctx: &crate::codegen_ay::context::AYCtx<'_, '_>,
    suffix: &str,
) -> Instance {
    crate::codegen_ay::test_fixtures::find_instance_by_suffix(ctx.tcx, suffix)
}

/// Extract the RHS expression from the SSA-defining assertion for a given
/// destination variable.
///
/// `assert_ssa_def` emits `Assert { expr: Eq(dest_var, computed_value) }`.
/// This function finds that assertion and returns the `computed_value` (the
/// RHS of the Eq). Handles both `Eq(dest, rhs)` and `Eq(rhs, dest)` since
/// equality is symmetric.
///
/// Consolidates 3 identical per-file copies (arithmetic, comparison, result).
pub(super) fn extract_ssa_rhs(commands: &[Constraint], dest_expr: &Expr) -> Option<Expr> {
    for cmd in commands {
        if let Constraint::Assert { expr, .. } = cmd
            && let ExprValue::Eq(lhs, rhs) = expr.value()
        {
            if lhs == dest_expr {
                return Some(rhs.clone());
            }
            if rhs == dest_expr {
                return Some(lhs.clone());
            }
        }
    }
    None
}

const AY_TEST_TIMEOUT_SECS: u64 = 5;

fn ay_test_timeout_secs_or(default_secs: u64) -> u64 {
    std::env::var("TRUST_MC_AY_TEST_TIMEOUT_SECS")
        .or_else(|_| std::env::var("TRUST_MC_Z3_TEST_TIMEOUT_SECS"))
        .ok()
        .and_then(|value| value.parse::<u64>().ok())
        .unwrap_or(default_secs)
}

fn run_ay_on_smt2_with_timeout(smt: &str, timeout_secs: u64) -> Result<String, String> {
    let commands = ay_frontend::parse(smt).map_err(|err| format!("AY parse failed: {err}"))?;
    let mut executor = ay_dpll::Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));

    let timeout = Duration::from_secs(timeout_secs);
    let (cancel_tx, cancel_rx) = std::sync::mpsc::channel();
    let timer_interrupt = Arc::clone(&interrupt);
    let timer = std::thread::spawn(move || {
        if cancel_rx.recv_timeout(timeout).is_err() {
            timer_interrupt.store(true, Ordering::Relaxed);
        }
    });

    let outputs =
        executor.execute_all(&commands).map_err(|err| format!("AY execution failed: {err}"));
    let timed_out = interrupt.load(Ordering::Relaxed);
    let _ = cancel_tx.send(());
    let _ = timer.join();
    if timed_out {
        return Err(format!(
            "AY timed out after {timeout_secs}s (set TRUST_MC_AY_TEST_TIMEOUT_SECS to increase)"
        ));
    }

    for output in outputs? {
        let result = output.trim();
        if matches!(result, "sat" | "unsat" | "unknown") {
            return Ok(result.to_string());
        }
    }

    Err("AY returned no sat/unsat/unknown verdict".to_string())
}

pub(super) fn assert_unsat_for_violation(
    ctx: &crate::codegen_ay::context::AYCtx<'_, 'static>,
    violation_expr: Expr,
    smt_var_prefix: &str,
    proof_name: &str,
) {
    let mut vc = ctx.bmc_vc.clone();
    vc.violations.clear();
    vc.model_queries.clear();
    vc.add_violation(
        Violation::new(PropertyId::new(0), PropertyKind::Assertion, violation_expr)
            .with_smt_var(format!("{smt_var_prefix}_{proof_name}")),
    );

    let smt = emit_bmc(vc).to_string();
    let timeout_secs = ay_test_timeout_secs_or(AY_TEST_TIMEOUT_SECS);
    match run_ay_on_smt2_with_timeout(&smt, timeout_secs) {
        Ok(result) => {
            assert_eq!(result, "unsat", "{proof_name}: expected UNSAT, got {result}. SMT:\n{smt}");
        }
        Err(err) => panic!("{proof_name}: AY execution failed: {err}. SMT:\n{smt}"),
    }
}
