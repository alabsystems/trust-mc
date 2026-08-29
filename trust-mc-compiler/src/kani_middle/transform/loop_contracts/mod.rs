// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module contains code related to the MIR-to-MIR pass to enable loop contracts.
//!

mod analysis;
mod rewrite;
mod rule;
pub(crate) use rule::TRANSFORMED_NESTED_LEGACY;
mod smt2;
mod transform;

#[cfg(test)]
mod tests;

use super::TransformPass;
use crate::kani_middle::KaniAttributes;
use crate::kani_middle::codegen_units::CodegenUnit;
use crate::kani_middle::kani_functions::{KaniHook, KaniIntrinsic, KaniModel};
use crate::kani_middle::transform::TransformationType;
use crate::kani_queries::QueryDb;
use lazy_static::lazy_static;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{BasicBlockIdx, Body};
use rustc_public::ty::{FnDef, RigidTy};
use rustc_span::Symbol;
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

// `#[kani::loop_decreases(...)]` (loop-variant / termination clause) lowers to
// an `#[inline(never)]` `kani_register_loop_decreases<id>(&|| <measure>, 0)`
// call. For the SUPPORTED shape (a single contracted loop whose measure is an
// unsigned-integer expression over scalar locals — see
// `instrument_loop_decreases` for the exact guards), this pass now encodes the
// CBMC-style back-edge ranking check: snapshot `old = measure()` where the
// register call sat, and at the (transformed) loop latch emit
// `new = measure(); safety_check(new < old); old = new`, so the strict-decrease
// obligation flows through the normal per-property CHC pipeline and ay proves
// or refutes it. For every UNSUPPORTED shape the register call is left
// untouched and trust-mc degrades conservatively at CHC codegen: because the
// register fn is `#[inline(never)]`, its call survives function inlining, and
// `codegen_ay::codegen_function::codegen_chc_path` detects it (under
// `-Z loop-contracts`) and emits a failing VC (never a false PROOF from
// silently ignoring a stale/increasing measure). The guards also deliberately
// keep Kani-parity on Kani's own `fixme_*` decreases limitations (struct-field
// measures, decreases+loop_modifies, nested contracted loops): Kani reports
// FAILURE there, so trust-mc must not silently out-verify the oracle.

/// Extracted loop invariant information for CHC solver hints.
#[derive(Debug, Clone)]
pub(crate) struct ExtractedLoopInvariant {
    /// The basic block index of the loop head.
    pub(crate) loop_head_bb: BasicBlockIdx,
    /// The basic block index of the new loop latch (if created).
    /// Read in tests; production CHC codegen uses loop_head_bb for relation naming.
    #[allow(dead_code)]
    pub(crate) loop_latch_bb: Option<BasicBlockIdx>,
    /// The CHC-visible loop-head block: the register call's terminator target,
    /// i.e. the block the transformed loop head jumps to and whose relation
    /// PDR actually synthesizes an invariant for. Part of #40: hints
    /// previously named the register-call block's relation (`__bb{register}`),
    /// which never matched a predicate, so every user invariant was silently
    /// skipped. `None` falls back to `loop_head_bb` (used by the lemma-hint
    /// detector, whose header indices are already CHC-visible).
    pub(crate) chc_loop_head_bb: Option<BasicBlockIdx>,
    /// The local variable indices captured by the invariant closure.
    pub(crate) captured_vars: Vec<usize>,
    /// The DefId index of the closure (for resolving the closure body).
    pub(crate) closure_def_index: Option<u32>,
    /// The extracted formula in SMT-LIB2 format (Part of #1562).
    ///
    /// When the closure body can be analyzed and converted to SMT-LIB2,
    /// this contains the formula string (e.g., "(>= x 0)").
    /// When extraction fails (complex closures), this is None.
    pub(crate) formula_smt2: Option<String>,
    /// Per-BB CHC relation argument positions for each captured variable.
    ///
    /// When present, entry `i` gives the argument position of `captured_vars[i]`
    /// in the loop header's CHC relation declaration. This is necessary because
    /// per-BB dead-local elimination and tuple flattening cause MIR local indices
    /// to differ from relation argument positions. Part of #3258.
    pub(crate) captured_rel_arg_positions: Option<Vec<usize>>,
}

lazy_static! {
    /// Global registry for extracted loop invariants, keyed by function name.
    // Part of #2267: Arc<str> keys avoid per-call String allocation from CHC codegen path.
    pub(crate) static ref LOOP_INVARIANT_REGISTRY: RwLock<HashMap<Arc<str>, Vec<ExtractedLoopInvariant>>> =
        RwLock::new(HashMap::new());
}

/// Register extracted loop invariants for a function.
///
/// Called during MIR transformation for `#[kani::loop_invariant(...)]` annotations,
/// and during CHC codegen for auto-detected accumulator patterns (#3258).
/// The invariants are stored in a global registry and retrieved later by
/// `build_loop_hints()` for the VcArtifact → driver PDR pipeline.
///
/// # Panics
/// Panics if the registry lock is poisoned (indicates prior panic during write).
pub(crate) fn register_loop_invariants(
    fn_name: impl Into<Arc<str>>,
    invariants: Vec<ExtractedLoopInvariant>,
) {
    if invariants.is_empty() {
        return;
    }
    let mut registry =
        LOOP_INVARIANT_REGISTRY.write().expect("LOOP_INVARIANT_REGISTRY lock poisoned");
    registry.insert(fn_name.into(), invariants);
}

/// Retrieve loop invariants for a function.
///
/// Returns the loop invariants registered for the given function name,
/// or `None` if no invariants were registered.
///
/// # Panics
/// Panics if the registry lock is poisoned (indicates prior panic during read).
pub(crate) fn get_loop_invariants(fn_name: &str) -> Option<Vec<ExtractedLoopInvariant>> {
    let registry = LOOP_INVARIANT_REGISTRY.read().expect("LOOP_INVARIANT_REGISTRY lock poisoned");
    registry.get(fn_name).cloned()
}

#[derive(Debug, Default, Clone)]
pub(crate) struct LoopContractPass {
    /// Cache KaniRunContract function used to implement contracts.
    run_contract_fn: Option<FnDef>,
    /// The map from original loop head to the new loop latch.
    /// We use this map to redirect all original loop latches to a new single loop latch.
    new_loop_latches: HashMap<usize, usize>,
    /// Extracted loop invariants for this transformation.
    extracted_invariants: Vec<ExtractedLoopInvariant>,
    /// Safety-check (assert+assume) hook used to emit the `decreases` ranking
    /// obligation at the loop latch. `None` when the unit has no harnesses;
    /// decreases instrumentation is then skipped (fail-closed at CHC codegen).
    safety_check_type: Option<super::body::CheckType>,
    /// Safety-check WITHOUT the assume half, used for the loop-invariant
    /// base/step obligations (#47). Those two sit on the loop-entry /
    /// post-iteration edge with a `SwitchInt(_v)` immediately after, so the
    /// `¬inv` continuation is already cut structurally (it goes to the
    /// `assume(false)` sink). Emitting the assume half as well would add an
    /// ordered `assume(inv)` to every contracted loop for no semantic gain —
    /// measured cost on `memchar_naive`: 54s (over its retry budget) with the
    /// assume, well inside it without.
    safety_check_no_assume_type: Option<super::body::CheckType>,
    /// `kani::assume` (AssumeHook) — used by the loop-contract proof rule for
    /// `assume(inv)` on the havocked state and the back-edge cut (#47).
    assume_fn: Option<FnDef>,
    /// `kani::internal::any_modifies::<T>` (AnyModifiesIntrinsic) — the havoc
    /// primitive for loop-modified locals (#47). No trait bounds, so it
    /// resolves for any sized `T`; codegen lowers it to a nondet destination.
    any_modifies_fn: Option<FnDef>,
    /// Decreases interplay (#47): the `(old_snapshot_local, source_local)`
    /// pairs recorded by `instrument_loop_decreases` so the proof rule can
    /// re-snapshot them after the havoc (the ranking check must compare
    /// within the symbolic iteration, not against the concrete entry state).
    ///
    /// One pair for an identity measure (`x`); one pair PER COMPONENT for a
    /// compound measure (`hi - lo` snapshots `hi` and `lo` separately). The
    /// components are snapshotted rather than the difference on purpose: a
    /// havocked state can make `hi < lo`, and snapshotting the difference
    /// would wrap it to a huge value, letting `new < old` hold spuriously —
    /// a fabricated termination proof. Recomputing the difference from
    /// freshly-snapshotted components keeps the underflow guard meaningful.
    decreases_snapshot: Option<Vec<(usize, usize)>>,
}

impl TransformPass for LoopContractPass {
    /// The type of transformation that this pass implements.
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        TransformationType::Stubbing
    }

    fn is_enabled(&self, query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        query_db.args().unstable_features.iter().any(|f| f == "loop-contracts")
    }

    fn transform(&mut self, tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        self.new_loop_latches = HashMap::new();
        self.extracted_invariants = Vec::new();
        self.decreases_snapshot = None;
        let result = match instance.ty().kind().rigid().expect("instance type should be rigid") {
            RigidTy::FnDef(_func, args) => {
                if KaniAttributes::for_instance(tcx, instance).fn_marker()
                    == Some(Symbol::intern("kani_register_loop_contract"))
                {
                    let run_contract_fn =
                        self.run_contract_fn.expect("run_contract_fn should be set");
                    let run = Instance::resolve(run_contract_fn, args)
                        .expect("failed to resolve run_contract_fn");
                    (true, run.body().expect("run_contract_fn should have a body"))
                } else {
                    self.transform_body_with_loop(tcx, body)
                }
            }
            RigidTy::Closure(_, _) => self.transform_body_with_loop(tcx, body),
            _ => {
                // external enum: RigidTy
                /* static variables case */
                (false, body)
            }
        };

        // Register extracted loop invariants for CHC solver hints.
        if !self.extracted_invariants.is_empty() {
            let fn_name = instance.name();
            register_loop_invariants(fn_name, std::mem::take(&mut self.extracted_invariants));
        }

        result
    }
}

impl LoopContractPass {
    pub(crate) fn new(_tcx: TyCtxt, queries: &QueryDb, unit: &CodegenUnit) -> LoopContractPass {
        if !unit.harnesses.is_empty() {
            let kani_fns = queries.kani_functions();
            let run_contract_fn = kani_fns.get(&KaniModel::RunLoopContract.into()).copied();
            assert!(run_contract_fn.is_some(), "Failed to find trust_mc run contract function");
            LoopContractPass {
                run_contract_fn,
                new_loop_latches: HashMap::new(),
                extracted_invariants: Vec::new(),
                safety_check_type: Some(super::body::CheckType::new_safety_check_assert_assume(
                    queries,
                )),
                safety_check_no_assume_type: Some(
                    super::body::CheckType::new_safety_check_assert_no_assume(queries),
                ),
                assume_fn: kani_fns.get(&KaniHook::Assume.into()).copied(),
                any_modifies_fn: kani_fns.get(&KaniIntrinsic::AnyModifies.into()).copied(),
                decreases_snapshot: None,
            }
        } else {
            LoopContractPass::default()
        }
    }
}
