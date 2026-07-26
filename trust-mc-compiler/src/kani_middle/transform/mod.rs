// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! This module is responsible for optimizing and instrumenting function bodies.
//!
//! We make transformations on bodies already monomorphized, which allow us to make stronger
//! decisions based on the instance types and constants.
//!
//! The main downside is that some transformation that don't depend on the specialized type may be
//! applied multiple times, one per specialization.
//!
//! Another downside is that these modifications cannot be applied to concrete playback, since they
//! are applied on the top of rustc_public body, which cannot be propagated back to rustc's backend.
//!
//! # Warn
//!
//! For all instrumentation passes, always use exhaustive matches to ensure soundness in case a new
//! case is added.
use crate::kani_middle::codegen_units::CodegenUnit;
use crate::kani_middle::reachability::CallGraph;
use crate::kani_middle::transform::body::CheckType;
use crate::kani_middle::transform::check_uninit::{DelayedUbPass, UninitPass};
use crate::kani_middle::transform::check_values::ValidValuePass;
use crate::kani_middle::transform::clone::{ClonableGlobalPass, ClonableTransformPass};
use crate::kani_middle::transform::contracts::{AnyModifiesPass, FunctionWithContractPass};
use crate::kani_middle::transform::kani_intrinsics::IntrinsicGeneratorPass;
use crate::kani_middle::transform::loop_contracts::LoopContractPass;
use crate::kani_middle::transform::stubs::{ExternFnStubPass, FnStubPass, LoweredMethodStubPass};
use crate::kani_queries::QueryDb;
use automatic::{AutomaticArbitraryPass, AutomaticHarnessPass};
use dump_mir_pass::DumpMirPass;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::Body;
use rustc_public::mir::mono::{Instance, MonoItem};
use std::collections::HashMap;
use std::fmt::Debug;

use crate::kani_middle::attributes::KaniAttributes;
use crate::kani_middle::transform::rustc_intrinsics::RustcIntrinsicsPass;
pub(crate) use internal_mir::RustcInternalMir;
pub(crate) use loop_contracts::{ExtractedLoopInvariant, get_loop_invariants};
use rustc_public::CrateDef;
use rustc_public::rustc_internal;
use std::cell::RefCell;
use std::panic::{AssertUnwindSafe, catch_unwind};

mod array_iter;
mod automatic;
pub(crate) mod body;
mod check_uninit;
mod check_values;
mod contracts;
mod contracts_frame;
mod dump_mir_pass;
pub(crate) mod inline;
mod internal_mir;
mod kani_intrinsics;
pub(crate) mod loop_contracts;
mod range_iter;
mod range_iter_transform;
mod rustc_intrinsics;
mod simple_str_iter;
mod stubs;

/// Object used to retrieve a transformed instance body.
/// The transformations to be applied may be controlled by user options.
///
/// The order however is always the same, we run optimizations first, and instrument the code
/// after.
#[derive(Debug)]
pub(crate) struct BodyTransformation {
    /// The passes that may change the function body according to harness configuration.
    /// The stubbing passes should be applied before so user stubs take precedence.
    stub_passes: Vec<Box<dyn ClonableTransformPass>>,
    /// The passes that may add safety checks to the function body.
    inst_passes: Vec<Box<dyn ClonableTransformPass>>,
    /// Cache transformation results.
    cache: HashMap<Instance, TransformationResult>,
}

impl BodyTransformation {
    pub(crate) fn new(queries: &QueryDb, tcx: TyCtxt, unit: &CodegenUnit) -> Self {
        let mut transformer = BodyTransformation {
            stub_passes: vec![],
            inst_passes: vec![],
            cache: Default::default(),
        };
        let safety_check_type = CheckType::new_safety_check_assert_assume(queries);
        let unsupported_check_type = CheckType::new_unsupported_check_assert_assume_false(queries);
        // This has to come first, since creating harnesses affects later stubbing and contract passes.
        transformer.add_pass(queries, AutomaticHarnessPass::new(queries));
        transformer.add_pass(queries, AutomaticArbitraryPass::new(unit, queries));
        transformer.add_pass(queries, FnStubPass::new(&unit.stubs));
        transformer.add_pass(queries, ExternFnStubPass::new(&unit.stubs));
        transformer.add_pass(queries, LoweredMethodStubPass::new(&unit.stubs));
        transformer.add_pass(queries, FunctionWithContractPass::new(tcx, queries, unit));
        // This has to come after the contract pass since we want this to only replace the closure
        // body that is relevant for this harness.
        transformer.add_pass(queries, AnyModifiesPass::new(tcx, queries, unit));
        // Transform array for-loops to indexed loops (before other instrumentation).
        transformer.add_pass(queries, array_iter::ArrayIterUnrollPass::new());
        // Transform range for-loops to explicit index loops (before other instrumentation).
        transformer.add_pass(queries, range_iter::RangeIterUnrollPass::new());
        // Rewrite direct str::chars()/bytes().nth(...) chains to indexed helpers before CHC
        // sees iterator-state datatypes.
        transformer.add_pass(queries, simple_str_iter::SimpleStrIterPass::new());
        transformer.add_pass(
            queries,
            ValidValuePass {
                safety_check_type,
                unsupported_check_type: unsupported_check_type.clone(),
            },
        );
        // Putting `UninitPass` after `ValidValuePass` makes sure that the code generated by
        // `UninitPass` does not get unnecessarily instrumented by valid value checks. However, it
        // would also make sense to check that the values are initialized before checking their
        // validity. In the future, it would be nice to have a mechanism to skip automatically
        // generated code for future instrumentation passes.
        transformer.add_pass(
            queries,
            UninitPass {
                // Since this uses demonic non-determinism under the hood, should not assume the assertion.
                safety_check_type: CheckType::new_safety_check_assert_no_assume(queries),
                unsupported_check_type: unsupported_check_type.clone(),
                mem_init_fn_cache: queries.kani_functions().clone(),
            },
        );
        transformer.add_pass(queries, IntrinsicGeneratorPass::new(unsupported_check_type, queries));
        transformer.add_pass(queries, LoopContractPass::new(tcx, queries, unit));
        transformer.add_pass(queries, RustcIntrinsicsPass::new(queries));
        transformer
    }

    /// Build a no-op transformer for unit tests that need a BodyTransformation
    /// instance without requiring full Kani hook/intrinsic discovery.
    #[cfg(test)]
    pub(crate) fn new_for_tests() -> Self {
        Self { stub_passes: vec![], inst_passes: vec![], cache: Default::default() }
    }

    /// Clear the transformation cache to reclaim memory.
    ///
    /// Call this between harness iterations to prevent unbounded memory growth.
    /// Each harness gets independent codegen, so cached bodies from previous
    /// harnesses are not reused. Part of #3075.
    pub(crate) fn clear_cache(&mut self) {
        self.cache.clear();
    }

    /// Equivalent to `body()`, but avoids cloning the returned `Body`.
    pub(crate) fn body_ref(&mut self, tcx: TyCtxt, instance: Instance) -> &Body {
        &self
            .cache
            .entry(instance)
            .or_insert_with(|| {
                // Transform and add to the cache if there's no existing entry.
                let mut body = instance.body().expect("instance should have body");

                for pass in self.stub_passes.iter_mut().chain(self.inst_passes.iter_mut()) {
                    let result = pass.transform(tcx, body, instance);
                    body = result.1;
                }

                TransformationResult(body)
            })
            .0
    }

    /// Retrieve the body of an instance. This does not apply global passes, but will retrieve the
    /// body after global passes running if they were previously applied.
    ///
    /// Note that this assumes that the instance does have a body since existing consumers already
    /// assume that. Use `instance.has_body()` to check if an instance has a body.
    pub(crate) fn body(&mut self, tcx: TyCtxt, instance: Instance) -> Body {
        self.body_ref(tcx, instance).clone()
    }

    fn add_pass<P: ClonableTransformPass + 'static>(&mut self, query_db: &QueryDb, pass: P) {
        if pass.is_enabled(query_db) {
            match P::transformation_type() {
                TransformationType::Instrumentation => self.inst_passes.push(Box::new(pass)),
                TransformationType::Stubbing => self.stub_passes.push(Box::new(pass)),
            }
        }
    }

    /// Snapshot this transformer for the CHC inline walker: same passes (with
    /// their CURRENT state — after reachability has transformed all reachable
    /// items, pass state like `FunctionWithContractPass::unused_closures` is
    /// final for the harness), but an EMPTY cache so only walker-fetched
    /// instances pay the transform cost.
    fn clone_for_walker(&self) -> Self {
        Self {
            stub_passes: self.stub_passes.clone(),
            inst_passes: self.inst_passes.clone(),
            cache: Default::default(),
        }
    }
}

thread_local! {
    /// Per-harness transformer snapshot for the CHC inline walker.
    ///
    /// The walker (codegen_call_fn_inline / codegen_call_virtual_inline) runs
    /// deep inside `ChcCtx`, which deliberately does not borrow `AYCtx` (the
    /// `mir_to_chc` unwind boundary in `codegen_chc_path` must not hold the
    /// `ay_ctx` borrow), so the live `&mut BodyTransformation` cannot be
    /// plumbed down. Instead `codegen_chc_path` installs a clone here for the
    /// duration of one harness translation.
    static WALKER_TRANSFORMER: RefCell<Option<BodyTransformation>> = const { RefCell::new(None) };
}

/// Scope guard that installs a [`BodyTransformation`] snapshot for the CHC
/// inline walker and uninstalls it on drop (including on unwind, so a panic
/// inside `mir_to_chc` cannot leak a stale transformer into the next harness).
pub(crate) struct WalkerTransformerScope {
    _private: (),
}

impl WalkerTransformerScope {
    pub(crate) fn install(transformer: &BodyTransformation) -> Self {
        WALKER_TRANSFORMER.with(|slot| {
            *slot.borrow_mut() = Some(transformer.clone_for_walker());
        });
        WalkerTransformerScope { _private: () }
    }
}

impl Drop for WalkerTransformerScope {
    fn drop(&mut self) {
        WALKER_TRANSFORMER.with(|slot| {
            slot.borrow_mut().take();
        });
    }
}

/// Fetch the TRANSFORMED body for `instance` for the CHC inline walker.
///
/// This is the walker's replacement for raw `instance.body()`: raw bodies
/// bypass the kani_middle transform pipeline, so inside walked contract chains
/// `kani_contract_mode()` stays the macro dummy ORIGINAL=0 and every walked
/// ensures/requires check dispatches to the dead arm (vacuous). Routing the
/// fetch through [`BodyTransformation`] gives the walker the same
/// mode-dispatched wrappers, stubs, and rewrites the non-inline codegen lane
/// consumes.
///
/// Behavior:
/// - No walker transformer installed (unit tests, standalone `ChcCtx` probes):
///   fall back to the raw body — identical to the previous behavior.
/// - `instance` has no body: `None` (mirrors raw `instance.body()`).
/// - `instance` is NOT contract-relevant (no contract attrs on it or on the
///   non-closure ancestor of a closure chain): raw body — identical to the
///   pre-keystone behavior. Only contract chains NEED the transformed view;
///   routing arbitrary stdlib/closure callees through the transform pipeline
///   perturbs their encoding (the `loop_assigns_for_ptr_fail` regression: a
///   transformed `as_ptr` collapsed the clause-tuple path, orphan-pruning
///   every error rule into a degenerate `(rule (=> false error))` false Safe).
/// - A transform pass panics (e.g. an out-of-unit shape a pass does not
///   expect): `None`, FAIL-CLOSED — the walker treats the callee as body-less
///   and takes its existing fresh-symbolic fallback + demotion path instead of
///   silently walking an untransformed (vacuous-mode) body.
pub(crate) fn walker_transformed_body(tcx: TyCtxt, instance: Instance) -> Option<Body> {
    WALKER_TRANSFORMER.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(transformer) = slot.as_mut() else {
            return instance.body();
        };
        // Out-of-scope fetches take the RAW route. Note `has_body()` false
        // does NOT imply raw `body()` is None (shims — e.g. the Fn
        // calling-convention shim — report no body yet materialize one), so
        // this must be `instance.body()`, never a forced None (tupled_closure
        // regression: a None here degraded the Fn::call shim inline to an
        // inferable predicate).
        if !walker_wants_transformed(tcx, instance) {
            return instance.body();
        }
        // Contract-relevant but the transform pipeline cannot run (no body to
        // transform): FAIL-CLOSED. Walking the raw body here would walk the
        // vacuous-mode dummy (kani_contract_mode()=ORIGINAL=0) and silently
        // pass every contract check — fail_missing_recursion_attr regression:
        // the recursive CHECK-mode chain false-proved SAFE in 219ms where
        // baseline held an honest demotion-carried FAILED.
        if !instance.has_body() {
            return None;
        }
        catch_unwind(AssertUnwindSafe(|| transformer.body(tcx, instance))).ok()
    })
}

/// Scope gate for [`walker_transformed_body`]: does the walker NEED the
/// transformed view of this instance?
///
/// True only for contract-relevant bodies, where the transform pipeline's
/// `FunctionWithContractPass::set_mode` turns the `kani_contract_mode()` macro
/// dummy into the real CHECK/REPLACE mode literal:
/// - the contracted function itself (its transformed body carries the contract
///   mode dispatch), and
/// - closures generated under a contracted function (check/replace/ensures
///   closures — the same ancestry walk as the codegen-side
///   `is_contract_machinery_def`).
///
/// Everything else (stdlib helpers, plain closures, ordinary callees) walks
/// the RAW body, exactly as before the transformed-fetch keystone.
fn walker_wants_transformed(tcx: TyCtxt, instance: Instance) -> bool {
    let def_id = rustc_internal::internal(tcx, instance.def.def_id());
    if KaniAttributes::for_item(tcx, def_id).has_contract() {
        return true;
    }
    let mut ancestor = def_id;
    while tcx.is_closure_like(ancestor) {
        let Some(parent) = tcx.opt_parent(ancestor) else {
            return false;
        };
        ancestor = parent;
    }
    ancestor != def_id && KaniAttributes::for_item(tcx, ancestor).has_contract()
}

/// The type of transformation that a pass may perform.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) enum TransformationType {
    /// Should only add assertion checks to ensure the program is correct.
    Instrumentation,
    /// Apply some sort of stubbing.
    Stubbing,
}

/// A trait to represent transformation passes that can be used to modify the body of a function.
pub(crate) trait TransformPass: Debug {
    /// The type of transformation that this pass implements.
    fn transformation_type() -> TransformationType
    where
        Self: Sized;

    fn is_enabled(&self, query_db: &QueryDb) -> bool
    where
        Self: Sized;

    /// Run a transformation pass in the function body.
    fn transform(&mut self, tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body);
}

/// A trait to represent transformation passes that operate on the whole codegen unit.
pub(crate) trait GlobalPass: Debug {
    fn is_enabled(&self, query_db: &QueryDb) -> bool
    where
        Self: Sized;

    /// Run a transformation pass on the whole codegen unit, returning a bool
    /// for whether modifications were made to the MIR that could affect reachability.
    fn transform(
        &mut self,
        tcx: TyCtxt,
        call_graph: &CallGraph,
        starting_items: &[MonoItem],
        instances: Vec<Instance>,
        transformer: &mut BodyTransformation,
    ) -> bool;
}

#[derive(Clone, Debug)]
/// The [Body] resulting from applying all transformations.
struct TransformationResult(Body);

#[derive(Clone)]
pub(crate) struct GlobalPasses {
    /// The passes that operate on the whole codegen unit, they run after all previous passes are
    /// done.
    global_passes: Vec<Box<dyn ClonableGlobalPass>>,
}

impl GlobalPasses {
    pub(crate) fn new(queries: &QueryDb, tcx: TyCtxt) -> Self {
        let mut global_passes = GlobalPasses { global_passes: vec![] };
        global_passes.add_global_pass(
            queries,
            DelayedUbPass::new(
                CheckType::new_safety_check_assert_assume(queries),
                CheckType::new_unsupported_check_assert_assume_false(queries),
                queries,
            ),
        );
        global_passes.add_global_pass(queries, DumpMirPass::new(tcx));
        global_passes
    }

    fn add_global_pass<P: ClonableGlobalPass + 'static>(&mut self, query_db: &QueryDb, pass: P) {
        if pass.is_enabled(query_db) {
            self.global_passes.push(Box::new(pass));
        }
    }

    /// Run all global passes and store the results in a cache that can later be queried by `body`.
    /// Returns a boolean for if a pass has modified the MIR bodies.
    pub(crate) fn run_global_passes(
        &mut self,
        transformer: &mut BodyTransformation,
        tcx: TyCtxt,
        starting_items: &[MonoItem],
        instances: Vec<Instance>,
        call_graph: CallGraph,
    ) -> bool {
        let mut modified = false;
        for global_pass in &mut self.global_passes {
            modified |= global_pass.transform(
                tcx,
                &call_graph,
                starting_items,
                instances.clone(),
                transformer,
            );
        }
        modified
    }
}

mod clone {
    //! This is all just machinery to implement `Clone` for a `Box<dyn TransformPass + Clone>`.
    //!
    //! To avoid circular reasoning, we use two traits that can each clone into a dyn of the other, and since
    //! we set both up to have blanket implementations for all `T: TransformPass + Clone`, the compiler pieces them together properly
    //! and we can implement `Clone` directly using the pair!

    /// Builds a new dyn compatible wrapper trait that's essentially equivalent to extending
    /// `$extends` with `Clone`. Requires an ident for an intermediate trait for avoiding cycles
    /// in the implementation.
    macro_rules! implement_clone {
        ($new_trait_name: ident, $intermediate_trait_name: ident, $extends: path) => {
            #[allow(private_interfaces)]
            pub(crate) trait $new_trait_name: $extends {
                fn clone_there(&self) -> Box<dyn $intermediate_trait_name>;
            }

            impl Clone for Box<dyn $new_trait_name> {
                fn clone(&self) -> Self {
                    self.clone_there().clone_back()
                }
            }

            #[allow(private_interfaces)]
            impl<T: $extends + Clone + 'static> $new_trait_name for T {
                fn clone_there(&self) -> Box<dyn $intermediate_trait_name> {
                    Box::new(self.clone())
                }
            }

            trait $intermediate_trait_name {
                fn clone_back(&self) -> Box<dyn $new_trait_name>;
            }

            impl<T: $extends + Clone + 'static> $intermediate_trait_name for T {
                fn clone_back(&self) -> Box<dyn $new_trait_name> {
                    Box::new(self.clone())
                }
            }
        };
    }

    implement_clone!(
        ClonableTransformPass,
        ClonableTransformPassMid,
        crate::kani_middle::transform::TransformPass
    );
    implement_clone!(
        ClonableGlobalPass,
        ClonableGlobalPassMid,
        crate::kani_middle::transform::GlobalPass
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn test_transformation_type_stubbing_eq() {
        assert_eq!(TransformationType::Stubbing, TransformationType::Stubbing);
    }

    #[test]
    fn test_transformation_type_instrumentation_eq() {
        assert_eq!(TransformationType::Instrumentation, TransformationType::Instrumentation);
    }

    #[test]
    fn test_transformation_type_variants_distinct() {
        assert_ne!(TransformationType::Stubbing, TransformationType::Instrumentation);
    }

    #[test]
    fn test_transformation_type_copy() {
        let t = TransformationType::Stubbing;
        let copied = t;
        assert_eq!(t, copied);
    }

    #[test]
    fn test_transformation_type_debug_format() {
        let dbg = format!("{:?}", TransformationType::Instrumentation);
        assert!(dbg.contains("Instrumentation"));
        let dbg2 = format!("{:?}", TransformationType::Stubbing);
        assert!(dbg2.contains("Stubbing"));
    }

    #[test]
    fn test_transformation_type_hash_distinct() {
        let mut set = HashSet::new();
        set.insert(TransformationType::Stubbing);
        set.insert(TransformationType::Instrumentation);
        assert_eq!(set.len(), 2, "both variants should hash distinctly");
    }

    #[test]
    fn test_transformation_type_hash_same() {
        let mut set = HashSet::new();
        set.insert(TransformationType::Stubbing);
        set.insert(TransformationType::Stubbing);
        assert_eq!(set.len(), 1, "same variant should hash identically");
    }

    #[test]
    fn test_transformation_result_debug() {
        fn assert_clone_debug<T: Clone + std::fmt::Debug>() {}
        assert_clone_debug::<TransformationResult>();
    }
}
