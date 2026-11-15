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
use crate::callee_body::CalleeBody;
use crate::kani_middle::codegen_units::CodegenUnit;
use crate::kani_middle::reachability::CallGraph;
use crate::kani_middle::transform::body::CheckType;
use crate::kani_middle::transform::check_uninit::{DelayedUbPass, UninitPass};
use crate::kani_middle::transform::check_values::ValidValuePass;
use crate::kani_middle::transform::clone::{ClonableGlobalPass, ClonableTransformPass};
use crate::kani_middle::transform::contracts::{AnyModifiesPass, FunctionWithContractPass};
use crate::kani_middle::transform::kani_intrinsics::IntrinsicGeneratorPass;
use crate::kani_middle::transform::loop_contracts::LoopContractPass;
use crate::kani_middle::transform::stubs::{CallSiteStubPass, FnStubPass, LoweredMethodStubPass};
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
mod contracts_mutual_recursion;
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
pub(crate) use stubs::stubbed_callee_instance;

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
    /// The unit's stub map, `from -> to`.
    ///
    /// Kept whole rather than as a bool so the obligation-free walk can RESOLVE
    /// through it and see the same program the encoder encodes. It used to be
    /// `has_stubs: bool` and the walk simply refused any stubbed unit, which
    /// was sound but cost `tests/kani/Stubbing/glob_{cycle,path}.rs`.
    stubs: crate::kani_middle::codegen_units::Stubs,
    /// The passes that may add safety checks to the function body.
    inst_passes: Vec<Box<dyn ClonableTransformPass>>,
    /// Cache transformation results.
    cache: HashMap<Instance, TransformationResult>,
}

/// The smallest unwind bound a harness of `unit` declares (`--unwind`, else
/// its `#[kani::unwind(U)]`, else `--default-unwind`) while Kani's unwinding
/// assertions are on; `None` when none does. A pass that removes a loop must
/// keep the loop's unwinding assertion under it (`array_iter.rs`).
fn unit_declared_unwind(queries: &QueryDb, tcx: TyCtxt, unit: &CodegenUnit) -> Option<u32> {
    let args = queries.args();
    if args.no_default_checks || args.no_unwinding_checks {
        return None;
    }
    unit.harnesses
        .iter()
        .filter_map(|harness| {
            let attributes =
                crate::kani_middle::attributes::KaniAttributes::for_instance(tcx, *harness);
            let declared = if attributes.is_proof_harness() {
                attributes.harness_attributes().unwind_value
            } else {
                None
            };
            args.unwind.or(declared).or(args.default_unwind)
        })
        .min()
}

/// The unwind bound `harness` runs under with Kani's unwinding assertions on
/// (`--unwind`, then `#[kani::unwind(U)]`, then `--default-unwind`), or `None`
/// (see [`BodyTransformation::set_harness_declared_unwind`]).
pub(crate) fn harness_declared_unwind(
    queries: &QueryDb,
    harness_unwind: Option<u32>,
) -> Option<u32> {
    let args = queries.args();
    if args.no_default_checks || args.no_unwinding_checks {
        return None;
    }
    args.unwind.or(harness_unwind).or(args.default_unwind)
}

impl BodyTransformation {
    pub(crate) fn new(queries: &QueryDb, tcx: TyCtxt, unit: &CodegenUnit) -> Self {
        let mut transformer = BodyTransformation {
            stub_passes: vec![],
            inst_passes: vec![],
            cache: Default::default(),
            // Recorded because the obligation-free certificate cannot resolve
            // callees on a stubbed program: it walks raw `Instance::resolve`,
            // which returns the ORIGINAL body. See `has_stubs`.
            stubs: unit.stubs.clone(),
        };
        let safety_check_type = CheckType::new_safety_check_assert_assume(queries);
        let unsupported_check_type = CheckType::new_unsupported_check_assert_assume_false(queries);
        // This has to come first, since creating harnesses affects later stubbing and contract passes.
        transformer.add_pass(queries, AutomaticHarnessPass::new(queries));
        transformer.add_pass(queries, AutomaticArbitraryPass::new(unit, queries));
        transformer.add_pass(queries, FnStubPass::new(&unit.stubs));
        transformer.add_pass(queries, CallSiteStubPass::new(&unit.stubs));
        transformer.add_pass(queries, LoweredMethodStubPass::new(&unit.stubs));
        transformer.add_pass(queries, FunctionWithContractPass::new(tcx, queries, unit));
        // This has to come after the contract pass since we want this to only replace the closure
        // body that is relevant for this harness.
        transformer.add_pass(queries, AnyModifiesPass::new(tcx, queries, unit));
        // Transform array for-loops to indexed loops (before other instrumentation).
        transformer.add_pass(
            queries,
            array_iter::ArrayIterUnrollPass::with_declared_unwind(unit_declared_unwind(
                queries, tcx, unit,
            )),
        );
        // Transform range for-loops to explicit index loops (before other instrumentation).
        transformer.add_pass(queries, range_iter::RangeIterUnrollPass::new());
        // Rewrite direct str::chars()/bytes().nth(...) chains to indexed helpers before CHC
        // sees iterator-state datatypes.
        transformer.add_pass(
            queries,
            simple_str_iter::SimpleStrIterPass::with_declared_unwind(unit_declared_unwind(
                queries, tcx, unit,
            )),
        );
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
        Self {
            stub_passes: vec![],
            inst_passes: vec![],
            cache: Default::default(),
            stubs: Default::default(),
        }
    }

    /// Re-key the loop-removing passes on the bound of the harness about to
    /// be translated (`harness_declared_unwind`), and drop every body
    /// transformed under the previous one.
    ///
    /// The passes start at the unit's smallest bound (`unit_declared_unwind`),
    /// which is sound for every harness of the unit but costs a harness with a
    /// larger bound a rewrite Kani's semantics allow: `"abcdefgh".chars().nth(4)`
    /// under `#[kani::unwind(8)]` kept the std loop, and failed, because another
    /// harness of the same file declared `unwind(3)` (walker fail-closed
    /// review 6 round 3, `str_chars_nth_unwind_dual.rs`
    /// `n1_chars_nth_u8_safe`). Every body a harness runs, a callee's
    /// included, runs under that harness's bound, and the cache is per
    /// harness (`clear_cache`), so the harness's own bound is exact.
    pub(crate) fn set_harness_declared_unwind(&mut self, declared_unwind: Option<u32>) {
        self.cache.clear();
        for pass in self.stub_passes.iter_mut().chain(self.inst_passes.iter_mut()) {
            pass.set_harness_declared_unwind(declared_unwind);
        }
    }

    /// Does this unit stub anything?
    pub(crate) fn has_stubs(&self) -> bool {
        !self.stubs.is_empty()
    }

    /// A copy of the stub map for the obligation-free walk.
    pub(crate) fn stub_map_for_walk(&self) -> crate::kani_middle::codegen_units::Stubs {
        self.stubs.clone()
    }

    /// The stub replacement for `fn_def`, if this unit stubs it.
    ///
    /// The obligation-free walk resolves callees through this so it inspects
    /// the STUB's body, not the original's. Without it the walk answered about
    /// a different program: `#[kani::stub(clean, panicking)]` made it see
    /// `clean`, find nothing to prove, and CERTIFY a harness whose emitted
    /// check FAILS.
    pub(crate) fn stub_target(
        &self,
        fn_def: rustc_public::ty::FnDef,
    ) -> Option<rustc_public::ty::FnDef> {
        self.stubs.get(&fn_def).copied()
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
                let mut body = crate::callee_body::transform_input_body(&instance)
                    .expect("instance should have body");

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

    /// Like [`body`], but DECLINES instead of panicking when the instance has
    /// no MIR at all.
    ///
    /// `body_ref` unwraps `instance.body()` with an `expect`, so every caller
    /// that reaches it with a body-less instance takes down the compiler.
    /// `AYCtx::body_or_instance_body` advertises `Option`, and its callers
    /// honour that — `try_inline_small_instance_call` writes
    /// `body_or_instance_body(instance)?` and declines gracefully — but the
    /// transformer arm wrapped this in `Some(..)`, so the `None` the contract
    /// promises could never actually be produced. The panic was a contract
    /// violation one frame below the code that respected it.
    ///
    /// The instances that hit this are `#[rustc_intrinsic]`s with no fallback
    /// body (`float_to_int_unchecked`, `arith_offset`, `caller_location`);
    /// measured, they are all `kind=Intrinsic, intrinsic=true, foreign=false`
    /// from `core`.
    ///
    /// Keyed on `instance.body().is_none()`, NOT on `has_body()`:
    /// `has_body() == false` does not imply `body() == None` — a shim reports
    /// no body yet still materializes one — so testing `has_body()` here would
    /// decline for instances that can in fact be inlined.
    ///
    /// Declining does NOT drop the call's obligations. The `Call` terminator
    /// survives, dispatch falls through to `unsupported_call_successors`, and
    /// that path calls `unsupported_with_fallback`, which bumps the
    /// per-harness demotion counter — so a harness containing one of these can
    /// never come back SUCCESSFUL. Anything implemented here must keep going
    /// through that path: plain `unsupported()` records diagnostics and bumps
    /// no counter, which would not demote, and that is the false-proof shape.
    pub(crate) fn try_body(&mut self, tcx: TyCtxt, instance: Instance) -> Option<Body> {
        if !self.cache.contains_key(&instance) {
            // Resolve BEFORE touching the cache, so a decline leaves no entry
            // behind to poison a later lookup.
            let mut body = instance.callee_body()?;
            for pass in self.stub_passes.iter_mut().chain(self.inst_passes.iter_mut()) {
                body = pass.transform(tcx, body, instance).1;
            }
            self.cache.insert(instance, TransformationResult(body));
        }
        self.cache.get(&instance).map(|result| result.0.clone())
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
            stubs: self.stubs.clone(),
        }
    }
}

thread_local! {
    /// The stub map of the unit whose harness the CHC encoder is translating,
    /// installed with [`WalkerTransformerScope`] when the unit stubs anything
    /// (`#[kani::stub]`). Read by [`stub_aware_instance_body`], which every raw
    /// callee-body fetch goes through (`CalleeBody::callee_body`). A separate
    /// slot from `WALKER_TRANSFORMER`, which [`walker_transformed_body`] holds
    /// mutably borrowed while it fetches a raw body.
    static UNIT_STUBS: RefCell<Option<std::rc::Rc<crate::kani_middle::codegen_units::Stubs>>> =
        const { RefCell::new(None) };
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
        UNIT_STUBS.with(|slot| {
            *slot.borrow_mut() =
                transformer.has_stubs().then(|| std::rc::Rc::new(transformer.stubs.clone()));
        });
        WalkerTransformerScope { _private: () }
    }
}

impl Drop for WalkerTransformerScope {
    fn drop(&mut self) {
        WALKER_TRANSFORMER.with(|slot| {
            slot.borrow_mut().take();
        });
        UNIT_STUBS.with(|slot| {
            slot.borrow_mut().take();
        });
    }
}

/// Test support: install `stubs` as the unit stub map
/// [`stub_aware_instance_body`] applies, without a transformer, until drop.
#[cfg(test)]
pub(crate) struct UnitStubsTestScope {
    _private: (),
}

#[cfg(test)]
impl UnitStubsTestScope {
    pub(crate) fn install(stubs: crate::kani_middle::codegen_units::Stubs) -> Self {
        UNIT_STUBS.with(|slot| *slot.borrow_mut() = Some(std::rc::Rc::new(stubs)));
        UnitStubsTestScope { _private: () }
    }
}

#[cfg(test)]
impl Drop for UnitStubsTestScope {
    fn drop(&mut self) {
        UNIT_STUBS.with(|slot| {
            slot.borrow_mut().take();
        });
    }
}

/// The installed unit stub map, when the unit stubs anything.
fn installed_unit_stubs() -> Option<std::rc::Rc<crate::kani_middle::codegen_units::Stubs>> {
    UNIT_STUBS.with(|slot| slot.borrow().clone())
}

/// A semantic shortcut must preserve every transitive replacement, not just
/// a stub of its outer entry point.
pub(crate) fn unit_has_stubs() -> bool {
    UNIT_STUBS.with(|slot| slot.borrow().as_ref().is_some_and(|stubs| !stubs.is_empty()))
}

/// Whether the current harness replaces this resolved instance. An exact
/// semantic shortcut must not substitute the original body for a unit stub.
pub(crate) fn instance_has_unit_stub(instance: &Instance) -> bool {
    installed_unit_stubs().is_some_and(|stubs| {
        let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)) =
            instance.ty().kind()
        else {
            return true;
        };
        stubs.contains_key(&def)
    })
}

/// `instance`'s body AS THE UNIT RUNS IT, for a raw callee-body fetch
/// (`CalleeBody::callee_body`): with the unit's stubs (`#[kani::stub]`)
/// applied when a CHC harness translation installed them
/// ([`WalkerTransformerScope`]), else the plain `instance.body()`.
///
/// Stubbing is a program transformation the harness asks for, and the pipeline
/// applies it to every body it transforms. The CHC inline walker and the
/// statement path's raw fetches (drop glue, `Fn`-trait and fn-pointer targets,
/// candidate bodies) read MIR outside the pipeline, so without this they saw
/// the unstubbed program: a stubbed function called from a walked body kept
/// its original meaning, and a path-keyed model of a stubbed standard-library
/// function claimed the call before any body fetch
/// (`tools/soundness-duals/stub_modelled_std_dual.rs`,
/// `walker_extern_stub_dual.rs`). Applied here:
/// - `FnStubPass`: a stubbed `instance` runs the stub's body
///   ([`stubs::stub_replacement_instance`]);
/// - `CallSiteStubPass`: every call site and fn-item operand naming a stubbed
///   function names the stub ([`stubs::rewrite_stubbed_call_sites`]), so no
///   handler keyed on the original's path claims it;
/// - `LoweredMethodStubPass`: a lowered `<[T]>::len` the unit stubs calls the
///   stub.
///
/// The instrumentation passes are NOT applied: the walker's raw route exists
/// to keep them off ordinary callees (see [`walker_transformed_body`]).
pub(crate) fn stub_aware_instance_body(instance: &Instance) -> Option<Body> {
    stubs::unit_instance_body(installed_unit_stubs().as_deref(), instance)
}

/// [`stub_aware_instance_body`] for a POLYMORPHIC def's body
/// (`CalleeBody::callee_body` on a `FnDef`).
pub(crate) fn stub_aware_def_body(def: &rustc_public::ty::FnDef) -> Option<Body> {
    stubs::unit_def_body(installed_unit_stubs().as_deref(), def)
}

/// The installed unit stubs' call-site rewrites applied to a body fetched
/// another way (a coroutine's `body()`); the body unchanged when the unit
/// stubs nothing.
pub(crate) fn apply_unit_stubs(body: Body) -> Body {
    match installed_unit_stubs() {
        Some(unit_stubs) => apply_stubs_to_body(&unit_stubs, body),
        None => body,
    }
}

fn apply_stubs_to_body(unit_stubs: &crate::kani_middle::codegen_units::Stubs, body: Body) -> Body {
    stubs::apply_call_site_stubs(unit_stubs, body)
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
/// - `instance` is a function the unit STUBS: the transformed body, which
///   `FnStubPass` makes the stub's ([`transformer_stubs`]); `None` when the
///   original has no body (an extern stub), fail-closed.
/// - A transform pass panics (e.g. an out-of-unit shape a pass does not
///   expect): `None`, FAIL-CLOSED — the walker treats the callee as body-less
///   and takes its existing fresh-symbolic fallback + demotion path instead of
///   silently walking an untransformed (vacuous-mode) body.
pub(crate) fn walker_transformed_body(tcx: TyCtxt, instance: Instance) -> Option<Body> {
    WALKER_TRANSFORMER.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(transformer) = slot.as_mut() else {
            return instance.callee_body();
        };
        // Out-of-scope fetches take the RAW route. Note `has_body()` false
        // does NOT imply raw `body()` is None (shims — e.g. the Fn
        // calling-convention shim — report no body yet materialize one), so
        // this must be `instance.body()`, never a forced None (tupled_closure
        // regression: a None here degraded the Fn::call shim inline to an
        // inferable predicate).
        if !transformer_stubs(transformer, instance) && !walker_wants_transformed(tcx, instance) {
            return instance.callee_body();
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
        match catch_unwind(AssertUnwindSafe(|| transformer.body(tcx, instance))) {
            Ok(body) => Some(body),
            Err(payload) => {
                // A translation timeout must reach the per-harness boundary,
                // not turn into "no body".
                let _ = crate::codegen_ay::translation_deadline::resume_if_timeout(payload);
                None
            }
        }
    })
}

/// The stub map of the unit the CHC walker is encoding (`#[kani::stub]`),
/// from the installed walker transformer; empty when none is installed (unit
/// tests, standalone `ChcCtx` probes) or the unit stubs nothing.
///
/// The walker's obligation scans resolve callees through it
/// (`obligation_free_walk::resolve_through_stubs`), so they inspect the body
/// the unit runs, not the original a stub replaces.
pub(crate) fn walker_stub_map() -> crate::kani_middle::codegen_units::Stubs {
    WALKER_TRANSFORMER.with(|slot| {
        slot.borrow()
            .as_ref()
            .map(|transformer| transformer.stub_map_for_walk())
            .unwrap_or_default()
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
///
/// NOT opted in, on purpose: `kani_register_loop_contract`. Its declared body
/// is `{ true }`; `LoopContractPass` swaps in a call of the invariant closure.
/// Walking that swapped body (tried in 290ac7cb8, reverted before landing)
/// made the walker EVALUATE the invariant at every legacy register call, but
/// the walker reads a closure's by-reference captures as addresses, and the
/// loop-contract macro lowers `while guard` to
/// `while kani_register_loop_contract(&inv, _) && guard`: a garbage invariant
/// value silently exited the loop. Measured against Kani, that proved bug
/// harnesses and made a safe one FAIL Genuine
/// (tools/soundness-duals/loop_contract_register_walk_dual.rs). Opt it in only
/// once the walker loads through by-reference captures AND the walked value
/// feeds a check rather than the loop-exit condition. Design 5 checks the legacy
/// latch without it: `LoopContractPass::instrument_declined_loops` evaluates the
/// invariant through the closure's `Fn::call` shim next to the register call and
/// feeds only an assert-only check, and the register body stays `{ true }`.
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

/// Does `transformer`'s unit stub `instance` (`#[kani::stub(f, g)]`)?
///
/// [`walker_transformed_body`] opts such an instance in: `FnStubPass` replaces
/// `f`'s body with `g`'s, and the raw fetch walked `f`'s own body instead, so
/// a walked `dyn` method calling a stubbed `clean` lost the stub's `assert!`
/// and the harness proved (`walker_stub_dual.rs`).
fn transformer_stubs(transformer: &BodyTransformation, instance: Instance) -> bool {
    let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)) =
        instance.ty().kind()
    else {
        return false;
    };
    transformer.stub_target(def).is_some()
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

    /// The unwind bound of the harness whose bodies the pass transforms next,
    /// with Kani's unwinding assertions on (`None` when it declares none, or
    /// the assertions are off). Only a pass that removes a loop Kani unwinds
    /// reads it ([`BodyTransformation::set_harness_declared_unwind`]).
    fn set_harness_declared_unwind(&mut self, _declared_unwind: Option<u32>) {}
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
